import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_ENC_PATH = REPO_ROOT / "lean_exports_bundle.enc"
DEFAULT_CERT_PATH = REPO_ROOT / "lean_exports" / "security_certificate.json"
DEFAULT_RESTORED_PATH = REPO_ROOT / "lean_exports_bundle_restored.tar.gz"
DEFAULT_SEED = "petruska_fenix_sovereign_core_2026_millennium"


def _derive_key_stream(seed: str) -> bytes:
    return hashlib.sha256(seed.encode("utf-8")).digest()


def decrypt_bundle(
    enc_path: str | os.PathLike | None = None,
    cert_path: str | os.PathLike | None = None,
    restored_path: str | os.PathLike | None = None,
    seed: str = DEFAULT_SEED,
    verbose: bool = False,
) -> dict[str, Any]:
    """Revierte la transformación XOR derivada de SHA-256 y verifica el hash original."""
    src = Path(enc_path) if enc_path is not None else DEFAULT_ENC_PATH
    cert = Path(cert_path) if cert_path is not None else DEFAULT_CERT_PATH
    dst = Path(restored_path) if restored_path is not None else DEFAULT_RESTORED_PATH

    if not src.exists() or not src.is_file():
        raise FileNotFoundError(f"No se encuentra el archivo empaquetado: {src}")
    if not cert.exists() or not cert.is_file():
        raise FileNotFoundError(f"No se encuentra el certificado de integridad: {cert}")

    security_meta = json.loads(cert.read_text(encoding="utf-8"))
    expected_hash = security_meta.get("sha256_original")
    if not expected_hash:
        raise ValueError(f"El certificado {cert} no contiene 'sha256_original'.")

    encrypted_bytes = src.read_bytes()
    key_stream = _derive_key_stream(seed)
    restored_bytes = bytes(
        b ^ key_stream[i % len(key_stream)] for i, b in enumerate(encrypted_bytes)
    )

    recovered_hash = hashlib.sha256(restored_bytes).hexdigest()
    integrity_ok = recovered_hash == expected_hash

    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_bytes(restored_bytes)

    result = {
        "encrypted_bundle": str(src),
        "certificate_path": str(cert),
        "restored_path": str(dst),
        "expected_sha256": expected_hash,
        "recovered_sha256": recovered_hash,
        "integrity_verified": integrity_ok,
    }

    if verbose:
        print(f"-> Archivo restaurado: {dst}")
        if integrity_ok:
            print(f"-> Integridad verificada (SHA-256 coincidente): {recovered_hash}")
        else:
            print(
                f"-> Advertencia: SHA-256 no coincide (esperado={expected_hash}, "
                f"obtenido={recovered_hash})"
            )

    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Restaura un bundle empaquetado con XOR y verifica su hash SHA-256."
    )
    parser.add_argument(
        "--enc",
        dest="enc_path",
        default=str(DEFAULT_ENC_PATH),
        help="Ruta al archivo empaquetado.",
    )
    parser.add_argument(
        "--cert",
        dest="cert_path",
        default=str(DEFAULT_CERT_PATH),
        help="Ruta al certificado JSON de integridad.",
    )
    parser.add_argument(
        "--out",
        dest="restored_path",
        default=str(DEFAULT_RESTORED_PATH),
        help="Ruta del archivo restaurado.",
    )
    parser.add_argument(
        "--seed",
        default=DEFAULT_SEED,
        help="Semilla para derivar la máscara XOR.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Imprime el resultado estructurado en JSON.",
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    summary = decrypt_bundle(
        enc_path=args.enc_path,
        cert_path=args.cert_path,
        restored_path=args.restored_path,
        seed=args.seed,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
