import argparse
import hashlib
import json
import os
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_BUNDLE_PATH = REPO_ROOT / "lean_exports_bundle.tar.gz"
DEFAULT_ENC_PATH = REPO_ROOT / "lean_exports_bundle.enc"
DEFAULT_CERT_PATH = REPO_ROOT / "lean_exports" / "security_certificate.json"
DEFAULT_SEED = "petruska_fenix_sovereign_core_2026_millennium"


def _derive_key_stream(seed: str) -> bytes:
    return hashlib.sha256(seed.encode("utf-8")).digest()


def encrypt_bundle(
    bundle_path: str | os.PathLike | None = None,
    enc_path: str | os.PathLike | None = None,
    cert_path: str | os.PathLike | None = None,
    seed: str = DEFAULT_SEED,
    verbose: bool = False,
) -> dict[str, Any]:
    """Aplica transformación XOR cíclica con clave derivada por SHA-256 y genera certificado.

    Nota: es una transformación reversible de empaquetado/ofuscación local con verificación
    de integridad SHA-256, no un cifrado criptográfico fuerte para secretos críticos.
    """
    src = Path(bundle_path) if bundle_path is not None else DEFAULT_BUNDLE_PATH
    dst = Path(enc_path) if enc_path is not None else DEFAULT_ENC_PATH
    cert = Path(cert_path) if cert_path is not None else DEFAULT_CERT_PATH

    if not src.exists() or not src.is_file():
        raise FileNotFoundError(f"El bundle de entrada no existe: {src}")

    data = src.read_bytes()
    file_hash = hashlib.sha256(data).hexdigest()
    key_stream = _derive_key_stream(seed)

    transformed = bytes(b ^ key_stream[i % len(key_stream)] for i, b in enumerate(data))
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_bytes(transformed)

    security_meta = {
        "sha256_original": file_hash,
        "source_file": src.name,
        "output_file": dst.name,
        "transform_protocol": "Petruska-XOR-HashDerivation",
        "status": "PACKAGED_LOCALLY",
    }
    cert.parent.mkdir(parents=True, exist_ok=True)
    cert.write_text(json.dumps(security_meta, indent=4, ensure_ascii=False), encoding="utf-8")

    result = {
        "input_bundle": str(src),
        "encrypted_bundle": str(dst),
        "certificate_path": str(cert),
        "sha256_original": file_hash,
        "bytes_processed": len(data),
    }

    if verbose:
        print(f"-> Bundle procesado: {dst}")
        print(f"-> Certificado generado: {cert}")
        print(f"-> SHA-256 original: {file_hash}")

    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Empaqueta un archivo bundle con XOR derivado de SHA-256 y registra su hash."
    )
    parser.add_argument(
        "--bundle",
        default=str(DEFAULT_BUNDLE_PATH),
        help="Ruta al archivo bundle de entrada.",
    )
    parser.add_argument(
        "--out",
        dest="enc_path",
        default=str(DEFAULT_ENC_PATH),
        help="Ruta de salida del archivo empaquetado.",
    )
    parser.add_argument(
        "--cert",
        dest="cert_path",
        default=str(DEFAULT_CERT_PATH),
        help="Ruta de salida del certificado JSON de integridad.",
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
    summary = encrypt_bundle(
        bundle_path=args.bundle,
        enc_path=args.enc_path,
        cert_path=args.cert_path,
        seed=args.seed,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
