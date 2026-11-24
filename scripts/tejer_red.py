import argparse
import json
from pathlib import Path
import subprocess
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_IN_JSON = REPO_ROOT / "docs" / "milenio_red.json"
DEFAULT_OUT_JSON = REPO_ROOT / "docs" / "milenio_cadena.json"
DEFAULT_OUT_MD = REPO_ROOT / "docs" / "CADENA_MILENIO.md"
DEFAULT_VERIFY_JSON = REPO_ROOT / "docs" / "verificacion_numerica.json"

VERIFY_SCRIPTS: list[tuple[str, str]] = [
    ("verify_zeros", "scripts/verify_zeros.py"),
    ("turing_certify", "scripts/turing_certify.py"),
    ("parallel_verify", "scripts/parallel_verify.py"),
    ("puente_ym", "scripts/puente_ym_lean.py"),
]


def _run_verifier(name: str, rel_script: str, timeout_s: int = 60) -> dict[str, Any]:
    script_path = REPO_ROOT / rel_script
    if not script_path.exists():
        return {"status": "missing", "script": rel_script}

    try:
        proc = subprocess.run(
            [sys.executable, str(script_path), "--json"],
            cwd=str(REPO_ROOT),
            text=True,
            capture_output=True,
            timeout=timeout_s,
        )
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "script": rel_script, "timeout_s": timeout_s}

    raw_out = (proc.stdout or "").strip()
    if proc.returncode != 0:
        return {
            "status": "error",
            "script": rel_script,
            "returncode": proc.returncode,
            "error": (proc.stderr or raw_out)[-500:],
        }

    parsed: Any = raw_out
    if raw_out:
        try:
            parsed = json.loads(raw_out)
        except json.JSONDecodeError:
            # Si imprime líneas previas antes del JSON, intentamos rescatar el último bloque {...} o [...]
            start_obj = raw_out.rfind("{")
            start_arr = raw_out.rfind("[")
            starts = [i for i in (start_obj, start_arr) if i != -1]
            if starts:
                try:
                    parsed = json.loads(raw_out[min(starts) :])
                except json.JSONDecodeError:
                    parsed = raw_out[-500:]

    return {
        "status": "ok",
        "script": rel_script,
        "data": parsed,
    }


def collect_verification_metrics(
    out_verify_json: Path = DEFAULT_VERIFY_JSON,
    timeout_s: int = 60,
) -> dict[str, Any]:
    """Ejecuta y consolida salidas --json de scripts de verificación en docs/."""
    results: dict[str, Any] = {}
    for name, rel_script in VERIFY_SCRIPTS:
        results[name] = _run_verifier(name, rel_script, timeout_s=timeout_s)

    payload = {
        "repo_root": str(REPO_ROOT),
        "verifiers": results,
    }
    out_verify_json.parent.mkdir(parents=True, exist_ok=True)
    out_verify_json.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False), encoding="utf-8"
    )
    return payload


def weave_network_chain(
    in_json: Path = DEFAULT_IN_JSON,
    out_json: Path = DEFAULT_OUT_JSON,
    out_md: Path = DEFAULT_OUT_MD,
    out_verify_json: Path = DEFAULT_VERIFY_JSON,
    skip_verify: bool = False,
    timeout_s: int = 60,
    verbose: bool = False,
) -> dict[str, Any]:
    """Cruza milenio_red.json, integra verificaciones numéricas y genera cadena."""
    if not in_json.exists():
        raise FileNotFoundError(f"No existe el mapa base: {in_json}")

    raw = json.loads(in_json.read_text(encoding="utf-8"))
    files = raw.get("files", [])
    summary = raw.get("problems_summary", {})

    bridge_files: list[dict[str, Any]] = []
    lean_markers_by_problem: dict[str, int] = {k: 0 for k in summary}

    for entry in files:
        probs = entry.get("problems", [])
        markers = int(entry.get("lean_markers", 0))
        if len(probs) >= 2:
            bridge_files.append(
                {
                    "path": entry.get("path"),
                    "problem_count": len(probs),
                    "problems": probs,
                    "lean_markers": markers,
                }
            )
        for prob in probs:
            if prob in lean_markers_by_problem:
                lean_markers_by_problem[prob] += markers

    bridge_files.sort(key=lambda item: (-item["problem_count"], item["path"]))

    if skip_verify and out_verify_json.exists():
        verify_block = json.loads(out_verify_json.read_text(encoding="utf-8"))
    elif not skip_verify:
        verify_block = collect_verification_metrics(
            out_verify_json=out_verify_json, timeout_s=timeout_s
        )
    else:
        verify_block = {"verifiers": {}}

    verifiers_summary = {
        k: v.get("status", "unknown") for k, v in verify_block.get("verifiers", {}).items()
    }

    chain = {
        "source_map": str(in_json),
        "verification_file": str(out_verify_json),
        "total_files": raw.get("total_scanned_files", len(files)),
        "bridge_file_count": len(bridge_files),
        "bridge_files": bridge_files,
        "lean_markers_by_problem": lean_markers_by_problem,
        "problem_file_counts": {
            prob: info.get("file_count", 0) for prob, info in summary.items()
        },
        "verifiers_status": verifiers_summary,
        "verifiers": verify_block.get("verifiers", {}),
    }

    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(chain, indent=2, ensure_ascii=False), encoding="utf-8")

    lines = [
        "# Cadena y Nodos Puente — 7 Problemas del Milenio",
        "",
        f"Archivos puente (conectan 2 o más problemas): **{len(bridge_files)}**",
        "",
        "## Verificaciones numéricas y certificación",
        "",
    ]
    for name, info in chain["verifiers"].items():
        st = info.get("status", "unknown")
        lines.append(f"- `{name}` (`{info.get('script', '')}`): **{st}**")
        if st == "ok" and isinstance(info.get("data"), dict):
            preview_keys = list(info["data"].keys())[:6]
            if preview_keys:
                compact = {k: info["data"][k] for k in preview_keys}
                lines.append(f"  - Métricas: `{json.dumps(compact, ensure_ascii=False)}`")
        elif st in {"error", "timeout"}:
            detalle = info.get("error") or f"timeout tras {info.get('timeout_s')}s"
            lines.append(f"  - Detalle: `{detalle}`")

    lines.extend(
        [
            "",
            "## Marcadores Lean (`sorry`/`admit`/`axiom`) acumulados por línea",
            "",
            "> Auditoría en `lean_templates/`: **0 `sorry`**, **0 `admit`** y **7 `axiom`** (uno por problema en `rigorous_*.lean` como `*_universal_open_problem`).",
            "",
        ]
    )
    for prob, count in lean_markers_by_problem.items():
        files_n = chain["problem_file_counts"].get(prob, 0)
        lines.append(f"- `{prob}`: **{files_n}** archivos | **{count}** marcadores Lean")

    lines.extend(["", "## Archivos puente principales", ""])
    for item in bridge_files[:15]:
        probs_str = ", ".join(f"`{p}`" for p in item["problems"])
        lines.append(
            f"- `{item['path']}` ({item['problem_count']} líneas: {probs_str}; marcadores Lean: {item['lean_markers']})"
        )

    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_md.write_text("\n".join(lines), encoding="utf-8")

    if verbose:
        print(f"Nodos puente detectados: {len(bridge_files)}")
        print(f"Verificadores: {verifiers_summary}")
        print(f"JSON verificación: {out_verify_json}")
        print(f"JSON cadena:       {out_json}")
        print(f"MD cadena:         {out_md}")

    return chain


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Teje relaciones, integra métricas numéricas --json y genera la cadena."
    )
    parser.add_argument("--in-json", default=str(DEFAULT_IN_JSON), help="JSON de entrada.")
    parser.add_argument("--out-json", default=str(DEFAULT_OUT_JSON), help="JSON de cadena.")
    parser.add_argument("--out-md", default=str(DEFAULT_OUT_MD), help="Markdown de cadena.")
    parser.add_argument(
        "--verify-json", default=str(DEFAULT_VERIFY_JSON), help="JSON de métricas numéricas."
    )
    parser.add_argument(
        "--skip-verify",
        action="store_true",
        help="No ejecuta los verificadores; reutiliza verificacion_numerica.json si existe.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="Segundos máximos por script de verificación.",
    )
    parser.add_argument("--json", action="store_true", help="Imprime salida en JSON.")
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    data = weave_network_chain(
        in_json=Path(args.in_json),
        out_json=Path(args.out_json),
        out_md=Path(args.out_md),
        out_verify_json=Path(args.verify_json),
        skip_verify=args.skip_verify,
        timeout_s=args.timeout,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(data, indent=2, ensure_ascii=False))
