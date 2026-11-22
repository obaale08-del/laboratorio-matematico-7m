import argparse
import json
from pathlib import Path
import re
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT_JSON = REPO_ROOT / "docs" / "milenio_red.json"
DEFAULT_OUT_MD = REPO_ROOT / "docs" / "RED_MILENIO.md"

PROBLEMS: dict[str, list[str]] = {
    "riemann": [
        r"\briemann\b",
        r"\bzeta\b",
        r"\bzetazero\b",
        r"\bsiegelz\b",
        r"\bturing\b",
        r"linea.?critica|línea.?crítica",
    ],
    "p_vs_np": [
        r"\bp\s*vs\.?\s*np\b",
        r"\bnp[-_]?completo\b",
        r"\bcomplejidad\b",
        r"\bsat\b",
    ],
    "navier_stokes": [
        r"\bnavier\b",
        r"\bstokes\b",
        r"\bturbulencia\b",
        r"\bfluido\b",
    ],
    "yang_mills": [
        r"\byang[-_\s]?mills\b",
        r"\bmass.?gap\b",
        r"\bgauge\b",
    ],
    "hodge": [
        r"\bhodge\b",
        r"\bcohomolog",
        r"\bciclos?\b",
    ],
    "birch_swinnerton_dyer": [
        r"\bbirch\b",
        r"\bswinnerton\b",
        r"\bcurvas?.?elipticas?|curvas?.?elípticas?\b",
        r"\bbsd\b",
    ],
    "poincare": [
        r"\bpoincare\b|\bpoincaré\b",
        r"\bvariedad\b",
        r"\btopolog",
    ],
}

LEAN_MARKERS = re.compile(r"\b(sorry|admit|axiom)\b")
TEXT_EXTS = {".py", ".lean", ".md", ".txt", ".json", ".toml", ".sh"}


def _scan_file(path: Path) -> dict[str, Any]:
    rel = path.relative_to(REPO_ROOT).as_posix()
    text = path.read_text(encoding="utf-8", errors="ignore")
    matched_problems: list[str] = []
    hit_counts: dict[str, int] = {}

    for prob, patterns in PROBLEMS.items():
        total = 0
        for pat in patterns:
            total += len(re.findall(pat, text, flags=re.IGNORECASE))
        if total > 0:
            matched_problems.append(prob)
            hit_counts[prob] = total

    lean_markers = len(LEAN_MARKERS.findall(text)) if path.suffix == ".lean" else 0
    return {
        "path": rel,
        "ext": path.suffix or "<sin_ext>",
        "size_bytes": path.stat().st_size,
        "problems": matched_problems,
        "hit_counts": hit_counts,
        "lean_markers": lean_markers,
    }


def build_milenio_network(
    out_json: Path = DEFAULT_OUT_JSON,
    out_md: Path = DEFAULT_OUT_MD,
    verbose: bool = False,
) -> dict[str, Any]:
    """Busca y conecta archivos del repositorio con los 7 problemas del Milenio."""
    files_data: list[dict[str, Any]] = []
    by_problem: dict[str, list[str]] = {k: [] for k in PROBLEMS}

    for p in sorted(REPO_ROOT.rglob("*")):
        if not p.is_file():
            continue
        if ".git" in p.parts or "__pycache__" in p.parts:
            continue
        if p.suffix.lower() not in TEXT_EXTS:
            continue

        info = _scan_file(p)
        files_data.append(info)
        for prob in info["problems"]:
            by_problem[prob].append(info["path"])

    network = {
        "repo_root": str(REPO_ROOT),
        "total_scanned_files": len(files_data),
        "problems_summary": {
            prob: {
                "file_count": len(paths),
                "files": paths,
            }
            for prob, paths in by_problem.items()
        },
        "files": files_data,
    }

    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(network, indent=2, ensure_ascii=False), encoding="utf-8")

    lines = [
        "# Red de Archivos — 7 Problemas del Milenio (Petruska Fenix)",
        "",
        f"Archivos escaneados: **{len(files_data)}**",
        "",
        "## Cobertura por problema",
        "",
    ]
    for prob, paths in by_problem.items():
        lines.append(f"### `{prob}` ({len(paths)} archivos)")
        if paths:
            for item in paths:
                lines.append(f"- `{item}`")
        else:
            lines.append("- Sin coincidencias directas aún")
        lines.append("")

    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_md.write_text("\n".join(lines), encoding="utf-8")

    if verbose:
        print(f"Escaneados {len(files_data)} archivos.")
        for prob, paths in by_problem.items():
            print(f"  - {prob}: {len(paths)} archivo(s)")
        print(f"JSON: {out_json}")
        print(f"MD:   {out_md}")

    return network


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Mapea archivos del repo vinculados a los 7 problemas del Milenio."
    )
    parser.add_argument("--out-json", default=str(DEFAULT_OUT_JSON), help="Ruta del JSON de red.")
    parser.add_argument("--out-md", default=str(DEFAULT_OUT_MD), help="Ruta del Markdown de red.")
    parser.add_argument("--json", action="store_true", help="Imprime el resumen en JSON.")
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    data = build_milenio_network(
        out_json=Path(args.out_json),
        out_md=Path(args.out_md),
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(data["problems_summary"], indent=2, ensure_ascii=False))
