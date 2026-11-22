import argparse
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_IN_JSON = REPO_ROOT / "docs" / "milenio_red.json"
DEFAULT_OUT_JSON = REPO_ROOT / "docs" / "milenio_cadena.json"
DEFAULT_OUT_MD = REPO_ROOT / "docs" / "CADENA_MILENIO.md"


def weave_network_chain(
    in_json: Path = DEFAULT_IN_JSON,
    out_json: Path = DEFAULT_OUT_JSON,
    out_md: Path = DEFAULT_OUT_MD,
    verbose: bool = False,
) -> dict[str, Any]:
    """Cruza milenio_red.json para detectar nodos puente y estado de marcadores Lean."""
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

    chain = {
        "source_map": str(in_json),
        "total_files": raw.get("total_scanned_files", len(files)),
        "bridge_file_count": len(bridge_files),
        "bridge_files": bridge_files,
        "lean_markers_by_problem": lean_markers_by_problem,
        "problem_file_counts": {
            prob: info.get("file_count", 0) for prob, info in summary.items()
        },
    }

    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(chain, indent=2, ensure_ascii=False), encoding="utf-8")

    lines = [
        "# Cadena y Nodos Puente — 7 Problemas del Milenio",
        "",
        f"Archivos puente (conectan 2 o más problemas): **{len(bridge_files)}**",
        "",
        "## Marcadores Lean (`sorry`/`admit`/`axiom`) acumulados por línea",
        "",
    ]
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
        print(f"JSON cadena: {out_json}")
        print(f"MD cadena:   {out_md}")

    return chain


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Teje relaciones entre problemas y marcadores Lean a partir de milenio_red.json."
    )
    parser.add_argument("--in-json", default=str(DEFAULT_IN_JSON), help="JSON de entrada.")
    parser.add_argument("--out-json", default=str(DEFAULT_OUT_JSON), help="JSON de salida.")
    parser.add_argument("--out-md", default=str(DEFAULT_OUT_MD), help="Markdown de salida.")
    parser.add_argument("--json", action="store_true", help="Imprime salida en JSON.")
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    data = weave_network_chain(
        in_json=Path(args.in_json),
        out_json=Path(args.out_json),
        out_md=Path(args.out_md),
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(data, indent=2, ensure_ascii=False))
