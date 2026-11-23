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
        r"\bciclos?\s+(de\s+hodge|algebraic\w*|anal[íi]tic\w*)\b",
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

    core_pat_re = re.compile(
        r"riemann|zeta|navier|stokes|yang|mills|hodge|poincar|bsd|p\s*vs\.?\s*np|np[-_]?completo",
        flags=re.IGNORECASE,
    )

    for prob, patterns in PROBLEMS.items():
        total = 0
        core_hits = 0
        for pat in patterns:
            matches = re.findall(pat, text, flags=re.IGNORECASE)
            cnt = len(matches)
            total += cnt
            if cnt > 0 and core_pat_re.search(pat):
                core_hits += cnt
        # Requiere al menos 2 coincidencias si solo hubo términos secundarios
        if total > 0 and (core_hits >= 1 or total >= 2):
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

    pair_stats: dict[tuple[str, str], dict[str, Any]] = {}
    bridge_nodes: list[dict[str, Any]] = []

    for item in files_data:
        probs = item.get("problems") or []
        counts = item.get("hit_counts") or {}
        if len(probs) >= 2:
            bridge_nodes.append(
                {
                    "path": item.get("path"),
                    "problem_count": len(probs),
                    "problems": probs,
                    "hit_counts": counts,
                }
            )
        for i in range(len(probs)):
            for j in range(i + 1, len(probs)):
                a, b = probs[i], probs[j]
                key = (a, b) if a < b else (b, a)
                hits_pair = int(counts.get(a, 0)) + int(counts.get(b, 0))
                if key not in pair_stats:
                    pair_stats[key] = {
                        "problems": [key[0], key[1]],
                        "shared_files": 0,
                        "weight": 0,
                        "files": [],
                    }
                pair_stats[key]["shared_files"] += 1
                pair_stats[key]["weight"] += hits_pair
                pair_stats[key]["files"].append(item.get("path"))

    bridge_edges = sorted(
        pair_stats.values(),
        key=lambda e: (-e["shared_files"], -e["weight"], e["problems"][0], e["problems"][1]),
    )
    bridge_nodes.sort(key=lambda n: (n["problem_count"], n["path"] or ""))

    network = {
        "repo_root": str(REPO_ROOT),
        "total_scanned_files": len(files_data),
        "total_bridge_nodes": len(bridge_nodes),
        "problems_summary": {
            prob: {
                "file_count": len(paths),
                "files": paths,
            }
            for prob, paths in by_problem.items()
        },
        "bridge_nodes": bridge_nodes,
        "bridge_edges": bridge_edges,
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


def _parse_bridge_spec(spec: str) -> tuple[int, int | None]:
    s = spec.strip()
    if s.endswith("+"):
        return (int(s[:-1]), None)
    if s.startswith(">="):
        return (int(s[2:]), None)
    if "-" in s:
        lo_s, hi_s = s.split("-", 1)
        return (int(lo_s), int(hi_s))
    exact = int(s)
    return (exact, exact)


def _filter_bridges(nodes: list[dict[str, Any]], spec: str) -> list[dict[str, Any]]:
    lo, hi = _parse_bridge_spec(spec)
    out: list[dict[str, Any]] = []
    for n in nodes:
        cnt = int(n.get("problem_count", len(n.get("problems") or [])))
        if cnt < lo:
            continue
        if hi is not None and cnt > hi:
            continue
        out.append(n)
    return out


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Mapea archivos del repo vinculados a los 7 problemas del Milenio."
    )
    parser.add_argument("--out-json", default=str(DEFAULT_OUT_JSON), help="Ruta del JSON de red.")
    parser.add_argument("--out-md", default=str(DEFAULT_OUT_MD), help="Ruta del Markdown de red.")
    parser.add_argument("--problema", default="", help="Filtra archivos por clave de problema.")
    parser.add_argument(
        "--puentes",
        default="",
        help="Filtra nodos puente por cantidad de problemas (ej: 2, 2-3, 2+, >=2).",
    )
    parser.add_argument("--json", action="store_true", help="Imprime el resultado en JSON.")
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    quiet_verbose = args.json or bool(args.problema) or bool(args.puentes)
    data = build_milenio_network(
        out_json=Path(args.out_json),
        out_md=Path(args.out_md),
        verbose=not quiet_verbose,
    )

    if args.problema:
        prob_key = args.problema.strip()
        if prob_key not in PROBLEMS:
            raise SystemExit(f"Problema desconocido '{prob_key}'. Válidos: {', '.join(PROBLEMS)}")
        matched_files = [
            f for f in data["files"] if prob_key in (f.get("problems") or [])
        ]
        if args.json:
            print(json.dumps({"problema": prob_key, "files": matched_files}, indent=2, ensure_ascii=False))
        else:
            print(f"Problema '{prob_key}' -> {len(matched_files)} archivo(s):")
            for f in matched_files:
                hc = (f.get("hit_counts") or {}).get(prob_key, 0)
                print(f"  - {f['path']} (hits={hc})")

    if args.puentes:
        filtered_bridges = _filter_bridges(data["bridge_nodes"], args.puentes)
        if args.json:
            print(json.dumps({"puentes": args.puentes, "nodes": filtered_bridges}, indent=2, ensure_ascii=False))
        else:
            print(f"Puentes '{args.puentes}' -> {len(filtered_bridges)} nodo(s):")
            for n in filtered_bridges:
                probs_str = ", ".join(n.get("problems") or [])
                print(f"  [{n['problem_count']}] {n['path']} -> {probs_str}")

    if not args.problema and not args.puentes and args.json:
        print(json.dumps(data["problems_summary"], indent=2, ensure_ascii=False))
