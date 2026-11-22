import argparse
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RED_JSON = REPO_ROOT / "docs" / "milenio_red.json"
DEFAULT_CADENA_JSON = REPO_ROOT / "docs" / "milenio_cadena.json"
DEFAULT_VERIFY_JSON = REPO_ROOT / "docs" / "verificacion_numerica.json"
DEFAULT_OUT_MD = REPO_ROOT / "docs" / "ANALISIS_ESTRUCTURA_MILENIO.md"

KEY_DOCS: list[str] = [
    "docs/HEPTALOGO_MANIFEST.md",
    "docs/HEPTALOGO_REPORT.md",
    "docs/millennium_dossier_resumen.txt",
    "README.md",
]


def _inspect_doc(rel_path: str) -> dict[str, Any]:
    path = REPO_ROOT / rel_path
    if not path.exists():
        return {"path": rel_path, "exists": False}

    raw_text = path.read_text(encoding="utf-8", errors="ignore")
    lines = raw_text.splitlines()
    headings = [
        line.strip()
        for line in lines
        if line.strip().startswith("#") or line.strip().isupper() and len(line.strip()) > 4
    ]
    preview = [line.strip() for line in lines if line.strip()][:8]
    return {
        "path": rel_path,
        "exists": True,
        "size_bytes": path.stat().st_size,
        "line_count": len(lines),
        "headings_sample": headings[:12],
        "preview": preview,
    }


def _folder_breakdown(files: list[dict[str, Any]]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for item in files:
        rel = item.get("path", "")
        top = rel.split("/", 1)[0] if "/" in rel else "<raiz>"
        counts[top] = counts.get(top, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


def analyze_repository_structure(
    red_json: Path = DEFAULT_RED_JSON,
    cadena_json: Path = DEFAULT_CADENA_JSON,
    verify_json: Path = DEFAULT_VERIFY_JSON,
    out_md: Path = DEFAULT_OUT_MD,
    verbose: bool = False,
) -> dict[str, Any]:
    """Analiza documentos sobre los 7 problemas, datos numéricos y estructura del repo."""
    red = json.loads(red_json.read_text(encoding="utf-8")) if red_json.exists() else {}
    cadena = (
        json.loads(cadena_json.read_text(encoding="utf-8")) if cadena_json.exists() else {}
    )
    verify = (
        json.loads(verify_json.read_text(encoding="utf-8")) if verify_json.exists() else {}
    )

    files = red.get("files", [])
    folders = _folder_breakdown(files)
    docs_info = [_inspect_doc(rel) for rel in KEY_DOCS]

    analysis = {
        "total_scanned_files": red.get("total_scanned_files", len(files)),
        "folders": folders,
        "bridge_file_count": cadena.get("bridge_file_count", 0),
        "problem_file_counts": cadena.get("problem_file_counts", {}),
        "lean_markers_by_problem": cadena.get("lean_markers_by_problem", {}),
        "verifiers_status": cadena.get("verifiers_status", {}),
        "verifiers_data": {
            k: v.get("data") for k, v in verify.get("verifiers", {}).items() if "data" in v
        },
        "key_documents": docs_info,
    }

    lines = [
        "# Análisis de Datos, Documentos y Estructura — 7 Problemas del Milenio",
        "",
        "## 1. Estructura general del repositorio",
        "",
        f"- Archivos escaneados en la red: **{analysis['total_scanned_files']}**",
        f"- Nodos puente (2 o más problemas): **{analysis['bridge_file_count']}**",
        "",
        "### Distribución por carpeta / bloque",
        "",
    ]
    for folder, cnt in folders.items():
        lines.append(f"- `{folder}`: **{cnt}** archivo(s)")

    lines.extend(["", "## 2. Cobertura y marcadores Lean por problema", ""])
    for prob, f_count in analysis["problem_file_counts"].items():
        m_count = analysis["lean_markers_by_problem"].get(prob, 0)
        lines.append(f"- `{prob}`: **{f_count}** archivos | **{m_count}** marcadores Lean")

    lines.extend(["", "## 3. Datos numéricos registrados", ""])
    for name, st in analysis["verifiers_status"].items():
        lines.append(f"- `{name}`: **{st}**")
        v_data = analysis["verifiers_data"].get(name)
        if isinstance(v_data, dict):
            lines.append(f"  - Detalle: `{json.dumps(v_data, ensure_ascii=False)}`")

    lines.extend(["", "## 4. Documentos principales que abordan los 7 problemas y la estructura", ""])
    for doc in docs_info:
        lines.append(f"### `{doc['path']}`")
        if not doc.get("exists"):
            lines.append("- No encontrado en el árbol actual.")
            lines.append("")
            continue
        lines.append(
            f"- Líneas: **{doc['line_count']}** | Tamaño: **{doc['size_bytes']}** bytes"
        )
        if doc["headings_sample"]:
            lines.append("- Secciones / encabezados detectados:")
            for h in doc["headings_sample"][:8]:
                lines.append(f"  - `{h}`")
        if doc["preview"]:
            lines.append("- Primeras líneas útiles:")
            for p_line in doc["preview"][:4]:
                lines.append(f"  - {p_line}")
        lines.append("")

    lines.extend(
        [
            "## 5. Arquitectura del pipeline construido",
            "",
            "1. `scripts/milenio_mapa.py`: escanea archivos y los asocia a los 7 problemas del Milenio (`docs/milenio_red.json`, `docs/RED_MILENIO.md`).",
            "2. `scripts/tejer_red.py`: detecta nodos puente entre problemas, acumula marcadores Lean y consolida métricas numéricas (`docs/verificacion_numerica.json`, `docs/milenio_cadena.json`, `docs/CADENA_MILENIO.md`).",
            "3. `scripts/lean_auditor.py`: audita las plantillas en `lean_templates/`.",
            "4. `scripts/tejer_y_subir.py`: ejecuta el encadenado completo, hace `git add`/`commit` y empuja a `origin/main`.",
            "5. `scripts/analizar_estructura.py`: sintetiza documentos, datos y estructura en `docs/ANALISIS_ESTRUCTURA_MILENIO.md`.",
        ]
    )

    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_md.write_text("\n".join(lines), encoding="utf-8")

    if verbose:
        print(f"Análisis generado en: {out_md}")
        print(f"Carpetas detectadas: {folders}")

    return analysis


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Genera un análisis de datos, documentos y estructura del proyecto."
    )
    parser.add_argument("--red-json", default=str(DEFAULT_RED_JSON), help="Ruta a milenio_red.json.")
    parser.add_argument(
        "--cadena-json", default=str(DEFAULT_CADENA_JSON), help="Ruta a milenio_cadena.json."
    )
    parser.add_argument(
        "--verify-json",
        default=str(DEFAULT_VERIFY_JSON),
        help="Ruta a verificacion_numerica.json.",
    )
    parser.add_argument("--out-md", default=str(DEFAULT_OUT_MD), help="Ruta del Markdown de salida.")
    parser.add_argument("--json", action="store_true", help="Imprime el análisis en JSON.")
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    res = analyze_repository_structure(
        red_json=Path(args.red_json),
        cadena_json=Path(args.cadena_json),
        verify_json=Path(args.verify_json),
        out_md=Path(args.out_md),
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(res, indent=2, ensure_ascii=False))
