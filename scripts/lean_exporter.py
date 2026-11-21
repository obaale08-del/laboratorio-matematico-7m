import argparse
import os
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXPORT_DIR = REPO_ROOT / "lean_exports"


def _sanitize_identifier(raw: str) -> str:
    cleaned = re.sub(r"[^0-9A-Za-z_]", "_", raw.strip())
    cleaned = re.sub(r"_+", "_", cleaned).strip("_")
    if not cleaned:
        return "generated_theorem"
    if cleaned[0].isdigit():
        return f"thm_{cleaned}"
    return cleaned


class LeanExporter:
    """Genera plantillas y borradores de modulos en Lean 4 de forma portable."""

    def __init__(self, output_dir: str | os.PathLike | None = None):
        base = Path(output_dir) if output_dir is not None else DEFAULT_EXPORT_DIR
        self.output_dir = base
        self.output_dir.mkdir(parents=True, exist_ok=True)

    def write_rigorous_theorem(
        self,
        problem_name: str,
        file_slug: str,
        definitions: str,
        theorem_statement: str,
        proof_script: str,
    ) -> Path:
        safe_slug = _sanitize_identifier(file_slug)
        indented_proof = "\n".join(
            f"  {line}" if line.strip() else ""
            for line in proof_script.splitlines()
        )
        lean_code = (
            "import Mathlib\n\n"
            "-- =====================================================================\n"
            "-- Marco de Trabajo / Plantilla Lean 4 - Petruska Fenix\n"
            f"-- Problema: {problem_name}\n"
            "-- =====================================================================\n\n"
            f"{definitions.strip()}\n\n"
            f"theorem rigorous_proof_{safe_slug} : {theorem_statement} := by\n"
            f"{indented_proof}\n"
        )
        filepath = self.output_dir / f"{safe_slug}.lean"
        filepath.write_text(lean_code, encoding="utf-8")
        return filepath

    def write_theorem(
        self,
        problem_name: str,
        theorem_statement: str,
        proof_tactic: str = "sorry",
        definitions: str = "-- Definicion base generada automaticamente\nvariable (x : R)",
        file_slug: str | None = None,
    ) -> Path:
        slug = file_slug if file_slug else problem_name.lower()
        return self.write_rigorous_theorem(
            problem_name=problem_name,
            file_slug=slug,
            definitions=definitions,
            theorem_statement=theorem_statement,
            proof_script=proof_tactic,
        )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Exporta una plantilla de teorema en Lean 4 a un archivo .lean."
    )
    parser.add_argument("--problem", required=True, help="Nombre o descripcion del problema.")
    parser.add_argument("--slug", default=None, help="Nombre base del archivo y teorema.")
    parser.add_argument(
        "--statement",
        default="True",
        help="Enunciado formal del teorema en Lean 4.",
    )
    parser.add_argument(
        "--tactic",
        default="sorry",
        help="Tactica o bloque de demostracion (por defecto: sorry).",
    )
    parser.add_argument(
        "--defs",
        default="-- Definiciones",
        help="Bloque de variables o definiciones previas.",
    )
    parser.add_argument(
        "--out-dir",
        default=str(DEFAULT_EXPORT_DIR),
        help="Directorio de salida (por defecto: lean_exports en la raiz del repo).",
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    exporter = LeanExporter(output_dir=args.out_dir)
    created = exporter.write_theorem(
        problem_name=args.problem,
        theorem_statement=args.statement,
        proof_tactic=args.tactic,
        definitions=args.defs,
        file_slug=args.slug,
    )
    print(f"-> Modulo exportado en: {created}")
