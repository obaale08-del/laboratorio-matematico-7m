import argparse
import json
import os
import re
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_AUDIT_DIR = REPO_ROOT / "lean_templates"


def audit_lean_files(
    target_dir: str | os.PathLike | None = None,
    log_path: str | os.PathLike | None = None,
    write_log: bool = True,
) -> dict[str, Any]:
    """Audita archivos .lean en busca de 'sorry', 'admit' y 'axiom'.

    Si no se indica `target_dir`, usa `lean_templates/` relativo a la raíz
    del repositorio. Devuelve un diccionario estructurado con el resumen.
    """
    base_dir = Path(target_dir) if target_dir is not None else DEFAULT_AUDIT_DIR
    if not base_dir.exists() or not base_dir.is_dir():
        raise FileNotFoundError(f"El directorio de archivos Lean no existe: {base_dir}")

    lean_files = sorted(base_dir.glob("*.lean"))
    audit_results: dict[str, dict[str, Any]] = {}

    total_sorries_and_admits = 0
    total_axioms = 0

    for file_path in lean_files:
        content = file_path.read_text(encoding="utf-8")
        sorries = len(re.findall(r"\bsorry\b", content))
        admits = len(re.findall(r"\badmit\b", content))
        axioms = len(re.findall(r"\baxiom\b", content))

        gaps = sorries + admits
        total_sorries_and_admits += gaps
        total_axioms += axioms

        audit_results[file_path.name] = {
            "sorries": sorries,
            "admits": admits,
            "sorries_and_admits": gaps,
            "axioms": axioms,
            "clean_status": gaps == 0,
        }

    resolved_log: Path | None = None
    if write_log:
        resolved_log = (
            Path(log_path)
            if log_path is not None
            else base_dir / "tactic_audit.log"
        )
        resolved_log.parent.mkdir(parents=True, exist_ok=True)
        lines = [
            "=== PETRUSKA FENIX: AUDITORIA DE RIGOR FORMAL ===",
            f"Directorio auditado: {base_dir}",
            f"Archivos analizados: {len(lean_files)}",
            f"Total de 'sorry/admit' encontrados: {total_sorries_and_admits}",
            f"Total de axiomas declarados: {total_axioms}",
            "",
        ]
        for filename, data in audit_results.items():
            status = (
                "LIBRE DE SORRIES/ADMITS"
                if data["clean_status"]
                else "CONTIENE BRECHAS PENDIENTES"
            )
            lines.extend([
                f"- Archivo: {filename}",
                f"  Estado: {status}",
                f"  Sorries/Admits: {data['sorries_and_admits']} "
                f"(sorry: {data['sorries']}, admit: {data['admits']})",
                f"  Axioms: {data['axioms']}",
                "",
            ])
        resolved_log.write_text("\n".join(lines), encoding="utf-8")

    return {
        "target_dir": str(base_dir),
        "log_path": str(resolved_log) if resolved_log else None,
        "files_analyzed": len(lean_files),
        "total_sorries_and_admits": total_sorries_and_admits,
        "total_axioms": total_axioms,
        "files": audit_results,
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Audita archivos .lean en busca de sorry, admit y axiom."
    )
    parser.add_argument(
        "--dir",
        dest="target_dir",
        default=str(DEFAULT_AUDIT_DIR),
        help="Directorio que contiene los archivos .lean (por defecto: lean_templates).",
    )
    parser.add_argument(
        "--log",
        dest="log_path",
        default=None,
        help="Ruta del archivo de reporte (por defecto: <dir>/tactic_audit.log).",
    )
    parser.add_argument(
        "--no-log",
        action="store_true",
        help="No escribe archivo de log en disco.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Imprime el resumen estructurado en formato JSON.",
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    summary = audit_lean_files(
        target_dir=args.target_dir,
        log_path=args.log_path,
        write_log=not args.no_log,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
    else:
        print(f"-> Auditoria completada en: {summary['target_dir']}")
        print(
            f"-> Estado global: {summary['total_sorries_and_admits']} brechas "
            f"y {summary['total_axioms']} axiomas en {summary['files_analyzed']} archivos."
        )
        if summary["log_path"]:
            print(f"-> Reporte guardado en: {summary['log_path']}")
