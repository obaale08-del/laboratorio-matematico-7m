#!/usr/bin/env python3
"""Registra mediciones y estado de Yang-Mills en un historial trazable."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess
import sys

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS_DIR = REPO_ROOT / "scripts"
LEAN_DIR = REPO_ROOT / "lean_templates"
DEFAULT_JSONL = REPO_ROOT / "docs" / "historial_ym.jsonl"
DEFAULT_MD = REPO_ROOT / "docs" / "HISTORIAL_YM.md"


def run_git_info(repo_root: Path) -> dict[str, object]:
    """Obtiene rama, commit actual y archivos tocados sin modificar el repo."""
    info: dict[str, object] = {
        "branch": None,
        "head_commit": None,
        "dirty_files": [],
    }
    try:
        branch = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        head = subprocess.run(
            ["git", "rev-parse", "--short", "HEAD"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
        status_lines = subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=repo_root,
            capture_output=True,
            text=True,
            check=True,
        ).stdout.splitlines()
        dirty = [line[3:].strip() for line in status_lines if len(line) > 3]
        info["branch"] = branch
        info["head_commit"] = head
        info["dirty_files"] = dirty
    except subprocess.CalledProcessError:
        pass
    return info


def scan_ym_lean_modules(lean_dir: Path) -> list[dict[str, object]]:
    """Resume declaraciones y posibles huecos/axiomas en archivos Lean de Yang-Mills."""
    modules: list[dict[str, object]] = []
    if not lean_dir.exists():
        return modules

    pattern = re.compile(
        r"^\s*(structure|def|abbrev|theorem|lemma|axiom)\s+([A-Za-z0-9_']+)"
    )
    for path in sorted(lean_dir.glob("*")):
        name_l = path.name.lower()
        if path.suffix != ".lean" or ("yang" not in name_l and "_ym" not in name_l):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        lines = text.splitlines()
        declarations: list[str] = []
        axioms: list[str] = []
        sorries = 0
        for line in lines:
            match = pattern.match(line)
            if match:
                kind, ident = match.group(1), match.group(2)
                declarations.append(f"{kind}:{ident}")
                if kind == "axiom":
                    axioms.append(ident)
            if re.search(r"\b(sorry|admit)\b", line):
                sorries += 1

        modules.append(
            {
                "file": str(path.relative_to(REPO_ROOT)),
                "lines": len(lines),
                "declarations_count": len(declarations),
                "axioms": axioms,
                "sorry_or_admit_lines": sorries,
            }
        )
    return modules


def load_puente_ym_summary(scripts_dir: Path) -> dict[str, object]:
    """Ejecuta o importa puente_ym_lean.py para extraer el estado numérico actual."""
    if str(scripts_dir) not in sys.path:
        sys.path.insert(0, str(scripts_dir))
    try:
        import puente_ym_lean  # type: ignore

        if hasattr(puente_ym_lean, "construir_resumen"):
            return puente_ym_lean.construir_resumen()
    except Exception:
        pass

    proc = subprocess.run(
        [sys.executable, str(scripts_dir / "puente_ym_lean.py"), "--json"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    raw = proc.stdout
    start = raw.find("{")
    if start == -1:
        return {"error": "No se encontro JSON en la salida de puente_ym_lean.py"}
    return json.loads(raw[start:])


def extract_blocks_metrics(puente_data: dict[str, object]) -> list[dict[str, object]]:
    """Aplana los bloques numéricos para inspección rápida."""
    rows: list[dict[str, object]] = []
    archivos = puente_data.get("archivos")
    if not isinstance(archivos, list):
        return rows
    for entry in archivos:
        if not isinstance(entry, dict):
            continue
        archivo = str(entry.get("archivo", ""))
        bloques = entry.get("bloques")
        if not isinstance(bloques, list):
            continue
        for blk in bloques:
            if not isinstance(blk, dict):
                continue
            rows.append(
                {
                    "archivo": archivo,
                    "bloque": blk.get("bloque"),
                    "delta": blk.get("delta"),
                    "E_sweep": blk.get("E_sweep"),
                    "x_max": blk.get("x_max"),
                    "activos": blk.get("activos"),
                    "crosses_gap": blk.get("sweep_bound_crosses_gap_holds"),
                }
            )
    return rows


def build_snapshot(
    label: str,
    notes: str,
    repo_root: Path = REPO_ROOT,
) -> dict[str, object]:
    """Construye un registro completo y trazable del estado de Yang-Mills."""
    puente_data = load_puente_ym_summary(repo_root / "scripts")
    blocks = extract_blocks_metrics(puente_data)
    lean_mods = scan_ym_lean_modules(repo_root / "lean_templates")
    git_info = run_git_info(repo_root)

    return {
        "timestamp_utc": datetime.now(timezone.utc).isoformat(),
        "label": label,
        "notes": notes,
        "scope_note": (
            "Registro de exploracion numerica, cotas de barrido y estructura "
            "de plantillas Lean; no equivale a demostracion cerrada del problema abierto."
        ),
        "git": git_info,
        "active_blocks_count": len(blocks),
        "active_samples_total": sum(
            int(b.get("activos") or 0) for b in blocks
        ),
        "blocks": blocks,
        "lean_modules": lean_mods,
    }


def render_markdown_report(records: list[dict[str, object]]) -> str:
    """Genera un resumen Markdown legible a partir de las entradas del historial."""
    lines = [
        "# Historial trazable — Yang-Mills (exploración y estado)",
        "",
        "> **Alcance:** Bitácora generada automáticamente desde el laboratorio experimental "
        "para trazar barridos numéricos, módulos Lean 4 y estado de trabajo antes de hacer `push`. "
        "Las cotas numéricas y plantillas formales no constituyen una resolución del problema abierto.",
        "",
    ]
    for idx, rec in enumerate(reversed(records), start=1):
        ts = rec.get("timestamp_utc", "")
        label = rec.get("label", "sin_etiqueta")
        notes = rec.get("notes", "")
        git_info = rec.get("git", {}) if isinstance(rec.get("git"), dict) else {}
        branch = git_info.get("branch", "?")
        head = git_info.get("head_commit", "?")
        dirty = git_info.get("dirty_files", [])
        blocks = rec.get("blocks", []) if isinstance(rec.get("blocks"), list) else []

        lines.append(f"## Registro {idx}: {label}")
        lines.append(f"- **Fecha (UTC):** `{ts}`")
        lines.append(f"- **Git:** rama `{branch}` en commit `{head}` | cambios locales: `{len(dirty) if isinstance(dirty, list) else 0}`")
        lines.append(
            f"- **Bloques activos:** `{rec.get('active_blocks_count', 0)}` | "
            f"**Muestras activas:** `{rec.get('active_samples_total', 0)}`"
        )
        if notes:
            lines.append(f"- **Notas:** {notes}")
        if blocks:
            lines.append("")
            lines.append("| Archivo | Bloque | Umbral | E_sweep | x_max | Activos | Cruce |")
            lines.append("| :--- | :--- | ---: | ---: | ---: | ---: | :---: |")
            for b in blocks:
                lines.append(
                    f"| `{b.get('archivo', '')}` | `{b.get('bloque', '')}` | "
                    f"{b.get('delta', '')} | {b.get('E_sweep', '')} | {b.get('x_max', '')} | "
                    f"{b.get('activos', '')} | {b.get('crosses_gap', '')} |"
                )
        lines.append("")

    return "\n".join(lines).strip() + "\n"


def append_history(
    record: dict[str, object],
    jsonl_path: Path = DEFAULT_JSONL,
    md_path: Path = DEFAULT_MD,
) -> None:
    """Añade el registro a JSONL y actualiza el resumen Markdown."""
    jsonl_path.parent.mkdir(parents=True, exist_ok=True)
    with jsonl_path.open("a", encoding="utf-8") as fh:
        fh.write(json.dumps(record, ensure_ascii=False) + "\n")

    all_records: list[dict[str, object]] = []
    with jsonl_path.open("r", encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line:
                all_records.append(json.loads(line))

    md_path.write_text(render_markdown_report(all_records), encoding="utf-8")


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Registra mediciones y estado de Yang-Mills en un historial trazable."
    )
    parser.add_argument(
        "--label",
        default="medicion_ym",
        help="Etiqueta corta de la tanda o medición (por defecto: medicion_ym).",
    )
    parser.add_argument(
        "--notes",
        default="",
        help="Nota breve sobre qué variable, analogía o ajuste estás probando.",
    )
    parser.add_argument(
        "--jsonl",
        type=Path,
        default=DEFAULT_JSONL,
        help="Ruta del archivo JSONL de historial.",
    )
    parser.add_argument(
        "--md",
        type=Path,
        default=DEFAULT_MD,
        help="Ruta del resumen Markdown generado.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Imprime el registro generado en formato JSON.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    record = build_snapshot(label=args.label, notes=args.notes, repo_root=REPO_ROOT)
    append_history(record=record, jsonl_path=args.jsonl, md_path=args.md)
    if args.json:
        print(json.dumps(record, indent=2, ensure_ascii=False))
    else:
        print(
            f"Registrado [{record['label']}] -> bloques={record['active_blocks_count']} "
            f"| muestras_activas={record['active_samples_total']} "
            f"| historial={args.jsonl}"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
