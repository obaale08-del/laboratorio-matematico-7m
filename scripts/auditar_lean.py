#!/usr/bin/env python3
"""Auditoría cruzada de plantillas Lean y su mapeo en milenio_mapa.py."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
if str(REPO_ROOT / "scripts") not in sys.path:
    sys.path.insert(0, str(REPO_ROOT / "scripts"))

import milenio_mapa as mm  # noqa: E402

DECL_RE = re.compile(r"^\s*(axiom|theorem|lemma|def|structure|inductive)\s+([A-Za-z0-9_']+)")
SORRY_RE = re.compile(r"\b(sorry|admit)\b")


def audit_lean_dir(target_dir: Path) -> dict[str, Any]:
    lean_files = sorted(target_dir.rglob("*.lean")) if target_dir.exists() else []
    results: list[dict[str, Any]] = []
    total_sorry = 0
    total_axioms = 0
    total_theorems = 0

    for fp in lean_files:
        text = fp.read_text(encoding="utf-8", errors="ignore")
        lines = text.splitlines()

        decls: list[dict[str, Any]] = []
        sorry_hits: list[dict[str, Any]] = []

        for idx, line in enumerate(lines, start=1):
            m_decl = DECL_RE.match(line)
            if m_decl:
                kind, name = m_decl.group(1), m_decl.group(2)
                decls.append({"line": idx, "kind": kind, "name": name})
                if kind == "axiom":
                    total_axioms += 1
                elif kind in ("theorem", "lemma"):
                    total_theorems += 1

            if SORRY_RE.search(line):
                total_sorry += 1
                sorry_hits.append({"line": idx, "text": line.strip()})

        scan = mm._scan_file(fp)
        mapped_probs = scan.get("problems") or []
        hit_counts = scan.get("hit_counts") or {}

        results.append(
            {
                "path": scan.get("path", str(fp.relative_to(REPO_ROOT))),
                "sorry_or_admit": len(sorry_hits),
                "sorry_hits": sorry_hits,
                "declarations_count": len(decls),
                "declarations": decls,
                "mapped_problems": mapped_probs,
                "hit_counts": hit_counts,
            }
        )

    return {
        "target_dir": str(target_dir.relative_to(REPO_ROOT)) if target_dir.exists() else str(target_dir),
        "total_lean_files": len(results),
        "total_sorry_or_admit": total_sorry,
        "total_axioms": total_axioms,
        "total_theorems_and_lemmas": total_theorems,
        "files": results,
    }


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Audita archivos .lean: sorry/admit, declaraciones y enlaces de problemas."
    )
    parser.add_argument(
        "--dir",
        default=str(REPO_ROOT / "lean_templates"),
        help="Directorio con archivos .lean a auditar.",
    )
    parser.add_argument("--json", action="store_true", help="Imprime salida en JSON.")
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    report = audit_lean_dir(Path(args.dir))
    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print(
            f"Lean audit ({report['target_dir']}): {report['total_lean_files']} archivos | "
            f"sorry/admit={report['total_sorry_or_admit']} | "
            f"axioms={report['total_axioms']} | "
            f"theorems/lemmas={report['total_theorems_and_lemmas']}"
        )
        for item in report["files"]:
            probs_txt = ", ".join(item["mapped_problems"]) if item["mapped_problems"] else "ninguno"
            print(
                f"  - {item['path']}: decls={item['declarations_count']}, "
                f"sorry={item['sorry_or_admit']} | probs=[{probs_txt}]"
            )
