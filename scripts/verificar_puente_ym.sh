#!/usr/bin/env bash
set -euo pipefail

REPO_DIR="/data/data/com.termux/files/home/repo_petruska_fenix"
JSON_PATH="/data/data/com.termux/files/home/tmp/ym_puente_lean.json"
OUT_LEAN="$REPO_DIR/lean_templates/yang_mills_puente.lean"

cd "$REPO_DIR"
python3 scripts/puente_ym_lean.py

python3 - "$JSON_PATH" "$OUT_LEAN" << 'PYEOF'
import json
import re
import sys
from pathlib import Path

json_path = Path(sys.argv[1])
out_lean = Path(sys.argv[2])

data = json.loads(json_path.read_text(encoding="utf-8"))

def sanitize_ident(name: str) -> str:
    s = re.sub(r"[^a-zA-Z0-9_]+", "_", name).strip("_")
    if not s or s[0].isdigit():
        s = "b_" + s
    return s.lower()

def fmt_r(v: float) -> str:
    s = f"{v:.10f}".rstrip("0").rstrip(".")
    return s if "." in s else s + ".0"

lines = [
    "-- Generado automáticamente desde ~/tmp/ym_puente_lean.json",
    "import Mathlib.Data.Real.Basic",
    "import Mathlib.Tactic.NormNum",
    "",
    "namespace YangMillsPuente",
    "",
    "def StrictMassGapBound (delta : ℝ) : Prop :=",
    "  0 < delta ∧ delta ≤ 1",
    "",
    "lemma sweep_bound_crosses_gap",
    "    (delta E_sweep x : ℝ)",
    "    (h_gap : StrictMassGapBound delta)",
    "    (h_sweep_ge_delta : delta ≤ E_sweep)",
    "    (hx_ge_sweep : E_sweep ≤ x) :",
    "    0 < E_sweep ∧ delta ≤ x ∧ 0 < x := by",
    "  have h_pos_sweep : 0 < E_sweep := lt_of_lt_of_le h_gap.1 h_sweep_ge_delta",
    "  have h_delta_le_x : delta ≤ x := le_trans h_sweep_ge_delta hx_ge_sweep",
    "  have h_pos_x : 0 < x := lt_of_lt_of_le h_pos_sweep hx_ge_sweep",
    "  exact ⟨h_pos_sweep, h_delta_le_x, h_pos_x⟩",
    "",
]

idx = 0
for archivo_entry in data.get("archivos", []):
    for bloque in archivo_entry.get("bloques", []):
        idx += 1
        delta_s = fmt_r(float(bloque["delta"]))
        esweep_s = fmt_r(float(bloque["E_sweep"]))
        xmax_s = fmt_r(float(bloque["x_max"]))
        ident = f"caso_{idx}_{sanitize_ident(bloque['bloque'])}"

        lines.append(f"-- Bloque: {bloque['bloque']} (archivo: {archivo_entry['archivo']})")
        lines.append(f"theorem {ident} :")
        lines.append(f"    (0 : ℝ) < {esweep_s} ∧ ({delta_s} : ℝ) ≤ {xmax_s} ∧ (0 : ℝ) < {xmax_s} := by")
        lines.append(f"  apply sweep_bound_crosses_gap ({delta_s} : ℝ) ({esweep_s} : ℝ) ({xmax_s} : ℝ)")
        lines.append(f"  · exact ⟨by norm_num, by norm_num⟩")
        lines.append(f"  · norm_num")
        lines.append(f"  · norm_num")
        lines.append("")

lines.append("end YangMillsPuente")
out_lean.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"Generado {out_lean} con {idx} teoremas.")
PYEOF

proot-distro login ubuntu -- bash -lc 'export PATH="$HOME/.elan/bin:$PATH"; cd /data/data/com.termux/files/home/repo_petruska_fenix && lake env lean lean_templates/yang_mills_puente.lean'
echo "Verificación Lean completada con éxito."
df -h "$HOME"
