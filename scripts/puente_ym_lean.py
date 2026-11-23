import json
import re
from pathlib import Path

TMP_DIR = Path.home() / "tmp"
OUT_JSON = TMP_DIR / "ym_puente_lean.json"

FILES = [
    TMP_DIR / "ym_experimentos.txt",
    TMP_DIR / "ym_barrido.txt",
    TMP_DIR / "ym_compensacion.txt",
]


def parse_delta(text: str, default: float = 0.25) -> float:
    m = re.search(r"delta\s*=\s*([0-9]+(?:\.[0-9]+)?)", text, re.IGNORECASE)
    return float(m.group(1)) if m else default


def parse_active_rows(path: Path) -> tuple[float, list[dict]]:
    text = path.read_text(encoding="utf-8", errors="ignore")
    delta = parse_delta(text)
    section = "general"
    active = []

    for raw_line in text.splitlines():
        line = raw_line.strip()
        sec_match = re.match(r"^\[([^\]]+)\]\s*(.+)$", line)
        if sec_match:
            section = f"{sec_match.group(1)}:{sec_match.group(2).strip()}"
            continue

        if "|" not in line:
            continue
        parts = [p.strip() for p in line.split("|")]
        if len(parts) < 6:
            continue
        if parts[0].lower() in {"escenario", "caso", "forma", "durac", "disip"}:
            continue
        if parts[-1] != "ACTIVA":
            continue

        try:
            e_cin = float(parts[1])
            aporte = float(parts[2])
            e_tot = float(parts[3])
            margen = float(parts[4])
        except ValueError:
            continue

        active.append({
            "seccion": section,
            "etiqueta": parts[0],
            "E_cin": e_cin,
            "Aporte": aporte,
            "E_tot": e_tot,
            "Margen": margen,
            "Estado": parts[-1],
        })

    return delta, active


def build_bound_summary(label: str, delta: float, rows: list[dict]) -> dict | None:
    if not rows:
        return None
    etots = [r["E_tot"] for r in rows]
    e_sweep = min(etots)
    x_max = max(etots)
    gap_ok = (0.0 < delta) and (delta <= 1.0)
    sweep_ge_delta = e_sweep >= delta
    xmax_ge_sweep = x_max >= e_sweep
    holds_crosses_gap = gap_ok and sweep_ge_delta and xmax_ge_sweep

    return {
        "bloque": label,
        "delta": delta,
        "E_sweep": e_sweep,
        "x_max": x_max,
        "activos": len(rows),
        "StrictMassGapBound": gap_ok,
        "E_sweep_ge_delta": sweep_ge_delta,
        "x_max_ge_sweep": xmax_ge_sweep,
        "sweep_bound_crosses_gap_holds": holds_crosses_gap,
        "muestras_activas": rows,
    }


def main() -> None:
    resumen = {"archivos": []}

    for path in FILES:
        if not path.exists():
            continue
        delta, active = parse_active_rows(path)

        by_sec: dict[str, list[dict]] = {}
        for r in active:
            by_sec.setdefault(r["seccion"], []).append(r)

        bloques = []
        if len(by_sec) > 1:
            for sec, s_rows in by_sec.items():
                b = build_bound_summary(sec, delta, s_rows)
                if b:
                    bloques.append(b)
        else:
            b = build_bound_summary(path.stem, delta, active)
            if b:
                bloques.append(b)

        resumen["archivos"].append({
            "archivo": path.name,
            "delta": delta,
            "total_activos": len(active),
            "bloques": bloques,
        })

        print(f"=== {path.name} (delta={delta:.4f}, activos={len(active)}) ===")
        for b in bloques:
            print(
                f"  [{b['bloque']}] E_sweep={b['E_sweep']:.4f} | x_max={b['x_max']:.4f} "
                f"| crosses_gap={b['sweep_bound_crosses_gap_holds']}"
            )

    OUT_JSON.write_text(json.dumps(resumen, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"\nGuardado resumen en: {OUT_JSON}")


if __name__ == "__main__":
    main()
