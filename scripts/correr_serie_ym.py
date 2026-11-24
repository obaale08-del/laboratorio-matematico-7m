#!/usr/bin/env python3
"""Genera y evalúa series paramétricas de prueba frente a un umbral delta."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = REPO_ROOT / "docs" / "ultima_serie_ym.json"


def compute_sample_energy(
    e_cin: float,
    forma: float,
    duracion: float,
    disipacion: float,
    delta: float = 0.25,
    gain: float = 0.25,
    damping_weight: float = 0.15,
) -> dict[str, object]:
    """Calcula Aporte, E_tot y Margen para una expresión heurística de trabajo.

    Nota: es un modelo numérico de exploración para estudiar sensibilidad entre
    forma, duración y disipación; no representa un Hamiltoniano cuántico exacto.
    """
    raw_aporte = gain * forma * (1.0 + 0.25 * (duracion - 1.0)) - damping_weight * disipacion
    aporte = max(0.0, round(raw_aporte, 4))
    e_tot = round(e_cin + aporte, 4)
    margen = round(e_tot - delta, 4)
    return {
        "forma": forma,
        "duracion": duracion,
        "disipacion": disipacion,
        "E_cin": round(e_cin, 4),
        "Aporte": aporte,
        "E_tot": e_tot,
        "delta": delta,
        "Margen": margen,
        "crosses_delta": e_tot >= delta,
    }


def generate_sweep_series(
    eje: str,
    valores: list[float],
    e_cin: float = 0.0612,
    forma: float = 0.80,
    duracion: float = 1.0,
    disipacion: float = 0.40,
    delta: float = 0.25,
) -> dict[str, object]:
    """Evalúa una serie variando un eje ('forma', 'duracion' o 'disipacion')."""
    samples: list[dict[str, object]] = []
    for idx, val in enumerate(valores, start=1):
        cur_forma = val if eje == "forma" else forma
        cur_dur = val if eje == "duracion" else duracion
        cur_dis = val if eje == "disipacion" else disipacion
        row = compute_sample_energy(
            e_cin=e_cin,
            forma=cur_forma,
            duracion=cur_dur,
            disipacion=cur_dis,
            delta=delta,
        )
        row["etiqueta"] = f"s{idx}_{eje}_{val}"
        samples.append(row)

    totals = [float(s["E_tot"]) for s in samples]
    e_sweep = min(totals) if totals else 0.0
    x_max = max(totals) if totals else 0.0
    crossing_count = sum(1 for s in samples if bool(s["crosses_delta"]))

    return {
        "eje": eje,
        "delta": delta,
        "base": {
            "E_cin": e_cin,
            "forma": forma,
            "duracion": duracion,
            "disipacion": disipacion,
        },
        "E_sweep": round(e_sweep, 4),
        "x_max": round(x_max, 4),
        "total_muestras": len(samples),
        "muestras_cruzan_delta": crossing_count,
        "muestras": samples,
    }


def parse_values(raw_vals: list[str]) -> list[float]:
    """Convierte valores separados por coma o espacios en flotantes."""
    parsed: list[float] = []
    for item in raw_vals:
        for token in item.split(","):
            token = token.strip()
            if token:
                parsed.append(float(token))
    if not parsed:
        raise ValueError("Debes indicar al menos un valor numérico para la serie.")
    return parsed


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Evalúa una serie paramétrica de prueba para Yang-Mills."
    )
    parser.add_argument(
        "--eje",
        choices=["forma", "duracion", "disipacion"],
        default="disipacion",
        help="Parámetro que varía a lo largo de la serie.",
    )
    parser.add_argument(
        "--valores",
        nargs="+",
        default=["0.40", "0.20", "0.00"],
        help="Lista de valores numéricos para el eje elegido (ej: 0.40 0.20 0.00).",
    )
    parser.add_argument("--e-cin", type=float, default=0.0612, help="Energía cinética base.")
    parser.add_argument("--forma", type=float, default=0.80, help="Forma base.")
    parser.add_argument("--duracion", type=float, default=1.0, help="Duración base.")
    parser.add_argument("--disipacion", type=float, default=0.40, help="Disipación base.")
    parser.add_argument("--delta", type=float, default=0.25, help="Umbral de referencia.")
    parser.add_argument(
        "--out",
        type=Path,
        default=DEFAULT_OUT,
        help="Ruta JSON de salida para guardar la última serie evaluada.",
    )
    parser.add_argument(
        "--no-save",
        action="store_true",
        help="No escribe archivo JSON en disco; solo imprime resultados.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Imprime el resumen completo en JSON.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    values = parse_values(args.valores)
    summary = generate_sweep_series(
        eje=args.eje,
        valores=values,
        e_cin=args.e_cin,
        forma=args.forma,
        duracion=args.duracion,
        disipacion=args.disipacion,
        delta=args.delta,
    )
    if not args.no_save:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(
            json.dumps(summary, indent=2, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )

    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
    else:
        print(
            f"Serie [{summary['eje']}] -> E_sweep={summary['E_sweep']} | "
            f"x_max={summary['x_max']} | cruzan({summary['delta']})="
            f"{summary['muestras_cruzan_delta']}/{summary['total_muestras']}"
        )
        for m in summary["muestras"]:
            print(
                f"  - {m['etiqueta']}: forma={m['forma']} dur={m['duracion']} "
                f"dis={m['disipacion']} -> E_tot={m['E_tot']} (Margen={m['Margen']}, "
                f"cruce={m['crosses_delta']})"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
