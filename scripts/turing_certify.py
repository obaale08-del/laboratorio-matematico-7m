import argparse
import json
import sys
import time
from typing import Any
import mpmath


def turing_interval_certification(
    t_start: float = 100.0,
    t_end: float = 200.0,
    step: float = 0.05,
    dps: int = 15,
    verbose: bool = False,
) -> dict[str, Any]:
    """Escanea [t_start, t_end] evaluando Z(t) (siegelz) y contabiliza cambios de signo.

    Nota: un cambio de signo en Z(t) indica al menos un cambio de signo en el paso
    muestreado; no sustituye una prueba formal ni garantiza detectar ceros sin cambio de signo.
    """
    if t_end < t_start:
        raise ValueError("t_end debe ser mayor o igual que t_start.")
    if step <= 0:
        raise ValueError("step debe ser un número positivo.")

    mpmath.mp.dps = dps
    start_time = time.perf_counter()

    t = mpmath.mpf(t_start)
    t_max = mpmath.mpf(t_end)
    step_mp = mpmath.mpf(step)
    total_range = float(t_max - t)

    prev_z = mpmath.siegelz(t)
    sign_changes = 0
    intervals_checked = 0

    while t < t_max:
        next_t = t + step_mp
        if next_t > t_max:
            next_t = t_max

        next_z = mpmath.siegelz(next_t)
        if prev_z * next_z < 0 or prev_z == 0:
            sign_changes += 1

        prev_z = next_z
        t = next_t
        intervals_checked += 1

        if verbose and intervals_checked % 50 == 0 and total_range > 0:
            elapsed = time.perf_counter() - start_time
            pct = (float(t - mpmath.mpf(t_start)) / total_range) * 100.0
            sys.stdout.write(
                f"\rProgreso T={float(t):.2f}/{t_end} ({pct:.1f}%) | "
                f"Cambios de signo: {sign_changes} | Tiempo: {elapsed:.1f}s"
            )
            sys.stdout.flush()

    if verbose and intervals_checked > 0:
        sys.stdout.write("\n")

    elapsed = time.perf_counter() - start_time
    result = {
        "t_start": t_start,
        "t_end": t_end,
        "step": step,
        "dps": dps,
        "intervals_checked": intervals_checked,
        "sign_changes_detected": sign_changes,
        "elapsed_seconds": round(elapsed, 4),
    }

    if verbose:
        print(
            f"Escaneo finalizado en {elapsed:.2f}s | intervalos={intervals_checked} | "
            f"cambios de signo en Z(t)={sign_changes}"
        )

    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Escanea cambios de signo de la función Z de Hardy (siegelz) en [t_start, t_end]."
    )
    parser.add_argument(
        "--t-start", type=float, default=100.0, help="Inicio del intervalo T (por defecto: 100.0)."
    )
    parser.add_argument(
        "--t-end", type=float, default=200.0, help="Fin del intervalo T (por defecto: 200.0)."
    )
    parser.add_argument(
        "--step", type=float, default=0.05, help="Paso de muestreo (por defecto: 0.05)."
    )
    parser.add_argument(
        "--dps", type=int, default=15, help="Dígitos de precisión (por defecto: 15)."
    )
    parser.add_argument(
        "--json", action="store_true", help="Imprime el resultado estructurado en JSON."
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    summary = turing_interval_certification(
        t_start=args.t_start,
        t_end=args.t_end,
        step=args.step,
        dps=args.dps,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
