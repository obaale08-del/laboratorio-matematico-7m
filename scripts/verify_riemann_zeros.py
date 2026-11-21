import argparse
import json
import sys
import time
from typing import Any
import mpmath


def verify_riemann_zeros(
    start_index: int = 1,
    count: int = 100,
    dps: int = 30,
    progress_every: int = 25,
    verbose: bool = False,
) -> dict[str, Any]:
    """Verifica ceros de zeta en la línea crítica reportando progreso periódicamente."""
    mpmath.mp.dps = dps
    anomalies: list[dict[str, str | int]] = []
    errors: list[dict[str, str | int]] = []
    tolerance = mpmath.mpf(10) ** (-dps + 6)

    start_time = time.perf_counter()
    for idx, n in enumerate(range(start_index, start_index + count), start=1):
        try:
            zero = mpmath.zetazero(n)
            val = mpmath.zeta(zero)
            if abs(val) > tolerance:
                anomalies.append({
                    "index": n,
                    "zero": str(zero),
                    "zeta_value": str(val),
                })
        except Exception as exc:
            errors.append({"index": n, "error": str(exc)})

        if verbose and progress_every > 0 and (idx % progress_every == 0 or idx == count):
            elapsed = time.perf_counter() - start_time
            pct = (idx / max(count, 1)) * 100.0
            sys.stdout.write(
                f"\rProgreso: {idx}/{count} ({pct:.1f}%) - Tiempo: {elapsed:.1f}s"
            )
            sys.stdout.flush()

    if verbose and count > 0:
        sys.stdout.write("\n")

    elapsed = time.perf_counter() - start_time
    result = {
        "start_index": start_index,
        "count": count,
        "dps": dps,
        "tolerance": str(tolerance),
        "elapsed_seconds": round(elapsed, 4),
        "anomalies": anomalies,
        "errors": errors,
        "all_within_tolerance": len(anomalies) == 0 and len(errors) == 0,
    }

    if verbose:
        print(
            f"Completado: {count} ceros en {elapsed:.2f}s | "
            f"anomalías={len(anomalies)} | errores={len(errors)}"
        )

    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Verifica ceros de Riemann con reporte de progreso."
    )
    parser.add_argument("--start", type=int, default=1, help="Índice inicial (por defecto: 1).")
    parser.add_argument(
        "--count", type=int, default=100, help="Cantidad de ceros a verificar (por defecto: 100)."
    )
    parser.add_argument(
        "--dps", type=int, default=30, help="Precisión decimal en dígitos (por defecto: 30)."
    )
    parser.add_argument(
        "--progress-every",
        type=int,
        default=25,
        help="Intervalo de pasos para mostrar progreso (por defecto: 25).",
    )
    parser.add_argument(
        "--json", action="store_true", help="Imprime el resumen en formato JSON."
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    summary = verify_riemann_zeros(
        start_index=args.start,
        count=args.count,
        dps=args.dps,
        progress_every=args.progress_every,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
