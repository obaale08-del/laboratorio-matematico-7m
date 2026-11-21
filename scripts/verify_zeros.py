import argparse
import json
import time
from typing import Any
import mpmath


def verify_riemann_zeros(
    start_index: int = 1,
    count: int = 100,
    dps: int = 30,
    verbose: bool = False,
) -> dict[str, Any]:
    """Verifica numéricamente ceros no triviales de zeta en la línea crítica con mpmath."""
    mpmath.mp.dps = dps
    anomalies: list[dict[str, str | int]] = []
    errors: list[dict[str, str | int]] = []
    tolerance = mpmath.mpf(10) ** (-dps + 6)

    start_time = time.perf_counter()
    for n in range(start_index, start_index + count):
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
            f"Verificados {count} ceros (desde n={start_index}, dps={dps}) "
            f"en {elapsed:.2f} s | anomalías={len(anomalies)} | errores={len(errors)}"
        )

    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Verifica numéricamente ceros de la función zeta de Riemann."
    )
    parser.add_argument("--start", type=int, default=1, help="Índice inicial (por defecto: 1).")
    parser.add_argument(
        "--count", type=int, default=100, help="Cantidad de ceros a comprobar (por defecto: 100)."
    )
    parser.add_argument(
        "--dps", type=int, default=30, help="Dígitos decimales de precisión (por defecto: 30)."
    )
    parser.add_argument(
        "--json", action="store_true", help="Imprime el resultado estructurado en JSON."
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    summary = verify_riemann_zeros(
        start_index=args.start,
        count=args.count,
        dps=args.dps,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
