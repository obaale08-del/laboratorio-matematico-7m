import argparse
import json
from multiprocessing import Pool
import os
import sys
import time
from typing import Any
import mpmath


def worker_check(task: tuple[int, int]) -> dict[str, Any]:
    """Evalúa un único índice n de cero de zeta a la precisión dps indicada."""
    n, dps = task
    mpmath.mp.dps = dps
    tolerance = mpmath.mpf(10) ** (-dps + 6)
    try:
        zero = mpmath.zetazero(n)
        val = mpmath.zeta(zero)
        if abs(val) > tolerance:
            return {
                "status": "anomaly",
                "index": n,
                "zero": str(zero),
                "zeta_value": str(val),
            }
        return {"status": "ok", "index": n}
    except Exception as exc:
        return {"status": "error", "index": n, "error": str(exc)}


def parallel_verify(
    start_index: int = 1,
    count: int = 200,
    dps: int = 30,
    workers: int | None = None,
    chunksize: int = 10,
    verbose: bool = False,
) -> dict[str, Any]:
    """Ejecuta la verificación de ceros de zeta en paralelo usando un pool de procesos."""
    num_workers = workers if workers and workers > 0 else (os.cpu_count() or 1)
    tasks = [(n, dps) for n in range(start_index, start_index + count)]

    anomalies: list[dict[str, Any]] = []
    errors: list[dict[str, Any]] = []
    completed = 0

    start_time = time.perf_counter()
    with Pool(processes=num_workers) as pool:
        for item in pool.imap_unordered(worker_check, tasks, chunksize=max(1, chunksize)):
            completed += 1
            if item["status"] == "anomaly":
                anomalies.append(item)
            elif item["status"] == "error":
                errors.append(item)

            if verbose and (completed % 50 == 0 or completed == count):
                elapsed = time.perf_counter() - start_time
                pct = (completed / max(count, 1)) * 100.0
                sys.stdout.write(
                    f"\rProgreso: {completed}/{count} ({pct:.1f}%) - Tiempo: {elapsed:.1f}s"
                )
                sys.stdout.flush()

    if verbose and count > 0:
        sys.stdout.write("\n")

    elapsed = time.perf_counter() - start_time
    result = {
        "start_index": start_index,
        "count": count,
        "dps": dps,
        "workers": num_workers,
        "elapsed_seconds": round(elapsed, 4),
        "anomalies": anomalies,
        "errors": errors,
        "all_within_tolerance": len(anomalies) == 0 and len(errors) == 0,
    }

    if verbose:
        print(
            f"Paralelo finalizado en {elapsed:.2f}s ({num_workers} procesos) | "
            f"anomalías={len(anomalies)} | errores={len(errors)}"
        )

    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Verifica ceros de Riemann en paralelo con multiprocessing."
    )
    parser.add_argument("--start", type=int, default=1, help="Índice inicial (por defecto: 1).")
    parser.add_argument(
        "--count", type=int, default=200, help="Cantidad de ceros (por defecto: 200)."
    )
    parser.add_argument(
        "--dps", type=int, default=30, help="Precisión decimal en dígitos (por defecto: 30)."
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=None,
        help="Número de procesos (por defecto: núcleos disponibles).",
    )
    parser.add_argument(
        "--chunksize",
        type=int,
        default=10,
        help="Tamaño de lote para imap_unordered (por defecto: 10).",
    )
    parser.add_argument(
        "--json", action="store_true", help="Imprime el resumen en formato JSON."
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    summary = parallel_verify(
        start_index=args.start,
        count=args.count,
        dps=args.dps,
        workers=args.workers,
        chunksize=args.chunksize,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
