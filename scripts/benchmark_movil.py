import argparse
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUT = REPO_ROOT / "docs" / "benchmark_movil.json"


def _run_cmd(args: list[str], timeout_s: int = 90) -> dict[str, Any]:
    t0 = time.perf_counter()
    try:
        proc = subprocess.run(
            [sys.executable, *args],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=timeout_s,
        )
        elapsed = round(time.perf_counter() - t0, 4)
        parsed: Any = None
        if proc.stdout.strip():
            try:
                parsed = json.loads(proc.stdout.strip().splitlines()[-1])
            except Exception:
                parsed = proc.stdout.strip()[-400:]
        return {
            "cmd": " ".join(args),
            "returncode": proc.returncode,
            "status": "ok" if proc.returncode == 0 else "error",
            "wall_seconds": elapsed,
            "output": parsed,
            "stderr_tail": proc.stderr.strip()[-300:] if proc.stderr.strip() else "",
        }
    except subprocess.TimeoutExpired:
        return {
            "cmd": " ".join(args),
            "returncode": -1,
            "status": "timeout",
            "wall_seconds": float(timeout_s),
            "output": None,
            "stderr_tail": f"Superado timeout de {timeout_s}s",
        }


def _cases_for_tier(tier: str) -> list[tuple[str, list[str]]]:
    if tier == "high":
        return [
            ("verify_zeros_220", ["scripts/verify_zeros.py", "--start", "1", "--count", "220", "--dps", "30", "--json"]),
            ("parallel_verify_450_w8", ["scripts/parallel_verify.py", "--start", "1", "--count", "450", "--dps", "30", "--workers", "8", "--json"]),
            ("turing_100_300_step005", ["scripts/turing_certify.py", "--t-start", "100.0", "--t-end", "300.0", "--step", "0.05", "--dps", "15", "--json"]),
        ]
    return [
        ("verify_zeros_150", ["scripts/verify_zeros.py", "--start", "1", "--count", "150", "--dps", "30", "--json"]),
        ("parallel_verify_300_w8", ["scripts/parallel_verify.py", "--start", "1", "--count", "300", "--dps", "30", "--workers", "8", "--json"]),
        ("turing_100_250_step005", ["scripts/turing_certify.py", "--t-start", "100.0", "--t-end", "250.0", "--step", "0.05", "--dps", "15", "--json"]),
    ]


def run_benchmark(out_json: Path = DEFAULT_OUT, timeout_s: int = 90, tier: str = "standard") -> dict[str, Any]:
    """Ejecuta pruebas escalonadas de verificación numérica midiendo tiempos reales en móvil."""
    cases = _cases_for_tier(tier)
    results: dict[str, Any] = {
        "generated_at_epoch": round(time.time(), 2),
        "tier": tier,
        "timeout_per_case_s": timeout_s,
        "cases": {},
    }
    for name, cmd_args in cases:
        print(f"[{tier}] Ejecutando {name}...")
        info = _run_cmd(cmd_args, timeout_s=timeout_s)
        results["cases"][name] = info
        print(f"  -> estado: {info['status']} | tiempo real: {info['wall_seconds']}s")

    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(results, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"Benchmark guardado en: {out_json}")
    return results


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Benchmark numérico controlado en Termux.")
    p.add_argument("--tier", choices=["standard", "high"], default="standard", help="Nivel de carga del benchmark.")
    p.add_argument("--out-json", default=str(DEFAULT_OUT), help="Ruta JSON de salida.")
    p.add_argument("--timeout", type=int, default=90, help="Timeout por prueba en segundos.")
    return p


if __name__ == "__main__":
    args = _build_parser().parse_args()
    run_benchmark(out_json=Path(args.out_json), timeout_s=args.timeout, tier=args.tier)
