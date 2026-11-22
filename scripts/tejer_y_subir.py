import argparse
import json
from pathlib import Path
import subprocess
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_cmd(cmd: list[str], cwd: Path = REPO_ROOT) -> subprocess.CompletedProcess[str]:
    return subprocess.run(cmd, cwd=str(cwd), text=True, capture_output=True)


def weave_and_push(
    commit_message: str,
    paths_to_add: list[str],
    do_push: bool = True,
    verbose: bool = False,
) -> dict[str, Any]:
    """Ejecuta mapa + tejido de cadena + auditoría Lean, hace commit y push opcional."""
    steps: dict[str, Any] = {}

    for name, script_rel, extra_args in [
        ("milenio_mapa", "scripts/milenio_mapa.py", ["--json"]),
        ("tejer_red", "scripts/tejer_red.py", ["--json"]),
        ("lean_auditor", "scripts/lean_auditor.py", ["--no-log", "--json"]),
    ]:
        proc = _run_cmd([sys.executable, str(REPO_ROOT / script_rel), *extra_args])
        steps[name] = {
            "returncode": proc.returncode,
            "output": proc.stdout.strip() or proc.stderr.strip(),
        }
        if proc.returncode != 0:
            raise RuntimeError(f"Fallo en {script_rel}:\n{proc.stderr or proc.stdout}")

    add_cmd = ["git", "add"] + (paths_to_add if paths_to_add else ["."])
    add_proc = _run_cmd(add_cmd)
    steps["git_add"] = {
        "returncode": add_proc.returncode,
        "output": add_proc.stdout.strip() or add_proc.stderr.strip(),
    }
    if add_proc.returncode != 0:
        raise RuntimeError(f"Fallo en git add:\n{add_proc.stderr}")

    status_proc = _run_cmd(["git", "status", "--porcelain"])
    pending = [line for line in status_proc.stdout.splitlines() if line.strip()]
    if not pending:
        result = {"status": "nothing_to_commit", "steps": steps}
        if verbose:
            print("No hay cambios pendientes para commit.")
        return result

    commit_proc = _run_cmd(["git", "commit", "-m", commit_message])
    steps["git_commit"] = {
        "returncode": commit_proc.returncode,
        "output": commit_proc.stdout.strip() or commit_proc.stderr.strip(),
    }
    if commit_proc.returncode != 0:
        raise RuntimeError(f"Fallo en git commit:\n{commit_proc.stderr}")

    pushed = False
    push_output = ""
    if do_push:
        push_proc = _run_cmd(["git", "push", "origin", "main"])
        pushed = push_proc.returncode == 0
        push_output = push_proc.stdout.strip() or push_proc.stderr.strip()
        steps["git_push"] = {
            "returncode": push_proc.returncode,
            "output": push_output,
        }
        if push_proc.returncode != 0:
            raise RuntimeError(f"Fallo en git push origin main:\n{push_output}")

    result = {
        "status": "pushed" if pushed else "committed",
        "commit_message": commit_message,
        "steps": steps,
    }
    if verbose:
        print(f"Estado final: {result['status']} | commit: {commit_message}")
    return result


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Conecta mapa + tejido de cadena + auditoría Lean + commit + push."
    )
    parser.add_argument(
        "-m",
        "--message",
        default="feat(chain): weave millennium network bridges and automate push pipeline",
        help="Mensaje del commit.",
    )
    parser.add_argument(
        "--add",
        nargs="*",
        default=[],
        help="Rutas específicas a añadir (por defecto añade todo).",
    )
    parser.add_argument(
        "--no-push",
        action="store_true",
        help="Solo ejecuta el pipeline y el commit sin hacer git push.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Imprime el resultado en JSON.",
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    out = weave_and_push(
        commit_message=args.message,
        paths_to_add=args.add,
        do_push=not args.no_push,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(out, indent=2, ensure_ascii=False))
