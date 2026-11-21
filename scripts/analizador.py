import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]


def analizar_rendimiento(
    input_path: str | os.PathLike,
    scale_width: int = 1280,
    crf: int = 28,
    preset: str = "ultrafast",
    verbose: bool = False,
) -> dict[str, Any]:
    """Mide tiempo de transcodificación y reducción de tamaño con ffmpeg."""
    src_path = Path(input_path)
    if not src_path.exists() or not src_path.is_file():
        raise FileNotFoundError(f"No se encuentra el archivo de entrada: {src_path}")

    orig_bytes = src_path.stat().st_size
    orig_mb = orig_bytes / (1024 * 1024)

    with tempfile.NamedTemporaryFile(suffix=".mp4", delete=False) as tmp_file:
        tmp_output = Path(tmp_file.name)

    start_time = time.perf_counter()
    try:
        cmd = [
            "ffmpeg",
            "-y",
            "-i",
            str(src_path),
            "-vf",
            f"scale={scale_width}:-2",
            "-vcodec",
            "libx264",
            "-preset",
            preset,
            "-crf",
            str(crf),
            "-threads",
            "0",
            "-pix_fmt",
            "yuv420p",
            "-acodec",
            "aac",
            "-b:a",
            "96k",
            str(tmp_output),
        ]
        subprocess.run(
            cmd,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        elapsed_time = time.perf_counter() - start_time

        new_bytes = tmp_output.stat().st_size if tmp_output.exists() else 0
        new_mb = new_bytes / (1024 * 1024)
        ratio_pct = ((1.0 - (new_mb / orig_mb)) * 100.0) if orig_mb > 0 else 0.0

        result = {
            "input_path": str(src_path),
            "original_mb": round(orig_mb, 2),
            "compressed_mb": round(new_mb, 2),
            "reduction_percent": round(ratio_pct, 2),
            "elapsed_seconds": round(elapsed_time, 2),
            "scale_width": scale_width,
            "crf": crf,
            "preset": preset,
        }

        if verbose:
            print(f"Archivo original: {orig_mb:.2f} MB")
            print(f"Tiempo de procesamiento: {elapsed_time:.2f} s")
            print(f"Tamaño comprimido: {new_mb:.2f} MB")
            print(f"Tasa de reducción: {ratio_pct:.2f}%")

        return result
    except FileNotFoundError as exc:
        raise RuntimeError("No se encontró 'ffmpeg' en el PATH del sistema.") from exc
    except subprocess.CalledProcessError as exc:
        output_msg = exc.stdout.decode("utf-8", errors="ignore") if exc.stdout else ""
        raise RuntimeError(f"Error durante la ejecución de ffmpeg:\n{output_msg}") from exc
    finally:
        if tmp_output.exists():
            tmp_output.unlink(missing_ok=True)


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Analiza rendimiento y compresión de vídeo mediante ffmpeg."
    )
    parser.add_argument(
        "--input",
        required=True,
        help="Ruta al archivo de vídeo de entrada.",
    )
    parser.add_argument(
        "--width",
        type=int,
        default=1280,
        help="Ancho de escalado conservando proporción (por defecto: 1280).",
    )
    parser.add_argument(
        "--crf",
        type=int,
        default=28,
        help="Factor de calidad CRF para libx264 (por defecto: 28).",
    )
    parser.add_argument(
        "--preset",
        default="ultrafast",
        help="Preset de codificación libx264 (por defecto: ultrafast).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Imprime el resultado en formato JSON.",
    )
    return parser


if __name__ == "__main__":
    args = _build_parser().parse_args()
    summary = analizar_rendimiento(
        input_path=args.input,
        scale_width=args.width,
        crf=args.crf,
        preset=args.preset,
        verbose=not args.json,
    )
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
