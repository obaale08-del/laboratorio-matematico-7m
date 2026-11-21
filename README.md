# Petruska Fenix — Laboratorio Matemático Experimental 7M

Entorno experimental y de auditoría para investigación matemática numérica, plantillas formales en Lean 4 y documentación del proyecto **Petruska Fenix**. Combina scripts en Python, módulos y borradores en Lean 4, y documentos de referencia para explorar, auditar y estructurar hipótesis y cálculos.

> **Estado del proyecto:** Este repositorio reúne código experimental, borradores de trabajo, verificaciones numéricas y plantillas formales en desarrollo. La presencia de un archivo o plantilla en `lean_templates/` o un script en `scripts/` indica material de trabajo o auditoría, no necesariamente una demostración formal completa verificada.

## Estructura del repositorio

- `docs/`: `HEPTALOGO_MANIFEST.md`, `HEPTALOGO_REPORT.md`, `millennium_dossier.pdf` y `millennium_dossier_resumen.txt`.
- `lean_templates/`: `lakefile.lean`, `Main.lean`, `PetruskaTactics.lean`, módulos base/constructivos y borradores o plantillas por línea temática.
- `scripts/`: `analizador.py`, `crypto_shield.py`, `crypto_unshield.py`, `lean_auditor.py`, `lean_exporter.py`, `parallel_verify.py`, `turing_certify.py`, `verify_riemann_zeros.py` y `verify_zeros.py`.

## Uso y criterios de portabilidad

- Trabaja con rutas relativas a la raíz del repositorio (`pathlib.Path(__file__).resolve().parents[1]`) o argumentos explícitos.
- Separa las funciones reutilizables de cálculo, auditoría o exportación respecto a la interfaz CLI (`argparse` / `if __name__ == "__main__":`).
- Comprueba siempre `git status` y `git diff` antes de hacer `commit` y `push` a `main`.

---

## Uso rápido de los scripts (`scripts/`)

Todos los scripts admiten `--help` y `--json` (donde aplica) y resuelven rutas relativas a la raíz del repositorio cuando no se indica una ruta explícita.

### Auditoría y generación de plantillas Lean 4

- Auditar `lean_templates/` sin generar log: `python3 scripts/lean_auditor.py --no-log`
- Auditar con salida JSON: `python3 scripts/lean_auditor.py --no-log --json`
- Generar una plantilla de teorema: `python3 scripts/lean_exporter.py --problem "Ejemplo base" --slug "ejemplo_base" --statement "1 + 1 = 2" --tactic "norm_num"`

### Verificación numérica y escaneo de cambios de signo

- Verificación secuencial rápida: `python3 scripts/verify_zeros.py --count 50 --dps 25`
- Verificación con progreso periódico: `python3 scripts/verify_riemann_zeros.py --start 1 --count 50 --progress-every 10`
- Verificación paralela: `python3 scripts/parallel_verify.py --start 1 --count 100 --workers 2`
- Escaneo de cambios de signo en `Z(t)` (`mpmath.siegelz`): `python3 scripts/turing_certify.py --t-start 100 --t-end 150 --step 0.1 --dps 15`

### Análisis de rendimiento y empaquetado con integridad

- Medir transcodificación con `ffmpeg`: `python3 scripts/analizador.py --input ruta/a/video.mp4`
- Empaquetar bundle con XOR + SHA-256: `python3 scripts/crypto_shield.py --bundle ruta/al/bundle.tar.gz`
- Restaurar bundle y verificar SHA-256: `python3 scripts/crypto_unshield.py --out ruta/al/restaurado.tar.gz`
