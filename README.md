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
