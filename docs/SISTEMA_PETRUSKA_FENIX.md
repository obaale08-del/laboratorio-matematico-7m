# Arquitectura y Funcionamiento del Sistema — Petruska Fenix

Este documento describe **Petruska Fenix** (`laboratorio-matematico-7m`) como sistema de trabajo: cómo se relacionan sus carpetas, qué hace cada componente, cómo se diseñan sus funciones para ser portables y cuál es el alcance de cada tipo de archivo.

---

## 1. Visión general del sistema

Petruska Fenix está planteado como un **laboratorio experimental y de auditoría** que articula tres capas complementarias:

1. **Capa documental (`docs/`):** define el marco conceptual, manifiestos, reportes y resúmenes de referencia (`HEPTALOGO_MANIFEST.md`, `HEPTALOGO_REPORT.md`, `millennium_dossier.pdf`, `millennium_dossier_resumen.txt`).
2. **Capa formal / plantillas Lean 4 (`lean_templates/`):** reúne la configuración del proyecto (`lakefile.lean`, `Main.lean`), tácticas auxiliares (`PetruskaTactics.lean`), módulos base o constructivos y borradores o plantillas organizadas por líneas temáticas y marcos unificados.
3. **Capa computacional y de auditoría (`scripts/`):** proporciona utilidades en Python para inspección estática de archivos `.lean`, generación de plantillas, pruebas numéricas con precisión arbitraria, ejecución paralela, análisis de rendimiento y empaquetado/restauración de archivos.

---

## 2. Flujo de interacción entre capas

El sistema no pretende ser un único programa monolítico, sino un conjunto de herramientas desacopladas que pueden usarse por separado o encadenarse según la tarea:

* **Contexto y trazabilidad (`docs/`):** sirve como punto de partida conceptual y de referencia antes de revisar plantillas o lanzar verificaciones.
* **Exploración y cálculo numérico (`scripts/`):** scripts como `verify_zeros.py`, `verify_riemann_zeros.py`, `parallel_verify.py` y `turing_certify.py` permiten realizar comprobaciones numéricas parametrizables y observar comportamientos o cambios de signo en intervalos.
* **Formalización y auditoría (`lean_templates/` + `lean_auditor.py` + `lean_exporter.py`):** permite mantener borradores o plantillas en Lean 4, generar nuevas plantillas de forma consistente (`LeanExporter`) y auditar los archivos `.lean` en busca de `sorry`, `admit` o `axiom` (`audit_lean_files`).
* **Soporte operativo y empaquetado (`analizador.py`, `crypto_shield.py`, `crypto_unshield.py`):** cubren tareas auxiliares como medición de rendimiento con `ffmpeg` o empaquetado/restauración con comprobación de integridad SHA-256.

---

## 3. Estándar de diseño para funciones y scripts

Para que el repositorio sea factible para cualquier usuario y fácil de mantener en distintos entornos (incluidos entornos móviles como Termux, Linux o estaciones de trabajo):

* **Rutas portables:** se evita depender de rutas absolutas fijas de un dispositivo concreto. Los scripts resuelven la raíz del repositorio mediante `pathlib.Path(__file__).resolve().parents[1]` y aceptan rutas explícitas por parámetro o argumento CLI.
* **Separación entre núcleo y CLI:** las funciones y clases principales (`audit_lean_files`, `LeanExporter`, etc.) reciben parámetros claros y devuelven estructuras de datos o rutas útiles, mientras que `argparse` y la impresión por consola viven en la capa de ejecución.
* **Valores por defecto razonables:** los cálculos numéricos y comprobaciones deben poder probarse con parámetros ligeros por defecto y escalarse mediante flags explícitos (`--start`, `--count`, `--dps`, `--step`, etc.).
* **Transparencia sobre rigor y seguridad:**
  * Una plantilla o borrador en `lean_templates/` o un reporte de `lean_auditor.py` indica el estado estructural del código y la presencia o ausencia de huecos (`sorry`/`admit`) o axiomas, no una validación matemática externa automática por sí sola.
  * Las utilidades `crypto_shield.py` y `crypto_unshield.py` aplican transformación XOR derivada de hash con verificación SHA-256; son útiles para empaquetado/verificación de integridad local sencilla, pero no sustituyen criptografía estándar para secretos críticos.

---

## 4. Alcance y límites del laboratorio

Petruska Fenix es un **espacio de investigación experimental, prototipado y auditoría**. Cada módulo debe interpretarse según su naturaleza:

* **Numérico / heurístico:** exploración de valores, precisión decimal y detección de cambios de signo o anomalías dentro de tolerancias definidas.
* **Formal / estructural:** organización de enunciados, tácticas y borradores en Lean 4 junto con auditoría estática de marcadores (`sorry`, `admit`, `axiom`).
* **Documental:** registro de ideas, manifiestos y síntesis del proyecto.
