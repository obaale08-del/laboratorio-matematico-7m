# Historial trazable — Yang-Mills (exploración y estado)

> **Alcance:** Bitácora generada automáticamente desde el laboratorio experimental para trazar barridos numéricos, módulos Lean 4 y estado de trabajo antes de hacer `push`. Las cotas numéricas y plantillas formales no constituyen una resolución del problema abierto.

## Registro 1: cuatro_facetas_y_serie_disipacion
- **Fecha (UTC):** `2026-11-24T10:05:32.428753+00:00`
- **Git:** rama `main` en commit `6e71767` | cambios locales: `8`
- **Bloques activos:** `5` | **Muestras activas:** `9`
- **Notas:** Documentadas 4 facetas y expresion de energia en docs/NOTAS_EXPLORACION_YM.md; anadido scripts/correr_serie_ym.py (E_sweep=0.2012, x_max=0.2612, 1/3 cruza 0.25)

| Archivo | Bloque | Umbral | E_sweep | x_max | Activos | Cruce |
| :--- | :--- | ---: | ---: | ---: | ---: | :---: |
| `ym_experimentos.txt` | `ym_experimentos` | 0.25 | 0.3169 | 0.3809 | 2 | True |
| `ym_barrido.txt` | `1:Variando FORMA (duracion=1.0, disipacion=0.4)` | 0.25 | 0.2594 | 0.2943 | 2 | True |
| `ym_barrido.txt` | `2:Variando DURACION (forma=0.80, disipacion=0.4)` | 0.25 | 0.276 | 0.2956 | 2 | True |
| `ym_barrido.txt` | `3:Variando DISIPACION (forma=0.80, duracion=1.0)` | 0.25 | 0.2788 | 0.3223 | 2 | True |
| `ym_compensacion.txt` | `ym_compensacion` | 0.25 | 0.2608 | 0.2608 | 1 | True |

## Registro 2: baseline_ym_puente
- **Fecha (UTC):** `2026-11-24T09:13:11.939259+00:00`
- **Git:** rama `main` en commit `6e71767` | cambios locales: `4`
- **Bloques activos:** `5` | **Muestras activas:** `9`
- **Notas:** Primera captura trazable de bloques activos y modulos Lean de Yang-Mills

| Archivo | Bloque | Umbral | E_sweep | x_max | Activos | Cruce |
| :--- | :--- | ---: | ---: | ---: | ---: | :---: |
| `ym_experimentos.txt` | `ym_experimentos` | 0.25 | 0.3169 | 0.3809 | 2 | True |
| `ym_barrido.txt` | `1:Variando FORMA (duracion=1.0, disipacion=0.4)` | 0.25 | 0.2594 | 0.2943 | 2 | True |
| `ym_barrido.txt` | `2:Variando DURACION (forma=0.80, disipacion=0.4)` | 0.25 | 0.276 | 0.2956 | 2 | True |
| `ym_barrido.txt` | `3:Variando DISIPACION (forma=0.80, duracion=1.0)` | 0.25 | 0.2788 | 0.3223 | 2 | True |
| `ym_compensacion.txt` | `ym_compensacion` | 0.25 | 0.2608 | 0.2608 | 1 | True |
