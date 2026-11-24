# Cadena y Nodos Puente — 7 Problemas del Milenio

Archivos puente (conectan 2 o más problemas): **38**

## Verificaciones numéricas y certificación

- `verify_zeros` (`scripts/verify_zeros.py`): **ok**
  - Métricas: `{"start_index": 1, "count": 100, "dps": 30, "tolerance": "1.0e-24", "elapsed_seconds": 14.8634, "anomalies": []}`
- `turing_certify` (`scripts/turing_certify.py`): **ok**
  - Métricas: `{"t_start": 100.0, "t_end": 200.0, "step": 0.05, "dps": 15, "intervals_checked": 2000, "sign_changes_detected": 50}`
- `parallel_verify` (`scripts/parallel_verify.py`): **ok**
  - Métricas: `{"start_index": 1, "count": 200, "dps": 30, "workers": 8, "elapsed_seconds": 8.6328, "anomalies": []}`
- `puente_ym` (`scripts/puente_ym_lean.py`): **ok**
  - Métricas: `{"archivos": [{"archivo": "ym_experimentos.txt", "delta": 0.25, "total_activos": 2, "bloques": [{"bloque": "ym_experimentos", "delta": 0.25, "E_sweep": 0.3169, "x_max": 0.3809, "activos": 2, "StrictMassGapBound": true, "E_sweep_ge_delta": true, "x_max_ge_sweep": true, "sweep_bound_crosses_gap_holds": true, "muestras_activas": [{"seccion": "general", "etiqueta": "E4_baja_disipacion", "E_cin": 0.1013, "Aporte": 0.2797, "E_tot": 0.3809, "Margen": 0.1309, "Estado": "ACTIVA"}, {"seccion": "general", "etiqueta": "E6_masa_mayor_lento", "E_cin": 0.1531, "Aporte": 0.1637, "E_tot": 0.3169, "Margen": 0.0669, "Estado": "ACTIVA"}]}]}, {"archivo": "ym_barrido.txt", "delta": 0.25, "total_activos": 6, "bloques": [{"bloque": "1:Variando FORMA (duracion=1.0, disipacion=0.4)", "delta": 0.25, "E_sweep": 0.2594, "x_max": 0.2943, "activos": 2, "StrictMassGapBound": true, "E_sweep_ge_delta": true, "x_max_ge_sweep": true, "sweep_bound_crosses_gap_holds": true, "muestras_activas": [{"seccion": "1:Variando FORMA (duracion=1.0, disipacion=0.4)", "etiqueta": "0.85", "E_cin": 0.0612, "Aporte": 0.1981, "E_tot": 0.2594, "Margen": 0.0094, "Estado": "ACTIVA"}, {"seccion": "1:Variando FORMA (duracion=1.0, disipacion=0.4)", "etiqueta": "1.00", "E_cin": 0.0612, "Aporte": 0.2331, "E_tot": 0.2943, "Margen": 0.0443, "Estado": "ACTIVA"}]}, {"bloque": "2:Variando DURACION (forma=0.80, disipacion=0.4)", "delta": 0.25, "E_sweep": 0.276, "x_max": 0.2956, "activos": 2, "StrictMassGapBound": true, "E_sweep_ge_delta": true, "x_max_ge_sweep": true, "sweep_bound_crosses_gap_holds": true, "muestras_activas": [{"seccion": "2:Variando DURACION (forma=0.80, disipacion=0.4)", "etiqueta": "1.50", "E_cin": 0.0612, "Aporte": 0.2147, "E_tot": 0.276, "Margen": 0.026, "Estado": "ACTIVA"}, {"seccion": "2:Variando DURACION (forma=0.80, disipacion=0.4)", "etiqueta": "2.50", "E_cin": 0.0612, "Aporte": 0.2344, "E_tot": 0.2956, "Margen": 0.0456, "Estado": "ACTIVA"}]}, {"bloque": "3:Variando DISIPACION (forma=0.80, duracion=1.0)", "delta": 0.25, "E_sweep": 0.2788, "x_max": 0.3223, "activos": 2, "StrictMassGapBound": true, "E_sweep_ge_delta": true, "x_max_ge_sweep": true, "sweep_bound_crosses_gap_holds": true, "muestras_activas": [{"seccion": "3:Variando DISIPACION (forma=0.80, duracion=1.0)", "etiqueta": "0.00", "E_cin": 0.0612, "Aporte": 0.261, "E_tot": 0.3223, "Margen": 0.0723, "Estado": "ACTIVA"}, {"seccion": "3:Variando DISIPACION (forma=0.80, duracion=1.0)", "etiqueta": "0.20", "E_cin": 0.0612, "Aporte": 0.2175, "E_tot": 0.2788, "Margen": 0.0288, "Estado": "ACTIVA"}]}]}, {"archivo": "ym_compensacion.txt", "delta": 0.25, "total_activos": 1, "bloques": [{"bloque": "ym_compensacion", "delta": 0.25, "E_sweep": 0.2608, "x_max": 0.2608, "activos": 1, "StrictMassGapBound": true, "E_sweep_ge_delta": true, "x_max_ge_sweep": true, "sweep_bound_crosses_gap_holds": true, "muestras_activas": [{"seccion": "general", "etiqueta": "C4_forma055_dur20_dis01", "E_cin": 0.0612, "Aporte": 0.1995, "E_tot": 0.2608, "Margen": 0.0108, "Estado": "ACTIVA"}]}]}]}`

## Marcadores Lean (`sorry`/`admit`/`axiom`) acumulados por línea

> Auditoría en `lean_templates/`: **0 `sorry`**, **0 `admit`** y **7 `axiom`** (uno por problema en `rigorous_*.lean` como `*_universal_open_problem`).

- `riemann`: **80** archivos | **2** marcadores Lean
- `p_vs_np`: **11** archivos | **1** marcadores Lean
- `navier_stokes`: **12** archivos | **1** marcadores Lean
- `yang_mills`: **29** archivos | **1** marcadores Lean
- `hodge`: **34** archivos | **1** marcadores Lean
- `birch_swinnerton_dyer`: **17** archivos | **1** marcadores Lean
- `poincare`: **984** archivos | **39** marcadores Lean

## Archivos puente principales

- `docs/millennium_dossier_resumen.txt` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `scripts/verificar_cotas.py` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/HEPTALOGO_MANIFEST.md` (6 líneas: `riemann`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/millennium_absolute_resolution.lean` (6 líneas: `riemann`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/millennium_master_unified.lean` (6 líneas: `riemann`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `scripts/milenio_mapa.py` (6 líneas: `riemann`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/RED_MILENIO.md` (5 líneas: `riemann`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/milenio_red.json` (5 líneas: `riemann`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/ANALISIS_ESTRUCTURA_MILENIO.md` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `docs/CADENA_MILENIO.md` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `docs/HEPTALOGO_REPORT.md` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/milenio_cadena.json` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `lean_templates/HeptalogoMain.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/MillenniumHeptad.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/PetruskaTactics.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)