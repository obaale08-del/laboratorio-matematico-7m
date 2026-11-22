# Cadena y Nodos Puente — 7 Problemas del Milenio

Archivos puente (conectan 2 o más problemas): **26**

## Verificaciones numéricas y certificación

- `verify_zeros` (`scripts/verify_zeros.py`): **ok**
  - Métricas: `{"start_index": 1, "count": 100, "dps": 30, "tolerance": "1.0e-24", "elapsed_seconds": 16.5115, "anomalies": []}`
- `turing_certify` (`scripts/turing_certify.py`): **ok**
  - Métricas: `{"t_start": 100.0, "t_end": 200.0, "step": 0.05, "dps": 15, "intervals_checked": 2000, "sign_changes_detected": 50}`
- `parallel_verify` (`scripts/parallel_verify.py`): **ok**
  - Métricas: `{"start_index": 1, "count": 200, "dps": 30, "workers": 8, "elapsed_seconds": 9.6287, "anomalies": []}`

## Marcadores Lean (`sorry`/`admit`/`axiom`) acumulados por línea

> Auditoría en `lean_templates/`: **0 `sorry`**, **0 `admit`** y **7 `axiom`** (uno por problema en `rigorous_*.lean` como `*_universal_open_problem`).

- `riemann`: **23** archivos | **1** marcadores Lean
- `p_vs_np`: **17** archivos | **1** marcadores Lean
- `navier_stokes`: **11** archivos | **1** marcadores Lean
- `yang_mills`: **21** archivos | **1** marcadores Lean
- `hodge`: **20** archivos | **1** marcadores Lean
- `birch_swinnerton_dyer`: **15** archivos | **1** marcadores Lean
- `poincare`: **25** archivos | **2** marcadores Lean

## Archivos puente principales

- `docs/HEPTALOGO_MANIFEST.md` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/millennium_dossier_resumen.txt` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/millennium_absolute_resolution.lean` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/millennium_master_unified.lean` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/RED_MILENIO.md` (5 líneas: `riemann`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/milenio_red.json` (5 líneas: `riemann`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/ANALISIS_ESTRUCTURA_MILENIO.md` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `docs/CADENA_MILENIO.md` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `docs/HEPTALOGO_REPORT.md` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/milenio_cadena.json` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `lean_templates/HeptalogoMain.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/MillenniumHeptad.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/PetruskaTactics.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `scripts/milenio_mapa.py` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `lean_templates/HeptalogoDeepExtension.lean` (3 líneas: `yang_mills`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)