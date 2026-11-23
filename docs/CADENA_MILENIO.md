# Cadena y Nodos Puente — 7 Problemas del Milenio

Archivos puente (conectan 2 o más problemas): **19**

## Verificaciones numéricas y certificación

- `verify_zeros` (`scripts/verify_zeros.py`): **timeout**
  - Detalle: `timeout tras 60s`
- `turing_certify` (`scripts/turing_certify.py`): **timeout**
  - Detalle: `timeout tras 60s`
- `parallel_verify` (`scripts/parallel_verify.py`): **ok**
  - Métricas: `{"start_index": 1, "count": 200, "dps": 30, "workers": 8, "elapsed_seconds": 31.4237, "anomalies": []}`

## Marcadores Lean (`sorry`/`admit`/`axiom`) acumulados por línea

> Auditoría en `lean_templates/`: **0 `sorry`**, **0 `admit`** y **7 `axiom`** (uno por problema en `rigorous_*.lean` como `*_universal_open_problem`).

- `riemann`: **25** archivos | **1** marcadores Lean
- `p_vs_np`: **9** archivos | **1** marcadores Lean
- `navier_stokes`: **11** archivos | **1** marcadores Lean
- `yang_mills`: **22** archivos | **1** marcadores Lean
- `hodge`: **20** archivos | **1** marcadores Lean
- `birch_swinnerton_dyer`: **17** archivos | **1** marcadores Lean
- `poincare`: **21** archivos | **1** marcadores Lean

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