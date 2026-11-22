# Cadena y Nodos Puente — 7 Problemas del Milenio

Archivos puente (conectan 2 o más problemas): **23**

## Verificaciones numéricas y certificación

- `verify_zeros` (`scripts/verify_zeros.py`): **ok**
  - Métricas: `{"start_index": 1, "count": 100, "dps": 30, "tolerance": "1.0e-24", "elapsed_seconds": 15.0874, "anomalies": []}`
- `turing_certify` (`scripts/turing_certify.py`): **timeout**
  - Detalle: `timeout tras 25s`
- `parallel_verify` (`scripts/parallel_verify.py`): **ok**
  - Métricas: `{"start_index": 1, "count": 200, "dps": 30, "workers": 8, "elapsed_seconds": 6.0594, "anomalies": []}`

## Marcadores Lean (`sorry`/`admit`/`axiom`) acumulados por línea

- `riemann`: **22** archivos | **1** marcadores Lean
- `p_vs_np`: **17** archivos | **1** marcadores Lean
- `navier_stokes`: **9** archivos | **1** marcadores Lean
- `yang_mills`: **20** archivos | **1** marcadores Lean
- `hodge`: **17** archivos | **1** marcadores Lean
- `birch_swinnerton_dyer`: **15** archivos | **1** marcadores Lean
- `poincare`: **24** archivos | **2** marcadores Lean

## Archivos puente principales

- `docs/HEPTALOGO_MANIFEST.md` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/millennium_dossier_resumen.txt` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/millennium_absolute_resolution.lean` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/millennium_master_unified.lean` (7 líneas: `riemann`, `p_vs_np`, `navier_stokes`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/RED_MILENIO.md` (5 líneas: `riemann`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/milenio_red.json` (5 líneas: `riemann`, `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/CADENA_MILENIO.md` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `docs/HEPTALOGO_REPORT.md` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `docs/milenio_cadena.json` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `lean_templates/HeptalogoMain.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/MillenniumHeptad.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/PetruskaTactics.lean` (4 líneas: `yang_mills`, `hodge`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `scripts/milenio_mapa.py` (4 líneas: `riemann`, `yang_mills`, `hodge`, `poincare`; marcadores Lean: 0)
- `lean_templates/HeptalogoDeepExtension.lean` (3 líneas: `yang_mills`, `birch_swinnerton_dyer`, `poincare`; marcadores Lean: 0)
- `lean_templates/espectro_unificado_milenioum.lean` (3 líneas: `riemann`, `navier_stokes`, `yang_mills`; marcadores Lean: 0)