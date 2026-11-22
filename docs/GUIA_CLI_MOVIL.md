# Guía CLI Rápida — Laboratorio en Termux

## 1. Ciclo principal (auditoría, reportes y push)
~~~bash
cd ~/repo_petruska_fenix
python3 scripts/tejer_y_subir.py -m "feat(scope): resumen breve del cambio"
~~~

## 2. Auditoría formal en Lean 4
~~~bash
python3 scripts/lean_auditor.py --json
~~~
Referencia base: `0` `sorry`/`admit` y `7` axiomas explícitos de conjetura abierta.

## 3. Verificación numérica (criterio práctico en móvil)
- **Serie (`verify_zeros.py`):** lotes moderados (p. ej. `count=100..150`, `dps=30`). Con `count=220` en carga acumulada ronda los ~55 s.
- **Paralelo (`parallel_verify.py`):** preferible en lotes mayores (`count=200..450`, `workers=8`, `dps=30`).
- **Certificación de Turing (`turing_certify.py`):** vigilar rango y paso (`100..300` con `step=0.05` ronda los ~33 s).

~~~bash
python3 scripts/verify_zeros.py --start 1 --count 100 --dps 30 --json
python3 scripts/parallel_verify.py --start 1 --count 200 --dps 30 --workers 8 --json
python3 scripts/turing_certify.py --t-start 100.0 --t-end 200.0 --step 0.05 --dps 15 --json
~~~

## 4. Benchmark de carga en el teléfono
~~~bash
python3 scripts/benchmark_movil.py --tier standard
python3 scripts/benchmark_movil.py --tier high
~~~

## 5. Empaquetado y restauración con integridad (`$TMPDIR`)
En Termux usa `$TMPDIR` (o `$HOME/.cache`) en lugar de `/tmp`:

~~~bash
LAB_TMP="${TMPDIR:-$HOME/.cache}/shield_work"
mkdir -p "$LAB_TMP"
cp docs/millennium_dossier_resumen.txt "$LAB_TMP/entrada.txt"

python3 scripts/crypto_shield.py \
  --bundle "$LAB_TMP/entrada.txt" \
  --out "$LAB_TMP/salida.enc" \
  --cert "$LAB_TMP/cert.json" \
  --seed "tu-semilla-privada" \
  --json

python3 scripts/crypto_unshield.py \
  --enc "$LAB_TMP/salida.enc" \
  --cert "$LAB_TMP/cert.json" \
  --out "$LAB_TMP/restaurado.txt" \
  --seed "tu-semilla-privada" \
  --json

rm -rf "$LAB_TMP"
~~~
