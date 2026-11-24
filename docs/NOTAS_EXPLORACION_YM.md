# Notas de Exploración Experimental — Yang-Mills

> **Alcance y separación de capas:** Este documento recoge el marco conceptual
> experimental de las series y expresiones de energía ("hamiltonianos" de trabajo)
> exploradas en el laboratorio. Es material de exploración numérica y diseño;
> **no** equivale a una demostración formal del problema abierto de Yang-Mills y
> la brecha de masa, ni sustituye la verificación en Lean 4.

---

## 1. Las 4 dimensiones / facetas del experimento

Para organizar las variables de cada prueba sin perder el foco, cada serie se
analiza a través de **cuatro facetas (dimensiones operativas)**:

1. **Forma / Configuración (`forma`)**: perfil o estado inicial de partida en la
   simulación (por ejemplo `0.55`, `0.80`, `0.85`, `1.00`).
2. **Duración / Evolución (`duracion`)**: extensión o ventana temporal del tramo
   evaluado (por ejemplo `1.0`, `1.50`, `2.0`, `2.50`).
3. **Disipación / Pérdida (`disipacion`)**: factor de amortiguamiento o pérdida
   asociada al proceso (por ejemplo `0.00`, `0.10`, `0.20`, `0.40`).
4. **Energía / Cota y Umbral (`E_cin`, `Aporte`, `E_tot`, `Margen` frente a `delta = 0.25`)**:
   energía de cada muestra activa y comparación frente al umbral de referencia
   (`0.25`).

*(Nota: en la teoría cuántica de campos, el espaciotiempo tiene 4 dimensiones y
el Hamiltoniano es un operador cuántico; aquí los 4 ejes ordenan la lectura del
experimento y sus variables).*

---

## 2. Expresiones de energía / "hamiltonianos" de trabajo

En las series numéricas del puente (`ym_experimentos.txt`, `ym_barrido.txt` y
`ym_compensacion.txt`), la energía total de cada muestra activa se expresa como:

$$E_{\text{tot}} = E_{\text{cin}} + \text{Aporte}$$

$$\text{Margen} = E_{\text{tot}} - \delta, \quad \text{con } \delta = 0.25$$

Las expresiones o funciones que combinan `forma`, `duracion`, `disipacion` y
`E_cin` son **modelos heurísticos de trabajo** para estudiar sensibilidad
paramétrica; en Lean 4, las plantillas actuales (`yang_mills.lean`,
`yang_mills_puente.lean`, `yang_mills_puente_enlace.lean`) verifican
desigualdades sobre `ℝ` y modelos espectrales simplificados `H_op : ℝ → ℝ`,
mientras que `rigorous_yang_mills.lean` mantiene la conjetura universal como
`axiom` explícito.

---

## 3. Flujo de trabajo en Termux

1. Documentar o ajustar la serie / expresión de trabajo en estas notas.
2. Evaluar la serie con `scripts/correr_serie_ym.py`.
3. Registrar el estado con `scripts/registrar_estado_ym.py` en
   `docs/historial_ym.jsonl` y `docs/HISTORIAL_YM.md` antes de `commit` y
   `push`.
