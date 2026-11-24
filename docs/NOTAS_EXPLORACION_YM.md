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

## Deslinde metodológico: exploración, Lean 4 y 4D

> **Punto de partida:** Sin estructura, deslinde explícito y trazabilidad es imposible distinguir qué nace de una hipótesis de trabajo, qué es resultado de un barrido paramétrico y qué está formalmente demostrado. Este bloque fija el andamiaje de trabajo: ordena la exploración y separa con claridad el modelo reducido, las plantillas formales en Lean 4 y los requisitos del problema abierto de Yang-Mills en 4D.

- **Modelo heurístico (`correr_serie_ym.py`, `E_tot`, `Margen`, $\delta = 0.25$):** sirve para estudiar sensibilidad paramétrica, aislar variables y dejar registro reproducible en `docs/historial_ym.jsonl` y `docs/HISTORIAL_YM.md`. No construye una teoría cuántica de campos ni equivale a demostrar una brecha espectral.
- **Formalización en Lean 4:** certifica la validez lógica de definiciones, lemas o modelos formalizados dentro del sistema, pero un lema sobre un modelo reducido o una declaración como `axiom` no constituye por sí sola la resolución del problema abierto.
- **Problema de Yang-Mills y brecha de masa en 4D:** exige construir rigurosamente la teoría cuántica de campos no abeliana en $\mathbb{R}^4$ para un grupo de gauge compacto simple $G$ (controlando límite continuo y renormalización) y demostrar una brecha de masa estrictamente positiva ($\Delta > 0$) sobre el vacío.

## Tabla de trazabilidad: modelo heurístico y 4D

| Faceta / Elemento | En el modelo heurístico actual | Función como base de trabajo | Requisito del problema en 4D |
| :--- | :--- | :--- | :--- |
| **Configuración / Perfil (`forma`)** | Parámetro escalar de perfil en series (`0.55` a `1.00`) y barridos registrados. | Permite aislar sensibilidad ante cambios de forma sin mezclar otras variables. | Campo de conexión/gauge no abeliano en $\mathbb{R}^4$ cocientado por simetría gauge física. |
| **Evolución / Escala (`duracion`)** | Parámetro de duración/sostenimiento (`1.0` a `2.5`) en barridos paramétricos. | Ayuda a observar cómo se comporta el sistema al sostener el régimen en el tiempo. | Dinámica cuántica en espaciotiempo de 4 dimensiones y control del límite continuo. |
| **Amortiguamiento (`disipacion`)** | Parámetro de disipación (`0.00` a `0.40`) evaluado en series y tandas. | Permite probar cuándo la pérdida compensa o no un umbral dado en el modelo. | Renormalización rigurosa (UV e IR) sin cortes artificiales no controlados. |
| **Energía y umbral (`E_tot`, `Margen`, $\delta = 0.25$)** | Expresión de trabajo ($E_{\text{tot}} = E_{\text{cin}} + \text{Aporte}$) comparada con `0.25`. | Define un criterio de prueba claro y repetible para comparar corridas. | Existencia del operador hamiltoniano cuántico y brecha espectral estrictamente positiva ($\Delta > 0$) sobre el vacío. |
| **Trazabilidad y verificación (`correr_serie_ym.py`, `registrar_estado_ym.py`, Lean 4)** | JSONL, Markdown, commits en `main` y plantillas/lemas formales en Lean 4. | Garantiza reproducibilidad, auditoría de cambios y separación entre conjetura, prueba y cálculo. | Demostración matemática completa de existencia de la teoría y brecha de masa para un grupo compacto simple $G$. |
| **Módulos Lean 4 YM (`yang_mills*.lean`, `rigorous_yang_mills.lean`)** | Lemas/puentes (`*_puente*`, `*_positivity*`) y conjetura como `axiom` (`rigorous_yang_mills.lean`). | Verifica consistencia lógica de piezas formales sin confundir `axiom` o modelo con prueba completa. | Demostración formal cerrada (sin `axiom` abiertos) para Yang-Mills en $\mathbb{R}^4$ con $\Delta > 0$. |

### Módulos Lean 4 enlazados a Yang-Mills
- **Exploración / puentes / positividad (`lean_templates/yang_mills.lean`, `yang_mills_mass_gap.lean`, `yang_mills_mass_gap_positivity.lean`, `yang_mills_puente.lean`, `yang_mills_puente_enlace.lean`):** estructuras y lemas de soporte o modelos/puentes formalizados en Lean 4; validan la lógica interna de sus definiciones, sin equivaler por sí solos a la teoría cuántica completa en 4D.
- **Postulado / conjetura formalizada (`lean_templates/rigorous_yang_mills.lean`):** contiene la conjetura general como `axiom` explícito, sirviendo como anclaje formal del enunciado y no como demostración resuelta.
