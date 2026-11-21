import Mathlib.Data.Nat.Basic

/-!
# Acotamientos Elementales de Polinomios

Este módulo formaliza propiedades básicas y acotamientos constructivos 
para polinomios evaluados en puntos enteros pequeños, totalmente compatibles con Mathlib4.
-/

namespace Complexity.Polynomials

/-- Define un polinomio simple de grado dos para pruebas de acotamiento. -/
def samplePoly (x : ℕ) : ℕ := x ^ 2 + 2 * x + 1

/-- Demuestra un acotamiento estricto para el polinomio evaluado en un punto fijo 
    utilizando automatización de tácticas directas. -/
theorem sample_poly_bound : samplePoly 4 ≤ 30 := by
  unfold samplePoly
  norm_num

end Complexity.Polynomials
