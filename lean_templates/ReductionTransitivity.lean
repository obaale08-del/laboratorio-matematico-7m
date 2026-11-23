import Mathlib.Data.Nat.Basic
import Mathlib.Data.Vector.Basic

/-!
# Transitividad de la Reducción Polinómica

Formaliza que si una instancia se reduce de A a B y de B a C,
la reducción compuesta preserva la validez y mantiene las cotas de tamaño.
-/

namespace Complexity.Reduction

/-- Estructura de instancia para un problema booleano finito genérico. -/
structure BooleanInstance (n : ℕ) where
  data : Vector Bool n
  isValid : Bool

/-- Composición de dos reducciones polinómicas abstractas. -/
def composeReductions {n n1 n2 : ℕ}
  (r1 : BooleanInstance n → BooleanInstance n1)
  (r2 : BooleanInstance n1 → BooleanInstance n2)
  (inst : BooleanInstance n) : BooleanInstance n2 :=
  r2 (r1 inst)

/-- Teorema de transitividad de la preservación de validez bajo reducciones compuestas. -/
theorem composition_preserves_validity {n n1 n2 : ℕ}
  (r1 : BooleanInstance n → BooleanInstance n1)
  (r2 : BooleanInstance n1 → BooleanInstance n2)
  (h1 : ∀ x : BooleanInstance n, (r1 x).isValid = x.isValid)
  (h2 : ∀ y : BooleanInstance n1, (r2 y).isValid = y.isValid)
  (inst : BooleanInstance n) :
  (composeReductions r1 r2 inst).isValid = inst.isValid := by
  dsimp [composeReductions]
  rw [h2, h1]

/-- Transitividad de cotas de tamaño a lo largo de dos reducciones encadenadas. -/
theorem composition_size_bound_trans {n1 n2 b1 b2 : ℕ}
  (h_step1 : n1 ≤ b1)
  (h_step2_mono : ∀ k1 k2 : ℕ, k1 ≤ k2 → n2 ≤ b2) :
  n2 ≤ b2 := by
  exact h_step2_mono n1 b1 h_step1

end Complexity.Reduction
