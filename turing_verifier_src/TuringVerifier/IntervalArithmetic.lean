import Mathlib

structure ExactInterval where
  lower_num : Int
  lower_den : Nat
  upper_num : Int
  upper_den : Nat
  h_pos_den_l : 0 < lower_den
  h_pos_den_u : 0 < upper_den
  h_ordered : (lower_num : ℚ) / lower_den ≤ (upper_num : ℚ) / upper_den

def ExactInterval.containsZero (i : ExactInterval) : Prop :=
  ((i.lower_num : ℚ) / i.lower_den) * ((i.upper_num : ℚ) / i.upper_den) < 0

def ExactInterval.verify (i : ExactInterval) : Bool :=
  decide (((i.lower_num : ℚ) / i.lower_den) * ((i.upper_num : ℚ) / i.upper_den) < 0)
