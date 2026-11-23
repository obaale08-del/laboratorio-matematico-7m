with open("Main.lean", "r") as f:
    content = f.read()

# Prepend interval arithmetic import and helper
new_content = """import TuringVerifier.IntervalArithmetic

def verify_subinterval_exact (lower_num lower_den upper_num upper_den : Int) 
    (h_l : (0 : Nat) < lower_den.toNat) (h_u : (0 : Nat) < upper_den.toNat) 
    (h_ord : ((lower_num : ℚ) / lower_den.toNat) ≤ ((upper_num : ℚ) / upper_den.toNat)) : Bool :=
  let interval : ExactInterval := {
    lower_num := lower_num,
    lower_den := lower_den.toNat,
    upper_num := upper_num,
    upper_den := upper_den.toNat,
    h_pos_den_l := h_l,
    h_pos_den_u := h_u,
    h_ordered := h_ord
  }
  interval.verify
""" + content

with open("Main.lean", "w") as f:
    f.write(new_content)

print("Main.lean actualizado correctamente.")
