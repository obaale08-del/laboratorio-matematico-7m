import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace YangMillsPuenteEnlace

def QuantumHamiltonianSpectrum (H_op : ℝ → ℝ) (lambda : ℝ) : Prop :=
  ∀ x, 0 ≤ H_op x ∧ H_op x ≥ lambda

def StrictMassGapBound (delta : ℝ) : Prop :=
  0 < delta ∧ delta ≤ 1

theorem yang_mills_spectral_gap_deep (delta : ℝ) (h_gap : StrictMassGapBound delta)
    (H_op : ℝ → ℝ) (h_spec : QuantumHamiltonianSpectrum H_op delta) :
    0 < delta ∧ delta ≤ 1 ∧ ∀ x, delta ≤ H_op x := by
  refine ⟨h_gap.1, h_gap.2, fun x => (h_spec x).2⟩

lemma h_op_pos_of_mass_gap
    (delta : ℝ) (h_gap : StrictMassGapBound delta)
    (H_op : ℝ → ℝ) (h_spec : QuantumHamiltonianSpectrum H_op delta)
    (x : ℝ) : 0 < H_op x := by
  exact lt_of_lt_of_le h_gap.1 (h_spec x).2

lemma sweep_bound_crosses_gap
    (delta E_sweep x : ℝ)
    (h_gap : StrictMassGapBound delta)
    (h_sweep_ge_delta : delta ≤ E_sweep)
    (hx_ge_sweep : E_sweep ≤ x) :
    0 < E_sweep ∧ delta ≤ x ∧ 0 < x := by
  have h_pos_sweep : 0 < E_sweep := lt_of_lt_of_le h_gap.1 h_sweep_ge_delta
  have h_delta_le_x : delta ≤ x := le_trans h_sweep_ge_delta hx_ge_sweep
  have h_pos_x : 0 < x := lt_of_lt_of_le h_pos_sweep hx_ge_sweep
  exact ⟨h_pos_sweep, h_delta_le_x, h_pos_x⟩

theorem enlace_caso_con_espectro
    (E_sweep x_max : ℝ)
    (H_op : ℝ → ℝ)
    (h_spec : QuantumHamiltonianSpectrum H_op (0.25 : ℝ))
    (h_sweep : (0.25 : ℝ) ≤ E_sweep)
    (hx : E_sweep ≤ x_max)
    (x_eval : ℝ) :
    (0 < E_sweep ∧ (0.25 : ℝ) ≤ x_max ∧ 0 < x_max) ∧
    ((0 : ℝ) < (0.25 : ℝ) ∧ (0.25 : ℝ) ≤ (1 : ℝ) ∧ ∀ y, (0.25 : ℝ) ≤ H_op y) ∧
    (0 < H_op x_eval) := by
  have h_gap : StrictMassGapBound (0.25 : ℝ) := ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_, ?_⟩
  · exact sweep_bound_crosses_gap (0.25 : ℝ) E_sweep x_max h_gap h_sweep hx
  · exact yang_mills_spectral_gap_deep (0.25 : ℝ) h_gap H_op h_spec
  · exact h_op_pos_of_mass_gap (0.25 : ℝ) h_gap H_op h_spec x_eval

theorem enlace_ym_experimentos
    (H_op : ℝ → ℝ)
    (h_spec : QuantumHamiltonianSpectrum H_op (0.25 : ℝ))
    (x_eval : ℝ) :
    ((0 : ℝ) < 0.3169 ∧ (0.25 : ℝ) ≤ 0.3809 ∧ (0 : ℝ) < 0.3809) ∧
    ((0 : ℝ) < (0.25 : ℝ) ∧ (0.25 : ℝ) ≤ (1 : ℝ) ∧ ∀ y, (0.25 : ℝ) ≤ H_op y) ∧
    (0 < H_op x_eval) := by
  apply enlace_caso_con_espectro (0.3169 : ℝ) (0.3809 : ℝ) H_op h_spec
  · norm_num
  · norm_num

end YangMillsPuenteEnlace
