-- Generado automáticamente desde ~/tmp/ym_puente_lean.json
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

namespace YangMillsPuente

def StrictMassGapBound (delta : ℝ) : Prop :=
  0 < delta ∧ delta ≤ 1

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

-- Bloque: ym_experimentos (archivo: ym_experimentos.txt)
theorem caso_1_ym_experimentos :
    (0 : ℝ) < 0.3169 ∧ (0.25 : ℝ) ≤ 0.3809 ∧ (0 : ℝ) < 0.3809 := by
  apply sweep_bound_crosses_gap (0.25 : ℝ) (0.3169 : ℝ) (0.3809 : ℝ)
  · exact ⟨by norm_num, by norm_num⟩
  · norm_num
  · norm_num

-- Bloque: 1:Variando FORMA (duracion=1.0, disipacion=0.4) (archivo: ym_barrido.txt)
theorem caso_2_b_1_variando_forma_duracion_1_0_disipacion_0_4 :
    (0 : ℝ) < 0.2594 ∧ (0.25 : ℝ) ≤ 0.2943 ∧ (0 : ℝ) < 0.2943 := by
  apply sweep_bound_crosses_gap (0.25 : ℝ) (0.2594 : ℝ) (0.2943 : ℝ)
  · exact ⟨by norm_num, by norm_num⟩
  · norm_num
  · norm_num

-- Bloque: 2:Variando DURACION (forma=0.80, disipacion=0.4) (archivo: ym_barrido.txt)
theorem caso_3_b_2_variando_duracion_forma_0_80_disipacion_0_4 :
    (0 : ℝ) < 0.276 ∧ (0.25 : ℝ) ≤ 0.2956 ∧ (0 : ℝ) < 0.2956 := by
  apply sweep_bound_crosses_gap (0.25 : ℝ) (0.276 : ℝ) (0.2956 : ℝ)
  · exact ⟨by norm_num, by norm_num⟩
  · norm_num
  · norm_num

-- Bloque: 3:Variando DISIPACION (forma=0.80, duracion=1.0) (archivo: ym_barrido.txt)
theorem caso_4_b_3_variando_disipacion_forma_0_80_duracion_1_0 :
    (0 : ℝ) < 0.2788 ∧ (0.25 : ℝ) ≤ 0.3223 ∧ (0 : ℝ) < 0.3223 := by
  apply sweep_bound_crosses_gap (0.25 : ℝ) (0.2788 : ℝ) (0.3223 : ℝ)
  · exact ⟨by norm_num, by norm_num⟩
  · norm_num
  · norm_num

-- Bloque: ym_compensacion (archivo: ym_compensacion.txt)
theorem caso_5_ym_compensacion :
    (0 : ℝ) < 0.2608 ∧ (0.25 : ℝ) ≤ 0.2608 ∧ (0 : ℝ) < 0.2608 := by
  apply sweep_bound_crosses_gap (0.25 : ℝ) (0.2608 : ℝ) (0.2608 : ℝ)
  · exact ⟨by norm_num, by norm_num⟩
  · norm_num
  · norm_num

end YangMillsPuente
