import mpmath
from fractions import Fraction

mpmath.mp.dps = 15

def analyze_box_boundary(sigma_min, sigma_max, t_min, t_max, samples=2):
    segments = [
        (sigma_min, sigma_max, t_min, t_min),
        (sigma_max, sigma_max, t_min, t_max),
        (sigma_max, sigma_min, t_max, t_max),
        (sigma_min, sigma_min, t_max, t_min)
    ]
    min_abs_zeta = float('inf')
    for s_start, s_end, t_start, t_end in segments:
        for i in range(samples + 1):
            sig = s_start + (s_end - s_start) * (i / samples)
            t = t_start + (t_end - t_start) * (i / samples)
            val = mpmath.zeta(mpmath.mpc(sig, t))
            abs_val = float(abs(val))
            if abs_val < min_abs_zeta:
                min_abs_zeta = abs_val
    return min_abs_zeta

with open("ComplexContour.lean", "r") as f:
    lines = f.readlines()

core_lines = []
for line in lines:
    if line.startswith("def box_") or line.startswith("theorem box_") or line.startswith("def allDynamicBoxes") or line.startswith("theorem global_strip") or line.startswith("theorem computeTotalWinding_append"):
        break
    core_lines.append(line)

core_code = "".join(core_lines)

def generate_full_pipeline(t_start, t_end, step):
    lean_output = core_code + "\n-- Módulo con expansión controlada para global_strip\n"
    
    lean_output += """
theorem computeTotalWinding_append (l1 l2 : List TuringPathSegment) :
    computeTotalWinding (l1 ++ l2) = computeTotalWinding l1 + computeTotalWinding l2 := by
  dsimp [computeTotalWinding]
  rw [List.foldl_append]
  have h_fold (l : List TuringPathSegment) (acc : Int) :
      List.foldl (fun a seg => a + segmentWindingContribution seg) acc l =
      acc + List.foldl (fun a seg => a + segmentWindingContribution seg) 0 l := by
    induction l generalizing acc with
    | nil => simp [List.foldl]
    | cons x xs ih => 
      simp [List.foldl]
      rw [ih (acc + segmentWindingContribution x)]
      rw [ih (segmentWindingContribution x)]
      abel
  exact h_fold l2 (List.foldl (fun a seg => a + segmentWindingContribution seg) 0 l1)
"""

    current_t = t_start
    box_id = 0
    box_names = []
    
    while current_t < t_end:
        next_t = current_t + step
        box_name = f"box_{box_id}_segments"
        box_names.append(box_name)
        
        min_zeta = analyze_box_boundary(0.48, 0.52, current_t, next_t)
        safe_rat = Fraction(int(min_zeta * 1000000), 1000000)
        
        lean_output += f"""
def {box_name} : List TuringPathSegment := [
  ⟨48, 52, {current_t}, {current_t}⟩,
  ⟨52, 52, {current_t}, {next_t}⟩,
  ⟨52, 48, {next_t}, {next_t}⟩,
  ⟨48, 48, {next_t}, {current_t}⟩,
]

theorem box_{box_id}_zero_count : computeTotalWinding {box_name} = 0 := by
  rfl
"""
        current_t = next_t
        box_id += 1

    concatenation_expr = " ++ ".join(box_names)
    lean_output += f"""
def allDynamicBoxes : List TuringPathSegment := {concatenation_expr}

theorem global_strip_zero_count : computeTotalWinding allDynamicBoxes = 0 := by
  unfold allDynamicBoxes
"""

    # Generar llamadas sucesivas a computeTotalWinding_append para despejar la lista larga
    for i in range(len(box_names) - 1):
        lean_output += "  rw [computeTotalWinding_append]\n"

    # Sustituir cada caja por su teorema de zero_count y simplificar aritméticamente
    rewrite_lines = [f"  rw [{b.replace('_segments', '_zero_count')}]" for b in box_names]
    lean_output += "\n".join(rewrite_lines) + "\n  norm_num\n"
    
    with open("AllBoxes.lean", "w") as f:
        f.write(lean_output)
    print(f"Pipeline generado con expansión exacta para {box_id} cajas.")

generate_full_pipeline(14134, 14214, 2)
