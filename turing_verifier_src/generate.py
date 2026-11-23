with open("ComplexContour.lean", "r") as f:
    lines = f.readlines()

core_lines = []
for line in lines:
    if line.startswith("def box_") or line.startswith("theorem box_") or line.startswith("def allDynamicBoxes") or line.startswith("theorem global_strip") or line.startswith("theorem computeTotalWinding_append"):
        break
    core_lines.append(line)

core_code = "".join(core_lines)

def generate_batch_boxes(t_start, t_end, step, sigma_min=48, sigma_max=52):
    lean_output = core_code + "\n-- Cajas de Turing con composición modular limpia\n"
    
    lean_output += """
theorem computeTotalWinding_append (l1 l2 : List TuringPathSegment) :
    computeTotalWinding (l1 ++ l2) = computeTotalWinding l1 + computeTotalWinding l2 := by
  dsimp [computeTotalWinding]
  rw [List.foldl_append]
  have h_fold (l : List TuringPathSegment) (acc : Int) :
      List.foldl (fun a seg => a + segmentWindingContribution seg) acc l =
      acc + List.foldl (fun a seg => a + segmentWindingContribution seg) 0 l := by
    induction l generalizing acc with
    | nil => 
      simp [List.foldl]
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
        lean_output += f"""
def {box_name} : List TuringPathSegment := [
  ⟨{sigma_min}, {sigma_max}, {current_t}, {current_t}⟩,
  ⟨{sigma_max}, {sigma_max}, {current_t}, {next_t}⟩,
  ⟨{sigma_max}, {sigma_min}, {next_t}, {next_t}⟩,
  ⟨{sigma_min}, {sigma_min}, {next_t}, {current_t}⟩,
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
  repeat rw [computeTotalWinding_append]
"""
    
    rewrite_lines = [f"  rw [{b.replace('_segments', '_zero_count')}]" for b in box_names]
    rewrites = "\n".join(rewrite_lines)
    lean_output += rewrites + "\n  simp\n"
    
    with open("AllBoxes.lean", "w") as f:
        f.write(lean_output)
    print(f"Se generó AllBoxes.lean con {box_id} cajas y cierre limpio con simp.")

generate_batch_boxes(0, 40, 2)
