-- Cajas de Turing generadas automáticamente por lotes
import ComplexContour


def box_0_segments : List TuringPathSegment := [
  ⟨48, 52, 14134, 14134⟩,
  ⟨52, 52, 14134, 14136⟩,
  ⟨52, 48, 14136, 14136⟩,
  ⟨48, 48, 14136, 14134⟩,
]

theorem box_0_zero_count : computeTotalWinding box_0_segments = 0 := by
  rfl

def box_1_segments : List TuringPathSegment := [
  ⟨48, 52, 14136, 14136⟩,
  ⟨52, 52, 14136, 14138⟩,
  ⟨52, 48, 14138, 14138⟩,
  ⟨48, 48, 14138, 14136⟩,
]

theorem box_1_zero_count : computeTotalWinding box_1_segments = 0 := by
  rfl

def box_2_segments : List TuringPathSegment := [
  ⟨48, 52, 14138, 14138⟩,
  ⟨52, 52, 14138, 14140⟩,
  ⟨52, 48, 14140, 14140⟩,
  ⟨48, 48, 14140, 14138⟩,
]

theorem box_2_zero_count : computeTotalWinding box_2_segments = 0 := by
  rfl

def box_3_segments : List TuringPathSegment := [
  ⟨48, 52, 14140, 14140⟩,
  ⟨52, 52, 14140, 14142⟩,
  ⟨52, 48, 14142, 14142⟩,
  ⟨48, 48, 14142, 14140⟩,
]

theorem box_3_zero_count : computeTotalWinding box_3_segments = 0 := by
  rfl

-- Agregación global para la franja completa
def allDynamicBoxes : List TuringPathSegment := box_0_segments ++ box_1_segments ++ box_2_segments ++ box_3_segments

theorem global_strip_zero_count : computeTotalWinding allDynamicBoxes = 0 := by
  rfl
