import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -9,
    lower_den := 16,
    upper_num := 5,
    upper_den := 16,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  },
  {
    lower_num := -11,
    lower_den := 20,
    upper_num := 7,
    upper_den := 20,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Conjunción Analítica 9x-3..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 9x-3 - Intervalo {index}] ¡Verificado y sintetizado!"
    else
      IO.println s!"[Canal 9x-3 - Intervalo {index}] Fallo de síntesis."
    index := index + 1
  IO.println "Conjunción Analítica 9x-3 finalizada."
