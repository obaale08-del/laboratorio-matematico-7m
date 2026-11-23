import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -5,
    lower_den := 8,
    upper_num := 3,
    upper_den := 8,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  },
  {
    lower_num := -7,
    lower_den := 10,
    upper_num := 3,
    upper_den := 10,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Conjunción Analítica 9x-2..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 9x-2 - Intervalo {index}] ¡Verificado y sintetizado!"
    else
      IO.println s!"[Canal 9x-2 - Intervalo {index}] Fallo de síntesis."
    index := index + 1
  IO.println "Conjunción Analítica 9x-2 finalizada."
