import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -25,
    lower_den := 72,
    upper_num := 31,
    upper_den := 72,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Conjunción Analítica 9x-7..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 9x-7 - Intervalo {index}] ¡Verificado y sintetizado!"
    else
      IO.println s!"[Canal 9x-7 - Intervalo {index}] Fallo de síntesis."
    index := index + 1
  IO.println "Conjunción Analítica 9x-7 finalizada."
