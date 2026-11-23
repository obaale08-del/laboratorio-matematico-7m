import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -27,
    lower_den := 80,
    upper_num := 37,
    upper_den := 80,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Conjunción Analítica 9x-8..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 9x-8 - Intervalo {index}] ¡Verificado y sintetizado!"
    else
      IO.println s!"[Canal 9x-8 - Intervalo {index}] Fallo de síntesis."
    index := index + 1
  IO.println "Conjunción Analítica 9x-8 finalizada."
