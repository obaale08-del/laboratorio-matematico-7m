import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -19,
    lower_den := 48,
    upper_num := 23,
    upper_den := 48,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Núcleo Cerrado 12x-6..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 12x-6 - Intervalo {index}] ¡Bucle cerrado y verificado!"
    else
      IO.println s!"[Canal 12x-6 - Intervalo {index}] Rotura de simetría."
    index := index + 1
  IO.println "Núcleo Cerrado 12x-6 finalizado."
