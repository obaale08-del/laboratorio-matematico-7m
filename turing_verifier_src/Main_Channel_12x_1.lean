import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -1,
    lower_den := 2,
    upper_num := 1,
    upper_den := 2,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  },
  {
    lower_num := -3,
    lower_den := 5,
    upper_num := 2,
    upper_den := 5,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Núcleo Cerrado 12x-1..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 12x-1 - Intervalo {index}] ¡Bucle cerrado y verificado!"
    else
      IO.println s!"[Canal 12x-1 - Intervalo {index}] Rotura de simetría."
    index := index + 1
  IO.println "Núcleo Cerrado 12x-1 finalizado."
