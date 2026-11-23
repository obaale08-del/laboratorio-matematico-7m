import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -13,
    lower_den := 24,
    upper_num := 11,
    upper_den := 24,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  },
  {
    lower_num := -15,
    lower_den := 32,
    upper_num := 13,
    upper_den := 32,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Núcleo Cerrado 12x-4..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 12x-4 - Intervalo {index}] ¡Bucle cerrado y verificado!"
    else
      IO.println s!"[Canal 12x-4 - Intervalo {index}] Rotura de simetría."
    index := index + 1
  IO.println "Núcleo Cerrado 12x-4 finalizado."
