import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -3,
    lower_den := 4,
    upper_num := 1,
    upper_den := 4,
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
  IO.println "Iniciando Canal Multiplicativo 2..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 6x-2 - Intervalo {index}] ¡Verificado rigurosamente!"
    else
      IO.println s!"[Canal 6x-2 - Intervalo {index}] Fallo de certificación."
    index := index + 1
  IO.println "Canal Multiplicativo 2 finalizado."
