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
    lower_num := -5,
    lower_den := 8,
    upper_num := 3,
    upper_den := 8,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Canal Multiplicativo 1..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 6x-1 - Intervalo {index}] ¡Verificado rigurosamente!"
    else
      IO.println s!"[Canal 6x-1 - Intervalo {index}] Fallo de certificación."
    index := index + 1
  IO.println "Canal Multiplicativo 1 finalizado."
