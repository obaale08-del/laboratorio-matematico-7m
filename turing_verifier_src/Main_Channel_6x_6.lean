import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := -21,
    lower_den := 56,
    upper_num := 25,
    upper_den := 56,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  },
  {
    lower_num := -23,
    lower_den := 64,
    upper_num := 29,
    upper_den := 64,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Canal Multiplicativo 6..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 6x-6 - Intervalo {index}] ¡Verificado rigurosamente!"
    else
      IO.println s!"[Canal 6x-6 - Intervalo {index}] Fallo de certificación."
    index := index + 1
  IO.println "Canal Multiplicativo 6 finalizado."
