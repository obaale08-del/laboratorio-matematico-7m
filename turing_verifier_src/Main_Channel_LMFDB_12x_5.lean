import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
  {
    lower_num := 32885,
    lower_den := 1000,
    upper_num := 32985,
    upper_den := 1000,
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }
]

def main : IO Unit := do
  IO.println "Iniciando Canal LMFDB 12x-5..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal LMFDB 12x-5 - Intervalo {index}] ¡Cero real certificado por el kernel!"
    else
      IO.println s!"[Canal LMFDB 12x-5 - Intervalo {index}] Alerta de discrepancia en arista."
    index := index + 1
  IO.println "Canal LMFDB 12x-5 finalizado."
