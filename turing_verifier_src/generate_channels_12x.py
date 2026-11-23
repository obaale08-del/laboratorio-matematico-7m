import json

def partition_dataset(dataset, parts=12):
    k, m = divmod(len(dataset), parts)
    return [dataset[i * k + min(i, m):(i + 1) * k + min(i + 1, m)] for i in range(parts)]

raw_dataset = [
    {"l_num": -1, "l_den": 2, "u_num": 1, "u_den": 2},
    {"l_num": -3, "l_den": 5, "u_num": 2, "u_den": 5},
    {"l_num": -5, "l_den": 8, "u_num": 3, "u_den": 8},
    {"l_num": -7, "l_den": 10, "u_num": 3, "u_den": 10},
    {"l_num": -9, "l_den": 16, "u_num": 5, "u_den": 16},
    {"l_num": -11, "l_den": 20, "u_num": 7, "u_den": 20},
    {"l_num": -13, "l_den": 24, "u_num": 11, "u_den": 24},
    {"l_num": -15, "l_den": 32, "u_num": 13, "u_den": 32},
    {"l_num": -17, "l_den": 40, "u_num": 19, "u_den": 40},
    {"l_num": -19, "l_den": 48, "u_num": 23, "u_den": 48},
    {"l_num": -21, "l_den": 56, "u_num": 25, "u_den": 56},
    {"l_num": -23, "l_den": 64, "u_num": 29, "u_den": 64},
    {"l_num": -25, "l_den": 72, "u_num": 31, "u_den": 72},
    {"l_num": -27, "l_den": 80, "u_num": 37, "u_den": 80},
    {"l_num": -29, "l_den": 96, "u_num": 41, "u_den": 96},
    {"l_num": -31, "l_den": 104, "u_num": 43, "u_den": 104}
]

channels = partition_dataset(raw_dataset, 12)

for idx, channel_data in enumerate(channels, start=1):
    lean_entries = [
        f"  {{\n    lower_num := {item['l_num']},\n    lower_den := {item['l_den']},\n    upper_num := {item['u_num']},\n    upper_den := {item['u_den']},\n    h_pos_den_l := by norm_num,\n    h_pos_den_u := by norm_num,\n    h_ordered := by norm_num\n  }}"
        for item in channel_data
    ]
    
    lean_code = f"""import TuringVerifier.IntervalArithmetic

def channelIntervals : List ExactInterval := [
{",\n".join(lean_entries)}
]

def main : IO Unit := do
  IO.println "Iniciando Núcleo Cerrado 12x-{idx}..."
  let mut index := 1
  for interval in channelIntervals do
    if interval.verify then
      IO.println s!"[Canal 12x-{idx} - Intervalo {{index}}] ¡Bucle cerrado y verificado!"
    else
      IO.println s!"[Canal 12x-{idx} - Intervalo {{index}}] Rotura de simetría."
    index := index + 1
  IO.println "Núcleo Cerrado 12x-{idx} finalizado."
"""
    with open(f"Main_Channel_12x_{idx}.lean", "w") as f:
        f.write(lean_code)

print("Estructura de 12 canales (núcleo cerrado) generada con éxito.")
