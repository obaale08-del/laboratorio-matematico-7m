import json

def generate_lean_main(intervals_data):
    lean_entries = []
    for item in intervals_data:
        entry = f"""  {{
    lower_num := {item['l_num']},
    lower_den := {item['l_den']},
    upper_num := {item['u_num']},
    upper_den := {item['u_den']},
    h_pos_den_l := by norm_num,
    h_pos_den_u := by norm_num,
    h_ordered := by norm_num
  }}"""
        lean_entries.append(entry)
    
    entries_str = ",\n".join(lean_entries)
    
    lean_code = f"""import TuringVerifier.IntervalArithmetic

def intervalsToVerify : List ExactInterval := [
{entries_str}
]

def main : IO Unit := do
  IO.println "Iniciando procesamiento automatizado de intervalos exactos..."
  let mut index := 1
  for interval in intervalsToVerify do
    if interval.verify then
      IO.println s!"[Intervalo {{index}}] ¡Verificado rigurosamente por IVT!"
    else
      IO.println s!"[Intervalo {{index}}] El intervalo no contiene un cambio de signo certificado."
    index := index + 1
  IO.println "Procesamiento automatizado finalizado."
"""
    return lean_code

dataset = [
    {"l_num": -1, "l_den": 2, "u_num": 1, "u_den": 2},
    {"l_num": -5, "l_den": 8, "u_num": 3, "u_den": 8},
    {"l_num": -3, "l_den": 4, "u_num": 1, "u_den": 4}
]

with open("Main.lean", "w") as f:
    f.write(generate_lean_main(dataset))

print("Script de Python ejecutado: Main.lean generado automáticamente con el dataset.")
