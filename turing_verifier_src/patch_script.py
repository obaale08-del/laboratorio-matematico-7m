import os

script_path = "generate_analytic_lab.py"
if os.path.exists(script_path):
    with open(script_path, "r", encoding="utf-8") as f:
        code = f.read()
    
    # Reemplazar la cota incorrecta por la cota inferior que espera Lean
    new_code = code.replace("Real.cos_le_one", "Real.neg_one_le_cos")
    
    with open(script_path, "w", encoding="utf-8") as f:
        f.write(new_code)
    print("[+] ¡generate_analytic_lab.py parcheado correctamente!")
else:
    print("[-] No se encontró generate_analytic_lab.py en la ruta actual.")
