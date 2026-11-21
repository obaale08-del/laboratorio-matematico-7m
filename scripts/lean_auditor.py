import os
import re

def audit_lean_files():
    export_dir = "lean_exports"
    if not os.path.exists(export_dir):
        print("-> Error: El directorio de exportación no existe.")
        return

    lean_files = [f for f in os.listdir(export_dir) if f.endswith(".lean")]
    audit_results = {}
    
    total_sorries = 0
    total_axioms = 0

    for file in lean_files:
        path = os.path.join(export_dir, file)
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
            
        sorries = len(re.findall(r'\bsorry\b', content))
        admits = len(re.findall(r'\badmit\b', content))
        axioms = len(re.findall(r'\baxiom\b', content))
        
        total_sorries += (sorries + admits)
        total_axioms += axioms
        
        audit_results[file] = {
            "sorries_and_admits": sorries + admits,
            "axioms": axioms,
            "clean_status": (sorries + admits == 0)
        }

    log_path = os.path.join(export_dir, "tactic_audit.log")
    with open(log_path, "w", encoding="utf-8") as log:
        log.write("=== PETRUSKA FENIX: AUDITORÍA DE RIGOR FORMAL ===\n")
        log.write(f"Archivos analizados: {len(lean_files)}\n")
        log.write(f"Total de 'sorry/admit' encontrados: {total_sorries}\n")
        log.write(f"Total de axiomas declarados: {total_axioms}\n\n")
        
        for file, data in audit_results.items():
            status = "LIBRE DE SORRIES (RIGOR MÁXIMO)" if data["clean_status"] else "CONTIENE BRECHAS PENDIENTES"
            log.write(f"- Archivo: {file}\n")
            log.write(f"  Estado: {status}\n")
            log.write(f"  Sorries/Admits: {data['sorries_and_admits']}\n")
            log.write(f"  Axioms: {data['axioms']}\n\n")

    print(f"-> Auditoría completada. Reporte generado en {log_path}")
    print(f"-> Estado global: {total_sorries} brechas encontradas en {len(lean_files)} módulos.")

if __name__ == "__main__":
    audit_lean_files()
