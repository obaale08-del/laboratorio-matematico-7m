import json
import sys

def convert_to_delta(input_path, output_path, scale=0.000001):
    try:
        with open(input_path, 'r') as f:
            data = json.load(f)
    except Exception as e:
        print(f"Error al leer el archivo de entrada: {e}")
        return

    intervals = data if isinstance(data, list) else data.get('subintervals', data)
    
    if not intervals:
        print("Error: No se encontraron subintervalos en el archivo.")
        return

    # Encontrar el valor mínimo de t para establecerlo como base_t global
    base_t = float(intervals[0].get('t_lower', 0.0))
    for item in intervals:
        t_l = float(item.get('t_lower', 0.0))
        if t_l < base_t:
            base_t = t_l

    delta_subintervals = []
    for idx, item in enumerate(intervals, start=1):
        t_l = float(item.get('t_lower', 0.0))
        t_u = float(item.get('t_upper', 0.0))
        z_l = float(item.get('z_lower', 0.0))
        z_u = float(item.get('z_upper', 0.0))
        
        delta_lower = round((t_l - base_t) / scale)
        delta_upper = round((t_u - base_t) / scale)
        
        delta_subintervals.append({
            "index": idx,
            "delta_lower": delta_lower,
            "delta_upper": delta_upper,
            "z_lower": z_l,
            "z_upper": z_u
        })
        
    certificate = {
        "theorem_name": "RiemannDeltaVerificationFull",
        "base_t": base_t,
        "scale": scale,
        "subintervals": delta_subintervals
    }
    
    with open(output_path, 'w') as f:
        json.dump(certificate, f)
        
    print(f"¡Conversión completada! Archivo generado: {output_path}")
    print(f"Total de registros: {len(delta_subintervals)}")
    print(f"Parámetros globales -> base_t: {base_t} | scale: {scale}")

if __name__ == '__main__':
    input_file = sys.argv[1] if len(sys.argv) > 1 else 'certificate_flat.json'
    output_file = sys.argv[2] if len(sys.argv) > 2 else 'certificate_delta.json'
    convert_to_delta(input_file, output_file)
