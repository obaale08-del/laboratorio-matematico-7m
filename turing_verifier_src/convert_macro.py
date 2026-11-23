import json
import sys

def convert_to_macro(input_path, output_path, block_size=1000, scale=0.000001):
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

    base_t = float(intervals[0].get('t_lower', 0.0))
    for item in intervals:
        t_l = float(item.get('t_lower', 0.0))
        if t_l < base_t:
            base_t = t_l

    macro_blocks = []
    for block_idx, i in enumerate(range(0, len(intervals), block_size), start=1):
        chunk = intervals[i:i + block_size]
        subintervals = []
        
        min_d = float('inf')
        float_min = float('-inf')
        max_d = float('-inf')
        
        for idx, item in enumerate(chunk, start=i+1):
            t_l = float(item.get('t_lower', 0.0))
            t_u = float(item.get('t_upper', 0.0))
            z_l = float(item.get('z_lower', 0.0))
            z_u = float(item.get('z_upper', 0.0))
            
            delta_lower = round((t_l - base_t) / scale)
            delta_upper = round((t_u - base_t) / scale)
            
            if delta_lower < min_d: min_d = delta_lower
            if delta_upper > max_d: max_d = delta_upper
            
            subintervals.append({
                "index": idx,
                "delta_lower": delta_lower,
                "delta_upper": delta_upper,
                "z_lower": z_l,
                "z_upper": z_u
            })
            
        macro_blocks.append({
            "block_index": block_idx,
            "min_delta": int(min_d),
            "max_delta": int(max_d),
            "subintervals": subintervals
        })
        
    certificate = {
        "theorem_name": "RiemannMacroVerificationFull",
        "base_t": base_t,
        "scale": scale,
        "macro_blocks": macro_blocks
    }
    
    with open(output_path, 'w') as f:
        json.dump(certificate, f)
        
    print(f"¡Conversión jerárquica completada! Archivo generado: {output_path}")
    print(f"Total de macro-bloques creados: {len(macro_blocks)}")
    print(f"Parámetros globales -> base_t: {base_t} | scale: {scale}")

if __name__ == '__main__':
    input_file = sys.argv[1] if len(sys.argv) > 1 else 'turing_certificate_detailed.json'
    output_file = sys.argv[2] if len(sys.argv) > 2 else 'certificate_macro.json'
    convert_to_macro(input_file, output_file)
