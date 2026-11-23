import json

def generate_massive_macro(output_path='certificate_massive.json', total_zeros=100000, block_size=1000):
    base_t = 10.0
    scale = 0.000001
    macro_blocks = []
    
    current_index = 1
    for block_idx in range(1, (total_zeros // block_size) + 1):
        subintervals = []
        min_d = float('inf')
        max_d = float('-inf')
        
        for _ in range(block_size):
            # Simulación realista de deltas espaciados
            delta_lower = (current_index - 1) * 5000
            delta_upper = current_index * 5000
            
            if delta_lower < min_d: min_d = delta_lower
            if delta_upper > max_d: max_d = delta_upper
            
            subintervals.append({
                "index": current_index,
                "delta_lower": delta_lower,
                "delta_upper": delta_upper,
                "z_lower": -0.5 + (current_index % 10) * 0.05,
                "z_upper": 0.5 - (current_index % 10) * 0.05
            })
            current_index += 1
            
        macro_blocks.append({
            "block_index": block_idx,
            "min_delta": int(min_d),
            "max_delta": int(max_d),
            "subintervals": subintervals
        })
        
    certificate = {
        "theorem_name": "RiemannMacroStressTest",
        "base_t": base_t,
        "scale": scale,
        "macro_blocks": macro_blocks
    }
    
    with open(output_path, 'w') as f:
        json.dump(certificate, f)
        
    print(f"¡Dataset masivo generado: {output_path} ({total_zeros} registros en {len(macro_blocks)} bloques)!")

if __name__ == '__main__':
    generate_massive_macro()
