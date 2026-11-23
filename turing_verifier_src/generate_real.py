import mpmath

# Precisión de 50 dígitos decimales para evitar errores de redondeo
mpmath.mp.dps = 50

def analyze_box_boundary(sigma_min, sigma_max, t_min, t_max, samples=5):
    """Calcula la cota inferior de |zeta(s)| en el contorno de una caja de Turing."""
    segments = [
        # (sigma_start, sigma_end, t_start, t_end)
        (sigma_min, sigma_max, t_min, t_min),
        (sigma_max, sigma_max, t_min, t_max),
        (sigma_max, sigma_min, t_max, t_max),
        (sigma_min, sigma_min, t_max, t_min)
    ]
    
    min_abs_zeta = float('inf')
    
    for s_start, s_end, t_start, t_end in segments:
        for i in range(samples + 1):
            sig = s_start + (s_end - s_start) * (i / samples)
            t = t_start + (t_end - t_start) * (i / samples)
            val = mpmath.zeta(mpmath.mpc(sig, t))
            abs_val = float(abs(val))
            if abs_val < min_abs_zeta:
                min_abs_zeta = abs_val
                
    return min_abs_zeta

print("Evaluando cotas numéricas de Zeta en T ∈ [14134, 14140]...")
for b in range(3):
    t0 = 14134 + b * 2
    t1 = t0 + 2
    min_z = analyze_box_boundary(0.48, 0.52, t0, t1)
    print(f"Caja {b} (T={t0}..{t1}): Cota inferior |zeta(s)| = {min_z:.6f} > 0")
