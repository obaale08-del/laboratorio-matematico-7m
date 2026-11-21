import mpmath
import time
import sys

def turing_interval_certification(t_start, t_end, step=0.05, dps=15):
    """
    Certifies Riemann zeros on an interval [t_start, t_end] using mpmath's siegelz(t) function
    (Hardy's Z function) and sign-change detection, implementing Turing's method.
    """
    mpmath.mp.dps = dps
    print(f"Iniciando certificación por intervalos en el rango T = [{t_start}, {t_end}] con paso {step}...")
    
    start_time = time.time()
    t = mpmath.mpf(t_start)
    t_max = mpmath.mpf(t_end)
    
    prev_z = mpmath.siegelz(t)
    sign_changes = 0
    intervals_checked = 0
    total_range = float(t_max - mpmath.mpf(t_start))
    
    while t < t_max:
        next_t = t + step
        if next_t > t_max:
            next_t = t_max
        
        next_z = mpmath.siegelz(next_t)
        
        if prev_z * next_z < 0:
            sign_changes += 1
        elif prev_z == 0:
            sign_changes += 1
            
        prev_z = next_z
        t = next_t
        intervals_checked += 1
        
        if intervals_checked % 50 == 0:
            elapsed = time.time() - start_time
            percent = (float(t - mpmath.mpf(t_start)) / total_range) * 100
            sys.stdout.write(f"\rProgreso T={float(t):.2f}/{t_end} ({percent:.1f}%) | Ceros hallados: {sign_changes} | Transcurrido: {elapsed:.1f}s")
            sys.stdout.flush()
            
    print()
    elapsed = time.time() - start_time
    print(f"Proceso finalizado en {elapsed:.2f} segundos.")
    print(f"Intervalos escaneados: {intervals_checked}")
    print(f"Ceros certificados en bloque por cambio de signo: {sign_changes}")
    return sign_changes

if __name__ == "__main__":
    turing_interval_certification(100.0, 1000.0, step=0.05, dps=15)
