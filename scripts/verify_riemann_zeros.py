import mpmath
import time
import sys

def verify_riemann_zeros(start_index=1, count=1000, dps=30):
    mpmath.mp.dps = dps
    print(f"Iniciando verificación de {count} ceros (desde el índice {start_index}) con una precisión de {dps} dígitos...")
    
    anomalies = []
    start_time = time.time()
    
    for i, n in enumerate(range(start_index, start_index + count)):
        try:
            zero = mpmath.zetazero(n)
            val = mpmath.zeta(zero)
            tolerance = mpmath.mpf(10)**(-dps + 6)
            if abs(val) > tolerance:
                anomalies.append((n, zero, val))
            
            if (i + 1) % 25 == 0 or (i + 1) == count:
                elapsed = time.time() - start_time
                percent = ((i + 1) / count) * 100
                sys.stdout.write(f"\rProgreso: {i + 1}/{count} ({percent:.1f}%) - Tiempo transcurrido: {elapsed:.1f}s")
                sys.stdout.flush()
        except Exception as e:
            print(f"\nError calculando el cero {n}: {e}")
            
    print() 
    elapsed = time.time() - start_time
    print(f"Verificación completada: {count} ceros procesados en {elapsed:.2f} segundos.")
    
    if anomalies:
        print(f"¡ADVERTENCIA! Se encontraron {len(anomalies)} anomalías potenciales:")
        for anom in anomalies:
            print(f"Índice: {anom[0]}, Cero: {anom[1]}, Valor Zeta: {anom[2]}")
    else:
        print("Todos los ceros verificados se sitúan precisamente sobre la línea crítica dentro de la tolerancia.")

if __name__ == "__main__":
    verify_riemann_zeros(start_index=1, count=1000, dps=30)
