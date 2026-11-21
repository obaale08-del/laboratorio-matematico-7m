import mpmath
import time
from multiprocessing import Pool, cpu_count
import sys

def worker_check(args):
    n, dps = args
    mpmath.mp.dps = dps
    try:
        zero = mpmath.zetazero(n)
        val = mpmath.zeta(zero)
        tolerance = mpmath.mpf(10)**(-dps + 6)
        if abs(val) > tolerance:
            return (n, zero, val)
    except Exception as e:
        return f"Error en cero {n}: {e}"
    return None

def parallel_verify(start_index=1, count=5000, dps=30):
    print(f"Lanzando verificación paralela de {count} ceros en {cpu_count()} núcleos...")
    start_time = time.time()
    
    tasks = [(n, dps) for n in range(start_index, start_index + count)]
    anomalies = []
    errors = []
    
    completed = 0
    with Pool(cpu_count()) as pool:
        for result in pool.imap_unordered(worker_check, tasks, chunksize=10):
            completed += 1
            if result is not None:
                if isinstance(result, str):
                    errors.append(result)
                else:
                    anomalies.append(result)
            
            if completed % 50 == 0 or completed == count:
                elapsed = time.time() - start_time
                percent = (completed / count) * 100
                sys.stdout.write(f"\rProgreso: {completed}/{count} ({percent:.1f}%) - Transcurrido: {elapsed:.1f}s")
                sys.stdout.flush()
                
    print()
    elapsed = time.time() - start_time
    print(f"Procesamiento paralelo finalizado en {elapsed:.2f} segundos.")
    print(f"Anomalías detectadas: {len(anomalies)} | Errores de cálculo: {len(errors)}")

if __name__ == "__main__":
    parallel_verify(1, 5000, 30)
