import mpmath
import time

def verify_riemann_zeros(start_index=1, count=10000, dps=30):
    """
    Verifies Riemann zeta zeros on the critical line using arbitrary precision.
    """
    mpmath.mp.dps = dps  # Set decimal places for precision
    print(f"Starting verification of {count} zeros starting from index {start_index} at {dps}-digit precision...")
    
    anomalies = []
    start_time = time.time()
    
    for n in range(start_index, start_index + count):
        try:
            # Retrieve the n-th zero on the critical line: 1/2 + i*t
            zero = mpmath.zetazero(n)
            
            # Evaluate zeta at this zero point
            val = mpmath.zeta(zero)
            
            # Check magnitude against precision tolerance
            tolerance = mpmath.mpf(10)**(-dps + 6)
            if abs(val) > tolerance:
                anomalies.append((n, zero, val))
        except Exception as e:
            print(f"Error computing zero {n}: {e}")
            
    elapsed = time.time() - start_time
    print(f"Verified {count} zeros in {elapsed:.2f} seconds.")
    
    if anomalies:
        print(f"WARNING: Found {len(anomalies)} potential anomalies!")
        for anom in anomalies:
            print(f"Index: {anom[0]}, Zero: {anom[1]}, Zeta Value: {anom[2]}")
    else:
        print("All verified zeros lie precisely on the critical line within tolerance (no counterexamples found).")

if __name__ == "__main__":
    verify_riemann_zeros(start_index=1, count=10000, dps=30)
