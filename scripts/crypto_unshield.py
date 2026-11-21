import os
import hashlib
import json

def decrypt_bundle():
    enc_path = "lean_exports_bundle.enc"
    cert_path = "lean_exports/security_certificate.json"
    
    if not os.path.exists(enc_path) or not os.path.exists(cert_path):
        print("-> Error: No se encuentra el bundle cifrado o el certificado de seguridad.")
        return

    with open(cert_path, "r") as f:
        security_meta = json.load(f)
        expected_hash = security_meta["sha256_original"]

    with open(enc_path, "rb") as f:
        encrypted_bytes = f.read()
        
    # Reversión utilizando la misma semilla soberana del motor Petruska Fenix
    seed_key = hashlib.sha256(b"petruska_fenix_sovereign_core_2026_millennium").digest()
    decrypted_bytes = bytearray(b ^ seed_key[i % len(seed_key)] for i, b in enumerate(encrypted_bytes))
    
    # Verificación de integridad SHA-256
    recovered_hash = hashlib.sha256(decrypted_bytes).hexdigest()
    
    restored_path = "lean_exports_bundle_restored.tar.gz"
    with open(restored_path, "wb") as f:
        f.write(decrypted_bytes)
        
    if recovered_hash == expected_hash:
        print(f"-> Descifrado exitoso: {restored_path}")
        print(f"-> Integridad verificada (SHA-256 coincidente): {recovered_hash}")
    else:
        print("-> Advertencia de integridad: El hash del archivo restaurado no coincide con el original.")

if __name__ == "__main__":
    decrypt_bundle()
