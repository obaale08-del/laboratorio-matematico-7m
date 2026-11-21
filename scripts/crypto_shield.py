import os
import hashlib
import json
import base64

def encrypt_bundle():
    bundle_path = "lean_exports_bundle.tar.gz"
    if not os.path.exists(bundle_path):
        print("-> Error: El bundle no existe.")
        return

    with open(bundle_path, "rb") as f:
        data = f.read()
        
    file_hash = hashlib.sha256(data).hexdigest()
    
    # Derivación de semilla soberana exclusiva del motor Petruska Fenix
    seed_key = hashlib.sha256(b"petruska_fenix_sovereign_core_2026_millennium").digest()
    encrypted_bytes = bytearray(b ^ seed_key[i % len(seed_key)] for i, b in enumerate(data))
    
    enc_path = "lean_exports_bundle.enc"
    with open(enc_path, "wb") as f:
        f.write(encrypted_bytes)
        
    security_meta = {
        "sha256_original": file_hash,
        "encryption_protocol": "Petruska-Sovereign-XOR-HashDerivation",
        "status": "SECURED_LOCALLY"
    }
    
    os.makedirs("lean_exports", exist_ok=True)
    with open("lean_exports/security_certificate.json", "w") as f:
        json.dump(security_meta, f, indent=4)
        
    print(f"-> Bundle cifrado con éxito: {enc_path}")
    print(f"-> SHA-256 de integridad: {file_hash}")

if __name__ == "__main__":
    encrypt_bundle()
