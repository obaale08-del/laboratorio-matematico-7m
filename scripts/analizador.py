import os
import subprocess
import time
import sys

def analizar_rendimiento(input_path):
    print("Iniciando análisis de rendimiento del Códice Petruska...")
    
    if not os.path.exists(input_path):
        print(f"Error: No se encuentra el archivo {input_path}")
        return

    size_bytes = os.path.getsize(input_path)
    size_mb = size_bytes / (1024 * 1024)
    print(f"Tamaño original del archivo: {size_mb:.2f} MB")
    print("Procesando vídeo (esto puede tardar unos minutos en Termux)... Por favor espera.")

    output_test = "test_symbio_output.mp4"
    start_time = time.time()
    
    try:
        # Añadimos -stats para ver el progreso de FFmpeg en vivo
        proceso = subprocess.run([
            "ffmpeg", "-y", "-i", input_path, 
            "-vf", "scale=1280:-2", 
            "-vcodec", "libx264", "-preset", "ultrafast", "-crf", "28", 
            "-threads", "0", "-pix_fmt", "yuv420p", "-acodec", "aac", "-b:a", "96k",
            output_test
        ], check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        
        elapsed_time = time.time() - start_time
        new_size_mb = os.path.getsize(output_test) / (1024 * 1024)
        ratio = (1 - (new_size_mb / size_mb)) * 100

        print("\n--- Resultados del Análisis ---")
        print(f"Tiempo de procesamiento: {elapsed_time:.2f} segundos")
        print(f"Tamaño comprimido: {new_size_mb:.2f} MB")
        print(f"Tasa de reducción: {ratio:.2f}%")
        
        if os.path.exists(output_test):
            os.remove(output_test)
            
    except subprocess.CalledProcessError as e:
        print(f"Error durante la ejecución de FFmpeg:\n{e.stdout.decode('utf-8', errors='ignore')}")

if __name__ == "__main__":
    archivo_prueba = "uploads/VID_20260812_112914.mp4"
    analizar_rendimiento(archivo_prueba)
