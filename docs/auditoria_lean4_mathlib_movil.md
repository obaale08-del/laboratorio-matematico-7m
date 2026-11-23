# Auditoría técnica: Lean 4 y Mathlib en entorno móvil

## 1. Arquitectura y entorno de ejecución
- **Hardware y sistema base:** Dispositivo móvil (`aarch64-unknown-linux-gnu`) ejecutando toda la pila de verificación de forma local sin PC.
- **Capa Linux:** Contenedor Ubuntu gestionado mediante `proot-distro` desde Termux.
- **Directorio de trabajo del verificador:** `~/turing_verifier` (dentro del entorno Ubuntu).
- **Repositorio de fuentes y documentación:** `laboratorio-matematico-7m` (`~/repo_petruska_fenix`, con fuentes en `turing_verifier_src/`).

## 2. Versiones y cadena de herramientas verificadas
- **Toolchain (`lean-toolchain`):** `leanprover/lean4:v4.34.0-rc2`
- **Gestor de toolchains (`elan`):** `elan 4.2.4 (227caca13 2026-08-25)` (`/root/.elan/bin/elan`)
- **Compilador (`lean`):** `Lean (version 4.34.0-rc2, aarch64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)` (`/root/.elan/bin/lean`)
- **Sistema de construcción (`lake`):** `Lake version 5.0.0-src+6a10ac8 (Lean version 4.34.0-rc2)` (`/root/.elan/bin/lake`)

## 3. Dependencias, compilación y almacenamiento
- **Dependencia principal (`lake-manifest.json`):** `mathlib` (`https://github.com/leanprover-community/mathlib4.git`, revisión `7073dfa7396aa551c07f783c58e1104719a3da9f`).
- **Otras dependencias declaradas:** `plausible`, `LeanSearchClient`, `importGraph`.
- **Compilación verificada (`lake build TuringVerifier.IntervalArithmetic`):** Completada con éxito (`Build completed successfully (8921 jobs)`) en `2m39.384s` (`real`: `2m39.384s`, `user`: `0m11.362s`, `sys`: `0m16.828s`).
- **Artefactos y caché en `.lake`:** ~11 GB en el dispositivo, con salidas compiladas en `.lake/build/lib/lean` (`Main.olean`, `Main.ilean`, `Main.trace`, `TuringVerifier/IntervalArithmetic.olean`, `TuringVerifier/IntervalArithmetic.ilean`, `TuringVerifier/IntervalArithmetic.trace`) y archivos IR/objeto en `.lake/build/ir`.

## 4. Observaciones operativas en entorno móvil
- En comandos no interactivos con `proot-distro login ubuntu -- bash -c '...'`, exportar `PATH="$HOME/.elan/bin:$PATH"` asegura el acceso directo a `elan`, `lean` y `lake`.
- La ejecución directa de `lake env lean` sobre archivos que importan módulos con `Mathlib` y tácticas como `norm_num` (`TestVerify.lean`) puede prolongarse varios minutos bajo `proot` en ARM64; verificar o completar primero el objetivo con `lake build` permite confirmar el grafo de dependencias (`8921 jobs`) y generar los artefactos `.olean`.
- `.lake/` y los certificados pesados (como `certificate_million.json`) permanecen excluidos de Git mediante `.gitignore` para respetar los límites de repositorio y el espacio disponible en el dispositivo.
