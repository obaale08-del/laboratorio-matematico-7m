import Lean

structure RangeData where
  t_start : Float
  t_end : Float
  step : Float
  deriving Lean.FromJson, Repr

structure TuringCertificate where
  theorem : String
  range : RangeData
  certified_zeros_count : Nat
  elapsed_seconds : Float
  status : String
  method : String
  deriving Lean.FromJson, Repr

def loadTuringCertificate (path : System.FilePath) : IO (Option TuringCertificate) := do
  let content ← IO.FS.readFile path
  match Lean.Json.parse content with
  | Except.ok json => 
      match Lean.fromJson? json with
      | Except.ok cert => pure (some cert)
      | Except.error _ => pure none
  | Except.error _ => pure none

def main : IO Unit := do
  let path : System.FilePath := "turing_certificate.json"
  match ← loadTuringCertificate path with
  | some cert => 
      IO.println s!"¡Certificado cargado con éxito en Lean 4!"
      IO.println s!"Teorema: {cert.theorem}"
      IO.println s!"Rango evaluado: T = [{cert.range.t_start}, {cert.range.t_end}]"
      IO.println s!"Ceros certificados: {cert.certified_zeros_count}"
      IO.println s!"Estado del sistema: {cert.status}"
  | none => 
      IO.println "Error crítico: No se pudo procesar el archivo JSON."
