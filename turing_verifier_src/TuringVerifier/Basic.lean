import Lean.Data.Json

open Lean

structure DeltaInterval where
  index : Nat
  delta_lower : Int
  delta_upper : Int
  z_lower : Float
  z_upper : Float
  deriving Lean.FromJson, Lean.ToJson, Repr

structure MacroBlock where
  block_index : Nat
  min_delta : Int
  max_delta : Int
  subintervals : List DeltaInterval
  deriving Lean.FromJson, Lean.ToJson, Repr

structure TuringMacroCertificate where
  theorem_name : String
  base_t : Float
  scale : Float
  macro_blocks : List MacroBlock
  deriving Lean.FromJson, Lean.ToJson, Repr

def reconstructT (base : Float) (scale : Float) (delta : Int) : Float :=
  base + (Float.ofInt delta) * scale

def loadMacroCertificate (path : System.FilePath) : IO (Option TuringMacroCertificate) := do
  let content ← IO.FS.readFile path
  match Lean.Json.parse content with
  | Except.error e => 
      IO.println s!"Error al parsear JSON: {e}"
      pure none
  | Except.ok json =>
      match Lean.fromJson? json with
      | Except.error e => 
          IO.println s!"Error en decodificación Lean: {e}"
          pure none
      | Except.ok cert => pure (some cert)
