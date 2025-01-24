import Lean
import JSON.JSONExport

open Lean
open JSONable

structure Config : Type where
  outDir : String
  imports : List String
  constants : List String
deriving instance Repr for Config

-- A parsing function that takes the list of string and returns a Config object with possible errors
-- before "--" are imports and outDir, after "--" are constants
def parseArgs (args : List String) : Except String Config := do
  let (importsAndOutDir, constants) := args.span (· != "--")
  -- importsAndOutDir must not be empty
  if importsAndOutDir.isEmpty then
    Except.error "No imports or outDir specified"
  else
  -- outDir must be the first element
    match importsAndOutDir with
    | [] => Except.error "No outDir specified"
    | outDir::imports =>
      let constants := constants.tail?
      match constants with
      | none => Except.ok { outDir := outDir, imports := imports, constants := [] }
      | some cs => Except.ok { outDir := outDir, imports := imports, constants := cs }

#eval parseArgs ["outDir", "imports", "--", "c1", "c2"]

unsafe
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let parsedArgs := parseArgs args
  match parsedArgs with
  | Except.error eS => panic! eS
  | Except.ok {outDir, imports, constants} =>
    IO.println s!"outDir: {outDir}, imports: {imports}, constants: {constants}"
    let imports := imports.toArray.map fun mod => { module := Syntax.decodeNameLit ("`" ++ mod) |>.get! }
    let env ← importModules imports {}
    let constants : List Name := match constants with
    | [] => env.constants.toList.map Prod.fst |>.filter (!·.isInternal)
    | cs => cs.map fun c => Syntax.decodeNameLit ("`" ++ c) |>.get!
    M.run env do
      for c in constants do
        let _ ← dumpJSONDeclarationToFile outDir c
