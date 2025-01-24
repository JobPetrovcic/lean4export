import Lean
import JSON.JSONable
import JSON.GetDependencies
import JSON.FileHandling

open Lean

structure Context where env : Environment
structure State where
  --visitedRecRules : HashMap RecursorRule Nat := {}
  visitedConstants : NameHashSet := {}
abbrev M := ReaderT Context <| StateT State IO

def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

def ConstantInfoJSONandDependencies (c : ConstantInfo) : (String × List Name) :=
  let deps := getDeclarationDeps c
  let json_content := JSONable.json c
  -- wrap the content in a JSON object with the dependencies
  let kvpairs := [("tag", "DeclarationProfile"), ("dependencies", jsonListAsJSONList deps), ("content", json_content)]
  (JSONable.json kvpairs, deps)

unsafe
def dumpJSONDeclarationToFile (folder : String) (c : Name) : M (Unit) := do
  if (← get).visitedConstants.contains c then
    return Unit.unit
  else
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  let possible_decl := (← read).env.find? c
  match possible_decl with
  | none => panic! "Declaration not found"
  | some decl =>
    if decl.isUnsafe then return Unit.unit
    else
      let (json, deps) := ConstantInfoJSONandDependencies decl
      let _ ← dumpStringToFile (folder ++ "/" ++ c.toString ++ ".json") json
      -- dump the dependencies
      for dep in deps do
        let _ ← dumpJSONDeclarationToFile folder dep
      return Unit.unit
