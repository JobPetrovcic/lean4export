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

-- The character '/' is not allowed in file names so we replace it with ' '
-- Names don't contain spaces so this should be an injective function
unsafe
def NameToFileFriendlyString (n : Name) : String :=
  -- if the name contains a '/' replace it with a space
  let sn := n.toString
  if sn.contains ' ' then
    panic! "Name contains a space"
  else
    sn.replace "/" " "

unsafe
def ConstantInfoJSONandDependencies (c : ConstantInfo) : (String × List Name) :=
  let deps := getDeclarationDeps c
  let json_content := JSONable.json c
  -- wrap the content in a JSON object with the dependencies
  -- the dependencies are a converted using NameToFileFriendlyString
  -- this is done so that when the parser reads the file it nows which file to look for (as opposed to having convert the name to a file friendly name)
  let kvpairs :=
    [
      ("dependencies", jsonListAsList (deps.map (surroundWithQuotes ∘ NameToFileFriendlyString))),
      ("content", json_content)
    ]
  (jsonListAsDict kvpairs, deps)

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
      let _ ← dumpStringToFile (folder ++ "/" ++ (NameToFileFriendlyString c) ++ ".json") json
      -- dump the dependencies
      for dep in deps do
        let _ ← dumpJSONDeclarationToFile folder dep
      return Unit.unit
