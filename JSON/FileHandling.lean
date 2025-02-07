import Lean

-- function that returns if the file with the given path exists
def fileExists (path : String) : IO Bool := do
  let r ← System.FilePath.pathExists path
  return r

-- dump the string into a file with the given name
-- if the file exists throw an error
def dumpStringToFile (path : String) (s : String) : IO Unit := do
  if (← fileExists path) then
    throw (IO.userError "File already exists")
  let h ← IO.FS.Handle.mk path IO.FS.Mode.write
  h.putStr s
