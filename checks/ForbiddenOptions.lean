/-! Check that no source file of the library or of the checks raises the heartbeat limit or sets
a `backward` compatibility option. The contributor instructions forbid both. This script is the
only file that may contain the forbidden text. -/

private def forbidden : List String :=
  ["set_option maxHeartbeats", "set_option backward."]

private def scan (path : System.FilePath) : IO (Array String) := do
  let mut found : Array String := #[]
  let mut number := 0
  for line in (← IO.FS.readFile path).splitOn "\n" do
    number := number + 1
    for text in forbidden do
      if (line.splitOn text).length > 1 then
        found := found.push s!"{path}:{number}: {text}"
  return found

def main : IO Unit := do
  let mut found : Array String := #[]
  let mut files : Nat := 0
  for root in ["ProjectAinos", "checks"] do
    for path in ← (root : System.FilePath).walkDir do
      if path.extension == some "lean" && path.fileName != some "ForbiddenOptions.lean" then
        files := files + 1
        found := found ++ (← scan path)
  if files == 0 then
    throw (IO.userError "No source file was found; run the check from the repository root")
  unless found.isEmpty do
    throw (IO.userError ("Forbidden options:\n" ++ "\n".intercalate found.toList))
  IO.println s!"No forbidden option in {files} files."
