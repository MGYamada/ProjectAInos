import Lean.Elab.Import

/-! Check that every project-local import from the shared cores stays in the
allowed cores. Checking all source modules also covers transitive imports. -/

open Lean

private def sharedCores : List Name :=
  [`ProjectAInos.SmoothAlgebra, `ProjectAInos.SmoothGeometry, `ProjectAInos.Variational]

private def checkImports (path : System.FilePath) (allowed : List Name) : IO Unit := do
  let (imports, _, messages) ← Elab.parseImports (← IO.FS.readFile path) (some path.toString)
  if messages.hasErrors then
    throw (IO.userError s!"Failed to parse the import header of {path}")
  for imp in imports do
    if ((`ProjectAInos).isPrefixOf imp.module || (`YM).isPrefixOf imp.module ||
        (`YangMills).isPrefixOf imp.module) &&
        !(allowed.any (·.isPrefixOf imp.module)) then
      throw (IO.userError s!"{path} imports {imp.module} across the shared-core boundary")

def main : IO Unit := do
  for core in ["SmoothAlgebra", "SmoothGeometry", "Variational"] do
    let root : System.FilePath := "ProjectAInos"
    let entry := root / (core ++ ".lean")
    if ← entry.pathExists then
      checkImports entry sharedCores
    let modules ← (root / core).walkDir
    for path in modules do
      if path.extension == some "lean" then
        checkImports path sharedCores
