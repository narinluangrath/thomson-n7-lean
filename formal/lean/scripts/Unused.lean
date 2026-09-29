import ThomsonN7
open Lean Meta

/-- Print declarations from `ThomsonN7.Solution` that the two main theorems do not depend on,
with their source line ranges. -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ThomsonN7 }] {} (trustLevel := 1024)
  let some modIdx := env.getModuleIdx? `ThomsonN7.Solution | throw (IO.userError "module not found")
  let inFile (n : Name) : Bool := env.getModuleIdxFor? n == some modIdx
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[`ThomsonN7.thomson_seven, `ThomsonN7.thomson_seven_unique,
    -- `rfl` simp lemmas: simp uses them by unfolding, so they never appear in proof terms
    `ThomsonN7.Kron.Ex.ev_one, `ThomsonN7.Kron.Ex.ev_mon, `ThomsonN7.Kron.Ex.ev_c]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    for c in ci.getUsedConstantsAsSet do
      if inFile c && !seen.contains c then todo := todo.push c
  let all := env.constants.map₁.toList.map (·.1) |>.filter inFile
  let unused := all.filter (fun n => !seen.contains n && !n.isInternal)
  IO.println s!"file decls: {all.length}  reachable: {seen.size}  unused (non-internal): {unused.length}"
  for n in unused do
    match declRangeExt.find? env n with
    | some r => IO.println s!"{n} {r.range.pos.line} {r.range.endPos.line}"
    | none => IO.println s!"{n} ? ?"

