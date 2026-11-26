namespace FlowAudit
open Lean Elab Command

def checks : List Name := [
  `Flow.SeymourSixFlow,
  `Flow.JLPTWellColouring
]

partial def inputs : Expr → NameSet
  | .forallE _ domain body _ => Id.run do
    let mut found := inputs body
    for name in domain.getUsedConstants do
      if checks.contains name then found := found.insert name
    return found
  | .letE _ _ _ body _ | .mdata _ body => inputs body
  | _ => {}

def report (name : Name) : CommandElabM Unit := do
  let decl ← getConstInfo name
  let deps := ((inputs decl.type).toList.map Name.toString).mergeSort (· ≤ ·)
  logInfo m!"CHECK_INPUTS|{name}|{String.intercalate "," deps}|END"
end FlowAudit
