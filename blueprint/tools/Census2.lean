open Lean

namespace Census2
partial def hasNum : Name → Bool
  | .anonymous => false
  | .str p _ => hasNum p
  | .num _ _ => true

def autoLast : List String :=
  ["rec","recOn","casesOn","brecOn","below","ibelow","binductionOn","noConfusion","noConfusionType",
   "injEq","inj","sizeOf_spec","eq_def","induct","induct_unfolding","fun_cases","fun_cases_unfolding","unfold","ctorIdx","toCtorIdx",
   "ctorElim","ctorElimType","ndrec","ndrecOn","elim","_sizeOf_inst","noConfusionEnum","ofNat"]

def lastStr : Name → String
  | .str _ s => s
  | _ => ""

def isAuto (n : Name) : Bool :=
  let l := lastStr n
  hasNum n || n.isInternalDetail || autoLast.contains l || l.startsWith "match_" || l.startsWith "proof_" ||
  l.startsWith "_" || l.startsWith "eq_" || l.startsWith "below_" || l.startsWith "brecOn_" || l.startsWith "rec_" || l.startsWith "casesOn_" ||
  l.startsWith "sizeOf_" || l.endsWith "_sizeOf_inst"
end Census2

open Census2 in
#eval show CoreM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut allOut : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let ms := (mods[idx.toNat]!).toString
    unless ms.startsWith "Lean4Lean" || ms == "Main" do continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let user := privateToUserName n
    allOut := allOut.push s!"{user}\t{ms}\t{kind}"
    if isAuto user || kind == "rec" then continue
    let line ← do
      match (← findDeclarationRanges? n) with
      | some r => pure (toString r.range.pos.line)
      | none => pure "-1"
    let axs ← collectAxioms n
    let axl := (axs.toList.map (·.toString))
    let axStr := if axl.isEmpty then "-" else String.intercalate "," axl
    let us := axs.contains ``sorryAx
    let vis := if n == user then "public" else "private"
    IO.println s!"{user}\t{ms}\t{kind}\t{line}\t{axStr}\t{us}\t{vis}"
  IO.FS.writeFile "ALLC_PATH" (String.intercalate "\n" allOut.toList ++ "\n")
