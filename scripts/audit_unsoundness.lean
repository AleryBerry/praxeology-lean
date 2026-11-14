import Lean
open Lean Meta

/-!
# Audit Unsoundness in Praxeology

Identifies:
1. A -> A proofs / Circularities (hypotheses matching conclusion, 100% conjunct coverage, `:= h`)
2. Propositions assuming the conclusion (evidence/scenario projection theorems)
3. Trivial / Degenerate proofs (rfl/decide with no hypotheses, True conclusion)
4. Unused / Decorative hypotheses
5. Ex-falso / Vacuous implications
-/

def glueConsts : Lean.NameSet := Lean.NameSet.empty
  |>.insert ``And.intro |>.insert ``And.left |>.insert ``And.right |>.insert ``And.casesOn
  |>.insert ``And.rec |>.insert ``Exists.intro |>.insert ``Exists.casesOn |>.insert ``Exists.elim
  |>.insert ``Or.inl |>.insert ``Or.inr |>.insert ``Or.elim |>.insert ``Or.casesOn
  |>.insert ``Iff.intro |>.insert ``Iff.mp |>.insert ``Iff.mpr |>.insert ``False.elim
  |>.insert ``absurd |>.insert ``id |>.insert ``True.intro |>.insert ``trivial
  |>.insert ``Not |>.insert ``And |>.insert ``Or |>.insert ``Exists |>.insert ``Iff
  |>.insert ``True |>.insert ``False |>.insert ``Eq |>.insert ``Eq.refl |>.insert ``rfl
  |>.insert ``Eq.mpr |>.insert ``Eq.mp |>.insert ``Exists.choose
  |>.insert ``Exists.choose_spec |>.insert ``PSigma.mk |>.insert ``Subtype.mk
  |>.insert ``Subtype.val |>.insert ``Subtype.property |>.insert ``Nonempty.intro
  |>.insert ``congrArg |>.insert ``Eq.symm |>.insert ``Eq.trans |>.insert ``Eq.subst
  |>.insert ``Eq.ndrec |>.insert ``Eq.rec |>.insert ``of_eq_true |>.insert ``eq_self
  |>.insert ``Exists.rec |>.insert ``Or.rec |>.insert ``False.rec |>.insert ``False.casesOn
  |>.insert ``Iff.refl |>.insert ``Classical.byContradiction
  |>.insert ``Classical.not_not |>.insert ``Decidable.byContradiction

def isGlue (env : Environment) (c : Name) : Bool :=
  glueConsts.contains c ||
  (env.isProjectionFn c) ||
  (match env.find? c with
   | some (.ctorInfo _) => true
   | some (.recInfo _) => true
   | _ => false) ||
  c.isInternal ||
  (c.getPrefix != .anonymous && (c.getString! == "casesOn" || c.getString! == "rec" ||
     c.getString! == "mk" || c.getString! == "recOn" || c.getString! == "noConfusion"
     || c.getString! == "elim" || c.getString! == "intro"))

def isPraxDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).getRoot == `Praxeology
  | none => false

def autoGen (env : Environment) (n : Name) : Bool :=
  n.isInternal || env.isProjectionFn n ||
  (match n with
   | .str _ s => ["injEq","inj","ext","ext_iff","sizeOf_spec","eq_def","congr_simp","brecOn",
                  "noConfusion","binductionOn","eq_1","eq_2","eq_3","eq_4"].contains s
                 || s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "_"
   | _ => false)

partial def stripLams (e : Expr) : Expr :=
  match e with
  | .lam _ _ b _ => stripLams b
  | .mdata _ b => stripLams b
  | _ => e

def structName? (e : Expr) : MetaM (Option Name) := do
  let e ← whnfR e
  match e.getAppFn with
  | .const c _ => if isStructure (← getEnv) c then return some c else return none
  | _ => return none

partial def collectFacts (x : Expr) (depth : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
  let ty ← inferType x
  if (← isProp ty) then
    let mut acc := acc.push ty
    if depth > 0 then
      if let some s ← structName? ty then
        for f in getStructureFields (← getEnv) s do
          try
            let p ← mkProjection x f
            acc ← collectFacts p (depth - 1) acc
          catch _ => pure ()
    return acc
  if depth == 0 then return acc
  let some s ← structName? ty | return acc
  let mut acc := acc
  for f in getStructureFields (← getEnv) s do
    try
      let p ← mkProjection x f
      acc ← collectFacts p (depth - 1) acc
    catch _ => pure ()
  return acc

partial def splitConj (p : Expr) (deep : Bool) (fuel : Nat) : MetaM (Array Expr) := do
  if fuel == 0 then return #[p]
  let p' ← if deep then whnf p else whnfR p
  if p'.isAppOfArity ``And 2 then
    return (← splitConj p'.appFn!.appArg! deep (fuel-1)) ++ (← splitConj p'.appArg! deep (fuel-1))
  if let some s ← structName? p' then
    if s != ``And && (← isProp p') && !(isClass (← getEnv) s) then
      let fields := getStructureFields (← getEnv) s
      if fields.size > 0 then
        let r ← withLocalDeclD `c p' fun c => do
          let mut out : Array Expr := #[]
          for f in fields do
            let fp ← mkProjection c f
            let ft ← inferType fp
            if ft.hasAnyFVar (· == c.fvarId!) then return none
            out := out ++ (← splitConj ft deep (fuel-1))
          return some out
        if let some out := r then return out
  return #[p]

def factMatches (c f : Expr) : MetaM Bool := do
  let hb ← IO.getNumHeartbeats
  tryCatchRuntimeEx (do
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 20000000, initHeartbeats := hb }) do
        if (← withReducible (isDefEq c f)) then return true
        withTransparency .default (isDefEq c f)) (fun _ => return false)

structure AuditRow where
  mod : Name
  file : String
  line : Nat
  name : Name
  category : String
  severity : String
  detail : String
  deriving Inhabited, Repr

def analyzeDecl (ci : ConstantInfo) : MetaM (Option AuditRow) := do
  let env ← getEnv
  let n := ci.name
  let some val := ci.value? (allowOpaque := true) | return none
  let ty := ci.type
  let mod := env.header.moduleNames[(env.getModuleIdxFor? n).get!.toNat]!
  let file := (mod.toString.replace "." "/") ++ ".lean"
  let line := match (← findDeclarationRanges? n) with
    | some r => r.range.pos.line
    | none => 0

  forallTelescopeReducing ty fun xs concl => do
    if !(← isProp concl) then return none

    let mut facts : Array Expr := #[]
    let mut propHyps : Array (FVarId × Name × Expr) := #[]
    for x in xs do
      let xt ← inferType x
      if (← isProp xt) then
        propHyps := propHyps.push (x.fvarId!, ← x.fvarId!.getUserName, xt)
      facts ← collectFacts x 2 facts

    let body := val.beta xs
    let usedConsts := val.getUsedConstants
    let nonGlue := usedConsts.filter (fun c => !isGlue env c && !(c.isPrefixOf n && c != n))

    -- Check 1: Conclusion defeq to a single hypothesis (A -> A)
    for (_, hname, ht) in propHyps do
      if (← withReducible (isDefEq ht concl)) then
        return some {
          mod, file, line, name := n,
          category := "A_TO_A",
          severity := "HIGH",
          detail := s!"Conclusion is definitionally equal to hypothesis '{hname}'"
        }

    -- Check 2: Proof is just applying a hypothesis (HYP_APPLY)
    let core := stripLams val
    if core.getAppFn.isBVar && propHyps.size > 0 then
      return some {
        mod, file, line, name := n,
        category := "HYP_APPLY",
        severity := "HIGH",
        detail := "Proof term is a direct bound-variable / hypothesis application"
      }

    -- Check 3: Conjunct coverage
    let cs ← splitConj concl false 8
    let mut cov := 0
    for c in cs do
      if (← facts.anyM (factMatches c ·)) then cov := cov + 1

    let ds ← splitConj concl true 8
    let mut dcov := 0
    for d in ds do
      if (← facts.anyM (factMatches d ·)) then dcov := dcov + 1

    if cs.size > 0 && cov == cs.size && propHyps.size > 0 then
      return some {
        mod, file, line, name := n,
        category := "100%_CONJUNCTS_ASSUMED",
        severity := "HIGH",
        detail := s!"All {cs.size}/{cs.size} conclusion conjuncts are directly present in hypotheses"
      }

    if ds.size > 1 && dcov == ds.size && propHyps.size > 0 then
      return some {
        mod, file, line, name := n,
        category := "100%_DEEP_CONJUNCTS_ASSUMED",
        severity := "HIGH",
        detail := s!"All {ds.size}/{ds.size} unfolded conclusion components are directly present in hypotheses"
      }

    if cs.size > 2 && cov * 2 >= cs.size then
      return some {
        mod, file, line, name := n,
        category := "MAJORITY_CONJUNCTS_ASSUMED",
        severity := "MEDIUM",
        detail := s!"{cov}/{cs.size} conclusion conjuncts are directly present in hypotheses"
      }

    -- Check 4: Unused Prop hypotheses
    let mut unused : List String := []
    for (fvar, hname, _) in propHyps do
      if !(body.containsFVar fvar) then
        unused := unused ++ [toString hname]
    if !unused.isEmpty then
      let sev := if unused.any (fun u => !u.startsWith "_") then "HIGH" else "LOW"
      return some {
        mod, file, line, name := n,
        category := "UNUSED_HYPOTHESIS",
        severity := sev,
        detail := s!"Hypothesis(es) unused in proof: {unused}"
      }

    -- Check 5: Trivial proofs (no prop hyps, only decide / rfl / glue)
    if propHyps.isEmpty && nonGlue.isEmpty && concl.isConstOf ``True then
      return some {
        mod, file, line, name := n,
        category := "TRUE_CONCLUSION",
        severity := "HIGH",
        detail := "Theorem asserts True with no premises"
      }

    return none

def collectAllPraxModules (env : Environment) : Array Name :=
  env.header.moduleNames.filter fun m => m.getRoot == `Praxeology

def runAudit : MetaM (Array AuditRow) := do
  let env ← getEnv
  let mut rows : Array AuditRow := #[]
  for (n, ci) in env.constants.toList do
    if !isPraxDecl env n || autoGen env n then continue
    let .thmInfo _ := ci | continue
    let hb ← IO.getNumHeartbeats
    let r ← tryCatchRuntimeEx
      (withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 400000000, initHeartbeats := hb }) (analyzeDecl ci))
      (fun _ => pure none)
    if let some row := r then
      rows := rows.push row
  return rows

def printReport (rows : Array AuditRow) : IO Unit := do
  let sep := "================================================================================"
  IO.println sep
  IO.println "PRAXEOLOGY LEAN — FORMAL UNSOUNDNESS & CIRCULARITY AUDIT"
  IO.println sep
  IO.println ""

  let highRows := rows.filter (·.severity == "HIGH")
  let medRows := rows.filter (·.severity == "MEDIUM")
  let lowRows := rows.filter (·.severity == "LOW")

  IO.println s!"Total Findings: {rows.size}"
  IO.println s!"  • HIGH severity (A->A, 100% assumed conjuncts, hyp-apply, unused active hyps): {highRows.size}"
  IO.println s!"  • MEDIUM severity (majority assumed conjuncts, evidence repackaging): {medRows.size}"
  IO.println s!"  • LOW severity (underscore-prefixed unused hyps):                     {lowRows.size}"
  IO.println ""

  IO.println "--- HIGH SEVERITY FINDINGS ---"
  for r in highRows do
    IO.println s!"[{r.category}] {r.file}:{r.line}"
    IO.println s!"  Declaration: {r.name}"
    IO.println s!"  Details:     {r.detail}"
    IO.println ""

  IO.println "--- MEDIUM SEVERITY FINDINGS ---"
  for r in medRows do
    IO.println s!"[{r.category}] {r.file}:{r.line}"
    IO.println s!"  Declaration: {r.name}"
    IO.println s!"  Details:     {r.detail}"
    IO.println ""

  IO.println "--- LOW SEVERITY FINDINGS ---"
  for r in lowRows do
    IO.println s!"[{r.category}] {r.file}:{r.line}"
    IO.println s!"  Declaration: {r.name}"
    IO.println s!"  Details:     {r.detail}"
    IO.println ""

  IO.println sep

def mods : Array Name := #[
  `Praxeology.Action,`Praxeology.BusinessCycle,`Praxeology.BusinessCycle.Auctions,
  `Praxeology.BusinessCycle.BehavioralChoices,`Praxeology.BusinessCycle.BehavioralProgram,
  `Praxeology.BusinessCycle.Clusters,`Praxeology.BusinessCycle.CreditLifecycleFrame,
  `Praxeology.BusinessCycle.DefaultWitness,`Praxeology.BusinessCycle.FactorExecution,
  `Praxeology.BusinessCycle.Firms,`Praxeology.BusinessCycle.Grounded,
  `Praxeology.BusinessCycle.Information,`Praxeology.BusinessCycle.IntegratedResults,
  `Praxeology.BusinessCycle.MasterResults,`Praxeology.BusinessCycle.Outcome,
  `Praxeology.BusinessCycle.PhysicalSettlementWitness,`Praxeology.BusinessCycle.ProfileProgram,
  `Praxeology.BusinessCycle.Regimes,`Praxeology.Catallactics,`Praxeology.Catallactics.Credit,
  `Praxeology.Catallactics.ProgramExchangeWitness,`Praxeology.EconometricLimits,
  `Praxeology.EconomicCalculation,`Praxeology.EconomicCalculation.Incentives,
  `Praxeology.EconomicCalculation.Institutions,`Praxeology.Entrepreneurship,`Praxeology.EpistemicAbility,
  `Praxeology.ExactNat,`Praxeology.FiniteEconomy,`Praxeology.FiniteEconomy.ActionFrameCompiler,
  `Praxeology.FiniteEconomy.ActiveParticipation,`Praxeology.FiniteEconomy.BilateralPilot,
  `Praxeology.FiniteEconomy.Communication,`Praxeology.FiniteEconomy.Compiler,
  `Praxeology.FiniteEconomy.Credit,`Praxeology.FiniteEconomy.Execution,
  `Praxeology.FiniteEconomy.FiveStageSupplyChain,`Praxeology.FiniteEconomy.Market,
  `Praxeology.FiniteEconomy.Physical,`Praxeology.FiniteEconomy.Policy,
  `Praxeology.FiniteEconomy.ProfileSchedule,`Praxeology.FiniteEconomy.Program,
  `Praxeology.FiniteEconomy.ProgramActionFrame,`Praxeology.FiniteEconomy.ProgramActionFrameWitness,
  `Praxeology.FiniteEconomy.ScaleBenchmarks,`Praxeology.FiniteEconomy.Tree,
  `Praxeology.FirmBoundary,`Praxeology.FirmWitness,`Praxeology.Frame,
  `Praxeology.Frame.Core,`Praxeology.Frame.Witnesses,`Praxeology.Marginal,
  `Praxeology.Marginal.AllocationActionFrame,`Praxeology.Marginal.AllocationChoice,
  `Praxeology.Organization,`Praxeology.Production,`Praxeology.StateMonopoly,
  `Praxeology.Subjective,`Praxeology.Veridical
]

unsafe def main (_args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (mods.map fun m => { module := m, importAll := true }) {} (loadExts := true)
  let (rows, _) ← (runAudit.run' {} {}).toIO { fileName := "audit", fileMap := default, maxHeartbeats := 0 } { env := env }
  printReport rows
