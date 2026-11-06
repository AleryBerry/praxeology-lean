/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Physical
import Mathlib.Tactic.IntervalCases

/-!
# Ten-agent five-stage physical supply-chain fixture

This finite payload runs five productive stages. Four exact bilateral
settlements move each intermediate good to the next producer; every buyer
starts with spendable money, so no same-transition inflow finances a trade.
The executable physical interpreter checks affordability and exact natural
number remainders at every edge. Preference and credit claims remain outside
this payload and require their ActionFrame-purpose certificates separately.
-/

@[expose] public section

namespace Praxeology

inductive SupplyChainOperation where
  | mine
  | refine
  | fabricate
  | assemble
  | retail
  deriving DecidableEq

instance : Fintype SupplyChainOperation where
  elems := {.mine, .refine, .fabricate, .assemble, .retail}
  complete := by
    intro op
    cases op <;> simp

abbrev SupplyChainAgent := Fin 10
abbrev SupplyChainGood := Fin 7
abbrev SupplyChainMoment := Fin 10

def supplyRaw : SupplyChainGood := 0
def supplyOre : SupplyChainGood := 1
def supplyComponent : SupplyChainGood := 2
def supplyPart : SupplyChainGood := 3
def supplyFinalGood : SupplyChainGood := 4
def supplyMoney : SupplyChainGood := 5

/-- A ten-moment chain: each non-root node points to its immediate
predecessor. -/
def fiveStageSupplyChainParent (t : SupplyChainMoment) : SupplyChainMoment :=
  if t.val = 0 then 0 else ⟨t.val - 1, by omega⟩

def fiveStageSupplyChainTree : FiniteTreeSpec where
  extraNodes := 9
  parent := fiveStageSupplyChainParent
  parent_root := by
    apply Fin.ext
    simp [fiveStageSupplyChainParent]
  parent_decreases := by
    intro v hv
    dsimp [fiveStageSupplyChainParent]
    split_ifs with hz
    · exact (hv (Fin.ext hz)).elim
    · rw [Fin.val_mk]
      omega

/-- The final chain node is a history leaf. -/
def fiveStageSupplyChainHistory : fiveStageSupplyChainTree.History :=
  ⟨9, by
    intro v hv heq
    have hvpos : 0 < v.val := by
      by_contra hn
      have hz : v.val = 0 := Nat.eq_zero_of_not_pos hn
      exact hv (Fin.ext hz)
    have hvlt : v.val < 10 := by simpa [fiveStageSupplyChainTree] using v.isLt
    have heqVal := congrArg Fin.val heq
    simp [fiveStageSupplyChainTree, fiveStageSupplyChainParent,
      Nat.ne_of_gt hvpos] at heqVal
    omega⟩

/-- Five operations transform raw material into a retail service. -/
def fiveStageSupplyChainOperations :
    OperationSemantics SupplyChainOperation SupplyChainGood Unit where
  input op m :=
    match op with
    | .mine => if m = supplyRaw then 1 else 0
    | .refine => if m = supplyOre then 1 else 0
    | .fabricate => if m = supplyComponent then 1 else 0
    | .assemble => if m = supplyPart then 1 else 0
    | .retail => if m = supplyFinalGood then 1 else 0
  output op m :=
    match op with
    | .mine => if m = supplyOre then 1 else 0
    | .refine => if m = supplyComponent then 1 else 0
    | .fabricate => if m = supplyPart then 1 else 0
    | .assemble => if m = supplyFinalGood then 1 else 0
    | .retail => 0
  service op _ := if op = .retail then 1 else 0

/-- The complete enacted action profile at each node. Even-numbered nodes
produce; the intervening odd-numbered nodes settle the next intermediate-good
exchange. -/
def fiveStageSupplyChainActionsAt (moment : Nat) :
    SupplyChainAgent → EconomyAction SupplyChainAgent SupplyChainGood
      SupplyChainOperation := fun agent =>
  match moment, agent.val with
  | 0, 0 => .operate .mine
  | 1, 0 => .offer 0 1 1 supplyOre 1 supplyMoney
  | 1, 1 => .accept 1 0 1 supplyOre 1 supplyMoney
  | 2, 1 => .operate .refine
  | 3, 1 => .offer 1 2 1 supplyComponent 1 supplyMoney
  | 3, 2 => .accept 2 1 1 supplyComponent 1 supplyMoney
  | 4, 2 => .operate .fabricate
  | 5, 2 => .offer 2 3 1 supplyPart 1 supplyMoney
  | 5, 3 => .accept 3 2 1 supplyPart 1 supplyMoney
  | 6, 3 => .operate .assemble
  | 7, 3 => .offer 3 4 1 supplyFinalGood 1 supplyMoney
  | 7, 4 => .accept 4 3 1 supplyFinalGood 1 supplyMoney
  | 8, 4 => .operate .retail
  | _, _ => .idle

def fiveStageSupplyChainActions (t : SupplyChainMoment) :
    SupplyChainAgent → EconomyAction SupplyChainAgent SupplyChainGood
      SupplyChainOperation := fiveStageSupplyChainActionsAt t.val

/-- Root inventory: agent 0 owns raw material; each downstream producer has
one unit of money to pay the preceding supplier. -/
def fiveStageSupplyChainInitial :
    PhysicalState SupplyChainAgent SupplyChainGood Unit :=
  { stock := fun agent good =>
      if agent = 0 then if good = supplyRaw then 1 else 0
      else if 1 ≤ agent.val ∧ agent.val ≤ 4 then
        if good = supplyMoney then 1 else 0
      else 0
    services := fun _ _ => 0 }

/-- The full five-stage supply-chain execution input to the generic finite
physical interpreter. -/
def fiveStageSupplyChainProgram :
    FinitePhysicalProgram fiveStageSupplyChainTree SupplyChainAgent
      SupplyChainGood SupplyChainOperation Unit where
  operations := fiveStageSupplyChainOperations
  initialState := fiveStageSupplyChainInitial
  actionProfile := fun _ => fiveStageSupplyChainActions
  profile_wellFormed := by
    intro _ t actor
    fin_cases t <;> fin_cases actor <;>
      simp [fiveStageSupplyChainActions, fiveStageSupplyChainActionsAt,
        EconomyAction.WellFormed]
  profile_bundle_invariant := by
    intro t h₁ h₂ _ _
    rfl

/-- Structurally recursive evaluator for the linear pilot. The generic
well-founded `runAt` remains the reusable interpreter; this bounded helper
provides a transparent computation target for the concrete ten-node chain. -/
def fiveStageSupplyChainRun : (n : Nat) →
    Option (PhysicalState SupplyChainAgent SupplyChainGood Unit)
  | 0 => some fiveStageSupplyChainInitial
  | n + 1 =>
      match fiveStageSupplyChainRun n with
      | none => none
      | some state =>
          advanceIfAffordable fiveStageSupplyChainOperations state
            (fiveStageSupplyChainActionsAt n)

/-- The transparent pilot evaluator agrees with the generic tree interpreter
at every node of the chain. -/
theorem fiveStageSupplyChain_runAt_eq (n : Nat) (hn : n ≤ 9) :
    fiveStageSupplyChainProgram.runAt fiveStageSupplyChainHistory
      ⟨n, by simpa [fiveStageSupplyChainTree] using Nat.lt_succ_of_le hn⟩ =
    fiveStageSupplyChainRun n := by
  induction n with
  | zero =>
      simpa [fiveStageSupplyChainRun, fiveStageSupplyChainProgram] using
        (FinitePhysicalProgram.runAt_root fiveStageSupplyChainProgram
          fiveStageSupplyChainHistory)
  | succ n ih =>
      let t : fiveStageSupplyChainTree.Node := ⟨n + 1, by
        simp [fiveStageSupplyChainTree]
        omega⟩
      let pt : fiveStageSupplyChainTree.Node := ⟨n, by
        simp [fiveStageSupplyChainTree]
        omega⟩
      have hidx : t ≠ 0 := by
        intro h
        have hval := congrArg Fin.val h
        simp [t] at hval
      have hparent : fiveStageSupplyChainTree.parent t = pt := by
        apply Fin.ext
        simp [t, pt, fiveStageSupplyChainTree, fiveStageSupplyChainParent]
      change fiveStageSupplyChainProgram.runAt fiveStageSupplyChainHistory t =
        fiveStageSupplyChainRun (n + 1)
      rw [FinitePhysicalProgram.runAt.eq_1, dite_eq_right hidx, hparent]
      rw [ih (by omega)]
      simp only [fiveStageSupplyChainRun]
      cases hrun : fiveStageSupplyChainRun n <;>
        simp [fiveStageSupplyChainProgram, fiveStageSupplyChainActions, pt]

/-- The executable interpreter reaches the terminal moment after all five
production stages and four solvent exchanges. -/
theorem fiveStageSupplyChain_reaches_terminal :
    (fiveStageSupplyChainProgram.runAt fiveStageSupplyChainHistory
      (9 : fiveStageSupplyChainTree.Node)).isSome := by
  have hsome : (fiveStageSupplyChainRun 9).isSome := by
    decide
  change (fiveStageSupplyChainProgram.runAt fiveStageSupplyChainHistory
    (⟨9, by simp [fiveStageSupplyChainTree]⟩ : fiveStageSupplyChainTree.Node)).isSome
  rw [fiveStageSupplyChain_runAt_eq 9 (by omega)]
  exact hsome

/-- The terminal physical state records one completed retail service. -/
theorem fiveStageSupplyChain_retail_service :
    ((fiveStageSupplyChainRun 9).get (by decide)).services 4 = 1 := by
  decide

/-- The linear supply-chain tree has only its terminal node as a leaf. -/
theorem fiveStageSupplyChain_history_unique
    (h : fiveStageSupplyChainTree.History) :
    h = fiveStageSupplyChainHistory := by
  apply Subtype.ext
  apply Fin.ext
  change h.1.val = 9
  have hbound : h.1.val < 10 := by
    exact h.1.isLt
  have hleaf : h.1.val = 9 := by
    by_contra hne
    have hlt : h.1.val < 9 := by omega
    let child : fiveStageSupplyChainTree.Node :=
      ⟨h.1.val + 1, by simp [fiveStageSupplyChainTree]; omega⟩
    have hchild_ne : child ≠ 0 := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [child] at hval
    have hparent : fiveStageSupplyChainTree.parent child = h.1 := by
      apply Fin.ext
      simp [child, fiveStageSupplyChainTree, fiveStageSupplyChainParent]
    exact h.2 child hchild_ne hparent
  exact hleaf

/-- Every prefix on the unique supply-chain history has a successful physical
run. -/
theorem fiveStageSupplyChain_runAt_successful
    (h : fiveStageSupplyChainTree.History)
    (t : fiveStageSupplyChainTree.Node)
    (_ht : fiveStageSupplyChainTree.MemHist t h) :
    ∃ state, fiveStageSupplyChainProgram.runAt h t = some state := by
  have hbound : t.val ≤ 9 := by
    have hlt := t.isLt
    simp [fiveStageSupplyChainTree] at hlt
    omega
  rw [fiveStageSupplyChain_history_unique h]
  rw [fiveStageSupplyChain_runAt_eq t.val hbound]
  have hsome : (fiveStageSupplyChainRun t.val).isSome := by
    interval_cases t.val <;> decide
  cases hrun : fiveStageSupplyChainRun t.val with
  | none => simp [hrun] at hsome
  | some state => exact ⟨state, rfl⟩

/-- Total physical ledger generated from the five-stage executable program.
Edge affordability is recovered from successful interpreter steps. -/
def fiveStageSupplyChainSolventProgram :
    SolventFinitePhysicalProgram fiveStageSupplyChainTree SupplyChainAgent
      SupplyChainGood SupplyChainOperation Unit :=
  SolventFinitePhysicalProgram.ofSuccessfulAt fiveStageSupplyChainProgram
    (by
      intro h t ht
      exact fiveStageSupplyChain_runAt_successful h t ht)

/-- The total state view reaches the same terminal retail service as the
original optional interpreter. -/
theorem fiveStageSupplyChainSolventProgram_retail_service
    (hterminal : fiveStageSupplyChainTree.MemHist 9
      fiveStageSupplyChainHistory) :
    (fiveStageSupplyChainSolventProgram.stateAt fiveStageSupplyChainHistory
      9 hterminal).services 4 = 1 := by
  have hrun := fiveStageSupplyChainSolventProgram.runAt_stateAt
    fiveStageSupplyChainHistory 9 hterminal
  change fiveStageSupplyChainProgram.runAt fiveStageSupplyChainHistory 9 = _ at hrun
  let terminal : fiveStageSupplyChainTree.Node :=
    ⟨9, by simp [fiveStageSupplyChainTree]⟩
  have hindex : (9 : fiveStageSupplyChainTree.Node) = terminal := by
    apply Fin.ext
    rfl
  have hrunNode : fiveStageSupplyChainProgram.runAt
      fiveStageSupplyChainHistory terminal =
      some (fiveStageSupplyChainSolventProgram.stateAt
        fiveStageSupplyChainHistory 9 hterminal) := by
    rw [← hindex]
    exact hrun
  have hrunEq := fiveStageSupplyChain_runAt_eq 9 (by omega)
  have hrunRun : fiveStageSupplyChainRun 9 =
      some (fiveStageSupplyChainSolventProgram.stateAt
        fiveStageSupplyChainHistory 9 hterminal) := by
    exact hrunEq.symm.trans hrunNode
  simpa [hrunRun] using fiveStageSupplyChain_retail_service

end Praxeology

end
