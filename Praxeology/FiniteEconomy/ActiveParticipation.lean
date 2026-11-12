/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

import Mathlib.Tactic.IntervalCases

public import Praxeology.FiniteEconomy.Compiler

/-!
# Active production schedules for 5C-agent chains

Each cohort has five producers and a nine-transition schedule: five productive
actions alternating with four matched exchanges. This file builds the schedule
from arithmetic indices rather than enumerating constructors or agents.
-/

@[expose] public section

namespace Praxeology

inductive ParticipationOperation where
  | mine
  | refine
  | fabricate
  | assemble
  | retail
  deriving DecidableEq

instance : Fintype ParticipationOperation where
  elems := {.mine, .refine, .fabricate, .assemble, .retail}
  complete := by
    intro op
    cases op <;> simp

abbrev ParticipationMeans := Fin 6

def participationRaw : ParticipationMeans := 0
def participationOre : ParticipationMeans := 1
def participationComponent : ParticipationMeans := 2
def participationPart : ParticipationMeans := 3
def participationFinalGood : ParticipationMeans := 4
def participationMoney : ParticipationMeans := 5

/-- The agent in cohort `g` assigned to productive slot `slot`. -/
def participationAgent (C g slot : Nat) (hg : g < C) (hslot : slot < 5) :
    Fin (5 * C) :=
  ⟨5 * g + slot, by
    have hmul := Nat.mul_lt_mul_of_pos_left hg (by decide : 0 < 5)
    omega⟩

@[simp] theorem participationAgent_eq_iff {C g s t : Nat}
    (hg : g < C) (hs : s < 5) (ht : t < 5) :
    participationAgent C g s hg hs = participationAgent C g t hg ht ↔ s = t := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    change 5 * g + s = 5 * g + t at hval
    omega
  · intro h
    subst t
    rfl

/-- One scheduled transition profile. Moment numbers are grouped into blocks
of nine; the final moment of the compiled linear tree is idle. -/
def participationAction {C : Nat} (moment : Nat)
    (actor : Fin (5 * C)) :
    EconomyAction (Fin (5 * C)) ParticipationMeans ParticipationOperation :=
  if hmoment : moment < 9 * C then
    let cohort := moment / 9
    have hcohort : cohort < C := by omega
    let p0 := participationAgent C cohort 0 hcohort (by omega)
    let p1 := participationAgent C cohort 1 hcohort (by omega)
    let p2 := participationAgent C cohort 2 hcohort (by omega)
    let p3 := participationAgent C cohort 3 hcohort (by omega)
    let p4 := participationAgent C cohort 4 hcohort (by omega)
    match moment % 9 with
    | 0 => if actor = p0 then .operate .mine else .idle
    | 1 => if actor = p0 then .offer p0 p1 1 participationOre 1 participationMoney
        else if actor = p1 then .accept p1 p0 1 participationOre 1 participationMoney
        else .idle
    | 2 => if actor = p1 then .operate .refine else .idle
    | 3 => if actor = p1 then
          .offer p1 p2 1 participationComponent 1 participationMoney
        else if actor = p2 then
          .accept p2 p1 1 participationComponent 1 participationMoney
        else .idle
    | 4 => if actor = p2 then .operate .fabricate else .idle
    | 5 => if actor = p2 then
          .offer p2 p3 1 participationPart 1 participationMoney
        else if actor = p3 then
          .accept p3 p2 1 participationPart 1 participationMoney
        else .idle
    | 6 => if actor = p3 then .operate .assemble else .idle
    | 7 => if actor = p3 then
          .offer p3 p4 1 participationFinalGood 1 participationMoney
        else if actor = p4 then
          .accept p4 p3 1 participationFinalGood 1 participationMoney
        else .idle
    | 8 => if actor = p4 then .operate .retail else .idle
    | _ => .idle
  else .idle

theorem participationAction_wellFormed {C : Nat} (moment : Nat)
    (actor : Fin (5 * C)) :
    EconomyAction.WellFormed actor (participationAction moment actor) := by
  by_cases hmoment : moment < 9 * C
  · have hphase : moment % 9 < 9 := Nat.mod_lt _ (by omega)
    interval_cases phase : moment % 9 <;>
      simp [participationAction, hmoment, phase] <;>
      split_ifs <;>
      simp_all [EconomyAction.WellFormed, participationAgent_eq_iff]
  · simp [participationAction, hmoment, EconomyAction.WellFormed]

/-- The complete profile enacted at one scheduled moment. -/
def participationProfile {C : Nat} (moment : Nat) :
    ActionProfile (Agent := Fin (5 * C)) (Means := ParticipationMeans)
      (Operation := ParticipationOperation) :=
  fun actor => participationAction moment actor

/-- Exactly the agents whose selected action is non-idle. -/
def participationActiveAgents {C : Nat} (moment : Nat) : Finset (Fin (5 * C)) :=
  Finset.univ.filter (fun actor =>
    participationProfile moment actor ≠ EconomyAction.idle)

/-- A compiler menu for one moment: active agents retain the idle alternative,
and every inactive agent has only that alternative. -/
def participationChoiceStage {C : Nat} (moment : Nat) :
    FiniteChoiceStage (Fin (5 * C)) ParticipationMeans ParticipationOperation :=
  FiniteChoiceStage.ofProfile (participationProfile moment)
    (participationActiveAgents moment)
    (by
      intro actor hactor
      exact (Finset.mem_filter.mp hactor).2)
    (by
      intro actor
      exact participationAction_wellFormed moment actor)

/-- Productive action assigned to each of a cohort's five agents. -/
def participationOperationOfSlot : Fin 5 → ParticipationOperation
  | 0 => .mine
  | 1 => .refine
  | 2 => .fabricate
  | 3 => .assemble
  | 4 => .retail

theorem participationAction_production {C cohort : Nat}
    (hcohort : cohort < C) (slot : Fin 5) :
    participationAction (9 * cohort + 2 * slot.val)
      (participationAgent C cohort slot.val hcohort slot.isLt) =
        .operate (participationOperationOfSlot slot) := by
  fin_cases slot
  · have hmoment : 9 * cohort < 9 * C := by omega
    have hgroup : (9 * cohort) / 9 = cohort := by omega
    simp [participationAction, hmoment, hgroup, participationOperationOfSlot]
  · have hmoment : 9 * cohort + 2 < 9 * C := by omega
    have hgroup : (9 * cohort + 2) / 9 = cohort := by omega
    simp [participationAction, hmoment, hgroup, participationOperationOfSlot]
  · have hmoment : 9 * cohort + 4 < 9 * C := by omega
    have hgroup : (9 * cohort + 4) / 9 = cohort := by omega
    simp [participationAction, hmoment, hgroup, participationOperationOfSlot]
  · have hmoment : 9 * cohort + 6 < 9 * C := by omega
    have hgroup : (9 * cohort + 6) / 9 = cohort := by omega
    simp [participationAction, hmoment, hgroup, participationOperationOfSlot]
  · have hmoment : 9 * cohort + 8 < 9 * C := by omega
    have hgroup : (9 * cohort + 8) / 9 = cohort := by omega
    simp [participationAction, hmoment, hgroup, participationOperationOfSlot]

/-- Every agent in a `5C`-agent chain is assigned one productive operation at
its unique even-numbered production moment. -/
theorem participation_agent_has_production {C : Nat} (actor : Fin (5 * C)) :
    ∃ moment : Nat, moment < 9 * C ∧ ∃ op,
      participationAction moment actor = .operate op := by
  let cohort := actor.val / 5
  let slot : Fin 5 := ⟨actor.val % 5, Nat.mod_lt _ (by omega)⟩
  have hcohort : cohort < C := by
    dsimp [cohort]
    have hlt := actor.isLt
    omega
  have hdecomp : actor.val = 5 * cohort + slot.val := by
    dsimp [cohort, slot]
    omega
  let moment := 9 * cohort + 2 * slot.val
  have hmoment : moment < 9 * C := by
    dsimp [moment]
    have hslot : slot.val < 5 := slot.isLt
    omega
  have hgroup : moment / 9 = cohort := by
    dsimp [moment]
    have hslot : slot.val < 5 := slot.isLt
    omega
  have hlocal : moment % 9 = 2 * slot.val := by
    dsimp [moment]
    have hslot : slot.val < 5 := slot.isLt
    omega
  have hactor : actor =
      participationAgent C cohort slot.val hcohort slot.isLt := by
    apply Fin.ext
    exact hdecomp
  refine ⟨moment, hmoment, participationOperationOfSlot slot, ?_⟩
  change participationAction (9 * cohort + 2 * slot.val) actor = _
  rw [hactor]
  exact participationAction_production hcohort slot

end Praxeology

end
