/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Program
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Finite choice compiler scale fixtures

The fixtures below keep two bilateral traders active while adding idle agents
to 10-, 25-, and 50-agent economies. Five repeated decision stages exercise
the branching program and tree flattener without multiplying tactic goals by
the number of agents. These are compiler fixtures, not preference or
doxastic models; those remain properties of an `ActionFrame` interpretation.
-/

@[expose] public section

namespace Praxeology

def scaleOffer {n : ℕ} : EconomyAction (Fin (n + 2)) (Fin 2) Empty :=
  .offer 0 1 1 0 1 1

def scaleAccept {n : ℕ} : EconomyAction (Fin (n + 2)) (Fin 2) Empty :=
  .accept 1 0 1 0 1 1

def scaleMenu {n : ℕ} (i : Fin (n + 2)) :
    Finset (EconomyAction (Fin (n + 2)) (Fin 2) Empty) :=
  if i = 0 then {.idle, scaleOffer} else
    if i = 1 then {.idle, scaleAccept} else {.idle}

theorem scaleMenu_eq_idle {n : ℕ} (i : Fin (n + 2))
    (h0 : i ≠ 0) (h1 : i ≠ 1) : scaleMenu i = {EconomyAction.idle} := by
  simp [scaleMenu, h0, h1]

/-- A finite economy stage with two purposeful trade choices and any number
of additional agents whose only menu choice is inertia. -/
def scaleChoiceStage (n : ℕ) : FiniteChoiceStage (Fin (n + 2)) (Fin 2) Empty where
  menu := scaleMenu
  idle_mem := by
    intro i
    by_cases h0 : i = 0
    · simp [scaleMenu, h0]
    · by_cases h1 : i = 1
      · simp [scaleMenu, h1]
      · simp [scaleMenu, h0, h1]
  activeAgents := {0, 1}
  active_iff := by
    intro i
    constructor
    · intro hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · subst i
        exact ⟨scaleOffer (n := n), by simp [scaleMenu, scaleOffer], by
          simp [scaleOffer]⟩
      · subst i
        exact ⟨scaleAccept (n := n), by simp [scaleMenu, scaleAccept], by
          simp [scaleAccept]⟩
    · rintro ⟨α, hα, hne⟩
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases h1 : i = 1
        · simp [h1]
        · have hα' : α = EconomyAction.idle := by
            change α ∈ scaleMenu i at hα
            rw [scaleMenu_eq_idle i h0 h1] at hα
            simpa using hα
          exact (hne hα').elim
  maxActiveAgents := 2
  activity_bound := by simp
  menu_wellFormed := by
    intro i α hα
    by_cases h0 : i = 0
    · subst i
      change α ∈ ({EconomyAction.idle, scaleOffer (n := n)} :
        Finset (EconomyAction (Fin (n + 2)) (Fin 2) Empty)) at hα
      simp only [Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with rfl | rfl <;>
        simp [EconomyAction.WellFormed, scaleOffer]
    · by_cases h1 : i = 1
      · subst i
        change α ∈ ({EconomyAction.idle, scaleAccept (n := n)} :
          Finset (EconomyAction (Fin (n + 2)) (Fin 2) Empty)) at hα
        simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with rfl | rfl <;>
          simp [EconomyAction.WellFormed, scaleAccept]
      · have hα' : α = EconomyAction.idle := by
          simpa [scaleMenu, h0, h1] using hα
        subst α
        simp [EconomyAction.WellFormed]

/-- A bilateral profile is present in every scale stage. -/
def scaleBilateralProfile {n : ℕ} :
    (scaleChoiceStage n).Profile :=
  ⟨fun i => if i = 0 then scaleOffer (n := n) else
      if i = 1 then scaleAccept (n := n) else .idle,
    by
      intro i
      by_cases h0 : i = 0
      · subst i
        simp [scaleChoiceStage, scaleMenu, scaleOffer]
      · by_cases h1 : i = 1
        · subst i
          simp [scaleChoiceStage, scaleMenu, scaleAccept, h0]
        · simp [scaleChoiceStage, scaleMenu, h0, h1]⟩

theorem scaleBilateralProfile_is_listed {n : ℕ} :
    scaleBilateralProfile (n := n) ∈ (scaleChoiceStage n).profiles :=
  (scaleChoiceStage n).mem_profiles (scaleBilateralProfile (n := n))

@[simp] theorem scaleBilateralProfile_offer {n : ℕ} :
    (scaleBilateralProfile (n := n)).1 (0 : Fin (n + 2)) = scaleOffer (n := n) := by
  simp [scaleBilateralProfile]

@[simp] theorem scaleBilateralProfile_accept {n : ℕ} :
    (scaleBilateralProfile (n := n)).1 (1 : Fin (n + 2)) = scaleAccept (n := n) := by
  simp [scaleBilateralProfile]

/-- Initial inventory for the scale fixture: agent 0 owns one unit of good 0,
agent 1 owns one unit of money, and every other coordinate is zero. -/
def scaleInitialStock {n : ℕ} (i : Fin (n + 2)) (m : Fin 2) : ℕ :=
  if i = 0 then if m = 0 then 1 else 0 else
    if i = 1 then if m = 1 then 1 else 0 else 0

/-- The menu choices are affordable from the same pre-transition inventory;
the buyer cannot use the incoming good to finance their payment. -/
def scalePhysicalStage (n : ℕ) :
    FinitePhysicalChoiceStage (Fin (n + 2)) (Fin 2) Empty Unit where
  choices := scaleChoiceStage n
  operations := ⟨fun op _ => Empty.elim op, fun op _ => Empty.elim op,
    fun op _ => Empty.elim op⟩
  before := PhysicalState.zeroServices scaleInitialStock
  menu_affordable := by
    intro actor α hα m
    by_cases h0 : actor = 0
    · subst actor
      change α ∈ ({EconomyAction.idle, scaleOffer (n := n)} :
        Finset (EconomyAction (Fin (n + 2)) (Fin 2) Empty)) at hα
      simp only [Finset.mem_insert, Finset.mem_singleton] at hα
      rcases hα with hα | hα
      · subst α
        simp [rawActionUse, PhysicalState.zeroServices, scaleInitialStock]
      · subst α
        simp [rawActionUse, scaleOffer, PhysicalState.zeroServices, scaleInitialStock]
    · by_cases h1 : actor = 1
      · subst actor
        change α ∈ ({EconomyAction.idle, scaleAccept (n := n)} :
          Finset (EconomyAction (Fin (n + 2)) (Fin 2) Empty)) at hα
        simp only [Finset.mem_insert, Finset.mem_singleton] at hα
        rcases hα with hα | hα
        · subst α
          simp [rawActionUse, PhysicalState.zeroServices, scaleInitialStock]
        · subst α
          simp [rawActionUse, scaleAccept, PhysicalState.zeroServices, scaleInitialStock]
      · have hα' : α = EconomyAction.idle := by
          change α ∈ scaleMenu actor at hα
          rw [scaleMenu_eq_idle actor h0 h1] at hα
          simpa using hα
        subst α
        simp [rawActionUse, PhysicalState.zeroServices, scaleInitialStock]

/-- The selected bilateral profile is solvent and satisfies exact inventory
accounting in every 10-, 25-, or 50-agent scale fixture. -/
theorem scalePhysicalStage_bilateral_balance {n : ℕ} (m : Fin 2)
    (i : Fin (n + 2)) :
    ((scalePhysicalStage n).advance scaleBilateralProfile).stock i m +
        effectiveUse (scalePhysicalStage n).operations
          scaleBilateralProfile.1 i m =
      (scalePhysicalStage n).before.stock i m +
        effectiveYield (scalePhysicalStage n).operations
          scaleBilateralProfile.1 i m := by
  exact (scalePhysicalStage n).advance_balance scaleBilateralProfile i m

/-- The matched exchange transfers the unit of good to the buyer. -/
theorem scalePhysicalStage_buyer_receives_good {n : ℕ} :
    ((scalePhysicalStage n).advance scaleBilateralProfile).stock
      (1 : Fin (n + 2)) (0 : Fin 2) = 1 := by
  have h := scalePhysicalStage_bilateral_balance (n := n) (0 : Fin 2)
    (1 : Fin (n + 2))
  simpa [scalePhysicalStage, scaleChoiceStage, scaleBilateralProfile,
    scaleAccept, scaleOffer, PhysicalState.zeroServices, scaleInitialStock,
    effectiveUse, effectiveYield] using h

/-- The matched exchange transfers the unit of money to the seller. -/
theorem scalePhysicalStage_seller_receives_money {n : ℕ} :
    ((scalePhysicalStage n).advance scaleBilateralProfile).stock
      (0 : Fin (n + 2)) (1 : Fin 2) = 1 := by
  have h := scalePhysicalStage_bilateral_balance (n := n) (1 : Fin 2)
    (0 : Fin (n + 2))
  simpa [scalePhysicalStage, scaleChoiceStage, scaleBilateralProfile,
    scaleAccept, scaleOffer, PhysicalState.zeroServices, scaleInitialStock,
    effectiveUse, effectiveYield] using h

/-- Repeat a simultaneous bilateral choice for `fuel` stages. Every complete
menu profile continues, so the flattened scenario exposes all branches at
each stage instead of retaining only a hand-picked path. -/
def scaleProgram (n : ℕ) :
    (fuel : ℕ) → FiniteEconomyProgram Unit (Fin (n + 2)) (Fin 2) Empty fuel ()
  | 0 => .halt
  | fuel + 1 => .decision (scaleChoiceStage n) (fun _ => ())
      (fun _ => scaleProgram n fuel)

def scaleProgram10 := scaleProgram 8 5
def scaleProgram25 := scaleProgram 23 5
def scaleProgram50 := scaleProgram 48 5

theorem scaleProgram10_tree_nodeCount :
    (compileFiniteProgramTree 5 scaleProgram10).extraNodes + 1 =
      FiniteEconomyProgram.nodeCount 5 () scaleProgram10 :=
  compileFiniteProgramTree_nodeCount 5 () scaleProgram10

theorem scaleProgram25_tree_nodeCount :
    (compileFiniteProgramTree 5 scaleProgram25).extraNodes + 1 =
      FiniteEconomyProgram.nodeCount 5 () scaleProgram25 :=
  compileFiniteProgramTree_nodeCount 5 () scaleProgram25

theorem scaleProgram50_tree_nodeCount :
    (compileFiniteProgramTree 5 scaleProgram50).extraNodes + 1 =
      FiniteEconomyProgram.nodeCount 5 () scaleProgram50 :=
  compileFiniteProgramTree_nodeCount 5 () scaleProgram50

/-- The menu product has four profiles at each scale because only the two
designated traders have a non-idle choice. -/
theorem scaleChoiceStage_profiles_card (n : ℕ) :
    (scaleChoiceStage n).profiles.card = 4 := by
  classical
  let S := scaleChoiceStage n
  have hinj : Set.InjOn S.profileOf
      ↑((Finset.univ.pi S.menu).attach) := by
    intro f hf g hg hfg
    apply Subtype.ext
    funext i hi
    have hval : (S.profileOf f).1 i = (S.profileOf g).1 i :=
      congrFun (congrArg Subtype.val hfg) i
    simpa [FiniteChoiceStage.profileOf] using hval
  rw [FiniteChoiceStage.profiles,
    Finset.card_image_iff.mpr hinj, Finset.card_attach, Finset.card_pi]
  have hcard0 : (S.menu (0 : Fin (n + 2))).card = 2 := by
    simp [S, scaleChoiceStage, scaleMenu, scaleOffer]
  have hcard1 : (S.menu (1 : Fin (n + 2))).card = 2 := by
    simp [S, scaleChoiceStage, scaleMenu, scaleAccept]
  have h1mem : (1 : Fin (n + 2)) ∈ Finset.univ.erase 0 := by simp
  have hrest : ∀ i ∈ (Finset.univ.erase 0).erase 1, (S.menu i).card = 1 := by
    intro i hi
    have hne1 : i ≠ 1 := (Finset.mem_erase.mp hi).1
    have hi0 : i ∈ Finset.univ.erase 0 := (Finset.mem_erase.mp hi).2
    have hne0 : i ≠ 0 := (Finset.mem_erase.mp hi0).1
    simp [S, scaleChoiceStage, scaleMenu, hne0, hne1]
  have h0mem : (0 : Fin (n + 2)) ∈ Finset.univ := Finset.mem_univ _
  have h0not : (0 : Fin (n + 2)) ∉ Finset.univ.erase 0 := by
    intro hi
    exact (Finset.mem_erase.mp hi).1 rfl
  have h1not : (1 : Fin (n + 2)) ∉ (Finset.univ.erase 0).erase 1 := by
    intro hi
    exact (Finset.mem_erase.mp hi).1 rfl
  calc
    ∏ i ∈ Finset.univ, (S.menu i).card =
        ∏ i ∈ insert 0 (Finset.univ.erase 0), (S.menu i).card := by
          rw [Finset.insert_erase h0mem]
    _ = (S.menu 0).card * ∏ i ∈ Finset.univ.erase 0, (S.menu i).card :=
      Finset.prod_insert h0not
    _ = (S.menu 0).card *
        ∏ i ∈ insert 1 ((Finset.univ.erase 0).erase 1), (S.menu i).card := by
          rw [Finset.insert_erase h1mem]
    _ = (S.menu 0).card *
        ((S.menu 1).card * ∏ i ∈ (Finset.univ.erase 0).erase 1,
          (S.menu i).card) := by rw [Finset.prod_insert h1not]
    _ = 4 := by rw [hcard0, hcard1, Finset.prod_eq_one hrest]; norm_num

theorem scaleProgram10_moment_count :
    FiniteEconomyProgram.nodeCount 5 () scaleProgram10 = 1365 := by
  simp [scaleProgram10, scaleProgram, FiniteEconomyProgram.nodeCount,
    scaleChoiceStage_profiles_card]

theorem scaleProgram25_moment_count :
    FiniteEconomyProgram.nodeCount 5 () scaleProgram25 = 1365 := by
  simp [scaleProgram25, scaleProgram, FiniteEconomyProgram.nodeCount,
    scaleChoiceStage_profiles_card]

theorem scaleProgram50_moment_count :
    FiniteEconomyProgram.nodeCount 5 () scaleProgram50 = 1365 := by
  simp [scaleProgram50, scaleProgram, FiniteEconomyProgram.nodeCount,
    scaleChoiceStage_profiles_card]

theorem scaleProgram10_history_count :
    FiniteEconomyProgram.historyCount 5 () scaleProgram10 = 1024 := by
  simp [scaleProgram10, scaleProgram, FiniteEconomyProgram.historyCount,
    scaleChoiceStage_profiles_card]

theorem scaleProgram25_history_count :
    FiniteEconomyProgram.historyCount 5 () scaleProgram25 = 1024 := by
  simp [scaleProgram25, scaleProgram, FiniteEconomyProgram.historyCount,
    scaleChoiceStage_profiles_card]

theorem scaleProgram50_history_count :
    FiniteEconomyProgram.historyCount 5 () scaleProgram50 = 1024 := by
  simp [scaleProgram50, scaleProgram, FiniteEconomyProgram.historyCount,
    scaleChoiceStage_profiles_card]

end Praxeology

end
