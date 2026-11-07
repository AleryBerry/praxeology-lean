/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith



/-!
# Human Action: Teleological Choice and Opportunity Cost

Foundational formalization of purposeful human action, felt unease, ordinal preference rankings,
demonstrated preference, and opportunity cost sets.
-/

@[expose] public section

namespace Praxeology


def findSatisfying? {α : Type} (p : α → Prop) [DecidablePred p] :
    List α → Option α
  | [] => none
  | a :: rest => if p a then some a else findSatisfying? p rest

/-- If a list member satisfies `p`, the search returns some list member. -/
theorem findSatisfying?_complete {α : Type} (p : α → Prop) [DecidablePred p]
    (xs : List α) (h : ∃ a, List.Mem a xs ∧ p a) :
    ∃ a, findSatisfying? p xs = some a := by
  induction xs with
  | nil =>
      rcases h with ⟨a, ha, _⟩
      cases ha
  | cons a rest ih =>
      by_cases ha : p a
      · have hfound : findSatisfying? p (a :: rest) = some a := by
          change (if p a then some a else findSatisfying? p rest) = some a
          simp [ha]
        exact ⟨a, hfound⟩
      · rcases h with ⟨x, hx, hpx⟩
        cases hx with
        | head =>
          exact (ha hpx).elim
        | tail _ htail =>
          rcases ih ⟨x, htail, hpx⟩ with ⟨w, hw⟩
          have hfound : findSatisfying? p (a :: rest) = some w := by
            change (if p a then some a else findSatisfying? p rest) = some w
            simp [ha, hw]
          exact ⟨w, hfound⟩

/-- A returned value satisfies the predicate. -/
theorem findSatisfying?_sound {α : Type} (p : α → Prop) [DecidablePred p]
    (xs : List α) (a : α) (h : findSatisfying? p xs = some a) : p a := by
  induction xs with
  | nil =>
      simp only [findSatisfying?] at h
      cases h
  | cons x rest ih =>
      by_cases hx : p x
      · have h' : some x = some a := by
          simpa only [findSatisfying?, ite_true, hx] using h
        have hxa : x = a := Option.some.inj h'
        subst a
        exact hx
      · have htail : findSatisfying? p rest = some a := by
          simpa only [findSatisfying?, ite_false, hx] using h
        exact ih htail

namespace ActionFrame


def findExecutionBranch? (F : ActionFrame) (i : F.Agent) (t : F.Moment)
    (α : F.Action) (candidates : List F.History)
    (decideExecution : (h' : F.History) → Decidable (@Exec F i t α h')) :
    Option F.History :=
  @findSatisfying? F.History (fun h' => @Exec F i t α h') decideExecution candidates

/-- Every branch returned by `findExecutionBranch?` satisfies `Exec`. -/
theorem findExecutionBranch?_sound (F : ActionFrame) (i : F.Agent) (t : F.Moment)
    (α : F.Action) (candidates : List F.History)
    (decideExecution : (h' : F.History) → Decidable (@Exec F i t α h'))
    (h' : F.History)
    (hfind : F.findExecutionBranch? i t α candidates decideExecution = some h') :
    @Exec F i t α h' := by
  exact @findSatisfying?_sound F.History (fun h' => @Exec F i t α h')
    decideExecution candidates h' hfind

/-- A candidate satisfying `Exec` is returned by `findExecutionBranch?`. -/
theorem findExecutionBranch?_complete (F : ActionFrame) (i : F.Agent) (t : F.Moment)
    (α : F.Action) (candidates : List F.History)
    (decideExecution : (h' : F.History) → Decidable (@Exec F i t α h'))
    (hw : ∃ h', List.Mem h' candidates ∧ @Exec F i t α h') :
    ∃ h', F.findExecutionBranch? i t α candidates decideExecution = some h' ∧
      @Exec F i t α h' := by
  rcases @findSatisfying?_complete F.History (fun h' => @Exec F i t α h')
      decideExecution candidates hw with ⟨h', hfind⟩
  exact ⟨h', hfind, F.findExecutionBranch?_sound i t α candidates
    decideExecution h' hfind⟩

/-- Decidable membership in the feasible menu. -/
@[instance_reducible]
def feasibleActionDecider (F : ActionFrame) (i : F.Agent) (t : F.Moment)
    (h : F.History) : DecidablePred (fun α => α ∈ F.A_feas i t h) := by
  letI : DecidableEq F.Action := F.instDecidableEqAction
  exact fun α => inferInstance

/-- Search a list for an action in the feasible menu. -/
def findFeasible? (F : ActionFrame) (i : F.Agent) (t : F.Moment) (h : F.History)
    (candidates : List F.Action) : Option F.Action :=
  @findSatisfying? F.Action (fun α => α ∈ F.A_feas i t h)
    (F.feasibleActionDecider i t h) candidates

/-- Every action returned by `findFeasible?` is in the feasible menu. -/
theorem findFeasible?_sound (F : ActionFrame) (i : F.Agent) (t : F.Moment) (h : F.History)
    (candidates : List F.Action) (α : F.Action)
    (hfind : F.findFeasible? i t h candidates = some α) : α ∈ F.A_feas i t h :=
  @findSatisfying?_sound F.Action (fun α => α ∈ F.A_feas i t h)
    (F.feasibleActionDecider i t h) candidates α hfind

/-- A feasible candidate is returned by `findFeasible?`. -/
theorem findFeasible?_complete (F : ActionFrame) (i : F.Agent) (t : F.Moment) (h : F.History)
    (candidates : List F.Action)
    (hw : ∃ α, List.Mem α candidates ∧ α ∈ F.A_feas i t h) :
    ∃ α, F.findFeasible? i t h candidates = some α ∧ α ∈ F.A_feas i t h := by
  rcases @findSatisfying?_complete F.Action (fun α => α ∈ F.A_feas i t h)
      (F.feasibleActionDecider i t h) candidates hw with ⟨α, hfind⟩
  exact ⟨α, hfind, F.findFeasible?_sound i t h candidates α hfind⟩


def findPlausible? (F : ActionFrame) (i : F.Agent) (t : F.Moment)
    (candidates : List F.History)
    (decidePlausible : (h : F.History) → Decidable (h ∈ F.MinPlausible i t)) :
    Option F.History :=
  @findSatisfying? F.History (fun h => h ∈ F.MinPlausible i t)
    decidePlausible candidates

/-- Every history returned by `findPlausible?` is minimally plausible. -/
theorem findPlausible?_sound (F : ActionFrame) (i : F.Agent) (t : F.Moment)
    (candidates : List F.History)
    (decidePlausible : (h : F.History) → Decidable (h ∈ F.MinPlausible i t))
    (h' : F.History) (hfind : F.findPlausible? i t candidates decidePlausible = some h') :
    h' ∈ F.MinPlausible i t :=
  @findSatisfying?_sound F.History (fun h => h ∈ F.MinPlausible i t)
    decidePlausible candidates h' hfind

/-- A minimally plausible candidate is returned by `findPlausible?`. -/
theorem findPlausible?_complete (F : ActionFrame) (i : F.Agent) (t : F.Moment)
    (candidates : List F.History)
    (decidePlausible : (h : F.History) → Decidable (h ∈ F.MinPlausible i t))
    (hw : ∃ h', List.Mem h' candidates ∧ h' ∈ F.MinPlausible i t) :
    ∃ h', F.findPlausible? i t candidates decidePlausible = some h' ∧
      h' ∈ F.MinPlausible i t := by
  rcases @findSatisfying?_complete F.History (fun h => h ∈ F.MinPlausible i t)
      decidePlausible candidates hw with ⟨h', hfind⟩
  exact ⟨h', hfind, F.findPlausible?_sound i t candidates decidePlausible h' hfind⟩

end ActionFrame

section ActionFoundations

variable [F : ActionFrame]


-- 1. Endowments and Requirements


/-- Minimum units of each means required for an end. -/
abbrev requirement : Ends → Means → ℕ :=
  F.requirement

/-- Means `m` is scarce if its endowment is below the requirement of some end. -/
def Scarce (i : Agent) (t : Moment) (h : History) (m : Means) : Prop :=
  ∃ e : Ends, endowment i t h m < requirement e m


-- 2. Ends of Actions and Ordinal Preference


/-- End associated with each action. -/
abbrev End_of : Agent → Action → Moment → History → Ends :=
  F.End_of

/-- Preference relation over ends for agent `i` at `⟨t, h⟩`. -/
abbrev Preference (i : Agent) (t : Moment) (h : History) : Ends → Ends → Prop :=
  F.Preference i t h

/-- Preference is asymmetric: if e₁ is strictly preferred to e₂, e₂ is not preferred to e₁. -/
theorem pref_asymm (i : Agent) (t : Moment) (h : History) {e1 e2 : Ends} :
    Preference i t h e1 e2 → ¬(Preference i t h e2 e1) :=
  F.pref_asymm i t h

/-- Preference is strictly irreflexive. -/
theorem pref_irrefl (i : Agent) (t : Moment) (h : History) (e : Ends) :
    ¬(Preference i t h e e) :=
  fun h_refl => pref_asymm i t h h_refl h_refl


-- 3. Purposeful Action


/-- The single purposeful-choice condition parameterized by the decision
maker's intended-end appraisal. Feasibility and execution remain actual
ActionFrame facts; only the two preference comparisons use `intendedEnd`. -/
def PurposefulActWithEnd
    (intendedEnd : Agent → Action → Moment → History → Ends)
    (R : Ends → Ends → Prop) (i : Agent) (t : Moment) (h : History)
    (α_star : Action) : Prop :=
  α_star ∈ A_feas i t h ∧
  Exec i t α_star h ∧
  (α_star = α₀ ∨ R (intendedEnd i α_star t h) (intendedEnd i α₀ t h)) ∧
  ∀ β ∈ A_feas i t h,
    ¬ R (intendedEnd i β t h) (intendedEnd i α_star t h)

def PurposefulActUnder (R : Ends → Ends → Prop) (i : Agent) (t : Moment) (h : History)
    (α_star : Action) : Prop :=
  PurposefulActWithEnd End_of R i t h α_star

/-- Purposeful action under the frame's preference relation. -/
abbrev PurposefulAct (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  PurposefulActUnder (Preference i t h) i t h α_star

/-- Resources alone suffice when combined with contemplation to characterize
decision feasibility. -/
def ResourceFeasible (i : Agent) (t : Moment) (h : History) (α : Action) : Prop :=
  ∀ m, F.use_means α m ≤ F.omega i t h m

theorem feasible_iff_contemplated_and_resource_feasible
    (i : Agent) (t : Moment) (h : History) (α : Action) :
    α ∈ A_feas i t h ↔ α ∈ A_cont i t h ∧ ResourceFeasible i t h α :=
  F.A_feas_coupling i t h α

/-- If the enacted choice is purposeful and `target` is strictly preferred to
every other feasible action, the enacted action must be `target`. -/
theorem enacted_eq_of_strictly_best
    (i : Agent) (t : Moment) (h : History) (target : Action)
    (hresponse : PurposefulAct i t h (F.enacted i t h))
    (htarget : target ∈ A_feas i t h)
    (hbetter : ∀ β ∈ A_feas i t h, β ≠ target →
      Preference i t h (End_of i target t h) (End_of i β t h)) :
    F.enacted i t h = target ∧ PurposefulAct i t h target := by
  have hchosen : F.enacted i t h ∈ A_feas i t h :=
    F.enacted_in_A_feas i t h hresponse.2.1.1
  have hEq : F.enacted i t h = target := by
    by_contra hne
    have hstrict := hbetter (F.enacted i t h) hchosen hne
    exact hresponse.2.2.2 target htarget hstrict
  constructor
  · exact hEq
  · simpa [hEq] using hresponse


structure PurposefulActionSearchData (i : Agent) (t : Moment) (h : History) where
  candidates : List Action
  candidates_complete : ∀ α, PurposefulAct i t h α → List.Mem α candidates
  decide_purposeful : (α : Action) → Decidable (PurposefulAct i t h α)

/-- First candidate satisfying `PurposefulAct`. -/
def PurposefulActionSearchData.first {i : Agent} {t : Moment} {h : History}
    (S : PurposefulActionSearchData i t h) :
    Option Action :=
  @findSatisfying? Action (PurposefulAct i t h) S.decide_purposeful S.candidates

/-- If purposeful action exists, `first` returns a purposeful action. -/
theorem PurposefulActionSearchData.first_complete {i : Agent} {t : Moment} {h : History}
    (S : PurposefulActionSearchData i t h)
    (h_exists : ∃ α, PurposefulAct i t h α) :
    ∃ α, S.first = some α ∧ PurposefulAct i t h α := by
  rcases h_exists with ⟨α, hα⟩
  have hmem := S.candidates_complete α hα
  rcases @findSatisfying?_complete Action (PurposefulAct i t h)
      S.decide_purposeful S.candidates ⟨α, hmem, hα⟩ with ⟨found, hfound⟩
  exact ⟨found, hfound, @findSatisfying?_sound Action (PurposefulAct i t h)
    S.decide_purposeful S.candidates found hfound⟩


def DemonstratedPref (i : Agent) (t : Moment) (h : History) (α_star β : Action) : Prop :=
  PurposefulAct i t h α_star ∧ β ∈ (A_feas i t h).erase α_star


def DemonstratedPrefEnd (i : Agent) (t : Moment) (h : History) (e1 e2 : Ends) : Prop :=
  e1 ≠ e2 ∧ ∃ α_star β, PurposefulAct i t h α_star ∧ β ∈ A_feas i t h ∧
    End_of i α_star t h = e1 ∧ End_of i β t h = e2

/-- Demonstrated preference rules out preference for the foregone end. -/
theorem demonstrated_pref_end_undominated (i : Agent) (t : Moment) (h : History) (e1 e2 : Ends)
    (h_dem : DemonstratedPrefEnd i t h e1 e2) :
    ¬ Preference i t h e2 e1 := by
  rcases h_dem with ⟨_, α_star, β, h_act, h_feas, h_end1, h_end2⟩
  have h_undom := h_act.2.2.2 β h_feas
  rw [h_end1, h_end2] at h_undom
  exact h_undom

/-- Under comparability, demonstrated preference implies preference for `e1` over `e2`. -/
theorem demonstrated_pref_grounding (i : Agent) (t : Moment) (h : History) (e1 e2 : Ends)
    (h_dem : DemonstratedPrefEnd i t h e1 e2)
    (h_comp : e1 ≠ e2 → Preference i t h e1 e2 ∨ Preference i t h e2 e1) :
    Preference i t h e1 e2 := by
  have h_undom := demonstrated_pref_end_undominated i t h e1 e2 h_dem
  rcases h_comp h_dem.1 with h12 | h21
  · exact h12
  · exact False.elim (h_undom h21)


theorem purposeful_act_choice_cell_pullback (i : Agent) (t : Moment) (h : History) (h_in : t ∈ h)
    (α_star : Action) :
    PurposefulAct i t h α_star ↔
    (∃ (cell : Set History),
      cell ⊆ {h' | t ∈ h'} ∧
      h ∈ cell ∧
      (∀ h' ∈ cell, enacted i t h' = enacted i t h) ∧
      PurposefulAct i t h α_star) := by
  constructor
  · intro h_purp
    refine ⟨{h' | t ∈ h' ∧ enacted i t h' = enacted i t h}, ?_, ⟨h_in, rfl⟩,
      fun _ hh' => hh'.2, h_purp⟩
    intro h' hh'
    exact hh'.1
  · rintro ⟨_, _, _, _, h_purp⟩
    exact h_purp


theorem purposeful_act_choice_cell_invariant (i : Agent) (t : Moment) (h1 h2 : History)
    (h1_in : t ∈ h1) (h2_in : t ∈ h2)
    (α_star : Action)
    (h_cell : enacted i t h1 = enacted i t h2) :
    PurposefulAct i t h1 α_star ↔ PurposefulAct i t h2 α_star := by
  have h_feas : A_feas i t h1 = A_feas i t h2 := A_feas_bundle_invariant i t h1_in h2_in
  have h_pref : Preference i t h1 = Preference i t h2 := Preference_bundle_invariant i t h1_in h2_in
  have h_end : ∀ α, End_of i α t h1 = End_of i α t h2 :=
    fun α => F.End_of_bundle_invariant i α t h1_in h2_in
  dsimp [PurposefulAct, PurposefulActUnder, PurposefulActWithEnd]
  rw [h_feas, h_pref]
  simp_rw [h_end]
  have h_exec : Exec i t α_star h1 ↔ Exec i t α_star h2 := by
    dsimp [Exec, ChoicePartition]
    rw [h_cell]
    simp only [h1_in, h2_in, true_and]
  rw [h_exec]

/-- Purposefulness is invariant across histories containing the same decision
when the enacted action at that node is the same. The result follows from the
frame's history-invariance laws for menus, preferences, and action ends. -/
theorem PurposefulAct.bundle_invariant (i : Agent) (t : Moment)
    (h₁ h₂ : History) (α : Action)
    (h₁_mem : F.mem_hist t h₁) (h₂_mem : F.mem_hist t h₂)
    (h_enacted : F.enacted i t h₁ = F.enacted i t h₂) :
    PurposefulAct i t h₁ α ↔ PurposefulAct i t h₂ α := by
  exact purposeful_act_choice_cell_invariant i t h₁ h₂ h₁_mem h₂_mem α h_enacted

/-- Purposeful action whose end is preferred to the baseline end. -/
def ActivePurposefulAct (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
  PurposefulAct i t h α_star ∧ Preference i t h (End_of i α_star t h) (End_of i α₀ t h)


theorem purposeful_act_active_diverges (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_act : PurposefulAct i t h α_star) (h_ne : α_star ≠ α₀) :
    End_of i α_star t h ≠ End_of i α₀ t h := by
  rcases h_act.2.2.1 with rfl | h_pref
  · exact (h_ne rfl).elim
  · intro h_eq
    rw [h_eq] at h_pref
    exact pref_irrefl i t h (End_of i α₀ t h) h_pref

/-- An action preferred to the baseline differs from the baseline action. -/
theorem purposeful_act_non_passive (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_act : PurposefulAct i t h α_star)
    (h_unease : Preference i t h (End_of i α_star t h) (End_of i α₀ t h)) :
    α_star ≠ α₀ ∧ End_of i α_star t h ≠ End_of i α₀ t h := by
  have h_not_end : End_of i α_star t h ≠ End_of i α₀ t h := by
    intro h_eq
    rw [h_eq] at h_unease
    exact pref_irrefl i t h (End_of i α₀ t h) h_unease
  have h_not_act : α_star ≠ α₀ := by
    intro h_eq
    subst h_eq
    exact h_not_end rfl
  exact ⟨h_not_act, h_not_end⟩


theorem purposeful_act_pref_of_ne_alpha_zero (i : Agent) (t : Moment) (h : History)
    (α_star : Action)
    (h_act : PurposefulAct i t h α_star) (h_ne : α_star ≠ α₀) :
    Preference i t h (End_of i α_star t h) (End_of i α₀ t h) := by
  rcases h_act.2.2.1 with rfl | h_pref
  · exact (h_ne rfl).elim
  · exact h_pref

/-- Active purposeful action is equivalent to purposeful action distinct from `alpha_zero`. -/
theorem active_purposeful_act_iff_ne_alpha_zero (i : Agent) (t : Moment) (h : History)
    (α_star : Action) :
    ActivePurposefulAct i t h α_star ↔ PurposefulAct i t h α_star ∧ α_star ≠ α₀ := by
  refine ⟨fun h_act => ⟨h_act.1, (purposeful_act_non_passive i t h α_star h_act.1 h_act.2).1⟩,
          fun ⟨h_act, h_ne⟩ =>
            ⟨h_act, purposeful_act_pref_of_ne_alpha_zero i t h α_star h_act h_ne⟩⟩


theorem active_purposeful_act_requires_causal_futurity_of_endowments
    {i : Agent} {t : Moment} {h : History} {α : Action}
    (h_act : ActivePurposefulAct i t h α)
    (h_feas_all : ∀ h' ∈ MinPlausible i t, α ∈ A_feas i (tau i t h') h')
    (h_ground : F.OutcomesGroundedInEndowments) :
    ∃ h' ∈ MinPlausible i t,
      let t' := tau i t h'
      Precedence t' (F.ExpectedMaturation i α t' (F.sigma i t' α h')) ∨
      Precedence t' (F.ExpectedMaturation i α₀ t' (F.sigma i t' α₀ h')) :=
  F.active_purposeful_act_requires_strict_future_maturation_of_endowments i t h α
    h_feas_all h_act.2 h_ground

/-- If a feasible action is preferred to baseline, purposeful action differs from `alpha_zero`. -/
theorem purposeful_act_ne_alpha_zero_of_dominated (i : Agent) (t : Moment) (h : History)
    (α_star : Action)
    (h_act : PurposefulAct i t h α_star)
    (β : Action) (hβ : β ∈ A_feas i t h)
    (h_dom : Preference i t h (End_of i β t h) (End_of i α₀ t h)) :
    α_star ≠ α₀ := by
  rintro rfl
  have h_undom := h_act.2.2.2 β hβ
  exact h_undom h_dom


theorem global_purposeful_act_branches_history (i : Agent) (t : Moment) (h : History)
    (α_star : Action)
    (h_act : PurposefulAct i t h α_star) (h_ne_α₀ : α_star ≠ α₀) :
    ∃ h₀ ∈ ChoicePartition i t α₀, h₀ ≠ h := by
  have h_α₀_feas := alpha_zero_feasible i t h
  obtain ⟨h₀, hh₀⟩ := choice_partition_nonempty i t h h_act.2.1.1 h_α₀_feas
  refine ⟨h₀, hh₀, ?_⟩
  rintro rfl
  have h_exec : Exec i t α_star h₀ := h_act.2.1
  dsimp [Exec] at h_exec
  have h_disj := choice_partition_disjoint i t h_ne_α₀
  exact Set.disjoint_left.mp h_disj h_exec hh₀

/-- Active action and refraining separate histories before any common future moment. -/
theorem global_purposeful_act_branches_incompatible_futures
    (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_act : PurposefulAct i t h α_star) (h_ne : α_star ≠ α₀) :
    ∃ h₀ ∈ ChoicePartition i t α₀,
      (∀ s, s < t → (s ∈ h ↔ s ∈ h₀)) ∧
      (∀ w, t < w → ¬ (w ∈ h ∧ w ∈ h₀)) ∧
      ∃ u v, u ∈ h ∧ v ∈ h₀ ∧ t < u ∧ t < v ∧
        ¬ u < v ∧ u ≠ v ∧ ¬ v < u := by
  obtain ⟨h₀, hh₀, hneq⟩ := global_purposeful_act_branches_history i t h α_star h_act h_ne
  have hpast : ∀ s, s < t → (s ∈ h ↔ s ∈ h₀) := by
    intro s hst
    constructor
    · intro _
      exact F.past_mem_of_mem h₀ s t hh₀.1 hst
    · intro _
      exact F.past_mem_of_mem h s t h_act.2.1.1 hst
  have hfuture : ∀ w, t < w → ¬ (w ∈ h ∧ w ∈ h₀) := by
    intro w htw ⟨hw1, hw0⟩
    have hsame := F.no_choice_between_undivided i t w h h₀
      h_act.2.1.1 hh₀.1 htw hw1 hw0
    have hchosen : F.enacted i t h = α_star := h_act.2.1.2
    have hpass : F.enacted i t h₀ = F.alpha_zero := hh₀.2
    exact h_ne (hchosen.symm.trans (hsame.trans hpass))
  have hdiv := F.distinct_histories_have_incompatible_futures t h h₀
    h_act.2.1.1 hh₀.1 hneq.symm
  exact ⟨h₀, hh₀, hpast, hfuture, hdiv⟩


theorem purposeful_act_unique_execution (i : Agent) (t : Moment) (h : History) (α₁ α₂ : Action)
    (h1 : PurposefulAct i t h α₁)
    (h2 : PurposefulAct i t h α₂) :
    α₁ = α₂ := by
  by_contra hne
  have h_disj := choice_partition_disjoint i t hne
  exact Set.disjoint_left.mp h_disj h1.2.1 h2.2.1


theorem three_option_menu_consistency
    (i : Agent) (t : Moment) (h : History)
    (α1 α2 α3 : Action)
    (h_menu : A_feas i t h = {α1, α2, α3})
    (h_exec1 : Exec i t α1 h)
    (h_pref10 : Preference i t h (End_of i α1 t h) (End_of i α₀ t h))
    (h_pref12 : Preference i t h (End_of i α1 t h) (End_of i α2 t h))
    (h_pref23 : Preference i t h (End_of i α2 t h) (End_of i α3 t h))
    (h_trans : ∀ e1 e2 e3,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    PurposefulAct i t h α1 ∧
    ¬ PurposefulAct i t h α2 ∧
    ¬ PurposefulAct i t h α3 := by
  have h_feas1 : α1 ∈ A_feas i t h := by rw [h_menu]; simp
  have h_feas2 : α2 ∈ A_feas i t h := by rw [h_menu]; simp
  have h_feas3 : α3 ∈ A_feas i t h := by rw [h_menu]; simp
  have h_pref13 : Preference i t h (End_of i α1 t h) (End_of i α3 t h) :=
    h_trans (End_of i α1 t h) (End_of i α2 t h) (End_of i α3 t h) h_pref12 h_pref23
  have h_act1 : PurposefulAct i t h α1 := by
    refine ⟨h_feas1, h_exec1, Or.inr h_pref10, ?_⟩
    intro β hβ
    rw [h_menu] at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with hβ1 | hβ2 | hβ3
    · rw [hβ1]; exact pref_irrefl i t h (End_of i α1 t h)
    · rw [hβ2]; exact pref_asymm i t h h_pref12
    · rw [hβ3]; exact pref_asymm i t h h_pref13
  have h_not_act2 : ¬ PurposefulAct i t h α2 := by
    intro h_act2
    have h_undom2 := h_act2.2.2.2 α1 h_feas1
    exact h_undom2 h_pref12
  have h_not_act3 : ¬ PurposefulAct i t h α3 := by
    intro h_act3
    have h_undom3 := h_act3.2.2.2 α2 h_feas2
    exact h_undom3 h_pref23
  exact ⟨h_act1, h_not_act2, h_not_act3⟩

/-- A Buridan tie between two distinct actions serving the same end is fully compatible
with purposeful action. -/
theorem buridan_tie_compatible_with_purposeful_act
    (i : Agent) (t : Moment) (h : History)
    (α1 α2 : Action)
    (h_diff : α1 ≠ α2)
    (h_same_end : End_of i α1 t h = End_of i α2 t h)
    (h_act : PurposefulAct i t h α1) :
    α1 ≠ α2 ∧
    End_of i α1 t h = End_of i α2 t h ∧
    PurposefulAct i t h α1 :=
  ⟨h_diff, h_same_end, h_act⟩

end ActionFoundations


-- 4. Finite Relation Results


/-- A nonempty finite set has an undominated element under an irreflexive transitive relation. -/
theorem exists_undominated_aux {α : Type} (n : ℕ) :
    ∀ (S : Finset α), S.card = n → S.Nonempty →
      ∀ (R : α → α → Prop),
        (∀ x ∈ S, ¬ R x x) →
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R y z → R x z) →
        ∃ m ∈ S, ∀ x ∈ S, ¬ R x m := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro S h_card h_ne R h_irrefl h_trans
      obtain ⟨a, ha⟩ := h_ne
      by_cases h_all : ∀ x ∈ S, ¬ R x a
      · exact ⟨a, ha, h_all⟩
      · push Not at h_all
        obtain ⟨b, hb, hba⟩ := h_all
        let S' := S.filter (fun x => R x a)
        have hb_in_S' : b ∈ S' := Finset.mem_filter.mpr ⟨hb, hba⟩
        have hS'_ne : S'.Nonempty := ⟨b, hb_in_S'⟩
        have h_sub : S' ⊆ S := Finset.filter_subset _ _
        have ha_notin : a ∉ S' := by
          intro ha_in
          have haa : R a a := (Finset.mem_filter.mp ha_in).2
          exact h_irrefl a ha haa
        have h_card_lt : S'.card < n := by
          have h_sub_erase : S' ⊆ S.erase a := by
            intro x hx
            rw [Finset.mem_erase]
            exact ⟨fun h_eq => ha_notin (h_eq ▸ hx), h_sub hx⟩
          have h1 : S'.card ≤ (S.erase a).card := Finset.card_le_card h_sub_erase
          have h2 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
          rw [h_card] at h2
          have h_pos : 0 < n := by
            rw [← h_card]
            exact Finset.card_pos.mpr ⟨a, ha⟩
          omega
        have h_irrefl' : ∀ x ∈ S', ¬ R x x := fun x hx => h_irrefl x (h_sub hx)
        have h_trans' : ∀ x ∈ S', ∀ y ∈ S', ∀ z ∈ S', R x y → R y z → R x z :=
          fun x hx y hy z hz hxy hyz =>
            h_trans x (h_sub hx) y (h_sub hy) z (h_sub hz) hxy hyz
        obtain ⟨m, hm, h_undom⟩ :=
          ih S'.card h_card_lt S' rfl hS'_ne R h_irrefl' h_trans'
        refine ⟨m, h_sub hm, ?_⟩
        intro x hx hxm
        have hxa : R x a :=
          h_trans x hx m (h_sub hm) a ha hxm (Finset.mem_filter.mp hm).2
        have hx' : x ∈ S' := Finset.mem_filter.mpr ⟨hx, hxa⟩
        exact h_undom x hx' hxm

/-- A nonempty finite set has an undominated element under the reversed relation. -/
theorem exists_least_urgent_aux {α : Type} (n : ℕ) :
    ∀ (S : Finset α), S.card = n → S.Nonempty →
      ∀ (R : α → α → Prop),
        (∀ x ∈ S, ¬ R x x) →
        (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R y z → R x z) →
        ∃ m ∈ S, ∀ x ∈ S, ¬ R m x := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S h_card h_ne R h_irrefl h_trans
    obtain ⟨a, ha⟩ := h_ne
    by_cases h_all : ∀ x ∈ S, ¬ R a x
    · exact ⟨a, ha, h_all⟩
    · push Not at h_all
      obtain ⟨b, hb_in, hab⟩ := h_all
      let S' := S.filter (fun x => R a x)
      have hb_in_S' : b ∈ S' := Finset.mem_filter.mpr ⟨hb_in, hab⟩
      have hS'_ne : S'.Nonempty := ⟨b, hb_in_S'⟩
      have h_sub : S' ⊆ S := Finset.filter_subset _ _
      have ha_notin : a ∉ S' := by
        intro ha_in
        have hra : R a a := (Finset.mem_filter.mp ha_in).2
        exact h_irrefl a ha hra
      have h_card_lt : S'.card < n := by
        have h_sub_erase : S' ⊆ S.erase a := by
          intro x hx
          rw [Finset.mem_erase]
          exact ⟨fun h_eq => ha_notin (h_eq ▸ hx), h_sub hx⟩
        have h1 : S'.card ≤ (S.erase a).card := Finset.card_le_card h_sub_erase
        have h2 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
        rw [h_card] at h2
        have h_pos : 0 < n := by
          rw [← h_card]
          exact Finset.card_pos.mpr ⟨a, ha⟩
        omega
      have h_irrefl' : ∀ x ∈ S', ¬ R x x := fun x hx => h_irrefl x (h_sub hx)
      have h_trans' : ∀ x ∈ S', ∀ y ∈ S', ∀ z ∈ S', R x y → R y z → R x z :=
        fun x hx y hy z hz => h_trans x (h_sub hx) y (h_sub hy) z (h_sub hz)
      obtain ⟨m, hm_in_S', hm_undom⟩ :=
        ih S'.card h_card_lt S' rfl hS'_ne R h_irrefl' h_trans'
      have hm_in_S : m ∈ S := h_sub hm_in_S'
      have ham : R a m := (Finset.mem_filter.mp hm_in_S').2
      refine ⟨m, hm_in_S, ?_⟩
      intro y hy hmy
      have hay : R a y := h_trans a ha m hm_in_S y hy ham hmy
      have hy_in_S' : y ∈ S' := Finset.mem_filter.mpr ⟨hy, hay⟩
      exact hm_undom y hy_in_S' hmy


-- 5. Foregone Actions and Opportunity Cost

section OpportunityCostAndSelfRefutation

variable [F : ActionFrame]


theorem exists_undominated_ends (i : Agent) (t : Moment) (h : History)
    (S : Finset Ends) (hS : S.Nonempty)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      Preference i t h x y → Preference i t h y z → Preference i t h x z) :
    ∃ m ∈ S, ∀ x ∈ S, ¬ Preference i t h x m := by
  have h_irrefl : ∀ x ∈ S, ¬ Preference i t h x x :=
    fun x _ => pref_irrefl i t h x
  exact exists_undominated_aux S.card S rfl hS (Preference i t h) h_irrefl h_trans


theorem exists_least_urgent_end (i : Agent) (t : Moment) (h : History)
    (S : Finset Ends) (hS : S.Nonempty)
    (h_trans : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      Preference i t h x y → Preference i t h y z → Preference i t h x z) :
    ∃ m ∈ S, ∀ x ∈ S, ¬ Preference i t h m x := by
  have h_irrefl : ∀ x ∈ S, ¬ Preference i t h x x :=
    fun x _ => pref_irrefl i t h x
  exact exists_least_urgent_aux S.card S rfl hS (Preference i t h) h_irrefl h_trans

/-- Foregone alternative actions when choosing α_star. -/
def ForegoneActions (i : Agent) (t : Moment) (h : History)
    (α_star : Action) : Finset Action :=
  (A_feas i t h).erase α_star


def ForegoneActionEnds (i : Agent) (t : Moment) (h : History)
    (α_star : Action) : Finset Ends :=
  (ForegoneActions i t h α_star).image (End_of i · t h)


def StrictForegoneEnds (i : Agent) (t : Moment) (h : History)
    (α_star : Action) : Finset Ends :=
  (ForegoneActionEnds i t h α_star).erase (End_of i α_star t h)


theorem foregone_action_ends_eq_strict_foregone_ends
    (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_no_tie : ∀ β ∈ ForegoneActions i t h α_star, End_of i β t h ≠ End_of i α_star t h) :
    ForegoneActionEnds i t h α_star = StrictForegoneEnds i t h α_star := by
  ext e
  dsimp [StrictForegoneEnds]
  rw [Finset.mem_erase]
  constructor
  · intro he
    refine ⟨?_, he⟩
    rintro rfl
    rcases Finset.mem_image.mp he with ⟨β, hβ, h_end⟩
    exact h_no_tie β hβ h_end
  · intro ⟨_, he⟩
    exact he

/-- Strict foregone ends are always a subset of foregone action ends. -/
theorem strict_foregone_ends_subset_foregone_action_ends
    (i : Agent) (t : Moment) (h : History) (α_star : Action) :
    StrictForegoneEnds i t h α_star ⊆ ForegoneActionEnds i t h α_star :=
  Finset.erase_subset (End_of i α_star t h) (ForegoneActionEnds i t h α_star)

/-- The realized end is not a strict foregone end. -/
theorem end_of_not_mem_strict_foregone_ends (i : Agent) (t : Moment) (h : History)
    (α_star : Action) :
    End_of i α_star t h ∉ StrictForegoneEnds i t h α_star := by
  intro h_mem
  have h_ne := (Finset.mem_erase.mp h_mem).1
  exact h_ne rfl

/-- A foregone action with the same end puts the realized end in `ForegoneActionEnds`. -/
theorem end_of_mem_foregone_action_ends_of_tie (i : Agent) (t : Moment) (h : History)
    (α_star : Action)
    (β : Action) (hβ : β ∈ ForegoneActions i t h α_star)
    (h_tie : End_of i β t h = End_of i α_star t h) :
    End_of i α_star t h ∈ ForegoneActionEnds i t h α_star := by
  dsimp [ForegoneActionEnds]
  rw [Finset.mem_image]
  exact ⟨β, hβ, h_tie⟩


def ActionOCSet (i : Agent) (t : Moment) (h : History) (α_star : Action)
    [∀ a b, Decidable (Preference i t h a b)] : Finset Ends :=
  (ForegoneActionEnds i t h α_star).filter (fun e =>
    ∀ e' ∈ ForegoneActionEnds i t h α_star, ¬ Preference i t h e' e)


def StrictOCSet (i : Agent) (t : Moment) (h : History) (α_star : Action)
    [∀ a b, Decidable (Preference i t h a b)] : Finset Ends :=
  (StrictForegoneEnds i t h α_star).filter (fun e =>
    ∀ e' ∈ StrictForegoneEnds i t h α_star, ¬ Preference i t h e' e)


theorem action_ocset_eq_strict_ocset (i : Agent) (t : Moment) (h : History) (α_star : Action)
    [∀ a b, Decidable (Preference i t h a b)]
    (h_no_tie : ∀ β ∈ ForegoneActions i t h α_star, End_of i β t h ≠ End_of i α_star t h) :
    ActionOCSet i t h α_star = StrictOCSet i t h α_star := by
  dsimp [ActionOCSet, StrictOCSet]
  rw [foregone_action_ends_eq_strict_foregone_ends i t h α_star h_no_tie]

/-- The realized end is not in `StrictOCSet`. -/
theorem end_of_not_mem_strict_ocset (i : Agent) (t : Moment) (h : History) (α_star : Action)
    [∀ a b, Decidable (Preference i t h a b)] :
    End_of i α_star t h ∉ StrictOCSet i t h α_star := by
  intro h_in
  have h_foregone := (Finset.mem_filter.mp h_in).1
  exact end_of_not_mem_strict_foregone_ends i t h α_star h_foregone


theorem end_of_mem_action_ocset_of_tie (i : Agent) (t : Moment) (h : History) (α_star : Action)
    [∀ a b, Decidable (Preference i t h a b)]
    (h_act : PurposefulAct i t h α_star)
    (β : Action) (hβ : β ∈ ForegoneActions i t h α_star)
    (h_tie : End_of i β t h = End_of i α_star t h) :
    End_of i α_star t h ∈ ActionOCSet i t h α_star := by
  dsimp [ActionOCSet]
  rw [Finset.mem_filter]
  refine ⟨end_of_mem_foregone_action_ends_of_tie i t h α_star β hβ h_tie, ?_⟩
  intro e' he'
  rcases Finset.mem_image.mp he' with ⟨γ, hγ, rfl⟩
  have hγ_feas : γ ∈ A_feas i t h := Finset.mem_of_mem_erase hγ
  exact h_act.2.2.2 γ hγ_feas


theorem strict_ocset_nonempty_of_star_order (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_star : ∀ e ∈ StrictForegoneEnds i t h α_star,
      ∀ e' ∈ StrictForegoneEnds i t h α_star, ¬ Preference i t h e' e)
    (h_ne : (StrictForegoneEnds i t h α_star).Nonempty) :
    StrictOCSet i t h α_star = StrictForegoneEnds i t h α_star ∧
    (StrictOCSet i t h α_star).Nonempty := by
  have h_eq : StrictOCSet i t h α_star = StrictForegoneEnds i t h α_star := by
    ext e
    dsimp [StrictOCSet]
    rw [Finset.mem_filter]
    constructor
    · intro h_in; exact h_in.1
    · intro he_in
      refine ⟨he_in, fun e' he'_in => h_star e he_in e' he'_in⟩
  exact ⟨h_eq, h_eq.symm ▸ h_ne⟩


theorem strict_ocset_nonempty_of_trans (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_ne : (StrictForegoneEnds i t h α_star).Nonempty)
    (h_trans : ∀ e1 ∈ StrictForegoneEnds i t h α_star,
      ∀ e2 ∈ StrictForegoneEnds i t h α_star, ∀ e3 ∈ StrictForegoneEnds i t h α_star,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    (StrictOCSet i t h α_star).Nonempty := by
  obtain ⟨m, hm_in, hm_undom⟩ := exists_undominated_ends i t h
    (StrictForegoneEnds i t h α_star) h_ne h_trans
  use m
  dsimp [StrictOCSet]
  rw [Finset.mem_filter]
  exact ⟨hm_in, hm_undom⟩

/-- Connected preference gives at most one strict opportunity-cost end. -/
theorem strict_ocset_card_le_one_of_connected (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_conn : ∀ e1 ∈ StrictForegoneEnds i t h α_star,
      ∀ e2 ∈ StrictForegoneEnds i t h α_star, e1 ≠ e2 →
      Preference i t h e1 e2 ∨ Preference i t h e2 e1) :
    (StrictOCSet i t h α_star).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  dsimp [StrictOCSet] at ha hb
  rw [Finset.mem_filter] at ha hb
  by_contra hne
  rcases h_conn a ha.1 b hb.1 hne with hab | hba
  · exact hb.2 a ha.1 hab
  · exact ha.2 b hb.1 hba


theorem strict_ocset_singleton_of_connected (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_ne : (StrictForegoneEnds i t h α_star).Nonempty)
    (h_trans : ∀ e1 ∈ StrictForegoneEnds i t h α_star,
      ∀ e2 ∈ StrictForegoneEnds i t h α_star, ∀ e3 ∈ StrictForegoneEnds i t h α_star,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3)
    (h_conn : ∀ e1 ∈ StrictForegoneEnds i t h α_star,
      ∀ e2 ∈ StrictForegoneEnds i t h α_star, e1 ≠ e2 →
      Preference i t h e1 e2 ∨ Preference i t h e2 e1) :
    (StrictOCSet i t h α_star).card = 1 := by
  have h_nonempty := strict_ocset_nonempty_of_trans i t h α_star h_ne h_trans
  have h_le := strict_ocset_card_le_one_of_connected i t h α_star h_conn
  have h_pos : 0 < (StrictOCSet i t h α_star).card := Finset.card_pos.mpr h_nonempty
  omega


theorem action_ocset_nonempty_of_trans (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_ne : (ForegoneActionEnds i t h α_star).Nonempty)
    (h_trans : ∀ e1 ∈ ForegoneActionEnds i t h α_star,
      ∀ e2 ∈ ForegoneActionEnds i t h α_star, ∀ e3 ∈ ForegoneActionEnds i t h α_star,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3) :
    (ActionOCSet i t h α_star).Nonempty := by
  obtain ⟨m, hm_in, hm_undom⟩ := exists_undominated_ends i t h
    (ForegoneActionEnds i t h α_star) h_ne h_trans
  use m
  dsimp [ActionOCSet]
  rw [Finset.mem_filter]
  exact ⟨hm_in, hm_undom⟩

/-- Connected preference gives at most one action opportunity-cost end. -/
theorem action_ocset_card_le_one_of_connected (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_conn : ∀ e1 ∈ ForegoneActionEnds i t h α_star,
      ∀ e2 ∈ ForegoneActionEnds i t h α_star, e1 ≠ e2 →
      Preference i t h e1 e2 ∨ Preference i t h e2 e1) :
    (ActionOCSet i t h α_star).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  dsimp [ActionOCSet] at ha hb
  rw [Finset.mem_filter] at ha hb
  by_contra hne
  rcases h_conn a ha.1 b hb.1 hne with hab | hba
  · exact hb.2 a ha.1 hab
  · exact ha.2 b hb.1 hba


theorem action_ocset_singleton_of_connected (i : Agent) (t : Moment) (h : History)
    (α_star : Action) [∀ a b, Decidable (Preference i t h a b)]
    (h_ne : (ForegoneActionEnds i t h α_star).Nonempty)
    (h_trans : ∀ e1 ∈ ForegoneActionEnds i t h α_star,
      ∀ e2 ∈ ForegoneActionEnds i t h α_star, ∀ e3 ∈ ForegoneActionEnds i t h α_star,
      Preference i t h e1 e2 → Preference i t h e2 e3 → Preference i t h e1 e3)
    (h_conn : ∀ e1 ∈ ForegoneActionEnds i t h α_star,
      ∀ e2 ∈ ForegoneActionEnds i t h α_star, e1 ≠ e2 →
      Preference i t h e1 e2 ∨ Preference i t h e2 e1) :
    (ActionOCSet i t h α_star).card = 1 := by
  have h_nonempty := action_ocset_nonempty_of_trans i t h α_star h_ne h_trans
  have h_le := action_ocset_card_le_one_of_connected i t h α_star h_conn
  have h_pos : 0 < (ActionOCSet i t h α_star).card := Finset.card_pos.mpr h_nonempty
  omega

end OpportunityCostAndSelfRefutation


-- 6. Communication and Purposeful Action


section CommunicativeAction

variable [F : ActionFrame]

/-- A proposition about histories. -/
abbrev StateProp (H : Type) := H → Prop

/-- Agent `i` executes action `α` at `⟨t, h⟩`. -/
def Utters (i : Agent) (t : Moment) (h : History) (α : Action) : Prop :=
  α ∈ A_feas i t h ∧ Exec i t α h

/-- Agent `i` executes `α`, which is associated with proposition `P`. -/
def Asserts (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (P : StateProp History) (α : Action) : Prop :=
  Utters i t h α ∧ content α = P


-- 6.1 Epistemic Assertions


/-- The asserted proposition holds at the history of assertion. -/
def VeridicalClaim (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (P : StateProp History) (α : Action) : Prop :=
  Asserts i t h content P α ∧ P h

/-- No agent acts purposefully. -/
def NoPurposefulActionProp : StateProp History :=
  fun h' => ∀ j t' α, ¬ PurposefulAct j t' h' α

structure CounterfactualRefraining (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (P : StateProp History) (α : Action) : Prop where
  h_assert : Asserts i t h content P α
  h_not_a0 : α ≠ α₀
  h_belief : ∀ h' ∈ MinPlausible i t, P h'
  h_falsifying : ∃ h_f, mem_hist (tau i t h_f) h_f ∧ ¬ P h_f
  h_reason_resp : ∀ h', mem_hist (tau i t h') h' → ¬ P h' → enacted i (tau i t h') h' = α₀

structure VeridicalPreferenceNorm (i : Agent) (t : Moment) (h : History)
    (P : StateProp History) (α : Action) where
  e_veridical : Ends
  e_silence : Ends
  h_pref_veri : ∀ h' ∈ MinPlausible i t, P h' → Preference i t h e_veridical e_silence
  h_out_veri : End_of i α t h = e_veridical
  h_out_silence : End_of i α₀ t h = e_silence
  h_undom_alt : ∀ h' ∈ MinPlausible i t, P h' → ∀ β ∈ A_feas i t h, β ≠ α →
    ¬ Preference i t h (End_of i β t h) e_veridical

structure DeliberativeEpistemicAssertion (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (P : StateProp History) (α : Action)
    extends CounterfactualRefraining i t h content P α,
      VeridicalPreferenceNorm i t h P α


theorem deliberative_epistemic_assertion_refraining_witness
    (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (P : StateProp History) (α : Action)
    (h_delib : DeliberativeEpistemicAssertion i t h content P α) :
    ∃ h_f, h_f ∈ ChoicePartition i (tau i t h_f) α₀ ∧ ¬ P h_f ∧ ¬ Exec i (tau i t h_f) α h_f := by
  obtain ⟨h_f, ht_f, h_not_P_f⟩ := h_delib.h_falsifying
  have h_enacted : enacted i (tau i t h_f) h_f = α₀ := h_delib.h_reason_resp h_f ht_f h_not_P_f
  have h_part : h_f ∈ ChoicePartition i (tau i t h_f) α₀ := ⟨ht_f, h_enacted⟩
  have h_disj := choice_partition_disjoint i (tau i t h_f) h_delib.h_not_a0
  have h_not_exec : ¬ Exec i (tau i t h_f) α h_f := fun h_ex =>
    Set.disjoint_left.mp h_disj h_ex h_part
  exact ⟨h_f, h_part, h_not_P_f, h_not_exec⟩


theorem purposeful_act_and_refraining_of_deliberative_epistemic_assertion
    (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (P : StateProp History) (α : Action)
    (h_delib : DeliberativeEpistemicAssertion i t h content P α) :
    PurposefulAct i t h α ∧ ∃ h_f,
      h_f ∈ ChoicePartition i (tau i t h_f) α₀ ∧ ¬ P h_f ∧ ¬ Exec i (tau i t h_f) α h_f := by
  have ⟨h_f, h_part, h_not_P_f, h_not_exec⟩ :=
    deliberative_epistemic_assertion_refraining_witness i t h content P α h_delib
  have h_feas := h_delib.h_assert.1.1
  have h_exec := h_delib.h_assert.1.2
  obtain ⟨h_pl, hh_pl⟩ := min_plausible_nonempty i t
  have h_P_pl : P h_pl := h_delib.h_belief h_pl hh_pl
  have h_pref_base : Preference i t h h_delib.e_veridical h_delib.e_silence :=
    h_delib.h_pref_veri h_pl hh_pl h_P_pl
  have h_pref : Preference i t h (End_of i α t h) (End_of i α₀ t h) := by
    rw [h_delib.h_out_veri, h_delib.h_out_silence]
    exact h_pref_base
  have h_undom : ∀ β ∈ A_feas i t h, ¬ Preference i t h (End_of i β t h) (End_of i α t h) := by
    intro β hβ
    by_cases h_eq : β = α
    · subst h_eq
      intro h_self
      exact pref_asymm i t h h_self h_self
    · rw [h_delib.h_out_veri]
      exact h_delib.h_undom_alt h_pl hh_pl h_P_pl β hβ h_eq
  exact ⟨⟨h_feas, h_exec, Or.inr h_pref, h_undom⟩, ⟨h_f, h_part, h_not_P_f, h_not_exec⟩⟩

theorem purposeful_act_of_deliberative_epistemic_assertion
    (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (P : StateProp History) (α : Action)
    (h_delib : DeliberativeEpistemicAssertion i t h content P α) :
    PurposefulAct i t h α :=
  (purposeful_act_and_refraining_of_deliberative_epistemic_assertion i t h content P α h_delib).1


theorem dialectical_self_falsification_under_deliberative_norms
    (i : Agent) (t : Moment) (h : History)
    (content : Action → StateProp History) (α : Action)
    (h_delib : DeliberativeEpistemicAssertion i t h content NoPurposefulActionProp α) :
    ¬ NoPurposefulActionProp h ∧
    ¬ VeridicalClaim i t h content NoPurposefulActionProp α := by
  have h_act : PurposefulAct i t h α :=
    purposeful_act_of_deliberative_epistemic_assertion i t h content
      NoPurposefulActionProp α h_delib
  have h_false : ¬ NoPurposefulActionProp h := by
    intro h_no_act
    exact h_no_act i t α h_act
  exact ⟨h_false, fun h_ver => h_false h_ver.2⟩

end CommunicativeAction


-- 7. Independence Examples


section IndependenceExamples

variable [F : ActionFrame]

theorem buridan_tie_refutes_strict_demonstrated_pref
    (i : Agent) (t : Moment) (h : History)
    (α₁ α₂ : Action) (e_star : Ends)
    (hne : α₁ ≠ α₂)
    (h1 : α₁ ∈ A_feas i t h)
    (h2 : α₂ ∈ A_feas i t h)
    (h_end1 : End_of i α₁ t h = e_star)
    (h_end2 : End_of i α₂ t h = e_star) :
    ¬ (∀ β ∈ (A_feas i t h).erase α₁, Preference i t h (End_of i α₁ t h) (End_of i β t h)) ∧
    ¬ (∀ β ∈ (A_feas i t h).erase α₂, Preference i t h (End_of i α₂ t h) (End_of i β t h)) := by
  constructor
  · intro h_strict1
    have h_mem2 : α₂ ∈ (A_feas i t h).erase α₁ := by
      rw [Finset.mem_erase]
      exact ⟨hne.symm, h2⟩
    have h_pref12 := h_strict1 α₂ h_mem2
    rw [h_end1, h_end2] at h_pref12
    exact pref_irrefl i t h e_star h_pref12
  · intro h_strict2
    have h_mem1 : α₁ ∈ (A_feas i t h).erase α₂ := by
      rw [Finset.mem_erase]
      exact ⟨hne, h1⟩
    have h_pref21 := h_strict2 α₁ h_mem1
    rw [h_end1, h_end2] at h_pref21
    exact pref_irrefl i t h e_star h_pref21


theorem buridan_distinct_ends_tie_refutes_strict_grounding
    (i : Agent) (t : Moment) (h : History)
    (α₁ α₂ : Action)
    (h_no12 : ¬ Preference i t h (End_of i α₁ t h) (End_of i α₂ t h))
    (h_no21 : ¬ Preference i t h (End_of i α₂ t h) (End_of i α₁ t h)) :
    ¬ Preference i t h (End_of i α₁ t h) (End_of i α₂ t h) ∧
    ¬ Preference i t h (End_of i α₂ t h) (End_of i α₁ t h) :=
  ⟨h_no12, h_no21⟩


theorem buridan_same_end_tie_action_ocset_continuity
    (i : Agent) (t : Moment) (h : History)
    (α₁ α₂ : Action)
    (hne : α₁ ≠ α₂)
    (h2 : α₂ ∈ A_feas i t h)
    (h_same : End_of i α₁ t h = End_of i α₂ t h) :
    let ForegoneActions1 : Finset Action := (A_feas i t h).erase α₁
    let ForegoneActionEnds1 : Finset Ends := ForegoneActions1.image (End_of i · t h)
    End_of i α₁ t h ∈ ForegoneActionEnds1 := by
  dsimp
  rw [Finset.mem_image]
  refine ⟨α₂, ?_, h_same.symm⟩
  rw [Finset.mem_erase]
  exact ⟨hne.symm, h2⟩


theorem opportunity_cost_independent_of_minimal_action
    (i : Agent) (t : Moment) (h : History)
    {e1 e2 : Ends} (hne : e1 ≠ e2)
    (h12 : ¬ Preference i t h e1 e2) (h21 : ¬ Preference i t h e2 e1) :
    let Foregone : Finset Ends := {e1, e2}
    ¬ ∃ e_opp ∈ Foregone, ∀ e' ∈ Foregone.erase e_opp, Preference i t h e_opp e' := by
  dsimp
  rintro ⟨e_opp, h_mem, h_max⟩
  have h_cases : e_opp = e1 ∨ e_opp = e2 := by
    simpa using h_mem
  rcases h_cases with heq1 | heq2
  · subst heq1
    have h2_in : e2 ∈ ({e_opp, e2} : Finset Ends).erase e_opp := by
      rw [Finset.mem_erase]
      refine ⟨hne.symm, ?_⟩
      simp
    exact h12 (h_max e2 h2_in)
  · subst heq2
    have h1_in : e1 ∈ ({e1, e_opp} : Finset Ends).erase e_opp := by
      rw [Finset.mem_erase]
      refine ⟨hne, ?_⟩
      simp
    exact h21 (h_max e1 h1_in)


theorem universal_action_not_proved_by_local_assertion
    (i : Agent) (t0 t1 : Moment) (h0 h1 : History) (α β : Action)
    (h_act : PurposefulAct i t0 h0 α)
    (_h_idle : enacted i t1 h1 = α₀)
    (h_feas_β : β ∈ A_feas i t1 h1)
    (h_pref_β : Preference i t1 h1 (End_of i β t1 h1) (End_of i α₀ t1 h1)) :
    PurposefulAct i t0 h0 α ∧ ¬ PurposefulAct i t1 h1 α₀ := by
  refine ⟨h_act, ?_⟩
  intro h_purp_idle
  have h_undom := h_purp_idle.2.2.2 β h_feas_β
  exact h_undom h_pref_β

end IndependenceExamples

section DoxasticActionFrames

variable [F : ActionFrame]


-- Section 8: Plausible Histories and Action


/-- Histories along which agent `i` enacts `α` at `t`. -/
def ChoiceCell (i : Agent) (t : Moment) (α : Action) : Set History :=
  { h | enacted i t h = α }

/-- Action `α` is feasible in `H_t` when it is enacted on some history in `H_t`. -/
def BranchFeas (i : Agent) (t : Moment) (H_t : Set History) (α : Action) : Prop :=
  ∃ h' ∈ H_t, enacted i t h' = α

/-- `α` is preferred to `β` at every plausible history. -/
def DoxasticUnanimousDominates (i : Agent) (t : Moment) (h : History) (α β : Action) : Prop :=
  ∀ h' ∈ MinPlausible i t, Preference i t h (MaturationEnd i α t h') (MaturationEnd i β t h')


def DoxasticWeakParetoDominates (i : Agent) (t : Moment) (h : History) (α β : Action) : Prop :=
  (∀ h' ∈ MinPlausible i t, MaturationEnd i α t h' = MaturationEnd i β t h' ∨
    Preference i t h (MaturationEnd i α t h') (MaturationEnd i β t h')) ∧
  (∃ h' ∈ MinPlausible i t, Preference i t h (MaturationEnd i α t h') (MaturationEnd i β t h'))


def DoxasticSureThingDominates (i : Agent) (t : Moment) (h : History) (α β : Action) : Prop :=
  (∀ h' ∈ MinPlausible i t, ¬ Preference i t h (MaturationEnd i β t h') (MaturationEnd i α t h')) ∧
  (∃ h' ∈ MinPlausible i t, Preference i t h (MaturationEnd i α t h') (MaturationEnd i β t h'))

/-- `α` is preferred to `β` at some plausible history. -/
def DoxasticPlausibleSupport (i : Agent) (t : Moment) (h : History) (α β : Action) : Prop :=
  ∃ h' ∈ MinPlausible i t, Preference i t h (MaturationEnd i α t h') (MaturationEnd i β t h')

/-- An action is uniformly available at the valid actual node and at each
plausible history's projected decision node. -/
def UniformlyAvailable (i : Agent) (x : F.DecisionIndex) (α : Action) : Prop :=
  α ∈ A_feas i x.moment x.history ∧
    ∀ h' ∈ MinPlausible i x.moment,
      α ∈ A_feas i (tau i x.moment h') h'

/-- Every admitted outcome pair is compared within the same compatible
circumstance, at each projected plausible decision node. -/
def ActionFrame.ContextCorrespondence.ContextUnanimousDominates
    {Context : Type} (C : F.ContextCorrespondence Context)
    (i : Agent) (x : F.DecisionIndex) (α β : Action) : Prop :=
  ∀ h' (hh' : h' ∈ MinPlausible i x.moment),
    let xp := F.projectedDecisionIndex i x.moment h' hh'
    ∀ c, C.compatible i xp.moment xp.history c →
      (C.Outcomes i xp c α).Nonempty ∧
      (C.Outcomes i xp c β).Nonempty ∧
      ∀ eα ∈ C.Outcomes i xp c α, ∀ eβ ∈ C.Outcomes i xp c β,
        Preference i x.moment x.history eα eβ

/-- Every outcome compatible with the same anchor circumstance ranks `α` over
`β`. This is the direct robust comparison used to ground causal appraisal. -/
def ActionFrame.ContextCorrespondence.OutcomesUnanimouslyRanked
    {Context : Type} (C : F.ContextCorrespondence Context)
    (i : Agent) (x : F.DecisionIndex) (α β : Action) : Prop :=
  ∀ c, C.compatible i x.moment x.history c →
    ∀ eα ∈ C.Outcomes i x c α, ∀ eβ ∈ C.Outcomes i x c β,
      Preference i x.moment x.history eα eβ

/-- If the correspondence ranks all outcomes in every compatible circumstance,
and those outcomes represent the frame's intended ends, the entrepreneur's
ordinary preference follows. Feasibility guarantees that both outcome sets
are nonempty. -/
theorem ActionFrame.ContextCorrespondence.outcomesUnanimouslyRanked_implies_intended_preference
    {Context : Type} (C : F.ContextCorrespondence Context)
    (i : Agent) (x : F.DecisionIndex) (α β : Action)
    (hα : α ∈ A_feas i x.moment x.history)
    (hβ : β ∈ A_feas i x.moment x.history)
    (hground : ∀ c, C.compatible i x.moment x.history c →
      ∀ eα ∈ C.Outcomes i x c α, ∀ eβ ∈ C.Outcomes i x c β,
        eα = End_of i α x.moment x.history ∧
        eβ = End_of i β x.moment x.history)
    (hranked : C.OutcomesUnanimouslyRanked i x α β) :
    Preference i x.moment x.history
      (End_of i α x.moment x.history) (End_of i β x.moment x.history) := by
  obtain ⟨c, hc⟩ := C.context_nonempty i x
  obtain ⟨eα, heα⟩ := C.outcomes_nonempty i x c α hc hα
  obtain ⟨eβ, heβ⟩ := C.outcomes_nonempty i x c β hc hβ
  have hpref := hranked c hc eα heα eβ heβ
  rcases hground c hc eα heα eβ heβ with ⟨rfl, rfl⟩
  exact hpref

/-- Contextual appraisal is separate from execution: it records uniform
availability, strict improvement on inaction, and maximality over feasible
uniformly available rivals. -/
def ActionFrame.ContextCorrespondence.ContextActiveAppraisal
    {Context : Type} (C : F.ContextCorrespondence Context)
    (i : Agent) (x : F.DecisionIndex) (α : Action) : Prop :=
  UniformlyAvailable i x α ∧
  C.ContextUnanimousDominates i x α α₀ ∧
  ∀ β ∈ A_feas i x.moment x.history,
    UniformlyAvailable i x β →
    ¬ C.ContextUnanimousDominates i x β α

/-- An alternative outcome can improve on the realized outcome without a
shared-context claim. -/
def AlternativeHistoryImprovement (i : Agent) (x : F.DecisionIndex)
    (τActual : Moment) (α β : Action) : Prop :=
  Exec i x.moment α x.history ∧
  mem_hist τActual x.history ∧
  β ∈ A_feas i x.moment x.history ∧
  ∃ hAlt τAlt,
    mem_hist x.moment hAlt ∧ enacted i x.moment hAlt = β ∧
    mem_hist τAlt hAlt ∧ (x.moment = τAlt ∨ Precedence x.moment τAlt) ∧
    Preference i τActual x.history
      (F.OutcomeOf i β x.moment τAlt hAlt)
      (F.OutcomeOf i α x.moment τActual x.history)

/-- Improvement of the particular alternative selected by the frame's sigma. -/
def SelectedAlternativeImprovement (i : Agent) (x : F.DecisionIndex)
    (τActual : Moment) (α β : Action) : Prop :=
  Exec i x.moment α x.history ∧
  mem_hist τActual x.history ∧
  β ∈ A_feas i x.moment x.history ∧
  mem_hist
    (F.ExpectedMaturation i β x.moment (F.sigma i x.moment β x.history))
    (F.sigma i x.moment β x.history) ∧
  Preference i τActual x.history
    (F.OutcomeOf i β x.moment
      (F.ExpectedMaturation i β x.moment (F.sigma i x.moment β x.history))
      (F.sigma i x.moment β x.history))
    (F.OutcomeOf i α x.moment τActual x.history)

/-- A possible foregone improvement whose realized and alternative outcomes
are admitted under one context. The actual history need not be plausible. -/
def ContextMatchedRegret {Context : Type}
    (C : F.ContextCorrespondence Context) (i : Agent) (x : F.DecisionIndex)
    (τActual : Moment) (α β : Action) : Prop :=
  β ∈ A_feas i x.moment x.history ∧
  ∃ c hAlt τAlt,
    C.compatible i x.moment x.history c ∧
    C.admissible i x c α x.history τActual ∧
    C.admissible i x c β hAlt τAlt ∧
    Preference i τActual x.history
      (F.OutcomeOf i β x.moment τAlt hAlt)
      (F.OutcomeOf i α x.moment τActual x.history)

/-- A selected counterfactual improvement is contextual regret under the
deterministic correspondence. The correspondence keeps the actual enacted
history centered and obtains the alternative by the frame's existing branch
selector; it adds no separate causal or preference premise. -/
theorem contextMatchedRegret_of_selected_outcome_improvement
    (i : Agent) (x : F.DecisionIndex) (α β : Action)
    (hα : α ∈ A_feas i x.moment x.history)
    (hαexec : Exec i x.moment α x.history)
    (hβ : β ∈ A_feas i x.moment x.history)
    (hbetter : Preference i
      (F.ExpectedMaturation i α x.moment x.history) x.history
      (F.OutcomeOf i β x.moment
        (F.ExpectedMaturation i β x.moment (F.sigma i x.moment β x.history))
        (F.sigma i x.moment β x.history))
      (F.OutcomeOf i α x.moment
        (F.ExpectedMaturation i α x.moment x.history) x.history)) :
    ContextMatchedRegret F.deterministicCorrespondence i x
      (F.ExpectedMaturation i α x.moment x.history) α β := by
  let C := F.deterministicCorrespondence
  let hAlt := F.sigma i x.moment β x.history
  let τAlt := F.ExpectedMaturation i β x.moment hAlt
  have hcenter : F.sigma i x.moment α x.history = x.history :=
    F.sigma_centering i x.moment x.history x.2 hαexec.2
  have hactual : C.admissible i x () α x.history
      (F.ExpectedMaturation i α x.moment x.history) := by
    dsimp [C, ActionFrame.deterministicCorrespondence]
    exact ⟨hα, hcenter.symm, by rw [hcenter]⟩
  have halt : C.admissible i x () β hAlt τAlt := by
    dsimp [C, hAlt, τAlt, ActionFrame.deterministicCorrespondence]
    exact ⟨hβ, rfl, rfl⟩
  exact ⟨hβ, (), hAlt, τAlt, trivial, hactual, halt, hbetter⟩

/-- Every admitted alternative outcome in one compatible context is better
than the admitted realized outcome; nonemptiness rules out vacuity. -/
def GuaranteedContextRegret {Context : Type}
    (C : F.ContextCorrespondence Context) (i : Agent) (x : F.DecisionIndex)
    (τActual : Moment) (α β : Action) : Prop :=
  β ∈ A_feas i x.moment x.history ∧
  ∃ c,
    C.compatible i x.moment x.history c ∧
    C.admissible i x c α x.history τActual ∧
    (C.Outcomes i x c β).Nonempty ∧
    ∀ e ∈ C.Outcomes i x c β,
      Preference i τActual x.history e
        (F.OutcomeOf i α x.moment τActual x.history)

/-- Guaranteed context-matched regret entails a possible context-matched
improvement. -/
theorem guaranteedContextRegret_implies_contextMatchedRegret
    {Context : Type} (C : F.ContextCorrespondence Context)
    (i : Agent) (x : F.DecisionIndex) (τActual : Moment) (α β : Action)
    (hregret : GuaranteedContextRegret C i x τActual α β) :
    ContextMatchedRegret C i x τActual α β := by
  rcases hregret with ⟨hβ, c, hc, hactual, ⟨e, he⟩, hbetter⟩
  rcases he with ⟨hAlt, τAlt, hadm, rfl⟩
  have hbetterAlt := hbetter _ ⟨hAlt, τAlt, hadm, rfl⟩
  exact ⟨hβ, c, hAlt, τAlt, hc, hactual, hadm, hbetterAlt⟩

theorem doxastic_sure_thing_asymm (i : Agent) (t : Moment) (h : History) (α β : Action) :
    DoxasticSureThingDominates i t h α β → ¬ DoxasticSureThingDominates i t h β α := by
  intro ⟨_, ⟨h_wit, hh_wit, h_pref⟩⟩ ⟨h_all2, _⟩
  exact h_all2 h_wit hh_wit h_pref


def DoxasticAppraisalCertificate (i : Agent) (t : Moment)
    (H_t : Set History) (h : History) : Prop :=
  h ∈ H_t ∧
  enacted i t h ∈ A_feas i t h ∧
  α₀ ∈ A_feas i t h ∧
  BranchFeas i t H_t α₀ ∧
  (MinPlausible i t).Nonempty ∧
  (∀ h' ∈ MinPlausible i t,
    Preference i t h
      (MaturationEnd i (enacted i t h) t h')
      (MaturationEnd i α₀ t h')) ∧
  (∀ β ∈ A_feas i t h, ¬ ∀ h' ∈ MinPlausible i t,
    Preference i t h
      (MaturationEnd i β t h')
      (MaturationEnd i (enacted i t h) t h'))


def SureThingAppraisalCertificate (i : Agent) (t : Moment) (H_t : Set History)
    (h : History) : Prop :=
  h ∈ H_t ∧
  enacted i t h ∈ A_feas i t h ∧
  α₀ ∈ A_feas i t h ∧
  BranchFeas i t H_t α₀ ∧
  (MinPlausible i t).Nonempty ∧
  DoxasticWeakParetoDominates i t h (enacted i t h) α₀ ∧
  (∀ β ∈ A_feas i t h, ¬ DoxasticWeakParetoDominates i t h β (enacted i t h))


def PlausibleSupportAppraisalCertificate (i : Agent) (t : Moment) (H_t : Set History)
    (h : History) : Prop :=
  h ∈ H_t ∧
  enacted i t h ∈ A_feas i t h ∧
  α₀ ∈ A_feas i t h ∧
  BranchFeas i t H_t α₀ ∧
  (MinPlausible i t).Nonempty ∧
  DoxasticPlausibleSupport i t h (enacted i t h) α₀ ∧
  (∀ β ∈ A_feas i t h, ¬ DoxasticWeakParetoDominates i t h β (enacted i t h)) ∧
  (∀ β ∈ A_feas i t h, ¬ ∀ h' ∈ MinPlausible i t,
    Preference i t h
      (MaturationEnd i β t h')
      (MaturationEnd i (enacted i t h) t h'))

/-- Preference is irreflexive. -/
theorem derived_pref_irrefl (i : Agent) (t : Moment) (h : History) (e : Ends) :
    ¬ Preference i t h e e :=
  fun h_refl => F.pref_asymm i t h h_refl h_refl


theorem derived_stit_partition_properties (i : Agent) (t : Moment) :
    (∀ h, h ∈ ChoiceCell i t (enacted i t h)) ∧
    (∀ α β, α ≠ β → Disjoint (ChoiceCell i t α) (ChoiceCell i t β)) ∧
    (∀ (H_t : Set History) α, BranchFeas i t H_t α ↔ (H_t ∩ ChoiceCell i t α).Nonempty) := by
  refine ⟨fun h => rfl, ?_, ?_⟩
  · intro α β hne
    refine Set.disjoint_left.2 ?_
    intro h (ha : enacted i t h = α) (hb : enacted i t h = β)
    subst ha hb
    exact hne rfl
  · intro H_t α
    constructor
    · rintro ⟨h', hh', h_act⟩
      exact ⟨h', hh', h_act⟩
    · rintro ⟨h', hh', (h_act : enacted i t h' = α)⟩
      exact ⟨h', hh', h_act⟩


theorem doxastic_action_non_passive (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_act : DoxasticAppraisalCertificate i t H_t h) :
    enacted i t h ≠ α₀ ∧
    ∀ h' ∈ MinPlausible i t,
      MaturationEnd i (enacted i t h) t h' ≠ MaturationEnd i α₀ t h' := by
  have ⟨_, _, _, _, h_pl_nonempty, h_unease, _⟩ := h_act
  rcases h_pl_nonempty with ⟨h_pl, h_pl_mem⟩
  have h_pref_pl := h_unease h_pl h_pl_mem
  have h_ne_act : enacted i t h ≠ α₀ := by
    intro h_eq
    rw [h_eq] at h_pref_pl
    exact derived_pref_irrefl i t h _ h_pref_pl
  refine ⟨h_ne_act, ?_⟩
  intro h' hh' h_out_eq
  have h_pref' := h_unease h' hh'
  rw [h_out_eq] at h_pref'
  exact derived_pref_irrefl i t h _ h_pref'


theorem action_implies_branching_universe (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_act : DoxasticAppraisalCertificate i t H_t h) :
    ∃ h₀ ∈ H_t, h₀ ≠ h ∧ enacted i t h₀ = α₀ ∧ enacted i t h ≠ α₀ := by
  have ⟨_, _, _, ⟨h₀, hh₀_in, h_en_h₀⟩, _, _, _⟩ := h_act
  have ⟨h_en_ne_α₀, _⟩ := doxastic_action_non_passive i t H_t h h_act
  have h_ne : h₀ ≠ h := by
    intro h_eq
    subst h_eq
    rw [h_en_h₀] at h_en_ne_α₀
    exact h_en_ne_α₀ rfl
  exact ⟨h₀, hh₀_in, h_ne, h_en_h₀, h_en_ne_α₀⟩

/-- An assertion with the listed belief, response, and preference conditions. -/
structure DoxasticDeliberativeEpistemicAssertion
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (P : History → Prop) (α_assert : Action) : Prop where
  in_bundle : h ∈ H_t
  enacted_assert : enacted i t h = α_assert
  not_a0 : α_assert ≠ α₀
  cont_assert : α_assert ∈ A_feas i t h
  cont_a0 : α₀ ∈ A_feas i t h
  pl_nonempty : (MinPlausible i t).Nonempty
  belief : ∀ h' ∈ MinPlausible i t, P h'
  reason_resp : ∀ h' ∈ H_t, ¬ P h' → enacted i t h' = α₀
  falsifying_branch : ∃ h_f ∈ H_t, ¬ P h_f
  pref_veri : ∀ h' ∈ MinPlausible i t, P h' →
    Preference i t h (MaturationEnd i α_assert t h') (MaturationEnd i α₀ t h')
  undom_alt : ∀ β ∈ A_feas i t h,
    ¬ ∀ h' ∈ MinPlausible i t,
      Preference i t h (MaturationEnd i β t h') (MaturationEnd i α_assert t h')

/-- The assertion conditions imply `DoxasticAppraisalCertificate`. -/
theorem doxastic_purposeful_act_of_deliberative_assertion
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (P : History → Prop) (α_assert : Action)
    (h_delib : DoxasticDeliberativeEpistemicAssertion i t H_t h P α_assert) :
    DoxasticAppraisalCertificate i t H_t h := by
  have ⟨h_f, hh_f, h_not_P_f⟩ := h_delib.falsifying_branch
  have h_refrain : enacted i t h_f = α₀ := h_delib.reason_resp h_f hh_f h_not_P_f
  have h_branch_feas : BranchFeas i t H_t α₀ := ⟨h_f, hh_f, h_refrain⟩
  refine ⟨h_delib.in_bundle, ?_, h_delib.cont_a0, h_branch_feas, h_delib.pl_nonempty, ?_, ?_⟩
  · rw [h_delib.enacted_assert]
    exact h_delib.cont_assert
  · intro h' hh'
    rw [h_delib.enacted_assert]
    exact h_delib.pref_veri h' hh' (h_delib.belief h' hh')
  · intro β hβ
    rw [h_delib.enacted_assert]
    exact h_delib.undom_alt β hβ


structure StructuralIntrospection
    (i : Agent) (t : Moment) (H_t : Set History) (h : History) : Prop where
  pl_in_bundle : ∀ h' ∈ MinPlausible i t, h' ∈ H_t
  act_introspection : ∀ h' ∈ MinPlausible i t, enacted i (tau i t h') h' = enacted i t h
  cont_introspection : ∀ h' ∈ MinPlausible i t, A_feas i (tau i t h') h' = A_feas i t h
  branch_introspection : ∀ h' ∈ MinPlausible i t, BranchFeas i (tau i t h') H_t α₀

structure EvaluativeIntrospection
    (i : Agent) (t : Moment) (H_t : Set History) (h : History) : Prop where
  pref_introspection : ∀ h' ∈ MinPlausible i t, Preference i (tau i t h') h' = Preference i t h
  eval_introspection : ∀ h' ∈ MinPlausible i t, ∀ α β,
    (∀ h'' ∈ MinPlausible i (tau i t h'),
      Preference i (tau i t h') h' (MaturationEnd i α (tau i t h') h'')
        (MaturationEnd i β (tau i t h') h'')) ↔
    (∀ h'' ∈ MinPlausible i t, Preference i t h (MaturationEnd i α t h'') (MaturationEnd i β t h''))

structure InternalDoxasticCoherence
    (i : Agent) (t : Moment) (H_t : Set History) (h : History) : Prop
    extends StructuralIntrospection i t H_t h, EvaluativeIntrospection i t H_t h


theorem doxastic_purposeful_act_of_internal_coherence
    (i : Agent) (t : Moment) (H_t : Set History) (h : History) (h_pl : History)
    (h_coh : InternalDoxasticCoherence i t H_t h)
    (hh_pl : h_pl ∈ MinPlausible i t)
    (h_purp : DoxasticAppraisalCertificate i t H_t h) :
    DoxasticAppraisalCertificate i (tau i t h_pl) H_t h_pl := by
  have ⟨_, h_act_cont, h_a0_cont, _, _, h_unease, h_undom⟩ := h_purp
  refine ⟨h_coh.pl_in_bundle h_pl hh_pl, ?_, ?_, h_coh.branch_introspection h_pl hh_pl,
          min_plausible_nonempty i (tau i t h_pl), ?_, ?_⟩
  · rw [h_coh.act_introspection h_pl hh_pl, h_coh.cont_introspection h_pl hh_pl]
    exact h_act_cont
  · rw [h_coh.cont_introspection h_pl hh_pl]
    exact h_a0_cont
  · rw [h_coh.act_introspection h_pl hh_pl]
    exact (h_coh.eval_introspection h_pl hh_pl (enacted i t h) α₀).mpr h_unease
  · intro β hβ h_all
    rw [h_coh.cont_introspection h_pl hh_pl] at hβ
    apply h_undom β hβ
    rw [h_coh.act_introspection h_pl hh_pl] at h_all
    exact (h_coh.eval_introspection h_pl hh_pl β (enacted i t h)).mp h_all


theorem deliberative_doxastic_action_denial_self_falsifying
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (α_assert : Action)
    (h_coh : InternalDoxasticCoherence i t H_t h)
    (h_delib : DoxasticDeliberativeEpistemicAssertion i t H_t h
      (fun h' => ¬ DoxasticAppraisalCertificate i (tau i t h') H_t h') α_assert) :
    False := by
  have h_act : DoxasticAppraisalCertificate i t H_t h :=
    doxastic_purposeful_act_of_deliberative_assertion i t H_t h
      (fun h' => ¬ DoxasticAppraisalCertificate i (tau i t h') H_t h') α_assert h_delib
  obtain ⟨h_pl, hh_pl⟩ := h_delib.pl_nonempty
  have h_believed_neg : ¬ DoxasticAppraisalCertificate i (tau i t h_pl) H_t h_pl :=
    h_delib.belief h_pl hh_pl
  have h_pl_purp : DoxasticAppraisalCertificate i (tau i t h_pl) H_t h_pl :=
    doxastic_purposeful_act_of_internal_coherence i t H_t h h_pl h_coh hh_pl h_act
  exact h_believed_neg h_pl_purp


theorem deliberative_doxastic_global_action_denial_self_falsifying
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (α_assert : Action)
    (h_delib : DoxasticDeliberativeEpistemicAssertion i t H_t h
      (fun _ => ∀ h_act ∈ H_t, ¬ DoxasticAppraisalCertificate i t H_t h_act) α_assert) :
    False := by
  have h_act : DoxasticAppraisalCertificate i t H_t h :=
    doxastic_purposeful_act_of_deliberative_assertion i t H_t h
      (fun _ => ∀ h_act ∈ H_t, ¬ DoxasticAppraisalCertificate i t H_t h_act) α_assert h_delib
  obtain ⟨h_pl, hh_pl⟩ := h_delib.pl_nonempty
  have h_denial_all : ∀ h_act ∈ H_t, ¬ DoxasticAppraisalCertificate i t H_t h_act :=
    h_delib.belief h_pl hh_pl
  exact h_denial_all h h_delib.in_bundle h_act


theorem prerequisite_action_blocks_downstream_completion
    (i : Agent) (t t' : Moment) (H_t'_cf : Set History)
    (α_build α_consume β_down : Action)
    (h_requires : ∀ h', enacted i t' h' = β_down → enacted i t h' = α_build)
    (h_cf_subset : H_t'_cf ⊆ ChoiceCell i t α_consume)
    (h_distinct : α_consume ≠ α_build) :
    ¬ BranchFeas i t' H_t'_cf β_down := by
  rintro ⟨h', hh'_in, (h_down : enacted i t' h' = β_down)⟩
  have h_cell := h_cf_subset hh'_in
  dsimp [ChoiceCell] at h_cell
  have h_built := h_requires h' h_down
  rw [h_cell] at h_built
  exact h_distinct h_built


theorem doxastic_unanimous_undominated_of_purposeful_act
    (i : Agent) (t : Moment) (h : History)
    (h_projected : ActionFrame.ProjectedFeasibility F)
    (h_act : PurposefulAct i t h (enacted i t h)) :
    ∀ β ∈ A_feas i t h,
      ¬ ∀ h' ∈ MinPlausible i t,
        Preference i t h
          (MaturationEnd i β t h')
          (MaturationEnd i (enacted i t h) t h') := by
  intro β hβ h_all
  have h_unan : ActionFrame.UnanimousDominates F i t h (MinPlausible i t) β (enacted i t h) := h_all
  have h_beta_app : F.ProjectedAppraisable i t β := by
    intro h' hh'
    exact projected_feasibility h_projected i t h h' β h_act.2.1.1 hh' hβ
  have h_enacted_app : F.ProjectedAppraisable i t (enacted i t h) := by
    intro h' hh'
    exact projected_feasibility h_projected i t h h' (enacted i t h) h_act.2.1.1 hh' h_act.1
  have h_pref := ActionFrame.doxastic_unanimous_bridge F i β (enacted i t h) t h
    ⟨h_beta_app, h_enacted_app⟩ h_unan
  exact h_act.2.2.2 β hβ h_pref


theorem plausible_support_doxastic_of_purposeful_act
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_in : h ∈ H_t)
    (h_base : α₀ ∈ A_feas i t h)
    (h_branch : BranchFeas i t H_t α₀)
    (h_projected : ActionFrame.ProjectedFeasibility F)
    (h_act : ActivePurposefulAct i t h (enacted i t h)) :
    PlausibleSupportAppraisalCertificate i t H_t h := by
  refine ⟨h_in, h_act.1.1, h_base, h_branch, F.min_plausible_nonempty i t, ?_, ?_, ?_⟩
  · have h_pref := h_act.2
    have h_app : ∀ h' ∈ MinPlausible i t,
        (enacted i t h) ∈ A_feas i (tau i t h') h' ∧ α₀ ∈ A_feas i (tau i t h') h' := by
      intro h' hh'
      exact ⟨projected_feasibility h_projected i t h h' (enacted i t h)
        h_act.1.2.1.1 hh' h_act.1.1,
        projected_feasibility h_projected i t h h' α₀ h_act.1.2.1.1 hh' h_base⟩
    obtain ⟨h_wit, hh_wit, h_wit_pref⟩ := F.doxastic_plausible_support
      i (enacted i t h) α₀ t h h_app h_pref
    exact ⟨h_wit, hh_wit, h_wit_pref⟩
  · intro β hβ h_wp
    have h_beta_app : F.ProjectedAppraisable i t β := by
      intro h' hh'
      exact projected_feasibility h_projected i t h h' β h_act.1.2.1.1 hh' hβ
    have h_enacted_app : F.ProjectedAppraisable i t (enacted i t h) := by
      intro h' hh'
      exact projected_feasibility h_projected i t h h' (enacted i t h)
        h_act.1.2.1.1 hh' h_act.1.1
    have h_pref := ActionFrame.doxastic_weak_pareto_bridge F i β (enacted i t h) t h
      ⟨h_beta_app, h_enacted_app⟩ h_wp
    exact h_act.1.2.2.2 β hβ h_pref
  · exact doxastic_unanimous_undominated_of_purposeful_act i t h h_projected h_act.1


theorem purposeful_act_of_doxastic_dominance
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_mem : t ∈ h)
    (h_projected : ActionFrame.ProjectedFeasibility F)
    (h_app : F.IsUnanimousAppraisal i t h)
    (h_dox : DoxasticAppraisalCertificate i t H_t h) :
    PurposefulAct i t h (enacted i t h) := by
  have ⟨_h_in, h_feas, _h_base_feas, _h_branch_feas, _h_nonempty, h_unease, h_undom⟩ := h_dox
  have h_enacted_app : F.ProjectedAppraisable i t (enacted i t h) := by
    intro h' hh'
    exact projected_feasibility h_projected i t h h' (enacted i t h) h_mem hh' h_feas
  have h_base_app : F.ProjectedAppraisable i t α₀ := by
    intro h' hh'
    exact projected_feasibility h_projected i t h h' α₀ h_mem hh' _h_base_feas
  refine ⟨h_feas, ⟨h_mem, rfl⟩, ?_, ?_⟩
  · right
    exact ActionFrame.doxastic_unanimous_bridge F i (enacted i t h) α₀ t h
      ⟨h_enacted_app, h_base_app⟩ h_unease
  · intro β hβ h_pref
    have h_beta_app : F.ProjectedAppraisable i t β := by
      intro h' hh'
      exact projected_feasibility h_projected i t h h' β h_mem hh' hβ
    have h_unan := h_app β (enacted i t h) h_beta_app h_enacted_app h_pref
    exact h_undom β hβ h_unan


theorem doxastic_dominance_of_purposeful_act
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_in : h ∈ H_t)
    (h_base : α₀ ∈ A_feas i t h)
    (h_branch : BranchFeas i t H_t α₀)
    (h_projected : ActionFrame.ProjectedFeasibility F)
    (h_app : F.IsUnanimousAppraisal i t h)
    (h_act : PurposefulAct i t h (enacted i t h))
    (h_unease : Preference i t h (End_of i (enacted i t h) t h) (End_of i α₀ t h)) :
    DoxasticAppraisalCertificate i t H_t h := by
  refine ⟨h_in, h_act.1, h_base, h_branch, F.min_plausible_nonempty i t, ?_, ?_⟩
  · have h_enacted_app : F.ProjectedAppraisable i t (enacted i t h) := by
      intro h' hh'
      exact projected_feasibility h_projected i t h h' (enacted i t h) h_act.2.1.1 hh' h_act.1
    have h_base_app : F.ProjectedAppraisable i t α₀ := by
      intro h' hh'
      exact projected_feasibility h_projected i t h h' α₀ h_act.2.1.1 hh' h_base
    exact h_app (enacted i t h) α₀ h_enacted_app h_base_app h_unease
  · exact doxastic_unanimous_undominated_of_purposeful_act i t h h_projected h_act


theorem doxastic_dominance_of_purposeful_act_singleton
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_in : h ∈ H_t)
    (h_base : α₀ ∈ A_feas i t h)
    (h_branch : BranchFeas i t H_t α₀)
    (h_pl : History)
    (h_singleton : MinPlausible i t = {h_pl})
    (h_projected : ActionFrame.ProjectedFeasibility F)
    (h_act : PurposefulAct i t h (enacted i t h))
    (h_unease : Preference i t h (End_of i (enacted i t h) t h) (End_of i α₀ t h)) :
    DoxasticAppraisalCertificate i t H_t h :=
  doxastic_dominance_of_purposeful_act i t H_t h h_in h_base h_branch
    h_projected (ActionFrame.is_unanimous_appraisal_of_singleton F i t h h_pl h_singleton)
    h_act h_unease


theorem purposeful_act_iff_doxastic_purposeful_act
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_mem : t ∈ h)
    (h_in : h ∈ H_t)
    (h_base : α₀ ∈ A_feas i t h)
    (h_branch : BranchFeas i t H_t α₀)
    (h_projected : ActionFrame.ProjectedFeasibility F)
    (h_app : F.IsUnanimousAppraisal i t h)
    (h_unease : Preference i t h (End_of i (enacted i t h) t h) (End_of i α₀ t h)) :
    PurposefulAct i t h (enacted i t h) ↔
      DoxasticAppraisalCertificate i t H_t h := by
  constructor
  · intro h_purp
    exact doxastic_dominance_of_purposeful_act i t H_t h h_in h_base h_branch
      h_projected h_app h_purp h_unease
  · intro h_dox
    exact purposeful_act_of_doxastic_dominance i t H_t h h_mem h_projected h_app h_dox

theorem purposeful_act_iff_doxastic_purposeful_act_singleton
    (i : Agent) (t : Moment) (H_t : Set History) (h : History)
    (h_mem : t ∈ h)
    (h_in : h ∈ H_t)
    (h_base : α₀ ∈ A_feas i t h)
    (h_branch : BranchFeas i t H_t α₀)
    (h_pl : History)
    (h_singleton : MinPlausible i t = {h_pl})
    (h_projected : ActionFrame.ProjectedFeasibility F)
    (h_unease : Preference i t h (End_of i (enacted i t h) t h) (End_of i α₀ t h)) :
    PurposefulAct i t h (enacted i t h) ↔
      DoxasticAppraisalCertificate i t H_t h :=
  purposeful_act_iff_doxastic_purposeful_act i t H_t h h_mem h_in h_base h_branch
    h_projected (ActionFrame.is_unanimous_appraisal_of_singleton F i t h h_pl h_singleton) h_unease


end DoxasticActionFrames

/-- A two-branch example where introspective coherence and an assertion of the
actual-history proposition are jointly satisfiable. -/
theorem two_history_doxastic_non_vacuity :
    ∃ (i : SubjectiveBilateralTradeActionFrame.Agent)
      (t : SubjectiveBilateralTradeActionFrame.Moment)
      (H_t : Set SubjectiveBilateralTradeActionFrame.History)
      (h : SubjectiveBilateralTradeActionFrame.History)
      (α : SubjectiveBilateralTradeActionFrame.Action),
      @InternalDoxasticCoherence SubjectiveBilateralTradeActionFrame i t H_t h ∧
      @DoxasticDeliberativeEpistemicAssertion SubjectiveBilateralTradeActionFrame i t H_t h
        (fun h' => h' = h) α := by
  let : ActionFrame := SubjectiveBilateralTradeActionFrame
  let i : Fin 2 := 0
  let t : BilateralMoment := .root
  let H_t : Set (Fin 4) := {(2 : Fin 4), 3}
  let h : Fin 4 := 3
  let α : ModelAction := ModelAction.offer 0 1 1 0 1 1
  have h_min : SubjectiveBilateralTradeActionFrame.MinPlausible i t =
      ({(3 : Fin 4)} : Set (Fin 4)) := by
    rfl
  refine ⟨i, t, H_t, h, α, ?_, ?_⟩
  · have h_struct : @StructuralIntrospection SubjectiveBilateralTradeActionFrame i t H_t h := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h' hh'
        change h' ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t at hh'
        rw [h_min] at hh'
        have hh3 : h' = (3 : Fin 4) := by simpa using hh'
        subst h'
        simp [H_t]
      · intro h' hh'
        change h' ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t at hh'
        rw [h_min] at hh'
        have hh3 : h' = (3 : Fin 4) := by simpa using hh'
        subst h'
        rfl
      · intro h' hh'
        change h' ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t at hh'
        rw [h_min] at hh'
        have hh3 : h' = (3 : Fin 4) := by simpa using hh'
        subst h'
        rfl
      · intro h' hh'
        refine ⟨(2 : Fin 4), ?_, ?_⟩
        · simp [H_t]
        · change SubjectiveBilateralTradeActionFrame.enacted i
            (SubjectiveBilateralTradeActionFrame.tau i t h') (2 : Fin 4) =
              SubjectiveBilateralTradeActionFrame.alpha_zero
          change bilateral_enacted i
            (SubjectiveBilateralTradeActionFrame.tau i t h') (2 : Fin 4) =
              ModelAction.idle
          cases SubjectiveBilateralTradeActionFrame.tau i t h' <;> rfl
    have h_eval : EvaluativeIntrospection i t H_t h := by
      refine ⟨?_, ?_⟩
      · intro h' hh'
        change h' ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t at hh'
        rw [h_min] at hh'
        have hh3 : h' = (3 : Fin 4) := by simpa using hh'
        subst h'
        rfl
      · intro h' hh' α' β
        change h' ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t at hh'
        rw [h_min] at hh'
        have hh3 : h' = (3 : Fin 4) := by simpa using hh'
        subst h'
        constructor <;> intro hall h'' hh'' <;> exact hall h'' hh''
    exact ⟨h_struct, h_eval⟩
  · have h_pref : SubjectiveBilateralTradeActionFrame.Preference i t h
        (SubjectiveBilateralTradeActionFrame.MaturationEnd i α t (3 : Fin 4))
        (SubjectiveBilateralTradeActionFrame.MaturationEnd i
          SubjectiveBilateralTradeActionFrame.alpha_zero t (3 : Fin 4)) := by
      have h_offer : SubjectiveBilateralTradeActionFrame.MaturationEnd i α t (3 : Fin 4) =
          SubjectiveBilateralTradeActionFrame.BundleEnd
            (bilateral_omega i .leaf3 3) := by
        change bilateral_subjective_outcome i α t
          (bilateral_subjective_maturation i α t (bilateral_sigma i t α (3 : Fin 4)))
          (bilateral_sigma i t α (3 : Fin 4)) = BilateralEnd.bundle _
        simp [bilateral_subjective_maturation, bilateral_subjective_outcome,
          bilateral_terminal_moment, bilateral_sigma, i, t, α]
      have h_idle : SubjectiveBilateralTradeActionFrame.MaturationEnd i
          SubjectiveBilateralTradeActionFrame.alpha_zero t (3 : Fin 4) =
          SubjectiveBilateralTradeActionFrame.BundleEnd
            (bilateral_omega i .root 3) := by
        change bilateral_subjective_outcome i (ModelAction.idle) t
          (bilateral_subjective_maturation i (ModelAction.idle) t
            (bilateral_sigma i t ModelAction.idle (3 : Fin 4)))
          (bilateral_sigma i t ModelAction.idle (3 : Fin 4)) = BilateralEnd.bundle _
        simp only [bilateral_subjective_outcome, Fin.isValue, bilateral_subjective_maturation,
          bilateral_terminal_moment, bilateral_sigma, ↓reduceIte, reduceCtorEq, Fin.reduceEq,
          or_true, Fin.coe_ofNat_eq_mod, Nat.reduceMod, BilateralEnd.bundle.injEq, i, t]
        funext m
        fin_cases m <;> simp [bilateral_omega]
      rw [h_offer, h_idle]
      exact SubjectiveBilateralTradeActionFrame.teleological_bundle_dominance_induces_preference
        i t h _ _ (bilateral_subjective_trade_dominance i)
    refine {
      in_bundle := by simp [H_t, h]
      enacted_assert := by decide
      not_a0 := by decide
      cont_assert := by decide
      cont_a0 := by decide
      pl_nonempty := by
        change (SubjectiveBilateralTradeActionFrame.MinPlausible i t).Nonempty
        rw [h_min]
        simp
      belief := ?_
      reason_resp := ?_
      falsifying_branch := ⟨(2 : Fin 4), by simp [H_t], by decide⟩
      pref_veri := ?_
      undom_alt := ?_ }
    · intro h' hh'
      change h' ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t at hh'
      rw [h_min] at hh'
      simpa [h] using hh'
    · intro h' hh' hnot
      have hh2 : h' = (2 : Fin 4) := by
        simp only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff, H_t] at hh'
        simp only [Fin.isValue, h] at hnot
        rcases hh' with hh2 | hh3
        · exact hh2
        · exact (hnot hh3).elim
      subst h'
      change SubjectiveBilateralTradeActionFrame.enacted i t (2 : Fin 4) =
        SubjectiveBilateralTradeActionFrame.alpha_zero
      decide
    · intro h' hh' hp
      change h' ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t at hh'
      rw [h_min] at hh'
      have hh3 : h' = (3 : Fin 4) := by simpa using hh'
      subst h'
      change SubjectiveBilateralTradeActionFrame.Preference i t h
        (SubjectiveBilateralTradeActionFrame.MaturationEnd i α t (3 : Fin 4))
        (SubjectiveBilateralTradeActionFrame.MaturationEnd i
          SubjectiveBilateralTradeActionFrame.alpha_zero t (3 : Fin 4))
      exact h_pref
    · intro β hβ hne
      have h_cases : β = ModelAction.idle ∨ β = α := by
        change β ∈ ({ModelAction.idle, ModelAction.offer 0 1 1 0 1 1} : Finset ModelAction) at hβ
        simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
        simpa [α] using hβ
      rcases h_cases with h_idle | h_offer
      · subst β
        have h_rev := hne (3 : Fin 4) (by
          change (3 : Fin 4) ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t
          rw [h_min]
          simp)
        change SubjectiveBilateralTradeActionFrame.Preference i t h
          (SubjectiveBilateralTradeActionFrame.MaturationEnd i
            SubjectiveBilateralTradeActionFrame.alpha_zero t (3 : Fin 4))
          (SubjectiveBilateralTradeActionFrame.MaturationEnd i α t (3 : Fin 4)) at h_rev
        exact (SubjectiveBilateralTradeActionFrame.pref_asymm i t h h_pref) h_rev
      · have h_same := hne (3 : Fin 4) (by
          change (3 : Fin 4) ∈ SubjectiveBilateralTradeActionFrame.MinPlausible i t
          rw [h_min]
          simp)
        change SubjectiveBilateralTradeActionFrame.Preference i t h
          (SubjectiveBilateralTradeActionFrame.MaturationEnd i β t (3 : Fin 4))
          (SubjectiveBilateralTradeActionFrame.MaturationEnd i α t (3 : Fin 4)) at h_same
        have h_same' : SubjectiveBilateralTradeActionFrame.Preference i t h
            (SubjectiveBilateralTradeActionFrame.MaturationEnd i α t (3 : Fin 4))
            (SubjectiveBilateralTradeActionFrame.MaturationEnd i α t (3 : Fin 4)) := by
          simpa [h_offer] using h_same
        exact (SubjectiveBilateralTradeActionFrame.pref_asymm i t h h_same') h_same'


end Praxeology

end
