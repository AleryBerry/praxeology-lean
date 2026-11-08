/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Marginal.AllocationChoice

/-!
# A stocked allocation choice inside an ActionFrame

This finite branching frame gives two agents the same three ranked uses and
the same ordinal ranking, while their focal stocks are one and two units.
Allocation ends are kept distinct from the physical inputs used to attain
them. The purposeful choices below are selected by ordinal choice and proved
undominated; no optimum relation is built into the frame.
-/

@[expose] public section

namespace Praxeology

namespace AllocationActionFrame

abbrev Agent := Fin 2
abbrev Means := Fin 1
abbrev Use := Fin 3
abbrev Allocation := Finset Use

inductive Action where
  | idle : Action
  | allocate : Allocation → Action
  | offer (i j : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action
  | accept (j i : Agent) (qA : ℕ) (mA : Means) (qB : ℕ) (mB : Means) : Action
  deriving DecidableEq, Inhabited

def stock : Agent → ℕ
  | 0 => 1
  | _ => 2

def useWeight (r : Use) : ℕ := 3 - r.val

def allocationScore (S : Allocation) : ℕ :=
  10 * (S.card + S.sum useWeight)

def actionUse : Action → Means → ℕ
  | .idle, _ => 0
  | .allocate S, _ => S.card
  | .offer _ _ qA mA _ _, m => if m = mA then qA else 0
  | .accept _ _ _ _ qB mB, m => if m = mB then qB else 0

def actionYield : Action → Means → ℕ
  | .idle, _ => 0
  | .allocate _, _ => 0
  | .offer _ _ _ _ qB mB, m => if m = mB then qB else 0
  | .accept _ _ qA mA _ _, m => if m = mA then qA else 0

def allocationMenu : Finset Action :=
  insert .idle (Finset.univ.image Action.allocate)

def feasibleMenu (i : Agent) : Finset Action :=
  allocationMenu.filter (fun a => ∀ m, actionUse a m ≤ stock i)

def profileValid (p : Action × Action) : Prop :=
  p.1 ∈ feasibleMenu 0 ∧ p.2 ∈ feasibleMenu 1

abbrev History := {p : Action × Action // profileValid p}
abbrev Moment := Option History

inductive End where
  | baseline : End
  | use : Use → End
  | allocation : Allocation → End
  | bundle : (Means → ℕ) → End
  | quantity : Means → ℕ → End
  | timed : End → Moment → End
  deriving DecidableEq, Inhabited

def endScore : End → ℕ
  | .baseline => 0
  | .use r => 100 + useWeight r
  | .allocation S => allocationScore S
  | .bundle b => 10 * b 0
  | .quantity _ q => 100 * q
  | .timed e _ => endScore e

def requirement : End → Means → ℕ
  | .baseline, _ => 0
  | .use _, _ => 1
  | .allocation S, _ => S.card
  | .bundle b, m => b m
  | .quantity m q, m' => if m = m' then q else 0
  | .timed e _, m => requirement e m

def profileAction (i : Agent) (p : Action × Action) : Action :=
  if i = 0 then p.1 else p.2

def updateProfile (i : Agent) (a : Action) (p : Action × Action) : Action × Action :=
  if i = 0 then (a, p.2) else (p.1, a)

theorem updateProfile_valid (i : Agent) (a : Action) (h : History)
    (ha : a ∈ feasibleMenu i) : profileValid (updateProfile i a h.1) := by
  fin_cases i
  · exact ⟨ha, h.2.2⟩
  · exact ⟨h.2.1, ha⟩

def updateHistory (i : Agent) (a : Action) (h : History)
    (ha : a ∈ feasibleMenu i) : History :=
  ⟨updateProfile i a h.1, updateProfile_valid i a h ha⟩

def precedence (t u : Moment) : Prop := t = none ∧ u.isSome

def inHistory (t : Moment) (h : History) : Prop := t = none ∨ t = some h

def profileMoment (h : History) : Moment := some h

def endOfAction : Action → End
  | .idle => .allocation ∅
  | .allocate S => .allocation S
  | .offer .. => .baseline
  | .accept .. => .baseline

def preference (_i : Agent) (_t : Moment) (_h : History) (e₁ e₂ : End) : Prop :=
  endScore e₂ < endScore e₁

/-- This purposeful allocation frame makes timed ends date-neutral. It is a
countermodel to deriving universal strict preference for earlier realization
from purposeful choice and feasibility alone. -/
theorem timed_end_preference_is_date_neutral
    (i : Agent) (t : Moment) (h : History) (e : End) (τ₁ τ₂ : Moment) :
    ¬ preference i t h (.timed e τ₁) (.timed e τ₂) ∧
      ¬ preference i t h (.timed e τ₂) (.timed e τ₁) := by
  simp [preference, endScore]

def canonicalHistory : History := by
  refine ⟨(.idle, .idle), ?_⟩
  constructor <;> simp [feasibleMenu, allocationMenu, actionUse, stock]

def plausibleHistory : Moment → History
  | none => canonicalHistory
  | some h => h

def branchSelection (i : Agent) (t : Moment) (a : Action) (h : History) : History :=
  if t = none then
    if ha : a ∈ feasibleMenu i then updateHistory i a h ha else h
  else h

private theorem mem_allocationMenu_not_trade (a : Action) (ha : a ∈ allocationMenu)
    (htrade : (∃ i j qA mA qB mB, a = Action.offer i j qA mA qB mB) ∨
      (∃ j i qA mA qB mB, a = Action.accept j i qA mA qB mB)) : False := by
  simp only [allocationMenu, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at ha
  rcases ha with rfl | ⟨S, rfl⟩
  · rcases htrade with ⟨i, j, qA, mA, qB, mB, h⟩ | ⟨j, i, qA, mA, qB, mB, h⟩ <;> cases h
  · rcases htrade with ⟨i, j, qA, mA, qB, mB, h⟩ | ⟨j, i, qA, mA, qB, mB, h⟩ <;> cases h

private theorem feasibleMenu_spec (i : Agent) (a : Action) :
    a ∈ feasibleMenu i ↔ a ∈ allocationMenu ∧ ∀ m, actionUse a m ≤ stock i := by
  simp [feasibleMenu, Finset.mem_filter]

private theorem profileAction_feasible (i : Agent) (h : History) :
    profileAction i h.1 ∈ feasibleMenu i := by
  fin_cases i
  · simpa [profileAction] using h.2.1
  · simpa [profileAction] using h.2.2

private theorem next_is_root_leaf {t t' : Moment} {h : History}
    (hn : IsNextMoment precedence inHistory t t' h) : t = none ∧ t' = some h := by
  rcases hn with ⟨_, hmem', hp, _⟩
  cases t with
  | none =>
    cases t' with
    | none => simp [precedence] at hp
    | some h' =>
      have hh : h' = h := by
        have : some h' = some h := by simpa [inHistory] using hmem'
        exact Option.some.inj this
      subst h'
      exact ⟨rfl, rfl⟩
  | some h' => simp [precedence] at hp

@[reducible, instance] def allocationChoiceFrame : ActionFrame where
  Agent := Agent
  Moment := Moment
  History := History
  Action := Action
  Means := Means
  Ends := End
  alpha_zero := .idle
  Precedence := precedence
  moment_lt_irrefl := by
    intro t ht
    cases t <;> simp [precedence] at ht
  moment_lt_trans := by
    intro t₁ t₂ t₃ h₁ h₂
    rcases h₁ with ⟨h₁eq, h₂some⟩
    subst t₁
    rcases h₂ with ⟨h₂eq, _⟩
    subst t₂
    simp at h₂some
  backward_linearity := by
    intro t₁ t₂ t₃ h₁ h₂
    change t₁ = none ∧ t₃.isSome at h₁
    change t₂ = none ∧ t₃.isSome at h₂
    rcases h₁ with ⟨rfl, _⟩
    rcases h₂ with ⟨rfl, _⟩
    exact Or.inr (Or.inl rfl)
  mem_hist := inHistory
  moment_in_history := by
    intro t
    cases t with
    | none => exact ⟨canonicalHistory, Or.inl rfl⟩
    | some h => exact ⟨h, Or.inr rfl⟩
  histories_maximal_linear := by
    intro h
    constructor
    · intro t₁ t₂ ht₁ ht₂
      simp only [Set.mem_ofPred_eq, inHistory] at ht₁ ht₂
      rcases ht₁ with rfl | rfl <;> rcases ht₂ with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (by simp [precedence])
      · exact Or.inr (Or.inr (by simp [precedence]))
      · exact Or.inr (Or.inl rfl)
    · intro s hs hsub t ht
      have hroot : none ∈ s := hsub (by simp [inHistory])
      have hleaf : (some h) ∈ s := hsub (by simp [inHistory])
      cases t with
      | none => change inHistory none h; exact Or.inl rfl
      | some h' =>
        have hcmp := hs ht hleaf
        rcases hcmp with hlt | heq | hgt
        · have hbad : ¬ precedence (some h') (some h) := by simp [precedence]
          exact (hbad hlt).elim
        · have hEq : h' = h := Option.some.inj heq
          subst h'
          change inHistory (some h) h
          exact Or.inr rfl
        · have hbad : ¬ precedence (some h) (some h') := by simp [precedence]
          exact (hbad hgt).elim
  histories_extensional := by
    intro h₁ h₂ hsame
    apply Subtype.ext
    have hh : some h₁ = some h₂ := by
      simpa [inHistory] using (hsame (some h₁)).mp (Or.inr rfl)
    exact congrArg Subtype.val (Option.some.inj hh)
  divergent_futures_witness := by
    intro t h₁ h₂ ht₁ ht₂ hne
    cases t with
    | none =>
      refine ⟨some h₁, some h₂, Or.inr rfl, Or.inr rfl, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨rfl, by simp⟩
      · exact ⟨rfl, by simp⟩
      · simp [precedence]
      · intro heq
        exact hne (Option.some.inj heq)
      · simp [precedence]
    | some h =>
      simp [inHistory] at ht₁ ht₂
      have h₁eq : h₁ = h := ht₁.symm
      have h₂eq : h₂ = h := ht₂.symm
      exact (hne (h₁eq.trans h₂eq.symm)).elim
  A_cont := fun _ t _ =>
    if t = none then allocationMenu else {.idle}
  A_cont_bundle_invariant := by
    intro i t h₁ h₂ ht₁ ht₂
    rfl
  alpha_zero_cont := by
    intro i t h
    cases t <;> simp [allocationMenu]
  omega := fun i t h m =>
    match t with
    | none => stock i
    | some h' => stock i - actionUse (profileAction i h'.1) 0
  omega_bundle_invariant := by
    intro i t m h₁ h₂ ht₁ ht₂
    cases t with
    | none => rfl
    | some h =>
      have h₁eq : h₁ = h := by
        have hh : h = h₁ := by simpa [inHistory] using ht₁
        exact hh.symm
      have h₂eq : h₂ = h := by
        have hh : h = h₂ := by simpa [inHistory] using ht₂
        exact hh.symm
      subst h₁eq
      subst h₂eq
      rfl
  use_means := actionUse
  yield_means := actionYield
  use_means_alpha_zero := by intro m; rfl
  yield_means_alpha_zero := by intro m; rfl
  enacted := fun i t h =>
    match t with
    | none => profileAction i h.1
    | some _ => .idle
  enacted_in_A_feas := by
    intro i t h ht
    cases t with
    | none =>
      have hmem := profileAction_feasible i h
      simp only [Finset.mem_filter]
      simpa [feasibleMenu] using hmem
    | some h' =>
      have heq : h' = h := by simpa [inHistory] using ht
      subst h'
      simp only [Finset.mem_filter]
      simp [actionUse]
  no_choice_between_undivided := by
    intro i t u h₁ h₂ ht₁ ht₂ htu hu₁ hu₂
    cases u with
    | none => simp [precedence] at htu
    | some x =>
      have hu1 : h₁ = x := by
        have hx : x = h₁ := by simpa [inHistory] using hu₁
        exact hx.symm
      have hu2 : h₂ = x := by
        have hx : x = h₂ := by simpa [inHistory] using hu₂
        exact hx.symm
      rw [hu1, hu2]
  sigma := branchSelection
  sigma_realization := by
    intro i t h h' a ht hα ht'
    cases t with
    | none =>
      have hα' : a ∈ feasibleMenu i := by
        rw [feasibleMenu, Finset.mem_filter]
        simpa [Finset.mem_filter] using hα
      have hsigma : branchSelection i none a h' = updateHistory i a h' hα' := by
        simp [branchSelection, hα']
      rw [hsigma]
      constructor
      · exact Or.inl rfl
      · change profileAction i (updateProfile i a h'.1) = a
        fin_cases i <;> simp [profileAction, updateProfile]
    | some h₀ =>
      have hh' : h₀ = h' := by simpa [inHistory] using ht'
      have hh' : h' = h₀ := hh'.symm
      subst h'
      simp only [Finset.mem_filter] at hα
      have ha : a = .idle := by simpa using hα.1
      subst a
      exact ⟨ht', by rfl⟩
  sigma_centering := by
    intro i t h' a ht' hen
    cases t with
    | none =>
      have ha : a ∈ feasibleMenu i := by
        have := profileAction_feasible i h'
        have hen' : profileAction i h'.1 = a := by simpa [enacted] using hen
        simpa [hen'] using this
      have hprof : updateProfile i a h'.1 = h'.1 := by
        fin_cases i
        · have hp : h'.1.1 = a := by simpa [enacted, profileAction] using hen
          exact Prod.ext hp.symm rfl
        · have hp : h'.1.2 = a := by simpa [enacted, profileAction] using hen
          exact Prod.ext rfl hp.symm
      change branchSelection i none a h' = h'
      simp [branchSelection, ha, updateHistory, hprof]
    | some h => rfl
  sigma_co_agency := by
    intro i j t h h' a hij ht hα ht'
    cases t with
    | none =>
      have hα' : a ∈ feasibleMenu i := by
        rw [feasibleMenu, Finset.mem_filter]
        simpa [Finset.mem_filter] using hα
      change profileAction j (branchSelection i none a h').1 = profileAction j h'.1
      simp only [branchSelection, updateHistory, updateProfile, profileAction,
        dite_eq_left hα']
      fin_cases i <;> fin_cases j <;> simp_all
    | some h₀ => rfl
  Offer := Action.offer
  Accept := Action.accept
  use_means_offer := by intros; rfl
  yield_means_offer := by intros; rfl
  use_means_accept := by intros; rfl
  yield_means_accept := by intros; rfl
  offer_inj := by
    intro i₁ j₁ qA₁ mA₁ qB₁ mB₁ i₂ j₂ qA₂ mA₂ qB₂ mB₂ h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  accept_inj := by
    intro j₁ i₁ qA₁ mA₁ qB₁ mB₁ j₂ i₂ qA₂ mA₂ qB₂ mB₂ h
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  offer_ne_accept := by intros i j qA mA qB mB j' i' qA' mA' qB' mB' h; cases h
  alpha_zero_ne_offer := by intros i j qA mA qB mB h; cases h
  alpha_zero_ne_accept := by intros j i qA mA qB mB h; cases h
  law_in_re_transition := by
    intro i t t' h a m hnontrade hen hnext
    have ⟨ht, ht'⟩ := next_is_root_leaf hnext
    subst t
    subst t'
    cases a with
    | idle =>
      have hact : profileAction i h.1 = .idle := by simpa [enacted] using hen
      change (stock i - actionUse (profileAction i h.1) 0) +
          actionUse .idle m =
        stock i + actionYield .idle m
      rw [hact]
      fin_cases m
      simp [actionUse, actionYield]
    | allocate S =>
      have hact : profileAction i h.1 = .allocate S := by simpa [enacted] using hen
      have hmem := profileAction_feasible i h
      have hcost : S.card ≤ stock i := by
        have hmem' : Action.allocate S ∈ feasibleMenu i := by simpa [hact] using hmem
        have hspec := (feasibleMenu_spec i _).mp hmem'
        have hc := hspec.2 0
        simpa [actionUse] using hc
      change (stock i - actionUse (profileAction i h.1) 0) +
          actionUse (.allocate S) m =
        stock i + actionYield (.allocate S) m
      fin_cases m
      rw [hact]
      simp [actionUse, actionYield]
      omega
    | offer i' j qA mA qB mB =>
      have htrade : (∃ i₀ j₀ qA₀ mA₀ qB₀ mB₀,
          Action.offer i' j qA mA qB mB = Action.offer i₀ j₀ qA₀ mA₀ qB₀ mB₀) :=
        ⟨i', j, qA, mA, qB, mB, rfl⟩
      exact False.elim (hnontrade (Or.inl htrade))
    | accept j i' qA mA qB mB =>
      have htrade : (∃ j₀ i₀ qA₀ mA₀ qB₀ mB₀,
          Action.accept j i' qA mA qB mB = Action.accept j₀ i₀ qA₀ mA₀ qB₀ mB₀) :=
        ⟨j, i', qA, mA, qB, mB, rfl⟩
      exact False.elim (hnontrade (Or.inr htrade))
  unilateral_offer_noop := by
    intro i j qA mA qB mB t t' h m hOffer hNotAccept hnext
    cases t with
    | none =>
      change profileAction i h.1 = Action.offer i j qA mA qB mB at hOffer
      have hmem : profileAction i h.1 ∈ allocationMenu :=
        (feasibleMenu_spec i _).mp (profileAction_feasible i h) |>.1
      exact False.elim (mem_allocationMenu_not_trade _ hmem
        (Or.inl ⟨i,j,qA,mA,qB,mB,hOffer⟩))
    | some h' =>
      change Action.idle = Action.offer i j qA mA qB mB at hOffer
      cases hOffer
  unilateral_accept_noop := by
    intro j i qA mA qB mB t t' h m hAccept hNotOffer hnext
    cases t with
    | none =>
      change profileAction j h.1 = Action.accept j i qA mA qB mB at hAccept
      have hmem : profileAction j h.1 ∈ allocationMenu :=
        (feasibleMenu_spec j _).mp (profileAction_feasible j h) |>.1
      exact False.elim (mem_allocationMenu_not_trade _ hmem
        (Or.inr ⟨j,i,qA,mA,qB,mB,hAccept⟩))
    | some h' =>
      change Action.idle = Action.accept j i qA mA qB mB at hAccept
      cases hAccept
  bilateral_transfer_law := by
    intro i j qA mA qB mB t t' h m hij hOffer hAccept hnext
    cases t with
    | none =>
      change profileAction i h.1 = Action.offer i j qA mA qB mB at hOffer
      have hmem : profileAction i h.1 ∈ allocationMenu :=
        (feasibleMenu_spec i _).mp (profileAction_feasible i h) |>.1
      exact False.elim (mem_allocationMenu_not_trade _ hmem
        (Or.inl ⟨i,j,qA,mA,qB,mB,hOffer⟩))
    | some h' =>
      change Action.idle = Action.offer i j qA mA qB mB at hOffer
      cases hOffer
  MinPlausible := fun _ t => {plausibleHistory t}
  min_plausible_nonempty := by intro i t; exact ⟨plausibleHistory t, by simp⟩
  min_plausible_node_incidence := by
    intro i t h' hh'
    simp only [Set.mem_singleton_iff] at hh'
    subst h'
    cases t <;> simp [plausibleHistory, inHistory]
  requirement := requirement
  ValuedEnd := fun _ _ _ _ => True
  valued_end_bundle_invariant := by intro i t h₁ h₂ e ht₁ ht₂; rfl
  OutcomeOf := fun _ a _ _ _ => endOfAction a
  ExpectedMaturation := fun _ _ t _ => t
  expected_maturation_mem_future := by
    intro i a t h ht hen
    exact ⟨ht, Or.inl rfl⟩
  End_of := fun _ a _ _ => endOfAction a
  End_of_bundle_invariant := by intro i a t h₁ h₂ ht₁ ht₂; rfl
  Preference := preference
  Preference_bundle_invariant := by intro i t h₁ h₂ ht₁ ht₂; rfl
  pref_asymm := by
    intro i t h e₁ e₂ h₁ h₂
    change endScore e₂ < endScore e₁ at h₁
    change endScore e₁ < endScore e₂ at h₂
    omega
  doxastic_sure_thing_bridge := by
    intro i a b t h hfeas hout hstrict
    rcases hstrict with ⟨h', hh', hpref⟩
    change preference i t h (endOfAction a) (endOfAction b) at hpref
    exact hpref
  doxastic_plausible_support := by
    intro i a b t h hfeas hpref
    refine ⟨plausibleHistory t, by simp, ?_⟩
    exact hpref
  BundleEnd := End.bundle
  teleological_bundle_dominance_induces_preference := by
    intro i t h b₁ b₂ hdom
    have hle : b₂ 0 ≤ b₁ 0 := by
      have hsingle : JointlyAttains requirement b₂ {End.bundle b₂} := by
        intro m
        simp [requirement]
      have hlarge := hdom.1 {End.bundle b₂} (fun _ _ => trivial) hsingle
      have h := hlarge 0
      simpa [JointlyAttains, requirement] using h
    have hne : b₁ 0 ≠ b₂ 0 := by
      intro heq
      rcases hdom.2 with ⟨S, _, h₁, h₂⟩
      apply h₂
      intro m
      fin_cases m
      simpa [JointlyAttains, requirement, heq] using h₁ 0
    have hlt : b₂ 0 < b₁ 0 := by omega
    change endScore (End.bundle b₂) < endScore (End.bundle b₁)
    simpa [endScore] using Nat.mul_lt_mul_of_pos_left hlt (by decide : 0 < 10)
  TimedEnd := End.timed
  QuantityEnd := End.quantity
  timed_end_inj := by
    intro e₁ τ₁ e₂ τ₂ h
    cases h
    exact ⟨rfl, rfl⟩
  quantity_end_inj := by
    intro m₁ q₁ m₂ q₂ h
    cases h
    exact ⟨rfl, rfl⟩

end AllocationActionFrame

def allocationFrameTechnology :
    HomogeneousUseTechnology (W := AllocationActionFrame.allocationChoiceFrame)
      (m := (0 : AllocationActionFrame.Means)) (N := 3) where
  useEnd := fun r => AllocationActionFrame.End.use r
  useEnd_injective := by intro r s h; cases h; rfl
  quantum := 1
  quantum_positive := by decide
  requirement_exact := by intro r; rfl

local instance : Fintype AllocationActionFrame.allocationChoiceFrame.Means := by
  change Fintype (Fin 1)
  infer_instance

def allocationFrameEnd (S : AllocationActionFrame.Allocation) :
    AllocationActionFrame.allocationChoiceFrame.Ends :=
  AllocationActionFrame.End.allocation S

theorem allocationFrame_ordinal_laws (i : AllocationActionFrame.Agent)
    (t : AllocationActionFrame.Moment) (h : AllocationActionFrame.History)
    (capacity : ℕ) :
    LocalOrdinalAllocationLaws (W := AllocationActionFrame.allocationChoiceFrame) i t h capacity
      allocationFrameEnd := by
  refine {
    add_unused := ?_
    replace_lower := ?_
    transitive := ?_ }
  · intro S _ r hr
    have hcard : (insert r S).card = S.card + 1 := Finset.card_insert_of_notMem hr
    have hsum : (insert r S).sum AllocationActionFrame.useWeight =
        AllocationActionFrame.useWeight r + S.sum AllocationActionFrame.useWeight :=
      Finset.sum_insert hr
    change 10 * (S.card + S.sum AllocationActionFrame.useWeight) <
      10 * ((insert r S).card + (insert r S).sum AllocationActionFrame.useWeight)
    rw [hcard, hsum]
    have hweight : 0 < AllocationActionFrame.useWeight r := by
      dsimp [AllocationActionFrame.useWeight]
      omega
    omega
  · intro S r s hrs hr hs
    have hrErase : r ∉ S.erase s := by
      intro hm
      exact hr (Finset.mem_of_mem_erase hm)
    have hcard : (insert r (S.erase s)).card = S.card := by
      rw [Finset.card_insert_of_notMem hrErase, Finset.card_erase_of_mem hs]
      have hspos : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
      omega
    have hsumNew : (insert r (S.erase s)).sum AllocationActionFrame.useWeight =
        AllocationActionFrame.useWeight r + (S.erase s).sum AllocationActionFrame.useWeight :=
      Finset.sum_insert hrErase
    have hsumOld : AllocationActionFrame.useWeight s +
        (S.erase s).sum AllocationActionFrame.useWeight =
        S.sum AllocationActionFrame.useWeight :=
      Finset.add_sum_erase S AllocationActionFrame.useWeight hs
    change 10 * (S.card + S.sum AllocationActionFrame.useWeight) <
      10 * ((insert r (S.erase s)).card +
        (insert r (S.erase s)).sum AllocationActionFrame.useWeight)
    rw [hcard, hsumNew, ← hsumOld]
    have hweights : AllocationActionFrame.useWeight r > AllocationActionFrame.useWeight s := by
      dsimp [AllocationActionFrame.useWeight]
      omega
    omega
  · intro e₁ e₂ e₃ h₁₂ h₂₃
    change AllocationActionFrame.endScore e₂ < AllocationActionFrame.endScore e₁ at h₁₂
    change AllocationActionFrame.endScore e₃ < AllocationActionFrame.endScore e₂ at h₂₃
    change AllocationActionFrame.endScore e₃ < AllocationActionFrame.endScore e₁
    omega

def allocationFrameRealize (S : AllocationActionFrame.Allocation) :
    AllocationActionFrame.Action :=
  if S = ∅ then AllocationActionFrame.Action.idle
  else AllocationActionFrame.Action.allocate S

def allocationFrameOfAction : AllocationActionFrame.Action → AllocationActionFrame.Allocation
  | AllocationActionFrame.Action.idle => ∅
  | AllocationActionFrame.Action.allocate S => S
  | AllocationActionFrame.Action.offer .. => ∅
  | AllocationActionFrame.Action.accept .. => ∅

def allocationFrameStockedContext (i : AllocationActionFrame.Agent)
    (h : AllocationActionFrame.History) :
    StockedAllocationContext (W := AllocationActionFrame.allocationChoiceFrame) i none h
      (0 : AllocationActionFrame.Means) allocationFrameTechnology
      (AllocationActionFrame.stock i) where
  capacity_le_N := by fin_cases i <;> decide
  remainder := 0
  remainder_lt_quantum := by
    intro hcap
    fin_cases i <;> decide
  actual_stock := by
    change AllocationActionFrame.stock i = AllocationActionFrame.stock i * 1 + 0
    omega
  allocationEnd := allocationFrameEnd
  bundleStock := fun S m => S.sum (fun r =>
    AllocationActionFrame.allocationChoiceFrame.requirement (AllocationActionFrame.End.use r) m)
  allocation_stock_exact := by intro S m; rfl
  allocationOf := allocationFrameOfAction
  action_end := by
    intro a ha
    change a ∈ AllocationActionFrame.allocationMenu at ha
    change AllocationActionFrame.endOfAction a = allocationFrameEnd (allocationFrameOfAction a)
    simp only [AllocationActionFrame.allocationMenu, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and] at ha
    rcases ha with ha | ⟨S, rfl⟩
    · subst a
      rfl
    · rfl
  action_use_exact := by
    intro a ha m
    change a ∈ AllocationActionFrame.allocationMenu at ha
    change AllocationActionFrame.actionUse a m = (allocationFrameOfAction a).sum
      (fun r => AllocationActionFrame.allocationChoiceFrame.requirement
        (AllocationActionFrame.End.use r) m)
    simp only [AllocationActionFrame.allocationMenu, Finset.mem_insert, Finset.mem_image,
      Finset.mem_univ, true_and] at ha
    rcases ha with ha | ⟨S, rfl⟩
    · subst a
      simp [AllocationActionFrame.actionUse, allocationFrameOfAction]
    · fin_cases m
      change S.card = S.sum (fun r =>
        AllocationActionFrame.requirement (AllocationActionFrame.End.use r) 0)
      simp [AllocationActionFrame.requirement]
  other_stock_suffices := by
    intro S m hne
    fin_cases m
    exact (hne rfl).elim
  realize := allocationFrameRealize
  realize_allocation := by
    intro S
    by_cases hS : S = ∅
    · subst S
      simp [allocationFrameRealize, allocationFrameOfAction]
    · simp [allocationFrameRealize, allocationFrameOfAction, hS]
  realize_contemplated := by
    intro S hS
    change allocationFrameRealize S ∈ AllocationActionFrame.allocationMenu
    by_cases hEmpty : S = ∅
    · subst S
      simp [allocationFrameRealize, AllocationActionFrame.allocationMenu]
    · simp [allocationFrameRealize, hEmpty, AllocationActionFrame.allocationMenu]
  realize_empty_is_passive := by
    change allocationFrameRealize ∅ = AllocationActionFrame.allocationChoiceFrame.alpha_zero
    rfl

def allocationFramePurposeHistory : AllocationActionFrame.History := by
  refine ⟨(AllocationActionFrame.Action.allocate {0},
      AllocationActionFrame.Action.allocate {0, 1}), ?_⟩
  constructor <;> decide

theorem allocationFrame_prefix_is_purposeful
    (i : AllocationActionFrame.Agent) (h : AllocationActionFrame.History)
    (hk : AllocationActionFrame.stock i ≤ 3)
    (hselected : AllocationActionFrame.allocationChoiceFrame.enacted i none h =
      allocationFrameRealize
        (rankedPrefix (AllocationActionFrame.stock i) hk)) :
    PurposefulAct (F := AllocationActionFrame.allocationChoiceFrame) i none h
      (allocationFrameRealize
        (rankedPrefix (AllocationActionFrame.stock i) hk)) := by
  let capacity := AllocationActionFrame.stock i
  let P := rankedPrefix capacity hk
  let α := allocationFrameRealize P
  let C := allocationFrameStockedContext i h
  have hcapacity : capacity = AllocationActionFrame.stock i := rfl
  have hPcard : P.card = capacity := rankedPrefix_card capacity hk
  have hstockpos : 0 < capacity := by
    dsimp [capacity]
    fin_cases i <;> decide
  have hPne : P ≠ ∅ := by
    intro hEmpty
    rw [hEmpty, Finset.card_empty] at hPcard
    omega
  have hαfeas : α ∈ AllocationActionFrame.allocationChoiceFrame.A_feas i none h := by
    have hEnactFeasible := AllocationActionFrame.allocationChoiceFrame.enacted_in_A_feas
      i none h (Or.inl rfl)
    change AllocationActionFrame.allocationChoiceFrame.enacted i none h = α at hselected
    rw [hselected] at hEnactFeasible
    exact hEnactFeasible
  have hPcont : α ∈ AllocationActionFrame.allocationChoiceFrame.A_cont i none h := by
    exact C.realize_contemplated P (by simpa [capacity] using hPcard.le)
  have hαend : AllocationActionFrame.allocationChoiceFrame.End_of i α none h =
      allocationFrameEnd P := by
    calc
      AllocationActionFrame.allocationChoiceFrame.End_of i α none h =
          C.allocationEnd (C.allocationOf α) := C.action_end α hPcont
      _ = allocationFrameEnd P := by
        have hreal : C.allocationOf α = P := by
          change C.allocationOf (C.realize P) = P
          exact C.realize_allocation P
        rw [hreal]
        change allocationFrameEnd P = allocationFrameEnd P
        rfl
  have hpos : 0 < AllocationActionFrame.endScore
      (AllocationActionFrame.End.allocation P) := by
    dsimp [AllocationActionFrame.endScore, AllocationActionFrame.allocationScore]
    rw [hPcard]
    omega
  have hprefBase : AllocationActionFrame.allocationChoiceFrame.Preference i none h
      (AllocationActionFrame.allocationChoiceFrame.End_of i α none h)
      (AllocationActionFrame.allocationChoiceFrame.End_of i
        AllocationActionFrame.allocationChoiceFrame.alpha_zero none h) := by
    change AllocationActionFrame.endScore
        (AllocationActionFrame.allocationChoiceFrame.End_of i
          AllocationActionFrame.allocationChoiceFrame.alpha_zero none h) <
      AllocationActionFrame.endScore
        (AllocationActionFrame.allocationChoiceFrame.End_of i α none h)
    rw [hαend]
    change 0 < AllocationActionFrame.endScore (AllocationActionFrame.End.allocation P)
    exact hpos
  have hpurpose : PurposefulActUnder
      (AllocationActionFrame.allocationChoiceFrame.Preference i none h) i none h α := by
    refine ⟨hαfeas, ?_, Or.inr hprefBase, ?_⟩
    · change h ∈ @ChoicePartition AllocationActionFrame.allocationChoiceFrame i none α
      change AllocationActionFrame.inHistory none h ∧
        AllocationActionFrame.allocationChoiceFrame.enacted i none h = α
      exact ⟨Or.inl rfl, hselected⟩
    · intro β hβ hbetter
      have hβcard := C.feasible_allocation_card_le β hβ
      have hopt := ranked_prefix_optimality hk allocationFrameEnd
        (allocationFrame_ordinal_laws i none h capacity)
        (C.allocationOf β) hβcard
      have hβcont : β ∈ AllocationActionFrame.allocationChoiceFrame.A_cont i none h :=
        (AllocationActionFrame.allocationChoiceFrame.A_feas_coupling i none h β).mp hβ |>.1
      have hβend : AllocationActionFrame.allocationChoiceFrame.End_of i β none h =
          allocationFrameEnd (C.allocationOf β) := C.action_end β hβcont
      rcases hopt with heq | hpreferred
      · change AllocationActionFrame.endScore
            (AllocationActionFrame.allocationChoiceFrame.End_of i α none h) <
          AllocationActionFrame.endScore
            (AllocationActionFrame.allocationChoiceFrame.End_of i β none h) at hbetter
        rw [hαend, hβend, heq] at hbetter
        exact Nat.lt_irrefl _ hbetter
      · have hforward : AllocationActionFrame.allocationChoiceFrame.Preference i none h
            (AllocationActionFrame.allocationChoiceFrame.End_of i α none h)
            (AllocationActionFrame.allocationChoiceFrame.End_of i β none h) := by
          change AllocationActionFrame.endScore
              (AllocationActionFrame.allocationChoiceFrame.End_of i β none h) <
            AllocationActionFrame.endScore
              (AllocationActionFrame.allocationChoiceFrame.End_of i α none h)
          rw [hβend, hαend]
          exact hpreferred
        exact AllocationActionFrame.allocationChoiceFrame.pref_asymm i none h
          hforward hbetter
  simpa [PurposefulAct] using hpurpose

theorem allocationFrame_ranked_prefix_one :
    rankedPrefix 1 (by decide : 1 ≤ 3) = ({0} : Finset (Fin 3)) := by
  ext r
  simp [rankedPrefix]

theorem allocationFrame_ranked_prefix_two :
    rankedPrefix 2 (by decide : 2 ≤ 3) = ({0, 1} : Finset (Fin 3)) := by
  ext r
  simp [rankedPrefix]
  omega

theorem allocationFrame_stock_one_purposeful_prefix :
    PurposefulAct (F := AllocationActionFrame.allocationChoiceFrame) (0 : Fin 2) none
      allocationFramePurposeHistory (allocationFrameRealize ({0} : Finset (Fin 3))) := by
  exact allocationFrame_prefix_is_purposeful (0 : Fin 2) allocationFramePurposeHistory
    (by decide) (by
      change AllocationActionFrame.profileAction (0 : Fin 2)
        allocationFramePurposeHistory.1 = allocationFrameRealize
          (rankedPrefix 1 (by decide))
      rw [allocationFrame_ranked_prefix_one]
      simp [AllocationActionFrame.profileAction, allocationFramePurposeHistory,
        allocationFrameRealize])

theorem allocationFrame_stock_two_purposeful_prefix :
    PurposefulAct (F := AllocationActionFrame.allocationChoiceFrame) (1 : Fin 2) none
      allocationFramePurposeHistory (allocationFrameRealize ({0, 1} : Finset (Fin 3))) := by
  exact allocationFrame_prefix_is_purposeful (1 : Fin 2) allocationFramePurposeHistory
    (by decide) (by
      change AllocationActionFrame.profileAction (1 : Fin 2)
        allocationFramePurposeHistory.1 = allocationFrameRealize
          (rankedPrefix 2 (by decide))
      rw [allocationFrame_ranked_prefix_two]
      simp [AllocationActionFrame.profileAction, allocationFramePurposeHistory,
        allocationFrameRealize])

/-- Two genuinely different stock contexts use one shared technology and
ordinal ranking. Their enacted purposeful allocations are the first use and
the first two uses, and the next marginal end is strictly lower ranked. -/
theorem allocationFrame_comparative_stock_witness :
    AllocationActionFrame.allocationChoiceFrame.omega (0 : Fin 2) none
      allocationFramePurposeHistory (0 : Fin 1) = 1 ∧
    AllocationActionFrame.allocationChoiceFrame.omega (1 : Fin 2) none
      allocationFramePurposeHistory (0 : Fin 1) = 2 ∧
    PurposefulAct (F := AllocationActionFrame.allocationChoiceFrame) (0 : Fin 2) none
      allocationFramePurposeHistory (allocationFrameRealize ({0} : Finset (Fin 3))) ∧
    PurposefulAct (F := AllocationActionFrame.allocationChoiceFrame) (1 : Fin 2) none
      allocationFramePurposeHistory
        (allocationFrameRealize ({0, 1} : Finset (Fin 3))) ∧
    AllocationActionFrame.allocationChoiceFrame.Preference (0 : Fin 2) none
      allocationFramePurposeHistory (AllocationActionFrame.End.use 0)
      (AllocationActionFrame.End.use 1) := by
  refine ⟨?_, ?_, allocationFrame_stock_one_purposeful_prefix,
    allocationFrame_stock_two_purposeful_prefix, ?_⟩
  · change AllocationActionFrame.stock (0 : Fin 2) = 1
    rfl
  · change AllocationActionFrame.stock (1 : Fin 2) = 2
    rfl
  · change AllocationActionFrame.endScore (AllocationActionFrame.End.use 1) <
      AllocationActionFrame.endScore (AllocationActionFrame.End.use 0)
    norm_num [AllocationActionFrame.endScore, AllocationActionFrame.useWeight]

/-- The same frame has a purposeful allocation while leaving an identical
service indifferent across dates. Purposeful choice and feasibility alone do
not imply universal strict preference for earlier realization. -/
theorem purposeful_allocation_coexists_with_date_neutrality :
    PurposefulAct (F := AllocationActionFrame.allocationChoiceFrame)
        (0 : Fin 2) none allocationFramePurposeHistory
        (allocationFrameRealize ({0} : Finset (Fin 3))) ∧
      ¬ AllocationActionFrame.allocationChoiceFrame.Preference (0 : Fin 2) none
        allocationFramePurposeHistory
        (.timed (.use 0) none)
        (.timed (.use 0) (some allocationFramePurposeHistory)) := by
  refine ⟨allocationFrame_stock_one_purposeful_prefix, ?_⟩
  change ¬ AllocationActionFrame.preference (0 : Fin 2) none
    allocationFramePurposeHistory (.timed (.use 0) none)
      (.timed (.use 0) (some allocationFramePurposeHistory))
  exact (AllocationActionFrame.timed_end_preference_is_date_neutral
    (0 : Fin 2) none
    allocationFramePurposeHistory (.use 0) none
    (some allocationFramePurposeHistory)).1

/-- The generic stocked-context theorem produces an executed purposeful
prefix in the existing two-agent frame. Its preference ranking and complete
allocation menu are supplied by the frame above; this theorem adds no
allocation-specific choice premise. -/
theorem allocationFrame_prefix_has_purposeful_execution
    (i : AllocationActionFrame.Agent) (h : AllocationActionFrame.History) :
    ∃ h', AllocationActionFrame.inHistory none h' ∧
      AllocationActionFrame.allocationChoiceFrame.enacted i none h' =
        allocationFrameRealize
          (rankedPrefix (AllocationActionFrame.stock i)
            (by fin_cases i <;> decide)) ∧
      PurposefulAct (F := AllocationActionFrame.allocationChoiceFrame) i none h'
        (allocationFrameRealize
          (rankedPrefix (AllocationActionFrame.stock i)
            (by fin_cases i <;> decide))) := by
  let : ActionFrame := AllocationActionFrame.allocationChoiceFrame
  let C := allocationFrameStockedContext i h
  exact C.ranked_prefix_has_purposeful_execution
    (allocationFrame_ordinal_laws i none h (AllocationActionFrame.stock i))
    (by
      change AllocationActionFrame.inHistory none h
      exact Or.inl rfl)

end Praxeology
