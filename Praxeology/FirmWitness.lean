/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame
public import Praxeology.Action
public import Praxeology.Catallactics
public import Praxeology.Organization
public import Praxeology.FirmBoundary

/-!
# Firm Witness: Concrete Praxeological Workshop Model

This module constructs a finite, concrete model witnessing the contractual
and authority structure of the firm, demonstrating the existence of non-trivial
firm boundaries and transactional equilibria in Lean 4.
-/

@[expose] public section

namespace Praxeology

noncomputable section

inductive WorkshopAgent where
  | entrepreneur : WorkshopAgent
  | operator : WorkshopAgent
  | customer : WorkshopAgent
  deriving DecidableEq, Inhabited

instance : Fintype WorkshopAgent where
  elems := {.entrepreneur, .operator, .customer}
  complete := by intro a; cases a <;> decide

abbrev WorkshopMeans := Fin 8
abbrev WorkshopHist := Fin 14

def workshopEntrepreneur : WorkshopAgent := .entrepreneur
def workshopOperator : WorkshopAgent := .operator
def workshopCustomer : WorkshopAgent := .customer

def tokenMeans : WorkshopMeans := 0
def rawMeans : WorkshopMeans := 1
def intermediate0Means : WorkshopMeans := 2
def intermediate1Means : WorkshopMeans := 3
def capacityMeans : WorkshopMeans := 4
def finalGood0Means : WorkshopMeans := 5
def finalGood1Means : WorkshopMeans := 6
def wasteMeans : WorkshopMeans := 7

inductive WorkshopAction where
  | idle : WorkshopAction
  | proposeScope : WorkshopAction
  | acceptScope : WorkshopAction
  | refuseScope : WorkshopAction
  | instruct0 : WorkshopAction
  | instruct1 : WorkshopAction
  | produceIntermediate0 : WorkshopAction
  | produceIntermediate1 : WorkshopAction
  | offer (i j : WorkshopAgent) (qA : ℕ) (mA : WorkshopMeans)
      (qB : ℕ) (mB : WorkshopMeans) : WorkshopAction
  | accept (j i : WorkshopAgent) (qA : ℕ) (mA : WorkshopMeans)
      (qB : ℕ) (mB : WorkshopMeans) : WorkshopAction
  deriving DecidableEq, Inhabited

inductive WMoment where
  | root : WMoment
  | instruction : WMoment
  | work : WMoment
  | transfer : WMoment
  | sale : WMoment
  | leaf0 : WMoment
  | leaf1 : WMoment
  | leaf2 : WMoment
  | leaf3 : WMoment
  | leaf4 : WMoment
  | leaf5 : WMoment
  | leaf6 : WMoment
  | leaf7 : WMoment
  | leaf8 : WMoment
  | leaf9 : WMoment
  | leaf10 : WMoment
  | leaf11 : WMoment
  | leaf12 : WMoment
  | leaf13 : WMoment
  deriving DecidableEq, Inhabited

instance : Fintype WMoment where
  elems := {.root, .instruction, .work, .transfer, .sale, .leaf0, .leaf1, .leaf2,
    .leaf3, .leaf4, .leaf5, .leaf6, .leaf7, .leaf8, .leaf9, .leaf10, .leaf11,
    .leaf12, .leaf13}
  complete := by intro t; cases t <;> simp

@[reducible] def wprec : WMoment → WMoment → Prop
  | .root, .instruction => True
  | .root, .work => True
  | .root, .transfer => True
  | .root, .sale => True
  | .root, .leaf0 | .root, .leaf1 | .root, .leaf2 | .root, .leaf3
  | .root, .leaf4 | .root, .leaf5 | .root, .leaf6 | .root, .leaf7
  | .root, .leaf8 | .root, .leaf9 | .root, .leaf10 | .root, .leaf11
  | .root, .leaf12 | .root, .leaf13 => True
  | .instruction, .work => True
  | .instruction, .transfer => True
  | .instruction, .sale => True
  | .instruction, .leaf0 | .instruction, .leaf1 | .instruction, .leaf2 | .instruction, .leaf3
  | .instruction, .leaf4 | .instruction, .leaf5 | .instruction, .leaf11
  | .instruction, .leaf12 | .instruction, .leaf13 => True
  | .work, .transfer => True
  | .work, .sale => True
  | .work, .leaf0 | .work, .leaf1 | .work, .leaf2 | .work, .leaf3
  | .work, .leaf4 | .work, .leaf11 | .work, .leaf12 | .work, .leaf13 => True
  | .transfer, .sale => True
  | .transfer, .leaf0 | .transfer, .leaf1 | .transfer, .leaf2 | .transfer, .leaf3
  | .transfer, .leaf11 | .transfer, .leaf12 | .transfer, .leaf13 => True
  | .sale, .leaf0 | .sale, .leaf1 | .sale, .leaf2 | .sale, .leaf3 => True
  | _, _ => False

instance (a b : WMoment) : Decidable (wprec a b) := by
  cases a <;> cases b <;> first | exact isTrue trivial | exact isFalse False.elim

theorem wprec_irrefl (a : WMoment) : ¬ wprec a a := by
  revert a
  decide

theorem wprec_trans {a b c : WMoment} (hab : wprec a b) (hbc : wprec b c) : wprec a c := by
  revert a b c hab hbc
  decide

def wmem : WMoment → WorkshopHist → Prop
  | .root, _ => True
  | .instruction, h => h.val < 6 ∨ (h.val ≥ 11 ∧ h.val ≤ 13)
  | .work, h => (h.val < 5 ∧ h.val ≠ 5) ∨ (h.val ≥ 11 ∧ h.val ≤ 13)
  | .transfer, h => h.val < 4 ∨ (h.val ≥ 11 ∧ h.val ≤ 13)
  | .sale, h => h.val < 4
  | .leaf0, h => h.val = 0
  | .leaf1, h => h.val = 1
  | .leaf2, h => h.val = 2
  | .leaf3, h => h.val = 3
  | .leaf4, h => h.val = 4
  | .leaf5, h => h.val = 5
  | .leaf6, h => h.val = 6
  | .leaf7, h => h.val = 7
  | .leaf8, h => h.val = 8
  | .leaf9, h => h.val = 9
  | .leaf10, h => h.val = 10
  | .leaf11, h => h.val = 11
  | .leaf12, h => h.val = 12
  | .leaf13, h => h.val = 13

instance (t : WMoment) (h : WorkshopHist) : Decidable (wmem t h) := by
  cases t <;> dsimp [wmem] <;> infer_instance

theorem w_backward_linear {t1 t2 t3 : WMoment}
    (h13 : wprec t1 t3) (h23 : wprec t2 t3) :
    wprec t1 t2 ∨ t1 = t2 ∨ wprec t2 t1 := by
  revert t1 t2 t3 h13 h23
  decide

def w_leaf (h : WorkshopHist) : WMoment :=
  match h.val with
  | 0 => .leaf0
  | 1 => .leaf1
  | 2 => .leaf2
  | 3 => .leaf3
  | 4 => .leaf4
  | 5 => .leaf5
  | 6 => .leaf6
  | 7 => .leaf7
  | 8 => .leaf8
  | 9 => .leaf9
  | 10 => .leaf10
  | 11 => .leaf11
  | 12 => .leaf12
  | _ => .leaf13

theorem wmem_leaf (h : WorkshopHist) : wmem (w_leaf h) h := by
  fin_cases h <;> decide

/-- A terminal moment occurs only on its own history. -/
theorem w_leaf_mem_iff (h1 h2 : WorkshopHist) :
    wmem (w_leaf h1) h2 ↔ h1 = h2 := by
  fin_cases h1 <;> fin_cases h2 <;> simp [w_leaf, wmem]

/-- Every moment on a history is its terminal moment or precedes it. -/
theorem w_mem_terminal_or_precedes (t : WMoment) (h : WorkshopHist)
    (ht : wmem t h) : t = w_leaf h ∨ wprec t (w_leaf h) := by
  fin_cases h <;> cases t <;> simp [wmem, w_leaf, wprec] at ht ⊢

/-- Terminal moments have no future moments. -/
theorem w_leaf_has_no_future (h : WorkshopHist) (u : WMoment) :
    ¬ wprec (w_leaf h) u := by
  fin_cases h <;> cases u <;> decide

/-- Any strict predecessor of a history's terminal moment lies on that
history. -/
theorem wprec_to_leaf_mem (h : WorkshopHist) (t : WMoment)
    (ht : wprec t (w_leaf h)) : wmem t h := by
  fin_cases h <;> cases t <;> simp [w_leaf, wprec, wmem] at ht ⊢

/-- Moments on one history are comparable. -/
theorem w_moments_comparable_on_history (h : WorkshopHist) (t1 t2 : WMoment)
    (ht1 : wmem t1 h) (ht2 : wmem t2 h) :
    wprec t1 t2 ∨ t1 = t2 ∨ wprec t2 t1 := by
  have h1 := w_mem_terminal_or_precedes t1 h ht1
  have h2 := w_mem_terminal_or_precedes t2 h ht2
  rcases h1 with h1 | h1
  · subst t1
    rcases h2 with h2 | h2
    · subst t2
      exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h2)
  · rcases h2 with h2 | h2
    · subst t2
      exact Or.inl h1
    · exact w_backward_linear h1 h2

theorem w_histories_maximal_linear (h : WorkshopHist) :
    IsMaximalLinearChain wprec { t | wmem t h } := by
  constructor
  · intro t1 t2 ht1 ht2
    exact w_moments_comparable_on_history h t1 t2 ht1 ht2
  · intro s' hs' hsub x hx
    have hleaf : w_leaf h ∈ s' := hsub (wmem_leaf h)
    have hlinear := hs' hx hleaf
    rcases hlinear with hbefore | heq | hafter
    · exact wprec_to_leaf_mem h x hbefore
    · rw [heq]
      exact wmem_leaf h
    · exact (w_leaf_has_no_future h x hafter).elim

theorem w_histories_extensional (h1 h2 : WorkshopHist)
    (hext : ∀ t : WMoment, wmem t h1 ↔ wmem t h2) : h1 = h2 := by
  apply (w_leaf_mem_iff h1 h2).mp
  exact (hext (w_leaf h1)).mp (wmem_leaf h1)

theorem w_divergent_futures (t : WMoment) (h1 h2 : WorkshopHist)
    (ht1 : wmem t h1) (ht2 : wmem t h2) (hne : h1 ≠ h2) :
    ∃ u v : WMoment,
      wmem u h1 ∧ wmem v h2 ∧
      wprec t u ∧ wprec t v ∧
      ¬ wprec u v ∧ u ≠ v ∧ ¬ wprec v u := by
  have hterminal1 := w_mem_terminal_or_precedes t h1 ht1
  have hterminal2 := w_mem_terminal_or_precedes t h2 ht2
  have ht1_strict : wprec t (w_leaf h1) := by
    rcases hterminal1 with heq | hprec
    · subst t
      have h_eq : h1 = h2 := (w_leaf_mem_iff h1 h2).mp ht2
      exact (hne h_eq).elim
    · exact hprec
  have ht2_strict : wprec t (w_leaf h2) := by
    rcases hterminal2 with heq | hprec
    · subst t
      have h_eq : h2 = h1 := (w_leaf_mem_iff h2 h1).mp ht1
      exact (hne h_eq.symm).elim
    · exact hprec
  have hleaf_ne : w_leaf h1 ≠ w_leaf h2 := by
    intro heq
    have hmem : wmem (w_leaf h1) h2 := by rw [heq]; exact wmem_leaf h2
    exact hne ((w_leaf_mem_iff h1 h2).mp hmem)
  exact ⟨w_leaf h1, w_leaf h2, wmem_leaf h1, wmem_leaf h2,
    ht1_strict, ht2_strict, w_leaf_has_no_future h1 (w_leaf h2),
    hleaf_ne, w_leaf_has_no_future h2 (w_leaf h1)⟩

def w_use_means (α : WorkshopAction) (m : WorkshopMeans) : ℕ :=
  match α with
  | .produceIntermediate0 => if m = rawMeans ∨ m = capacityMeans then 1 else 0
  | .offer _ _ qA mA _ _ => if m = mA then qA else 0
  | .accept _ _ _ _ qB mB => if m = mB then qB else 0
  | _ => 0

def w_yield_means (α : WorkshopAction) (m : WorkshopMeans) : ℕ :=
  match α with
  | .produceIntermediate0 => if m = finalGood0Means then 1 else 0
  | .offer _ _ _ _ qB mB => if m = mB then qB else 0
  | .accept _ _ qA mA _ _ => if m = mA then qA else 0
  | _ => 0

def w_omega (i : WorkshopAgent) (t : WMoment) (_h : WorkshopHist) (m : WorkshopMeans) : ℕ :=
  match t, i with
  | .root, .entrepreneur | .instruction, .entrepreneur | .work, .entrepreneur =>
      if m = tokenMeans then 2 else 0
  | .root, .operator | .instruction, .operator | .work, .operator =>
      if m = rawMeans ∨ m = capacityMeans then 1 else 0
  | .root, .customer | .instruction, .customer | .work, .customer =>
      if m = tokenMeans then 4 else 0
  | .transfer, .entrepreneur =>
      if m = tokenMeans then 2 else 0
  | .transfer, .operator =>
      if m = finalGood0Means then 1 else 0
  | .transfer, .customer =>
      if m = tokenMeans then 4 else 0
  | .sale, .entrepreneur =>
      if m = finalGood0Means then 1 else 0
  | .sale, .operator =>
      if m = tokenMeans then 2 else 0
  | .sale, .customer =>
      if m = tokenMeans then 4 else 0
  | .leaf0, .entrepreneur =>
      if m = tokenMeans then 4 else 0
  | .leaf0, .operator =>
      if m = tokenMeans then 2 else 0
  | .leaf0, .customer =>
      if m = finalGood0Means then 1 else 0
  | .leaf1, .entrepreneur | .leaf2, .entrepreneur | .leaf3, .entrepreneur =>
      if m = finalGood0Means then 1 else 0
  | .leaf1, .operator | .leaf2, .operator | .leaf3, .operator =>
      if m = tokenMeans then 2 else 0
  | .leaf1, .customer | .leaf2, .customer | .leaf3, .customer =>
      if m = tokenMeans then 4 else 0
  | .leaf11, .entrepreneur | .leaf12, .entrepreneur | .leaf13, .entrepreneur =>
      if m = tokenMeans then 2 else 0
  | .leaf11, .operator | .leaf12, .operator | .leaf13, .operator =>
      if m = finalGood0Means then 1 else 0
  | .leaf11, .customer | .leaf12, .customer | .leaf13, .customer =>
      if m = tokenMeans then 4 else 0
  | _, .entrepreneur =>
      if m = tokenMeans then 2 else 0
  | _, .operator =>
      if m = rawMeans ∨ m = capacityMeans then 1 else 0
  | _, .customer =>
      if m = tokenMeans then 4 else 0

def w_witness (t : WMoment) : WorkshopHist :=
  match t with
  | .root => 0
  | .instruction => 0
  | .work => 0
  | .transfer => 0
  | .sale => 0
  | .leaf0 => 0
  | .leaf1 => 1
  | .leaf2 => 2
  | .leaf3 => 3
  | .leaf4 => 4
  | .leaf5 => 5
  | .leaf6 => 6
  | .leaf7 => 7
  | .leaf8 => 8
  | .leaf9 => 9
  | .leaf10 => 10
  | .leaf11 => 11
  | .leaf12 => 12
  | .leaf13 => 13

def w_enacted (i : WorkshopAgent) (t : WMoment) (h : WorkshopHist) : WorkshopAction :=
  match t, i with
  | .root, .entrepreneur => if h.val ≥ 8 ∧ h.val ≤ 10 then .idle else .proposeScope
  | .root, .operator =>
    if h.val = 6 ∨ h.val = 9 then .refuseScope
    else if h.val = 7 ∨ h.val = 10 then .idle
    else .acceptScope
  | .instruction, .entrepreneur => if h.val = 5 then .idle else .instruct0
  | .work, .operator => if h.val = 4 then .idle else .produceIntermediate0
  | .transfer, .entrepreneur =>
    if h.val = 12 ∨ h.val = 13 then .idle else
      .accept .entrepreneur .operator 1 finalGood0Means 2 tokenMeans
  | .transfer, .operator =>
    if h.val = 11 ∨ h.val = 13 then .idle else
      .offer .operator .entrepreneur 1 finalGood0Means 2 tokenMeans
  | .sale, .entrepreneur =>
    if h.val = 2 ∨ h.val = 3 then .idle else
      .offer .entrepreneur .customer 1 finalGood0Means 4 tokenMeans
  | .sale, .customer =>
    if h.val = 1 ∨ h.val = 3 then .idle else
      .accept .customer .entrepreneur 1 finalGood0Means 4 tokenMeans
  | _, _ => .idle

def w_A_cont (i : WorkshopAgent) (t : WMoment) (_h : WorkshopHist) : Finset WorkshopAction :=
  match t, i with
  | .root, .entrepreneur => {.idle, .proposeScope}
  | .root, .operator => {.idle, .acceptScope, .refuseScope}
  | .instruction, .entrepreneur => {.idle, .instruct0}
  | .work, .operator => {.idle, .produceIntermediate0}
  | .transfer, .entrepreneur =>
    {.idle, .accept .entrepreneur .operator 1 finalGood0Means 2 tokenMeans}
  | .transfer, .operator => {.idle, .offer .operator .entrepreneur 1 finalGood0Means 2 tokenMeans}
  | .sale, .entrepreneur => {.idle, .offer .entrepreneur .customer 1 finalGood0Means 4 tokenMeans}
  | .sale, .customer => {.idle, .accept .customer .entrepreneur 1 finalGood0Means 4 tokenMeans}
  | _, _ => {.idle}

def w_A_feas (i : WorkshopAgent) (t : WMoment) (h : WorkshopHist) : Finset WorkshopAction :=
  w_A_cont i t h

def w_sigma (i : WorkshopAgent) (t : WMoment)
    (α : WorkshopAction) (h' : WorkshopHist) : WorkshopHist :=
  if w_enacted i t h' = α then h'
  else match t, i with
  | .root, .entrepreneur =>
      let a1 := w_enacted .operator .root h'
      if α = .idle then (if a1 = .refuseScope then 9 else if a1 = .idle then 10 else 8)
      else (if a1 = .refuseScope then 6 else if a1 = .idle then 7 else 0)
  | .root, .operator =>
      let a0 := w_enacted .entrepreneur .root h'
      if a0 = .proposeScope then (if α = .refuseScope then 6 else if α = .idle then 7 else 0)
      else (if α = .refuseScope then 9 else if α = .idle then 10 else 8)
  | .instruction, .entrepreneur =>
      if α = .idle then 5 else 0
  | .work, .operator =>
      if α = .idle then 4 else 0
  | .transfer, .entrepreneur =>
      let a1 := w_enacted .operator .transfer h'
      if α = .idle then (if a1 = .idle then 13 else 12)
      else (if a1 = .idle then 11 else 0)
  | .transfer, .operator =>
      let a0 := w_enacted .entrepreneur .transfer h'
      if a0 = .idle then (if α = .idle then 13 else 12)
      else (if α = .idle then 11 else 0)
  | .sale, .entrepreneur =>
      let a2 := w_enacted .customer .sale h'
      if α = .idle then (if a2 = .idle then 3 else 2)
      else (if a2 = .idle then 1 else 0)
  | .sale, .customer =>
      let a0 := w_enacted .entrepreneur .sale h'
      if a0 = .idle then (if α = .idle then 3 else 2)
      else (if α = .idle then 1 else 0)
  | _, _ => h'

theorem w_sigma_realization (i : WorkshopAgent) (t : WMoment) (h h' : WorkshopHist)
    {α : WorkshopAction} (_ht : wmem t h) (hα : α ∈ w_A_feas i t h) (ht' : wmem t h') :
    wmem t (w_sigma i t α h') ∧ w_enacted i t (w_sigma i t α h') = α := by
  dsimp [w_A_feas, w_A_cont] at hα
  cases t <;> cases i
  case root.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  case root.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  case instruction.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  case work.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  case transfer.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  case transfer.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  case sale.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  case sale.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> (revert ht'; decide)
  all_goals {
    simp only [Finset.mem_singleton] at hα
    subst hα
    dsimp [w_sigma, w_enacted]
    exact ⟨ht', rfl⟩
  }

theorem w_sigma_centering (i : WorkshopAgent) (t : WMoment) (h' : WorkshopHist)
    {α : WorkshopAction} (h_enact : w_enacted i t h' = α) :
    w_sigma i t α h' = h' := by
  subst h_enact
  dsimp [w_sigma]
  simp only [↓reduceIte]

theorem w_sigma_co_agency (i j : WorkshopAgent) (t : WMoment) (h h' : WorkshopHist)
    (α : WorkshopAction) (hij : i ≠ j) (_ht : wmem t h) (hα : α ∈ w_A_feas i t h)
    (_ht' : wmem t h') :
    w_enacted j t (w_sigma i t α h') = w_enacted j t h' := by
  dsimp [w_A_feas, w_A_cont] at hα
  cases t <;> cases i <;> cases j <;> try { exact (hij rfl).elim }
  case root.entrepreneur.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case root.entrepreneur.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case root.operator.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case root.operator.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case instruction.entrepreneur.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case instruction.entrepreneur.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case work.operator.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case work.operator.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case transfer.entrepreneur.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case transfer.entrepreneur.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case transfer.operator.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case transfer.operator.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case sale.entrepreneur.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case sale.entrepreneur.customer =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case sale.customer.entrepreneur =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  case sale.customer.operator =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at hα
    rcases hα with rfl | rfl <;> fin_cases h' <;> dsimp [w_sigma, w_enacted]
  all_goals {
    simp only [Finset.mem_singleton] at hα
    subst hα
    dsimp [w_sigma]
    split_ifs <;> rfl
  }

inductive WorkshopEnd where
  | entrepreneurProfit : WorkshopEnd
  | entrepreneurLiquidity : WorkshopEnd
  | operatorCompensation : WorkshopEnd
  | customerEnd0 : WorkshopEnd
  | customerEnd1 : WorkshopEnd
  | bundle (b : WorkshopMeans → ℕ) : WorkshopEnd
  deriving DecidableEq

def workshop_requirement (e : WorkshopEnd) (m : WorkshopMeans) : ℕ :=
  match e with
  | .entrepreneurProfit => if m = tokenMeans then 3 else 0
  | .entrepreneurLiquidity => if m = tokenMeans then 2 else 0
  | .operatorCompensation => if m = tokenMeans then 1 else 0
  | .customerEnd0 => if m = finalGood0Means then 1 else 0
  | .customerEnd1 => if m = finalGood1Means then 1 else 0
  | .bundle b => b m

def workshopValuedEnd (i : WorkshopAgent) (t : WMoment)
    (_h : WorkshopHist) (e : WorkshopEnd) : Prop :=
  match i, e with
  | .entrepreneur, .entrepreneurProfit => True
  | .entrepreneur, .entrepreneurLiquidity => t = .sale
  | .operator, .operatorCompensation => True
  | .customer, .customerEnd0 => True
  | _, _ => False

def workshopPreference (i : WorkshopAgent) (t : WMoment) (h : WorkshopHist)
    (e1 e2 : WorkshopEnd) : Prop :=
  match e1, e2 with
  | .bundle b1, .bundle b2 =>
      SubjectiveTeleologicalDominates workshop_requirement
        (workshopValuedEnd i t h) b1 b2
  | _, _ => False

def workshop_terminal_moment (h : WorkshopHist) : WMoment :=
  w_leaf h

def workshopMaturation (_i : WorkshopAgent) (_α : WorkshopAction) (_t : WMoment)
    (h : WorkshopHist) : WMoment :=
  workshop_terminal_moment h

def workshopEndOf (i : WorkshopAgent) (α : WorkshopAction) (_t : WMoment)
    (_h : WorkshopHist) : WorkshopEnd :=
  let h_sel := w_sigma i _t α (w_witness _t)
  .bundle (w_omega i (workshop_terminal_moment h_sel) h_sel)

syntax "pick_branch" : tactic
macro_rules
  | `(tactic| pick_branch) =>
    `(tactic| first | (left; refine ⟨rfl, rfl, ?_⟩; decide)
                    | (refine ⟨rfl, rfl, ?_⟩; decide)
                    | (right; pick_branch))

theorem workshop_next_moment_cases {t t' : WMoment} {h : WorkshopHist}
    (h_next : IsNextMoment wprec wmem t t' h) :
    (t = .root ∧ t' = .instruction ∧
      (h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 5 ∨ h = 11 ∨ h = 12 ∨ h = 13)) ∨
    (t = .root ∧ t' = .leaf6 ∧ h = 6) ∨
    (t = .root ∧ t' = .leaf7 ∧ h = 7) ∨
    (t = .root ∧ t' = .leaf8 ∧ h = 8) ∨
    (t = .root ∧ t' = .leaf9 ∧ h = 9) ∨
    (t = .root ∧ t' = .leaf10 ∧ h = 10) ∨
    (t = .instruction ∧ t' = .work ∧
      (h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 4 ∨ h = 11 ∨ h = 12 ∨ h = 13)) ∨
    (t = .instruction ∧ t' = .leaf5 ∧ h = 5) ∨
    (t = .work ∧ t' = .transfer ∧ (h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3 ∨ h = 11 ∨ h = 12 ∨ h = 13)) ∨
    (t = .work ∧ t' = .leaf4 ∧ h = 4) ∨
    (t = .transfer ∧ t' = .sale ∧ (h = 0 ∨ h = 1 ∨ h = 2 ∨ h = 3)) ∨
    (t = .transfer ∧ t' = .leaf11 ∧ h = 11) ∨
    (t = .transfer ∧ t' = .leaf12 ∧ h = 12) ∨
    (t = .transfer ∧ t' = .leaf13 ∧ h = 13) ∨
    (t = .sale ∧ t' = .leaf0 ∧ h = 0) ∨
    (t = .sale ∧ t' = .leaf1 ∧ h = 1) ∨
    (t = .sale ∧ t' = .leaf2 ∧ h = 2) ∨
    (t = .sale ∧ t' = .leaf3 ∧ h = 3) := by
  cases t <;> cases t'
  case root.instruction | root.leaf6 | root.leaf7 | root.leaf8 | root.leaf9 | root.leaf10 |
       instruction.work | instruction.leaf5 |
       work.transfer | work.leaf4 |
       transfer.sale | transfer.leaf11 | transfer.leaf12 | transfer.leaf13 |
       sale.leaf0 | sale.leaf1 | sale.leaf2 | sale.leaf3 =>
    have hmem := h_next.2.1
    fin_cases h <;> (
      first
      | pick_branch
      | exact ((by decide : ¬ wmem _ _) hmem).elim
    )
  all_goals {
    have hprec := h_next.2.2.1
    first
    | (cases hprec; done)
    | have hmem := h_next.2.1
      fin_cases h <;> (
        first
        | exact ((by decide : ¬ wmem _ _) hmem).elim
        | exact (h_next.2.2.2 .instruction (by decide) ⟨trivial, trivial⟩).elim
        | exact (h_next.2.2.2 .work (by decide) ⟨trivial, trivial⟩).elim
        | exact (h_next.2.2.2 .transfer (by decide) ⟨trivial, trivial⟩).elim
        | exact (h_next.2.2.2 .sale (by decide) ⟨trivial, trivial⟩).elim
      )
  }

/-- The chosen action is determined by any later moment that remains on the
history. This single-history lemma avoids enumerating pairs of histories. -/
def w_future_choice (i : WorkshopAgent) (t u : WMoment) : WorkshopAction :=
  match t, i with
  | .root, .entrepreneur =>
      if u = .leaf8 ∨ u = .leaf9 ∨ u = .leaf10 then .idle else .proposeScope
  | .root, .operator =>
      if u = .leaf6 ∨ u = .leaf9 then .refuseScope
      else if u = .leaf7 ∨ u = .leaf10 then .idle else .acceptScope
  | .instruction, .entrepreneur => if u = .leaf5 then .idle else .instruct0
  | .work, .operator => if u = .leaf4 then .idle else .produceIntermediate0
  | .transfer, .entrepreneur =>
      if u = .leaf12 ∨ u = .leaf13 then .idle
      else .accept .entrepreneur .operator 1 finalGood0Means 2 tokenMeans
  | .transfer, .operator =>
      if u = .leaf11 ∨ u = .leaf13 then .idle
      else .offer .operator .entrepreneur 1 finalGood0Means 2 tokenMeans
  | .sale, .entrepreneur =>
      if u = .leaf2 ∨ u = .leaf3 then .idle
      else .offer .entrepreneur .customer 1 finalGood0Means 4 tokenMeans
  | .sale, .customer =>
      if u = .leaf1 ∨ u = .leaf3 then .idle
      else .accept .customer .entrepreneur 1 finalGood0Means 4 tokenMeans
  | _, _ => .idle

theorem w_enacted_eq_future_choice (i : WorkshopAgent) (t u : WMoment)
    (h : WorkshopHist) (htu : wprec t u) (hu : wmem u h) :
    w_enacted i t h = w_future_choice i t u := by
  cases t <;> cases i <;> cases u <;>
    simp only [wprec] at htu <;>
    simp only [wmem] at hu <;>
    simp only [w_enacted, w_future_choice] <;>
    split_ifs at * <;>
    simp_all <;>
    omega

@[reducible] instance WorkshopActionFrame : ActionFrame where
  Agent := WorkshopAgent
  Moment := WMoment
  History := WorkshopHist
  Action := WorkshopAction
  Means := WorkshopMeans
  Ends := WorkshopEnd
  alpha_zero := .idle
  Precedence := wprec
  moment_lt_irrefl := wprec_irrefl
  moment_lt_trans := wprec_trans
  backward_linearity := w_backward_linear
  mem_hist := wmem
  moment_in_history := by
    intro t
    cases t <;> try { exact ⟨0, by decide⟩ }
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨4, by decide⟩
    · exact ⟨5, by decide⟩
    · exact ⟨6, by decide⟩
    · exact ⟨7, by decide⟩
    · exact ⟨8, by decide⟩
    · exact ⟨9, by decide⟩
    · exact ⟨10, by decide⟩
    · exact ⟨11, by decide⟩
    · exact ⟨12, by decide⟩
    · exact ⟨13, by decide⟩
  histories_maximal_linear := w_histories_maximal_linear
  histories_extensional := w_histories_extensional
  divergent_futures_witness := fun h1 h2 ht1 ht2 hne => w_divergent_futures _ h1 h2 ht1 ht2 hne
  A_cont := w_A_cont
  A_cont_bundle_invariant := by intro _ _ _ _ _ _; rfl
  alpha_zero_cont := by intro i t h; revert h; cases t <;> cases i <;> decide
  omega := w_omega
  omega_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
  use_means := w_use_means
  yield_means := w_yield_means
  use_means_alpha_zero := by intro m; fin_cases m <;> rfl
  yield_means_alpha_zero := by intro m; fin_cases m <;> rfl
  A_feas := w_A_feas
  A_feas_coupling := by
    intro i t h α
    constructor
    · intro hα
      refine ⟨hα, fun m => ?_⟩
      cases t <;> cases i <;> {
        dsimp [w_A_feas, w_A_cont, w_omega, w_use_means] at hα ⊢
        first
        | { simp only [Finset.mem_singleton] at hα; subst hα; exact Nat.zero_le _ }
        | {
            simp only [Finset.mem_insert, Finset.mem_singleton] at hα
            rcases hα with rfl | rfl
            · exact Nat.zero_le _
            · fin_cases m <;> decide
          }
        | {
            simp only [Finset.mem_insert, Finset.mem_singleton] at hα
            rcases hα with rfl | rfl | rfl
            · exact Nat.zero_le _
            · exact Nat.zero_le _
            · exact Nat.zero_le _
          }
      }
    · intro ⟨hα, _⟩; exact hα
  enacted := w_enacted
  enacted_in_A_feas := by
    intro i t h ht
    cases t <;> cases i <;> fin_cases h <;> {
      first
      | exfalso; revert ht; decide
      | dsimp [w_A_feas, w_A_cont, w_enacted]; decide
    }
  no_choice_between_undivided := by
    intro i t u h1 h2 _ht1 _ht2 htu hu1 hu2
    rw [w_enacted_eq_future_choice i t u h1 htu hu1,
      w_enacted_eq_future_choice i t u h2 htu hu2]
  sigma := w_sigma
  sigma_realization := w_sigma_realization
  sigma_centering := by
    intro i t h' α _ht' h_enact
    exact w_sigma_centering i t h' h_enact
  sigma_co_agency := by
    intro i j t h h' α hij ht hα ht'
    exact w_sigma_co_agency i j t h h' α hij ht hα ht'
  expected_maturation_mem_future := by
    intro i α t h ht _h_enact
    dsimp [workshopMaturation, workshop_terminal_moment]
    fin_cases h <;> cases t <;> {
      first
      | exfalso; revert ht; decide
      | exact ⟨by decide, Or.inl rfl⟩
      | exact ⟨by decide, Or.inr (by decide)⟩
    }
  law_in_re_transition := by
    intro i t t' h α m h_not_tr _h_uninv h_enact h_next
    rcases workshop_next_moment_cases h_next with
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals {
      cases i <;> {
        dsimp [w_enacted] at h_enact
        subst h_enact
        first
        | exfalso; apply h_not_tr
          first
          | exact Or.inl ⟨.entrepreneur, .customer, 1, 5, 4, 0, rfl⟩
          | exact Or.inr ⟨.customer, .entrepreneur, 1, 5, 4, 0, rfl⟩
          | exact Or.inl ⟨.operator, .entrepreneur, 1, 5, 2, 0, rfl⟩
          | exact Or.inr ⟨.entrepreneur, .operator, 1, 5, 2, 0, rfl⟩
        | fin_cases m <;> decide
      }
    }
  IsTradeAction := fun α =>
    (∃ i j qA mA qB mB, α = WorkshopAction.offer i j qA mA qB mB) ∨
    (∃ j i qA mA qB mB, α = WorkshopAction.accept j i qA mA qB mB)
  alpha_zero_not_trade := by
    intro h
    rcases h with ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ <;> cases h
  MinPlausible := fun _ t => { w_witness t }
  min_plausible_nonempty := by intro _ t; exact ⟨w_witness t, Set.mem_singleton _⟩
  tau := fun _ t _ => t
  min_plausible_node_incidence := by
    intro _ t h' hh
    have heq : h' = w_witness t := Set.mem_singleton_iff.mp hh
    subst heq
    cases t <;> decide
  tau_centering := by intro _ _ _ _; rfl
  requirement := workshop_requirement
  ValuedEnd := workshopValuedEnd
  valued_end_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
  OutcomeOf := fun i _ _ τ h => .bundle (w_omega i τ h)
  ExpectedMaturation := workshopMaturation
  End_of := workshopEndOf
  End_of_bundle_invariant := by intro _ _ _ _ _ _ _; rfl
  Preference := workshopPreference
  Preference_bundle_invariant := by intro _ _ _ _ _ _; rfl
  pref_asymm := by
    intro i t h e1 e2 h12 h21
    cases e1 <;> cases e2 <;> simp_all only [workshopPreference]
    rcases h12 with ⟨_, ⟨S, hvalued, h_att, h_not⟩⟩
    exact h_not (h21.1 S hvalued h_att)
  doxastic_sure_thing_bridge := by
    intro i α β t h _ _ h_strict
    rcases h_strict with ⟨h', hh', hpref⟩
    have heq : h' = w_witness t := Set.mem_singleton_iff.mp hh'
    subst heq
    exact hpref
  doxastic_plausible_support := by
    intro i α β t h _ hpref
    refine ⟨w_witness t, Set.mem_singleton _, hpref⟩
  BundleEnd := WorkshopEnd.bundle
  teleological_bundle_dominance_induces_preference := by
    intro i t h b1 b2 hdom
    exact hdom

instance : BilateralExchangeFrame WorkshopActionFrame where
  Offer := WorkshopAction.offer
  Accept := WorkshopAction.accept
  offer_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact WorkshopAction.offer.inj h
  accept_inj := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; exact WorkshopAction.accept.inj h
  offer_ne_accept := by intro _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
  alpha_zero_ne_offer := by intro _ _ _ _ _ _ h; cases h
  alpha_zero_ne_accept := by intro _ _ _ _ _ _ h; cases h
  use_means_offer := by intro _ _ _ _ _ _ _; rfl
  yield_means_offer := by intro _ _ _ _ _ _ _; rfl
  use_means_accept := by intro _ _ _ _ _ _ _; rfl
  yield_means_accept := by intro _ _ _ _ _ _ _; rfl
  unilateral_offer_noop := by
    intro i j qA mA qB mB t t' h m h_enact h_not_acc h_next
    rcases workshop_next_moment_cases h_next with
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals {
      cases i <;> {
        dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact
        first
        | (cases h_enact; done)
        | cases h_enact; exfalso; apply h_not_acc; decide
        | cases h_enact; fin_cases m <;> decide
      }
    }
  unilateral_accept_noop := by
    intro j i qA mA qB mB t t' h m h_enact h_not_off h_next
    rcases workshop_next_moment_cases h_next with
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals {
      cases j <;> {
        dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact
        first
        | (cases h_enact; done)
        | cases h_enact; exfalso; apply h_not_off; decide
        | cases h_enact; fin_cases m <;> decide
      }
    }
  bilateral_transfer_law := by
    intro i j qA mA qB mB t t' h m h_ne h_enact_i h_enact_j h_next
    rcases workshop_next_moment_cases h_next with
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl | rfl | rfl | rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals {
      cases i <;> cases j
      · exact (h_ne rfl).elim
      · dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact_i
        cases h_enact_i
      · dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact_i h_enact_j
        first
        | (cases h_enact_i; done)
        | (cases h_enact_j; done)
        | cases h_enact_i; cases h_enact_j; fin_cases m <;> decide
      · dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact_i h_enact_j
        first
        | (cases h_enact_i; done)
        | (cases h_enact_j; done)
        | cases h_enact_i; cases h_enact_j; fin_cases m <;> decide
      · exact (h_ne rfl).elim
      · dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact_i
        cases h_enact_i
      · dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact_i
        cases h_enact_i
      · dsimp only [ActionFrame.enacted, WorkshopActionFrame, w_enacted] at h_enact_i
        cases h_enact_i
      · exact (h_ne rfl).elim
    }
  is_trade_action_def := by intro α; rfl

theorem entrepreneur_purposeful_proposal :
    @PurposefulAct WorkshopActionFrame .entrepreneur
      WMoment.root (0 : WorkshopHist) WorkshopAction.proposeScope := by
  refine ⟨by decide, ⟨trivial, rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .entrepreneur WMoment.root 0)
      (w_omega .entrepreneur .leaf0 0) (w_omega .entrepreneur .leaf8 8)
    refine ⟨?_, ⟨{.entrepreneurProfit}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS _hS_att m
      have h_sub : S ⊆ {.entrepreneurProfit} := by
        intro w hw
        have hw_val := hS w hw
        dsimp [workshopValuedEnd] at hw_val
        cases w <;> first | exact Finset.mem_singleton_self _ | contradiction
      rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
      · simp
      · fin_cases m <;> decide
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att tokenMeans; revert h0; decide
  · intro β hβ
    change β ∈ ({.idle, .proposeScope} : Finset WorkshopAction) at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · intro h_pref
      have h_idle_att := h_pref.1 {.entrepreneurProfit} (by simp [workshopValuedEnd]) ?_
      · have h0 := h_idle_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .entrepreneur
        WMoment.root (0 : WorkshopHist) h_pref h_pref

/-- Concrete storage and security evidence in the workshop frame. The enacted
proposal yields enough tokens to attain the entrepreneur's valued profit end;
the feasible idle alternative yields only two tokens. This inhabits the
earlier-control record without requiring both alternatives to execute on one
history. -/
def workshopEarlierControlSecurityEvidence :
    @EarlierControlSecurityEvidence WorkshopActionFrame
      .entrepreneur WMoment.root (0 : WorkshopHist) := by
  refine {
    earlierBundle := w_omega .entrepreneur .leaf0 0
    laterBundle := w_omega .entrepreneur .leaf8 8
    earlierAction := .proposeScope
    laterAction := .idle
    earlierAction_feasible := by decide
    laterAction_feasible := by decide
    earlierAction_executed := ⟨trivial, rfl⟩
    earlierAction_end := by rfl
    laterAction_end := by rfl
    storage_reproduces_valued_plans := ?_
    earlySecurityService := .entrepreneurProfit
    security_is_valued := by
      change workshopValuedEnd .entrepreneur .root 0 .entrepreneurProfit
      change True
      trivial
    security_attainable_early := by
      change AttainsEnd workshop_requirement
        (w_omega .entrepreneur .leaf0 0) .entrepreneurProfit
      intro m
      fin_cases m <;> decide
    security_unattainable_late := ?_
  }
  · intro S hvalued hlate
    change (∀ e ∈ S, workshopValuedEnd .entrepreneur .root 0 e) at hvalued
    change JointlyAttains workshop_requirement
      (w_omega .entrepreneur .leaf8 8) S at hlate
    have hsubset : S ⊆ {.entrepreneurProfit} := by
      intro e he
      have heval := hvalued e he
      cases e <;> simp [workshopValuedEnd] at heval ⊢
    rcases Finset.subset_singleton_iff.mp hsubset with hempty | hsingleton
    · subst S
      intro m
      simp
    · subst S
      have hfalse : False := by
        have htoken := hlate tokenMeans
        norm_num [JointlyAttains, workshop_requirement, tokenMeans, w_omega] at htoken
      exact hfalse.elim
  · change ¬ AttainsEnd workshop_requirement
      (w_omega .entrepreneur .leaf8 8) .entrepreneurProfit
    intro hattains
    have htoken := hattains tokenMeans
    change 3 ≤ 2 at htoken
    omega

theorem operator_purposeful_acceptance :
    @PurposefulAct WorkshopActionFrame .operator
      WMoment.root (0 : WorkshopHist) WorkshopAction.acceptScope := by
  refine ⟨by decide, ⟨trivial, rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .operator WMoment.root 0)
      (w_omega .operator .leaf0 0) (w_omega .operator .leaf7 7)
    refine ⟨?_, ⟨{.operatorCompensation}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS _hS_att m
      have h_sub : S ⊆ {.operatorCompensation} := by
        intro w hw
        have hw_val := hS w hw
        dsimp [workshopValuedEnd] at hw_val
        cases w <;> first | exact Finset.mem_singleton_self _ | contradiction
      rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
      · simp
      · fin_cases m <;> decide
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att tokenMeans; revert h0; decide
  · intro β hβ
    change β ∈ ({.idle, .acceptScope, .refuseScope} : Finset WorkshopAction) at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl | rfl
    · intro h_pref
      have h_idle_att := h_pref.1 {.operatorCompensation} (by simp [workshopValuedEnd]) ?_
      · have h0 := h_idle_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .operator WMoment.root (0 : WorkshopHist) h_pref h_pref
    · intro h_pref
      have h_refuse_att := h_pref.1 {.operatorCompensation} (by simp [workshopValuedEnd]) ?_
      · have h0 := h_refuse_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide

theorem entrepreneur_purposeful_instruction :
    @PurposefulAct WorkshopActionFrame .entrepreneur
      WMoment.instruction (0 : WorkshopHist) WorkshopAction.instruct0 := by
  refine ⟨by decide, ⟨Or.inl (by decide), rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .entrepreneur WMoment.instruction 0)
      (w_omega .entrepreneur .leaf0 0) (w_omega .entrepreneur .leaf5 5)
    refine ⟨?_, ⟨{.entrepreneurProfit}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS _hS_att m
      have h_sub : S ⊆ {.entrepreneurProfit} := by
        intro w hw
        have hw_val := hS w hw
        dsimp [workshopValuedEnd] at hw_val
        cases w <;> first | exact Finset.mem_singleton_self _ | contradiction
      rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
      · simp
      · fin_cases m <;> decide
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att tokenMeans; revert h0; decide
  · intro β hβ
    change β ∈ ({.idle, .instruct0} : Finset WorkshopAction) at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · intro h_pref
      have h_idle_att := h_pref.1 {.entrepreneurProfit} (by simp [workshopValuedEnd]) ?_
      · have h0 := h_idle_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .entrepreneur
        WMoment.instruction (0 : WorkshopHist) h_pref h_pref

theorem operator_purposeful_work :
    @PurposefulAct WorkshopActionFrame .operator
      WMoment.work (0 : WorkshopHist) WorkshopAction.produceIntermediate0 := by
  refine ⟨by decide, ⟨Or.inl ⟨by decide, by decide⟩, rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .operator WMoment.work 0)
      (w_omega .operator .leaf0 0) (w_omega .operator .leaf4 4)
    refine ⟨?_, ⟨{.operatorCompensation}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS _hS_att m
      have h_sub : S ⊆ {.operatorCompensation} := by
        intro w hw
        have hw_val := hS w hw
        dsimp [workshopValuedEnd] at hw_val
        cases w <;> first | exact Finset.mem_singleton_self _ | contradiction
      rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
      · simp
      · fin_cases m <;> decide
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att tokenMeans; revert h0; decide
  · intro β hβ
    change β ∈ ({.idle, .produceIntermediate0} : Finset WorkshopAction) at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · intro h_pref
      have h_idle_att := h_pref.1 {.operatorCompensation} (by simp [workshopValuedEnd]) ?_
      · have h0 := h_idle_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .operator WMoment.work (0 : WorkshopHist) h_pref h_pref

theorem entrepreneur_purposeful_sale :
    @PurposefulAct WorkshopActionFrame .entrepreneur WMoment.sale (0 : WorkshopHist)
      (WorkshopAction.offer .entrepreneur .customer 1 finalGood0Means 4 tokenMeans) := by
  refine ⟨by decide, ⟨(by decide : wmem .sale 0), rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .entrepreneur WMoment.sale 0)
      (w_omega .entrepreneur .leaf0 0) (w_omega .entrepreneur .leaf2 2)
    refine ⟨?_, ⟨{.entrepreneurProfit}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS hAtt m
      have h_empty : S = ∅ := by
        ext w
        constructor
        · intro hw
          have h_val := hS w hw
          have h_positive : 0 < workshop_requirement w tokenMeans := by
            cases w <;>
              simp [workshopValuedEnd, workshop_requirement, tokenMeans] at h_val ⊢
          have h_single := Finset.single_le_sum
            (f := fun w => workshop_requirement w tokenMeans)
            (fun _ _ => Nat.zero_le _) hw
          have h_bound := hAtt tokenMeans
          change S.sum (fun w => workshop_requirement w tokenMeans) ≤
            w_omega .entrepreneur .leaf2 2 tokenMeans at h_bound
          have h_actual : w_omega .entrepreneur .leaf2 2 tokenMeans = 0 := by decide
          rw [h_actual] at h_bound
          omega
        · intro hw
          simp at hw
      subst S
      simp
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att tokenMeans; revert h0; decide
  · intro β hβ
    change β ∈
      ({.idle,
        .offer .entrepreneur .customer 1 finalGood0Means 4 tokenMeans} : Finset WorkshopAction)
      at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · intro h_pref
      have h_idle_att := h_pref.1 {.entrepreneurProfit} (by simp [workshopValuedEnd]) ?_
      · have h0 := h_idle_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .entrepreneur
        WMoment.sale (0 : WorkshopHist) h_pref h_pref

theorem customer_purposeful_purchase :
    @PurposefulAct WorkshopActionFrame .customer WMoment.sale (0 : WorkshopHist)
      (WorkshopAction.accept .customer .entrepreneur 1 finalGood0Means 4 tokenMeans) := by
  refine ⟨by decide, ⟨(by decide : wmem .sale 0), rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .customer WMoment.sale 0)
      (w_omega .customer .leaf0 0) (w_omega .customer .leaf1 1)
    refine ⟨?_, ⟨{.customerEnd0}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS _hS_att m
      have h_sub : S ⊆ {.customerEnd0} := by
        intro w hw
        have hw_val := hS w hw
        dsimp [workshopValuedEnd] at hw_val
        cases w <;> first | exact Finset.mem_singleton_self _ | cases hw_val
      rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
      · simp
      · fin_cases m <;> decide
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att finalGood0Means; revert h0; decide
  · intro β hβ
    change β ∈
      ({.idle,
        .accept .customer .entrepreneur 1 finalGood0Means 4 tokenMeans} : Finset WorkshopAction)
      at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · intro h_pref
      have h_idle_att := h_pref.1 {.customerEnd0} (by simp [workshopValuedEnd]) ?_
      · have h0 := h_idle_att finalGood0Means; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .customer WMoment.sale (0 : WorkshopHist) h_pref h_pref

/-- The principal purposefully accepts the operator's intermediate-good
transfer. The accepted exchange preserves the principal's profit end on the
selected branch, while declining it leaves the principal below that threshold. -/
theorem entrepreneur_purposeful_internal_acceptance :
    @PurposefulAct WorkshopActionFrame .entrepreneur WMoment.transfer (0 : WorkshopHist)
      (WorkshopAction.accept .entrepreneur .operator 1 finalGood0Means 2 tokenMeans) := by
  refine ⟨by decide, ⟨(by decide : wmem .transfer 0), rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .entrepreneur WMoment.transfer 0)
      (w_omega .entrepreneur .leaf0 0) (w_omega .entrepreneur .leaf12 12)
    refine ⟨?_, ⟨{.entrepreneurProfit}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS _hS_att m
      have h_sub : S ⊆ {.entrepreneurProfit} := by
        intro w hw
        have hw_val := hS w hw
        cases w <;> simp [workshopValuedEnd] at hw_val ⊢
      rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
      · simp
      · fin_cases m <;> decide
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att tokenMeans; revert h0; decide
  · intro β hβ
    change β ∈
      ({.idle,
        .accept .entrepreneur .operator 1 finalGood0Means 2 tokenMeans} : Finset WorkshopAction)
      at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · intro h_pref
      have h_accept_att := h_pref.1 {.entrepreneurProfit}
        (by simp [workshopValuedEnd]) ?_
      · have h0 := h_accept_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .entrepreneur
        WMoment.transfer (0 : WorkshopHist) h_pref h_pref

/-- The operator purposefully makes the matched offer that settles the
principal's internal transfer. -/
theorem operator_purposeful_internal_offer :
    @PurposefulAct WorkshopActionFrame .operator WMoment.transfer (0 : WorkshopHist)
      (WorkshopAction.offer .operator .entrepreneur 1 finalGood0Means 2 tokenMeans) := by
  refine ⟨by decide, ⟨(by decide : wmem .transfer 0), rfl⟩, Or.inr ?_, ?_⟩
  · change SubjectiveTeleologicalDominates workshop_requirement
      (workshopValuedEnd .operator WMoment.transfer 0)
      (w_omega .operator .leaf0 0) (w_omega .operator .leaf11 11)
    refine ⟨?_, ⟨{.operatorCompensation}, by simp [workshopValuedEnd], ?_, ?_⟩⟩
    · intro S hS _hS_att m
      have h_sub : S ⊆ {.operatorCompensation} := by
        intro w hw
        have hw_val := hS w hw
        cases w <;> simp [workshopValuedEnd] at hw_val ⊢
      rcases Finset.subset_singleton_iff.mp h_sub with rfl | rfl
      · simp
      · fin_cases m <;> decide
    · intro m; fin_cases m <;> decide
    · intro h_att; have h0 := h_att tokenMeans; revert h0; decide
  · intro β hβ
    change β ∈
      ({.idle,
        .offer .operator .entrepreneur 1 finalGood0Means 2 tokenMeans} : Finset WorkshopAction)
      at hβ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hβ
    rcases hβ with rfl | rfl
    · intro h_pref
      have h_offer_att := h_pref.1 {.operatorCompensation}
        (by simp [workshopValuedEnd]) ?_
      · have h0 := h_offer_att tokenMeans; revert h0; decide
      · intro m; fin_cases m <;> decide
    · intro h_pref
      exact WorkshopActionFrame.pref_asymm .operator
        WMoment.transfer (0 : WorkshopHist) h_pref h_pref

def workshopVocabulary : DelegationVocabulary WorkshopActionFrame where
  acceptsAssignment := fun a b => a = WorkshopAction.proposeScope ∧ b = WorkshopAction.acceptScope
  taskInScope := fun a t => a = WorkshopAction.proposeScope ∧
    (t = WorkshopAction.produceIntermediate0 ∨ t = WorkshopAction.produceIntermediate1)
  instructionSelectsTask := fun a i t =>
    a = WorkshopAction.proposeScope ∧
      ((i = WorkshopAction.instruct0 ∧ t = WorkshopAction.produceIntermediate0) ∨
       (i = WorkshopAction.instruct1 ∧ t = WorkshopAction.produceIntermediate1))
  compensation := fun a m => if a = WorkshopAction.proposeScope ∧ m = tokenMeans then 2 else 0
  authorizesTerms := fun a o ac =>
    a = WorkshopAction.proposeScope ∧
      ((o = WorkshopAction.offer .operator .entrepreneur 1 5 2 0 ∧
        ac = WorkshopAction.accept .entrepreneur .operator 1 5 2 0) ∨
       (o = WorkshopAction.offer .operator .entrepreneur 1 6 2 0 ∧
        ac = WorkshopAction.accept .entrepreneur .operator 1 6 2 0))

def workshopProposal : DelegationProposal workshopVocabulary where
  principal := workshopEntrepreneur
  operator := workshopOperator
  decisionMoment := WMoment.root
  history := (0 : WorkshopHist)
  assignment := WorkshopAction.proposeScope
  acceptance := WorkshopAction.acceptScope
  taskScope := {WorkshopAction.produceIntermediate0, WorkshopAction.produceIntermediate1}
  compensationMeans := tokenMeans
  compensationQuantity := 2
  agents_distinct := by decide
  decision_incident := trivial
  assignment_active := by decide
  acceptance_active := by decide
  scope_interpreted := by
    intro task htask
    simp only [Finset.mem_insert, Finset.mem_singleton] at htask
    rcases htask with rfl | rfl <;> exact ⟨rfl, by decide⟩
  compensation_interpreted := by decide
  acceptance_content := ⟨rfl, rfl⟩

def workshopExecution : DelegationExecution workshopProposal where
  instructionMoment := WMoment.instruction
  instruction := WorkshopAction.instruct0
  workMoment := WMoment.work
  task := WorkshopAction.produceIntermediate0
  instruction_incident := Or.inl (by decide)
  work_incident := Or.inl ⟨by decide, by decide⟩
  decision_precedes_instruction := trivial
  instruction_precedes_work := trivial
  instruction_active := by decide
  instruction_selects_task := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  task_active := by decide
  task_in_scope := by decide
  task_scope_interpreted := ⟨rfl, Or.inl rfl⟩

def workshopAcceptedDelegation : AcceptedDelegation workshopVocabulary where
  proposal := workshopProposal
  execution := workshopExecution
  principal_chooses_assignment := entrepreneur_purposeful_proposal
  principal_issues_instruction := entrepreneur_purposeful_instruction
  operator_accepts_assignment := operator_purposeful_acceptance
  operator_executes_task := operator_purposeful_work

def workshopBargainingMeaning : MarketBargainingMeaning WorkshopActionFrame where
  independentGovernance := fun p1 p2 _ _ => p1 ≠ p2
  freshlyBargained := fun _ _ _ _ _ _ _ _ => True

def workshopMarketInterface :
    IndependentMarketInterface workshopVocabulary workshopBargainingMeaning where
  seller := workshopEntrepreneur
  buyer := workshopCustomer
  sellerPrincipal := workshopEntrepreneur
  buyerPrincipal := workshopCustomer
  moment := WMoment.sale
  history := (0 : WorkshopHist)
  qA := 1
  mA := finalGood0Means
  qB := 4
  mB := tokenMeans
  sellerRole := {
    actor := workshopEntrepreneur
    principal := workshopEntrepreneur
    capacity := .principal
    decision := WorkshopAction.offer .entrepreneur .customer 1 5 4 0
    authority := rfl
  }
  buyerRole := {
    actor := workshopCustomer
    principal := workshopCustomer
    capacity := .principal
    decision := WorkshopAction.accept .customer .entrepreneur 1 5 4 0
    authority := rfl
  }
  seller_role_actor := rfl
  seller_role_principal := rfl
  seller_role_decision := rfl
  buyer_role_actor := rfl
  buyer_role_principal := rfl
  buyer_role_decision := rfl
  exchange := ⟨by decide, by decide, by decide, entrepreneur_purposeful_sale, by decide,
    customer_purposeful_purchase, by decide⟩
  principals_distinct := by decide
  independently_governed := by intro h; cases h

def workshopFirmNetwork : OrganizationNetwork workshopVocabulary workshopBargainingMeaning :=
  threeStageFirmNetwork workshopAcceptedDelegation workshopMarketInterface rfl rfl trivial

theorem workshop_has_firm_boundary_and_structure :
    workshopFirmNetwork.HasFirmStructure ∧ workshopFirmNetwork.HasFirmBoundary := by
  have hs := threeStageFirmNetwork_has_firm_structure workshopAcceptedDelegation
    workshopMarketInterface rfl rfl trivial
  exact ⟨hs, (OrganizationNetwork.firm_structure_components workshopFirmNetwork hs).2⟩

theorem workshop_refusal_leaves_idle_inventories :
    w_omega .operator .leaf6 6 rawMeans = 1 ∧
    w_omega .operator .leaf6 6 capacityMeans = 1 ∧
    w_omega .entrepreneur .leaf6 6 tokenMeans = 2 := by
  decide

theorem workshop_restored_demand_signal_delivers_requested_good :
    w_omega .customer .leaf0 0 finalGood0Means = 1 := by
  decide

theorem workshop_excessive_costs_defeat_dominance (net_cash : ℕ) (h_costly : net_cash ≤ 2) :
    ¬ (net_cash ≥ 3) := by
  omega

end

end Praxeology
