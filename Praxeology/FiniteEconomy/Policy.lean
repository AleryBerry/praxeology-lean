/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame.Core

/-!
# Finite end and preference policies

This module defines the finite scenario encoding of state-contingent ends and
auxiliary ordering calculations over those ends. These calculations do not
define or replace `ActionFrame.Preference`. A generated frame must retain its
own preference and doxastic fields, and prove its bundle-preference field from
`SubjectiveTeleologicalDominates`.
-/

@[expose] public section

namespace Praxeology

/-- Primitive ends and state-contingent plans for finite scenario data. -/
inductive EconomyEnd (State PrimitiveEnd : Type)
  | primitive : PrimitiveEnd → EconomyEnd State PrimitiveEnd
  | plan : (State → PrimitiveEnd) → EconomyEnd State PrimitiveEnd

/-- Evaluate a plan at the state under consideration. -/
def EconomyEnd.evaluate {State PrimitiveEnd : Type}
    (s : State) : EconomyEnd State PrimitiveEnd → PrimitiveEnd
  | .primitive e => e
  | .plan f => f s

/-- Normalize a finite plan to a primitive end exactly when it is constant on
the supplied finite support. Outside support the plan remains state-contingent.
The optional representative is explicit so normalization remains computable
and independent of any enumeration order. -/
def normalizePlan {State PrimitiveEnd : Type} [DecidableEq State]
    [DecidableEq PrimitiveEnd] (support : Finset State)
    (representative : Option State)
    (f : State → PrimitiveEnd) : EconomyEnd State PrimitiveEnd := by
  cases representative with
  | none => exact .plan f
  | some s =>
      exact if s ∈ support ∧ ∀ s' ∈ support, f s' = f s then
        .primitive (f s) else .plan f

/-- Normalization preserves a plan's realized end on every supported state. -/
theorem normalizePlan_evaluate {State PrimitiveEnd : Type}
    [DecidableEq State] [DecidableEq PrimitiveEnd]
    (support : Finset State) (representative : Option State)
    (f : State → PrimitiveEnd) {s : State}
    (hs : s ∈ support) :
    (normalizePlan support representative f).evaluate s = f s := by
  cases representative with
  | none => rfl
  | some r =>
      by_cases hrep : r ∈ support
      · by_cases hconstant : ∀ s' ∈ support, f s' = f r
        · change (if r ∈ support ∧ (∀ s' ∈ support, f s' = f r) then
              EconomyEnd.primitive (f r) else EconomyEnd.plan f).evaluate s = f s
          rw [ite_eq_left ⟨hrep, hconstant⟩]
          simp only [EconomyEnd.evaluate]
          exact (hconstant s hs).symm
        · change (if r ∈ support ∧ (∀ s' ∈ support, f s' = f r) then
              EconomyEnd.primitive (f r) else EconomyEnd.plan f).evaluate s = f s
          rw [ite_eq_right (fun hc => hconstant hc.2)]
          rfl
      · change (if r ∈ support ∧ (∀ s' ∈ support, f s' = f r) then
            EconomyEnd.primitive (f r) else EconomyEnd.plan f).evaluate s = f s
        rw [ite_eq_right (fun hc => hrep hc.1)]
        rfl

/-- A plan constant on nonempty support normalizes to its primitive end. -/
theorem normalizePlan_eq_primitive_of_constant {State PrimitiveEnd : Type}
    [DecidableEq State] [DecidableEq PrimitiveEnd]
    (support : Finset State) (representative : State)
    (f : State → PrimitiveEnd) (e : PrimitiveEnd)
    (hrepresentative : representative ∈ support)
    (hconstant : ∀ s ∈ support, f s = e) :
    normalizePlan support (some representative) f = .primitive e := by
  have hsame : ∀ s' ∈ support, f s' = f representative := by
    intro s' hs'
    calc
      f s' = e := hconstant s' hs'
      _ = f representative := (hconstant representative hrepresentative).symm
  change (if representative ∈ support ∧
      (∀ s' ∈ support, f s' = f representative) then
    EconomyEnd.primitive (f representative) else EconomyEnd.plan f) =
      EconomyEnd.primitive e
  rw [ite_eq_left ⟨hrepresentative, hsame⟩]
  exact congrArg EconomyEnd.primitive (hconstant representative hrepresentative)

/-- Requirements for a primitive end, interpreted branchwise for plans. -/
def EconomyEnd.requirement {State PrimitiveEnd Means : Type}
    (primitiveRequirement : PrimitiveEnd → Means → ℕ)
    [DecidableEq State] (support : Finset State)
    (e : EconomyEnd State PrimitiveEnd) : Means → ℕ :=
  match e with
  | .primitive p => primitiveRequirement p
  | .plan f => fun m => support.sup (fun s => primitiveRequirement (f s) m)

/-- Every supported branch's requirement is bounded by the finite plan
requirement. -/
theorem EconomyEnd.requirement_plan_ge {State PrimitiveEnd Means : Type}
    [DecidableEq State]
    (primitiveRequirement : PrimitiveEnd → Means → ℕ)
    (support : Finset State) (f : State → PrimitiveEnd) {s : State}
    (hs : s ∈ support) (m : Means) :
    primitiveRequirement (f s) m ≤
      (EconomyEnd.plan f).requirement primitiveRequirement support m := by
  change primitiveRequirement (f s) m ≤
    support.sup (fun s => primitiveRequirement (f s) m)
  exact Finset.le_sup (f := fun s => primitiveRequirement (f s) m) hs

/-- An auxiliary weak ordering over primitive scenario ends, with preorder
laws supplied once for each state. This is separate from an ActionFrame's
preference relation; bundle comparisons inside a frame remain governed by its
subjective teleological dominance field. -/
structure PrimitivePreferencePolicy (State PrimitiveEnd : Type) where
  weak : State → PrimitiveEnd → PrimitiveEnd → Prop
  weak_refl : ∀ s e, weak s e e
  weak_trans : ∀ s {a b c}, weak s a b → weak s b c → weak s a c

namespace PrimitivePreferencePolicy

/-- Strict preference induced by the primitive weak preorder. -/
def Strict {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd)
    (s : State) (a b : PrimitiveEnd) : Prop :=
  P.weak s a b ∧ ¬ P.weak s b a

/-- Weak improvement composed with strict improvement remains strict. -/
theorem weak_strict_trans {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (s : State)
    {a b c : PrimitiveEnd} (hab : P.weak s a b) (hbc : P.Strict s b c) :
    P.Strict s a c := by
  refine ⟨P.weak_trans s hab hbc.1, ?_⟩
  intro hca
  exact hbc.2 (P.weak_trans s hca hab)

/-- Strict improvement composed with weak improvement remains strict. -/
theorem strict_weak_trans {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (s : State)
    {a b c : PrimitiveEnd} (hab : P.Strict s a b) (hbc : P.weak s b c) :
    P.Strict s a c := by
  refine ⟨P.weak_trans s hab.1 hbc, ?_⟩
  intro hca
  exact hab.2 (P.weak_trans s hbc hca)

/-- Lift weak comparison at every plausible state and strict comparison at one
plausible state to a preference between state-contingent ends. -/
def PreferenceOnOutcomes {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (support : Finset State)
    (a b : State → PrimitiveEnd) : Prop :=
  (∀ s ∈ support, P.weak s (a s) (b s)) ∧
  (∃ s ∈ support, P.Strict s (a s) (b s))

/-- Lifted preference between primitive ends or contingent plans. -/
def Preference {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (support : Finset State)
    (a b : EconomyEnd State PrimitiveEnd) : Prop :=
  P.PreferenceOnOutcomes support (fun s => a.evaluate s) (fun s => b.evaluate s)

/-- The lifted relation is asymmetric. -/
theorem preference_asymm {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (support : Finset State)
    {a b : EconomyEnd State PrimitiveEnd}
    (hab : P.Preference support a b) : ¬ P.Preference support b a := by
  rintro ⟨_, ⟨s, hs, hstrict⟩⟩
  exact hstrict.2 ((hab.1 s hs))

/-- The lifted relation is transitive. -/
theorem preference_trans {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (support : Finset State)
    {a b c : EconomyEnd State PrimitiveEnd}
    (hab : P.Preference support a b) (hbc : P.Preference support b c) :
    P.Preference support a c := by
  refine ⟨?_, ?_⟩
  · intro s hs
    exact P.weak_trans s (hab.1 s hs) (hbc.1 s hs)
  · rcases hab.2 with ⟨s, hs, hstrict⟩
    exact ⟨s, hs, P.strict_weak_trans s hstrict (hbc.1 s hs)⟩

/-- The sure-thing comparison follows from statewise equality-or-weak gain and
one strict supported outcome. -/
theorem sure_thing_bridge {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (support : Finset State)
    (a b : EconomyEnd State PrimitiveEnd)
    (hpointwise : ∀ s ∈ support,
      a.evaluate s = b.evaluate s ∨ P.weak s (a.evaluate s) (b.evaluate s))
    (hstrict : ∃ s ∈ support, P.Strict s (a.evaluate s) (b.evaluate s)) :
    P.Preference support a b := by
  refine ⟨?_, hstrict⟩
  intro s hs
  rcases hpointwise s hs with hEq | hweak
  · change P.weak s (a.evaluate s) (b.evaluate s)
    rw [hEq]
    exact P.weak_refl s _
  · exact hweak

/-- The plausible-support bridge extracts the strict state already required
by the lifted preference definition. -/
theorem plausible_support {State PrimitiveEnd : Type}
    (P : PrimitivePreferencePolicy State PrimitiveEnd) (support : Finset State)
    {a b : EconomyEnd State PrimitiveEnd}
    (h : P.Preference support a b) :
    ∃ s ∈ support, P.Strict s (a.evaluate s) (b.evaluate s) := h.2

end PrimitivePreferencePolicy

end Praxeology

end
