/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Action
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card

/-!
# Allocation Technology and Local Ordinal Choice Laws

This module separates a homogeneous-use technology from stock and preference
assumptions. It proves a finite prefix result from local strict improvements:
adding an unused end improves an allocation, replacing a used lower-ranked end
with an unused higher-ranked end improves it, and preference is transitive.
The result is not a claim that every ActionFrame has these economic laws.
-/

@[expose] public section

namespace Praxeology

/-- An ordered list of distinct ends, each requiring the same positive number
of units of one focal means. This technology contains no stock or preference
assumptions. -/
structure HomogeneousUseTechnology (W : ActionFrame) (m : W.Means) (N : ℕ) where
  useEnd : Fin N → W.Ends
  useEnd_injective : Function.Injective useEnd
  quantum : ℕ
  quantum_positive : 0 < quantum
  requirement_exact : ∀ r, W.requirement (useEnd r) m = quantum

/-- The first k items in an ordered finite technology. -/
def rankedPrefix {N : ℕ} (k : ℕ) (_hk : k ≤ N) : Finset (Fin N) :=
  Finset.filter (fun r => r.val < k) Finset.univ

theorem rankedPrefix_card {N : ℕ} (k : ℕ) (hk : k ≤ N) :
    (rankedPrefix k hk).card = k := by
  dsimp [rankedPrefix]
  let emb (r : Fin k) : Fin N := ⟨r.val, Nat.lt_of_lt_of_le r.isLt hk⟩
  have emb_inj : Function.Injective emb := by
    intro x y h
    have hv : (emb x).val = (emb y).val :=
      congrArg (fun z : Fin N => z.val) h
    exact Fin.ext hv
  have h_filter :
      Finset.filter (fun r : Fin N => r.val < k) Finset.univ =
        Finset.univ.image emb := by
    ext r
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro ⟨_, hr⟩
      refine ⟨⟨r.val, hr⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rfl
    · rintro ⟨x, _, hx⟩
      have hxval : x.val = r.val := by
        simpa [emb] using congrArg Fin.val hx
      exact ⟨Finset.mem_univ _, by simpa [hxval] using x.isLt⟩
  rw [h_filter, Finset.card_image_of_injective _ emb_inj]
  simp

/-- Local ordinal laws over allocations of ranked uses. add_unused records
strict improvement from adding an attainable unused end. replace_lower records
strict improvement from replacing a used lower-ranked end with an unused
higher-ranked end while holding all other uses fixed. -/
structure LocalOrdinalAllocationLaws {W : ActionFrame} (i : W.Agent)
    (t : W.Moment) (h : W.History) {N : ℕ} (capacity : ℕ)
    (allocationEnd : Finset (Fin N) → W.Ends) : Prop where
  add_unused : ∀ S, S.card < capacity → ∀ r, r ∉ S →
    W.Preference i t h (allocationEnd (insert r S)) (allocationEnd S)
  replace_lower : ∀ S r s, r.val < s.val → r ∉ S → s ∈ S →
    W.Preference i t h (allocationEnd (insert r (S.erase s))) (allocationEnd S)
  transitive : ∀ e₁ e₂ e₃,
    W.Preference i t h e₁ e₂ → W.Preference i t h e₂ e₃ →
      W.Preference i t h e₁ e₃

/-- A stocked context connects the independent use technology to the actual
ActionFrame endowment and menu. The menu is complete for every allocation that
fits the stock; each action has an exact allocation and outcome. -/
structure StockedAllocationContext {W : ActionFrame} (i : W.Agent)
    (t : W.Moment) (h : W.History) (m : W.Means) {N : ℕ}
    (T : HomogeneousUseTechnology W m N) (capacity : ℕ) where
  capacity_le_N : capacity ≤ N
  remainder : ℕ
  /-- Below satiation, the stock has only a sub-quantum remainder. At
  satiation, additional stock is allowed and does not create another use. -/
  remainder_lt_quantum : capacity < N → remainder < T.quantum
  actual_stock : W.omega i t h m = capacity * T.quantum + remainder
  allocationEnd : Finset (Fin N) → W.Ends
  bundleStock : Finset (Fin N) → W.Means → ℕ
  allocation_stock_exact : ∀ S m',
    bundleStock S m' = S.sum (fun r => W.requirement (T.useEnd r) m')
  allocationOf : W.Action → Finset (Fin N)
  action_end : ∀ α, α ∈ W.A_cont i t h →
    W.End_of i α t h = allocationEnd (allocationOf α)
  /-- Every contemplated allocation action uses exactly the inputs represented
  by its selected uses. -/
  action_use_exact : ∀ α, α ∈ W.A_cont i t h → ∀ m',
    W.use_means α m' = bundleStock (allocationOf α) m'
  /-- Non-focal stocks cover each candidate allocation's additional inputs. -/
  other_stock_suffices : ∀ S m', m' ≠ m →
    bundleStock S m' ≤ W.omega i t h m'
  realize : Finset (Fin N) → W.Action
  realize_allocation : ∀ S, allocationOf (realize S) = S
  realize_contemplated : ∀ S, S.card ≤ capacity →
    realize S ∈ W.A_cont i t h
  realize_empty_is_passive : realize ∅ = W.alpha_zero

/-- At the finite-use ceiling, stock beyond the last complete use is
represented as surplus remainder. The strict remainder bound applies only
below the ceiling, so `N = 3`, quantum `1`, stock `4` has capacity `3` and
surplus `1`. -/
theorem satiated_capacity_allows_surplus_stock :
    ∃ capacity remainder : ℕ,
      capacity ≤ 3 ∧ capacity = 3 ∧ 4 = capacity * 1 + remainder ∧
        (capacity < 3 → remainder < 1) := by
  exact ⟨3, 1, by decide, rfl, by decide, by omega⟩

namespace StockedAllocationContext

/-- The same allocation technology and menu data can be read on any history
through the decision moment. Only the frame's bundle-invariance laws are used
to transport the history-indexed fields. -/
def transport
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h h' : W.History}
    {m : W.Means} {N : ℕ} {T : HomogeneousUseTechnology W m N}
    {capacity : ℕ} (C : StockedAllocationContext i t h m T capacity)
    (ht : W.mem_hist t h) (ht' : W.mem_hist t h') :
    StockedAllocationContext i t h' m T capacity := by
  refine
    { capacity_le_N := C.capacity_le_N
      remainder := C.remainder
      remainder_lt_quantum := C.remainder_lt_quantum
      actual_stock := ?_
      allocationEnd := C.allocationEnd
      bundleStock := C.bundleStock
      allocation_stock_exact := C.allocation_stock_exact
      allocationOf := C.allocationOf
      action_end := ?_
      action_use_exact := ?_
      other_stock_suffices := ?_
      realize := C.realize
      realize_allocation := C.realize_allocation
      realize_contemplated := ?_
      realize_empty_is_passive := C.realize_empty_is_passive }
  · calc
      W.omega i t h' m = W.omega i t h m :=
        W.omega_bundle_invariant i t m ht' ht
      _ = capacity * T.quantum + C.remainder := C.actual_stock
  · intro α hα
    have hα' : α ∈ W.A_cont i t h := by
      rw [W.A_cont_bundle_invariant i t ht ht']
      exact hα
    calc
      W.End_of i α t h' = W.End_of i α t h :=
        (W.End_of_bundle_invariant i α t ht ht').symm
      _ = C.allocationEnd (C.allocationOf α) := C.action_end α hα'
  · intro α hα m'
    have hα' : α ∈ W.A_cont i t h := by
      rw [W.A_cont_bundle_invariant i t ht ht']
      exact hα
    exact C.action_use_exact α hα' m'
  · intro S m' hm
    have hω : W.omega i t h' m' = W.omega i t h m' :=
      W.omega_bundle_invariant i t m' ht' ht
    rw [hω]
    exact C.other_stock_suffices S m' hm
  · intro S hS
    rw [← W.A_cont_bundle_invariant i t ht ht']
    exact C.realize_contemplated S hS

end StockedAllocationContext

namespace LocalOrdinalAllocationLaws

/-- Local preference laws are history invariant at a shared moment, as
required by the enclosing `ActionFrame`. -/
theorem transport
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h h' : W.History}
    {N capacity : ℕ} {allocationEnd : Finset (Fin N) → W.Ends}
    (L : LocalOrdinalAllocationLaws i t h capacity allocationEnd)
    (ht : W.mem_hist t h) (ht' : W.mem_hist t h') :
    LocalOrdinalAllocationLaws i t h' capacity allocationEnd := by
  have hPref := W.Preference_bundle_invariant i t ht ht'
  refine
    { add_unused := ?_
      replace_lower := ?_
      transitive := ?_ }
  · intro S hS r hr
    rw [← hPref]
    exact L.add_unused S hS r hr
  · intro S r s hrs hr hs
    rw [← hPref]
    exact L.replace_lower S r s hrs hr hs
  · intro e₁ e₂ e₃ h12 h23
    have h12' : W.Preference i t h e₁ e₂ := by rw [hPref]; exact h12
    have h23' : W.Preference i t h e₂ e₃ := by rw [hPref]; exact h23
    rw [← hPref]
    exact L.transitive e₁ e₂ e₃ h12' h23'

end LocalOrdinalAllocationLaws

theorem HomogeneousUseTechnology.requirement_sum_eq
    {W : ActionFrame} {m : W.Means} {N : ℕ}
    (T : HomogeneousUseTechnology W m N) (S : Finset (Fin N)) :
    S.sum (fun r => W.requirement (T.useEnd r) m) = S.card * T.quantum := by
  have hconst : ∀ r ∈ S, W.requirement (T.useEnd r) m = T.quantum :=
    fun r _ => T.requirement_exact r
  rw [Finset.sum_congr rfl hconst, Finset.sum_const]
  rfl

theorem StockedAllocationContext.action_use_focal
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {m : W.Means} {N : ℕ} {T : HomogeneousUseTechnology W m N}
    {capacity : ℕ} (C : StockedAllocationContext i t h m T capacity)
    (α : W.Action) (hα : α ∈ W.A_cont i t h) :
    W.use_means α m = (C.allocationOf α).card * T.quantum := by
  rw [C.action_use_exact α hα m, C.allocation_stock_exact,
    T.requirement_sum_eq]

private theorem rankedPrefix_eq_or_preferred
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {N capacity : ℕ} (hk : capacity ≤ N)
    (allocationEnd : Finset (Fin N) → W.Ends)
    (laws : LocalOrdinalAllocationLaws i t h capacity allocationEnd)
    (S : Finset (Fin N)) (hcard : S.card ≤ capacity) :
    S = rankedPrefix capacity hk ∨
      W.Preference i t h (allocationEnd (rankedPrefix capacity hk)) (allocationEnd S) := by
  let P := rankedPrefix capacity hk
  have hPcard : P.card = capacity := by
    dsimp [P]
    exact rankedPrefix_card capacity hk
  let measure (A : Finset (Fin N)) := capacity - (A ∩ P).card
  have hmain : ∀ n, ∀ A : Finset (Fin N), A.card ≤ capacity →
      measure A = n →
      A = P ∨ W.Preference i t h (allocationEnd P) (allocationEnd A) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hA hmeasure
      by_cases hEq : A = P
      · exact Or.inl hEq
      · have hscore_le : (A ∩ P).card ≤ capacity := by
          calc
            (A ∩ P).card ≤ P.card := Finset.card_le_card Finset.inter_subset_right
            _ = capacity := hPcard
        by_cases hbase : n = 0
        · have hscore : (A ∩ P).card = capacity := by
            dsimp [measure] at hmeasure
            omega
          have hInterEq : A ∩ P = P :=
            Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hscore, hPcard])
          have hPsubA : P ⊆ A := by
            intro x hx
            have hx' : x ∈ A ∩ P := by rw [hInterEq]; exact hx
            exact (Finset.mem_inter.mp hx').1
          exact Or.inl
            (Finset.eq_of_subset_of_card_le hPsubA (by rw [hPcard]; exact hA)).symm
        have hscore_lt : (A ∩ P).card < capacity := by
          dsimp [measure] at hmeasure
          omega
        have hmiss : (P \ A).Nonempty := by
          by_contra hempty
          have hPsubA : P ⊆ A := by
            intro x hx
            by_contra hxA
            exact hempty ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxA⟩⟩
          have hInterEq : A ∩ P = P := by
            ext x
            simp only [Finset.mem_inter]
            exact ⟨fun hx => hx.2, fun hx => ⟨hPsubA hx, hx⟩⟩
          have : (A ∩ P).card = capacity := by rw [hInterEq, hPcard]
          omega
        obtain ⟨r, hr⟩ := hmiss
        have hrP : r ∈ P := (Finset.mem_sdiff.mp hr).1
        have hrA : r ∉ A := (Finset.mem_sdiff.mp hr).2
        have hrlt : r.val < capacity := (Finset.mem_filter.mp hrP).2
        by_cases hSmall : A.card < capacity
        · let A' := insert r A
          have hstep : W.Preference i t h (allocationEnd A') (allocationEnd A) :=
            laws.add_unused A hSmall r hrA
          have hcard' : A'.card ≤ capacity := by
            dsimp [A']
            rw [Finset.card_insert_of_notMem hrA]
            omega
          have hInter : A' ∩ P = insert r (A ∩ P) := by
            ext x
            simp [A', Finset.mem_inter, Finset.mem_insert, hrP]
          have hscore' : (A' ∩ P).card = (A ∩ P).card + 1 := by
            rw [hInter, Finset.card_insert_of_notMem
              (by intro hx; exact hrA (Finset.mem_inter.mp hx).1)]
          have hmeasure' : measure A' < n := by
            dsimp [measure]
            rw [hscore']
            dsimp [measure] at hmeasure
            omega
          have hrec := ih (measure A') hmeasure' A' hcard' rfl
          rcases hrec with hEq' | hpref'
          · right
            rw [hEq'] at hstep
            exact hstep
          · exact Or.inr (laws.transitive _ _ _ hpref' hstep)
        · have hAcard : A.card = capacity := by omega
          have hout : ∃ s ∈ A, s ∉ P := by
            by_contra hnone
            push Not at hnone
            have hAsubP : A ⊆ P := fun x hx => hnone x hx
            have hEq' := Finset.eq_of_subset_of_card_le hAsubP (by rw [hPcard, hAcard])
            exact hEq hEq'
          obtain ⟨s, hsA, hsP⟩ := hout
          have hsge : capacity ≤ s.val := by
            by_contra hnot
            have hslt : s.val < capacity := by omega
            exact hsP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hslt⟩)
          have hrs : r.val < s.val := Nat.lt_of_lt_of_le hrlt hsge
          let A' := insert r (A.erase s)
          have hstep : W.Preference i t h (allocationEnd A') (allocationEnd A) :=
            laws.replace_lower A r s hrs hrA hsA
          have hcard' : A'.card ≤ capacity := by
            dsimp [A']
            rw [Finset.card_insert_of_notMem]
            · rw [Finset.card_erase_of_mem hsA]
              omega
            · intro hrErase
              exact hrA (Finset.mem_of_mem_erase hrErase)
          have hInter : A' ∩ P = insert r (A ∩ P) := by
            ext x
            by_cases hxr : x = r
            · subst x
              simp [A', hrP, hrA]
            · have hnot_s : x ∈ P → x ≠ s := by
                intro hx heq
                exact hsP (heq ▸ hx)
              simp only [A', Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
              constructor
              · rintro ⟨hA, hP⟩
                rcases hA with hxr' | ⟨_, hA⟩
                · exact (hxr hxr').elim
                · exact Or.inr ⟨hA, hP⟩
              · intro hx
                rcases hx with hxr' | ⟨hA, hP⟩
                · exact (hxr hxr').elim
                · exact ⟨Or.inr ⟨hnot_s hP, hA⟩, hP⟩
          have hscore' : (A' ∩ P).card = (A ∩ P).card + 1 := by
            rw [hInter, Finset.card_insert_of_notMem
              (by intro hx; exact hrA (Finset.mem_inter.mp hx).1)]
          have hmeasure' : measure A' < n := by
            dsimp [measure]
            rw [hscore']
            dsimp [measure] at hmeasure
            omega
          have hrec := ih (measure A') hmeasure' A' hcard' rfl
          rcases hrec with hEq' | hpref'
          · right
            rw [hEq'] at hstep
            exact hstep
          · exact Or.inr (laws.transitive _ _ _ hpref' hstep)
  exact hmain (measure S) S hcard rfl

/-- Under the local ordinal laws, the ranked prefix is either the chosen set
itself or strictly preferred to it whenever the set fits the available number
of homogeneous-use quanta. This theorem uses no premise that the prefix
globally dominates all feasible allocations. -/
theorem ranked_prefix_optimality
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {N capacity : ℕ} (hk : capacity ≤ N)
    (allocationEnd : Finset (Fin N) → W.Ends)
    (laws : LocalOrdinalAllocationLaws i t h capacity allocationEnd)
    (S : Finset (Fin N)) (hcard : S.card ≤ capacity) :
    S = rankedPrefix capacity hk ∨
      W.Preference i t h (allocationEnd (rankedPrefix capacity hk)) (allocationEnd S) :=
  rankedPrefix_eq_or_preferred hk allocationEnd laws S hcard

/-- The replacement law alone orders singleton allocations: holding the
allocation context fixed, an allocation containing a higher-ranked use is
preferred to the singleton allocation containing a lower-ranked use. -/
theorem LocalOrdinalAllocationLaws.higher_ranked_singleton_preferred
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {N capacity : ℕ} {allocationEnd : Finset (Fin N) → W.Ends}
    (laws : LocalOrdinalAllocationLaws i t h capacity allocationEnd)
    (r s : Fin N) (hrs : r.val < s.val) :
    W.Preference i t h (allocationEnd {r}) (allocationEnd {s}) := by
  have hrne : r ≠ s := by
    intro hEq
    have : r.val = s.val := congrArg Fin.val hEq
    omega
  have hrnot : r ∉ ({s} : Finset (Fin N)) := by simp [hrne]
  have hs : s ∈ ({s} : Finset (Fin N)) := Finset.mem_singleton_self _
  have hreplace := laws.replace_lower ({s} : Finset (Fin N)) r s hrs hrnot hs
  simpa using hreplace

/-- Under the same technology and ordinal allocation laws, the marginal
singleton allocation at the smaller capacity is preferred to the one at the
larger capacity. The capacities parameterize the two resource contexts; the
shared `allocationEnd` and preference law are the ceteris-paribus premises. -/
theorem ranked_prefix_marginal_preference
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {N capacity : ℕ} {allocationEnd : Finset (Fin N) → W.Ends}
    (laws : LocalOrdinalAllocationLaws i t h capacity allocationEnd)
    (k₁ k₂ : ℕ) (hk₁ : 1 ≤ k₁) (hk₂ : k₂ ≤ N) (horder : k₁ < k₂) :
    W.Preference i t h
      (allocationEnd ({⟨k₁ - 1, by omega⟩} : Finset (Fin N)))
      (allocationEnd ({⟨k₂ - 1, by omega⟩} : Finset (Fin N))) := by
  let r : Fin N := ⟨k₁ - 1, by omega⟩
  let s : Fin N := ⟨k₂ - 1, by omega⟩
  have hrs : r.val < s.val := by
    change k₁ - 1 < k₂ - 1
    omega
  simpa [r, s] using laws.higher_ranked_singleton_preferred r s hrs

/-- Difference of adjacent ranked prefixes is the singleton of the marginal use. -/
theorem diff_rankedPrefix_pred {N : ℕ} (k : ℕ) (hk_pos : 1 ≤ k) (hk : k ≤ N) :
    rankedPrefix k hk \ rankedPrefix (k - 1) (by omega) =
      {⟨k - 1, by omega⟩} := by
  ext r
  rw [Finset.mem_sdiff, Finset.mem_singleton]
  dsimp [rankedPrefix]
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨_, hr_lt⟩, h_not⟩
    have hr_ge : k - 1 ≤ r.val := by
      by_contra hc
      have hlt : r.val < k - 1 := by omega
      exact h_not ⟨Finset.mem_univ _, hlt⟩
    have hr_eq : r.val = k - 1 := by omega
    exact Fin.ext hr_eq
  · rintro rfl
    refine ⟨⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
    intro ⟨_, hbad⟩
    dsimp at hbad
    omega

/-- Mengerian backward value imputation derived from local ordinal allocation laws:
having capacity `k` strictly dominates capacity `k - 1`, and the loss of that unit of capacity
is valued as the loss of the single marginal use `k - 1`. -/
theorem ordinal_backward_value_imputation
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {N : ℕ} {capacity : ℕ} (hk_pos : 1 ≤ capacity) (hk : capacity ≤ N)
    (allocationEnd : Finset (Fin N) → W.Ends)
    (laws : LocalOrdinalAllocationLaws i t h capacity allocationEnd) :
    (rankedPrefix capacity hk \ rankedPrefix (capacity - 1) (by omega) =
      {⟨capacity - 1, by omega⟩}) ∧
    W.Preference i t h (allocationEnd (rankedPrefix capacity hk))
      (allocationEnd (rankedPrefix (capacity - 1) (by omega))) := by
  have hdiff := diff_rankedPrefix_pred capacity hk_pos hk
  refine ⟨hdiff, ?_⟩
  have h_le_N : capacity - 1 ≤ N := by omega
  have hcard : (rankedPrefix (capacity - 1) h_le_N).card < capacity := by
    rw [rankedPrefix_card (capacity - 1) h_le_N]
    omega
  have hnot : (⟨capacity - 1, by omega⟩ : Fin N) ∉
      rankedPrefix (capacity - 1) h_le_N := by
    dsimp [rankedPrefix]
    rw [Finset.mem_filter]
    rintro ⟨_, hbad⟩
    dsimp at hbad
    omega
  have hadd := laws.add_unused (rankedPrefix (capacity - 1) h_le_N) hcard
    ⟨capacity - 1, by omega⟩ hnot
  have hinsert : insert (⟨capacity - 1, by omega⟩ : Fin N)
      (rankedPrefix (capacity - 1) h_le_N) = rankedPrefix capacity hk := by
    ext r
    rw [Finset.mem_insert]
    dsimp [rankedPrefix]
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro (rfl | ⟨_, hr_lt⟩)
      · exact ⟨Finset.mem_univ _, by dsimp; omega⟩
      · exact ⟨Finset.mem_univ _, by omega⟩
    · rintro ⟨_, hr_lt⟩
      by_cases hr : r.val = capacity - 1
      · left; exact Fin.ext hr
      · right; exact ⟨Finset.mem_univ _, by omega⟩
  rw [hinsert] at hadd
  exact hadd


/-! ## Finite ordinal witness

The existing finite branching frame has a concrete stock of two focal units.
The following ranked ends witness local preference laws in that frame, whose
own action type does not realize every ranked subset. The finite allocation
enumeration below makes the complete menu and execution histories explicit.
`Praxeology.Marginal.AllocationActionFrame` separately instantiates the
allocation context and purposeful-choice result inside an `ActionFrame`.
-/

/-- Higher urgency is represented by a larger amount of a non-focal attribute;
each ranked end still requires exactly one focal unit. -/
def finiteRankedEndWeight (r : Fin 3) : ℕ := 3 - r.val

def finiteRankedUseEnd (r : Fin 3) : FiniteBranchingModel.Ends :=
  ModelEnd.bundle (fun m =>
    if m = (0 : Fin 3) then 1
    else if m = (1 : Fin 3) then finiteRankedEndWeight r
    else 0)

/-- A three-end, homogeneous, one-unit technology in the finite branching
frame. -/
def finiteModelRankedTechnology :
    HomogeneousUseTechnology FiniteBranchingModel (0 : Fin 3) 3 where
  useEnd := finiteRankedUseEnd
  useEnd_injective := by
    intro r s h
    have hweight : finiteRankedEndWeight r = finiteRankedEndWeight s := by
      have h' := congrArg
        (fun e : ModelEnd =>
          match e with
          | .bundle b => b (1 : Fin 3)
          | _ => 0) h
      simpa [finiteRankedUseEnd] using h'
    apply Fin.ext
    dsimp [finiteRankedEndWeight] at hweight
    omega
  quantum := 1
  quantum_positive := by decide
  requirement_exact := by
    intro r
    change finite_model_requirement (finiteRankedUseEnd r) 0 = 1
    simp [finiteRankedUseEnd, finite_model_requirement]

/-- Allocation outcomes aggregate the physical requirements of the selected
ranked ends. -/
def finiteModelRankedAllocationEnd (S : Finset (Fin 3)) : ModelEnd :=
  ModelEnd.bundle (fun m => S.sum fun r =>
    finite_model_requirement (finiteRankedUseEnd r) m)

private theorem finiteModelRankedAllocationEnd_rank (S : Finset (Fin 3)) :
    end_rank (finiteModelRankedAllocationEnd S) =
      10 * (S.card + S.sum finiteRankedEndWeight) := by
  have h0 : S.sum (fun r => finite_model_requirement
      (finiteRankedUseEnd r) (0 : Fin 3)) = S.card := by
    simp [finiteRankedUseEnd, finite_model_requirement]
  have h1 : S.sum (fun r => finite_model_requirement
      (finiteRankedUseEnd r) (1 : Fin 3)) =
      S.sum (fun r => finiteRankedEndWeight r) := by
    simp [finiteRankedUseEnd, finite_model_requirement]
  have h2 : S.sum (fun r => finite_model_requirement
      (finiteRankedUseEnd r) (2 : Fin 3)) = 0 := by
    simp [finiteRankedUseEnd, finite_model_requirement]
  change 10 * ((S.sum (fun r => finite_model_requirement
      (finiteRankedUseEnd r) (0 : Fin 3)) +
    S.sum (fun r => finite_model_requirement
      (finiteRankedUseEnd r) (1 : Fin 3))) +
    S.sum (fun r => finite_model_requirement
      (finiteRankedUseEnd r) (2 : Fin 3))) = _
  rw [h0, h1, h2]
  simp

/-- The frame's concrete endowment is exactly two one-unit ranked uses. -/
theorem finite_model_ranked_stock_is_two_units :
    FiniteBranchingModel.omega (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
      (0 : Fin 3) = 2 := by
  rfl

/-- The finite frame's ordinal preference validates adding any unused ranked
end while fewer than `capacity` ends are selected. -/
theorem finiteModelRankedOrdinalLawsFor (capacity : ℕ) :
    LocalOrdinalAllocationLaws (W := FiniteBranchingModel)
      (0 : Fin 2) (0 : Fin 4) (0 : Fin 3) capacity finiteModelRankedAllocationEnd := {
  add_unused := by
    intro S _ r hr
    change end_rank (finiteModelRankedAllocationEnd S) <
      end_rank (finiteModelRankedAllocationEnd (insert r S))
    have hcard : (insert r S).card = S.card + 1 :=
      Finset.card_insert_of_notMem hr
    have hsum : (insert r S).sum finiteRankedEndWeight =
        finiteRankedEndWeight r + S.sum finiteRankedEndWeight :=
      Finset.sum_insert hr
    rw [finiteModelRankedAllocationEnd_rank, finiteModelRankedAllocationEnd_rank,
      hcard, hsum]
    have hrlt : r.val < 3 := r.isLt
    omega
  replace_lower := by
    intro S r s hrs hr hs
    have hrErase : r ∉ S.erase s := by
      intro hmem
      exact hr (Finset.mem_of_mem_erase hmem)
    have hcard : (insert r (S.erase s)).card = S.card := by
      rw [Finset.card_insert_of_notMem hrErase, Finset.card_erase_of_mem hs]
      have hspos : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
      omega
    have hsumNew : (insert r (S.erase s)).sum finiteRankedEndWeight =
        finiteRankedEndWeight r + (S.erase s).sum finiteRankedEndWeight :=
      Finset.sum_insert hrErase
    have hsumOld : finiteRankedEndWeight s +
        (S.erase s).sum finiteRankedEndWeight = S.sum finiteRankedEndWeight :=
      Finset.add_sum_erase S finiteRankedEndWeight hs
    change end_rank (finiteModelRankedAllocationEnd S) <
      end_rank (finiteModelRankedAllocationEnd (insert r (S.erase s)))
    rw [finiteModelRankedAllocationEnd_rank, finiteModelRankedAllocationEnd_rank,
      hcard, hsumNew, ← hsumOld]
    simp [finiteRankedEndWeight]
    omega
  transitive := by
    intro e₁ e₂ e₃ h₁₂ h₂₃
    change end_rank e₂ < end_rank e₁ at h₁₂
    change end_rank e₃ < end_rank e₂ at h₂₃
    change end_rank e₃ < end_rank e₁
    omega
}

/-- The concrete two-unit-stock instance of the finite local ordinal laws. -/
theorem finiteModelRankedOrdinalLaws :
    LocalOrdinalAllocationLaws (W := FiniteBranchingModel)
      (0 : Fin 2) (0 : Fin 4) (0 : Fin 3) 2 finiteModelRankedAllocationEnd :=
  finiteModelRankedOrdinalLawsFor 2

/-- In the finite model with two units, the top-two ranked allocation is
strictly preferred to selecting the first and third ends. -/
theorem finite_model_top_two_beats_nonprefix :
    FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
      (finiteModelRankedAllocationEnd ({0, 1} : Finset (Fin 3)))
      (finiteModelRankedAllocationEnd ({0, 2} : Finset (Fin 3))) := by
  let hk : 2 ≤ 3 := by omega
  have hprefix : rankedPrefix 2 hk = ({0, 1} : Finset (Fin 3)) := by
    ext r
    simp [rankedPrefix]
    omega
  have hchoice := ranked_prefix_optimality
    (W := FiniteBranchingModel) (i := (0 : Fin 2)) (t := (0 : Fin 4))
    (h := (0 : Fin 3)) (N := 3) (capacity := 2) hk
    finiteModelRankedAllocationEnd finiteModelRankedOrdinalLaws
    ({0, 2} : Finset (Fin 3)) (by norm_num)
  have hne : ({0, 2} : Finset (Fin 3)) ≠ rankedPrefix 2 hk := by
    rw [hprefix]
    decide
  rcases hchoice with heq | hpreferred
  · exact (hne heq).elim
  · rw [hprefix] at hpreferred
    exact hpreferred

/-! ### A complete finite allocation-choice witness

This small model makes all seven stock-feasible allocations available as
actions. Feasibility is exactly the two-unit stock constraint, each action has
an explicit allocation history, and ends inherit the ordinal ranking above.
The proof of purposeful choice uses the local addition and replacement laws;
the globally best allocation is not included as a premise.
-/

/-- Every subset of the three ranked uses is a contemplated allocation action. -/
def finiteCompleteAllocationMenu : Finset (Finset (Fin 3)) := Finset.univ

/-- Allocations that fit a two-unit stock when each ranked use costs one unit. -/
def finiteTwoUnitAllocationMenu : Finset (Finset (Fin 3)) :=
  finiteCompleteAllocationMenu.filter (fun S => S.card ≤ 2)

/-- The complete feasible menu consists of the empty allocation, three
single-use allocations, and three two-use allocations. -/
theorem finiteTwoUnitAllocationMenu_explicit :
    finiteTwoUnitAllocationMenu =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}} := by
  decide

/-- The feasible menu for a one-unit technology at capacity zero, one, and
two. -/
theorem finite_one_quantum_stock_menu_table :
    (finiteCompleteAllocationMenu.filter (fun S => S.card ≤ 0)) = {∅} ∧
    (finiteCompleteAllocationMenu.filter (fun S => S.card ≤ 1)) =
      {∅, {0}, {1}, {2}} ∧
    finiteTwoUnitAllocationMenu =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}} := by
  decide

/-- The finite model's allocation action directly selects a subset of ranked
uses. -/
abbrev FiniteAllocationAction := Finset (Fin 3)

/-- An execution history is either the passive baseline or the history that
records the allocation selected at the decision node. -/
abbrev FiniteAllocationHistory := Option FiniteAllocationAction

/-- Read the enacted allocation from an execution history. -/
def finiteAllocationEnacted : FiniteAllocationHistory → FiniteAllocationAction
  | none => ∅
  | some S => S

/-- Each allocation action has an explicit history on which it is enacted. -/
theorem finite_allocation_has_execution_history (S : FiniteAllocationAction) :
    ∃ h : FiniteAllocationHistory, finiteAllocationEnacted h = S := by
  exact ⟨some S, rfl⟩

/-- The physical end associated with a finite allocation. -/
def finiteAllocationEnd (S : FiniteAllocationAction) : ModelEnd :=
  finiteModelRankedAllocationEnd S

/-- Purposeful allocation in the finite model: the action fits stock, either
leaves the agent at the passive baseline or improves on it, and no feasible
allocation is strictly preferred to it. The final conjunct records enactment
on an explicit branch. -/
def finiteAllocationPurposeful (capacity : ℕ) (S : FiniteAllocationAction) : Prop :=
  S.card ≤ capacity ∧
  (S = ∅ ∨ FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
    (finiteAllocationEnd S) (finiteAllocationEnd ∅)) ∧
  (∀ R : FiniteAllocationAction, R.card ≤ capacity →
    ¬ FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
      (finiteAllocationEnd R) (finiteAllocationEnd S)) ∧
  ∃ h : FiniteAllocationHistory, finiteAllocationEnacted h = S

/-- A purposeful allocation in the finite three-use model selects exactly the
ranked prefix allowed by its stock. -/
theorem finite_allocation_purposeful_is_ranked_prefix
    (capacity : ℕ) (hcapacity : capacity ≤ 3) (S : FiniteAllocationAction)
    (hS : finiteAllocationPurposeful capacity S) :
    S = rankedPrefix capacity hcapacity := by
  have hchoice := ranked_prefix_optimality hcapacity
    finiteModelRankedAllocationEnd (finiteModelRankedOrdinalLawsFor capacity)
    S hS.1
  rcases hchoice with heq | hbetter
  · exact heq
  · exact (hS.2.2.1 (rankedPrefix capacity hcapacity)
      (by rw [rankedPrefix_card]) hbetter).elim

/-- For every capacity through three uses, the ranked prefix is purposeful:
it is feasible, improves on the passive baseline when nonempty, is undominated
in the complete feasible menu, and has an execution-history witness. -/
theorem finite_ranked_prefix_is_purposeful
    (capacity : ℕ) (hcapacity : capacity ≤ 3) :
    finiteAllocationPurposeful capacity (rankedPrefix capacity hcapacity) := by
  let P := rankedPrefix capacity hcapacity
  have hPcard : P.card = capacity := rankedPrefix_card capacity hcapacity
  refine ⟨by simpa [P] using hPcard.le, ?_, ?_, ⟨some P, rfl⟩⟩
  · by_cases hEmpty : P = ∅
    · exact Or.inl hEmpty
    · right
      change end_rank (finiteModelRankedAllocationEnd ∅) <
        end_rank (finiteModelRankedAllocationEnd P)
      rw [finiteModelRankedAllocationEnd_rank, finiteModelRankedAllocationEnd_rank]
      simp only [Finset.card_empty, Finset.sum_empty]
      have hnonempty : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hpositive : 0 < P.card := Finset.card_pos.mpr hnonempty
      omega
  · intro R hR hRbetter
    have hchoice := ranked_prefix_optimality hcapacity
      finiteModelRankedAllocationEnd (finiteModelRankedOrdinalLawsFor capacity)
      R hR
    rcases hchoice with heq | hbetter
    · subst R
      exact FiniteBranchingModel.pref_asymm (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
        hRbetter hRbetter
    · exact FiniteBranchingModel.pref_asymm (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
        hbetter hRbetter

/-- At one unit of stock, the highest-ranked use is purposeful. -/
theorem finite_one_unit_stock_choice :
    finiteAllocationPurposeful 1 ({0} : Finset (Fin 3)) := by
  have hcap : 1 ≤ 3 := by omega
  have hprefix : rankedPrefix 1 hcap = ({0} : Finset (Fin 3)) := by
    ext r
    simp [rankedPrefix]
  rw [← hprefix]
  exact finite_ranked_prefix_is_purposeful 1 hcap

/-- At two units of stock, the two highest-ranked uses are purposeful. -/
theorem finite_two_unit_stock_choice :
    finiteAllocationPurposeful 2 ({0, 1} : Finset (Fin 3)) := by
  have hcap : 2 ≤ 3 := by omega
  have hprefix : rankedPrefix 2 hcap = ({0, 1} : Finset (Fin 3)) := by
    ext r
    simp [rankedPrefix]
    omega
  rw [← hprefix]
  exact finite_ranked_prefix_is_purposeful 2 hcap

/-- Exact feasible-allocation menu when each use consumes two units. -/
def finiteTwoQuantumAllocationMenu (stock : ℕ) : Finset (Finset (Fin 3)) :=
  finiteCompleteAllocationMenu.filter (fun S => 2 * S.card ≤ stock)

/-- The full finite table for two-unit requirements: stocks zero and one permit
only the empty allocation; two and three permit any one use; four permits any
two uses. -/
theorem finite_two_quantum_stock_menu_table :
    finiteTwoQuantumAllocationMenu 0 = {∅} ∧
    finiteTwoQuantumAllocationMenu 1 = {∅} ∧
    finiteTwoQuantumAllocationMenu 2 = {∅, {0}, {1}, {2}} ∧
    finiteTwoQuantumAllocationMenu 3 = {∅, {0}, {1}, {2}} ∧
    finiteTwoQuantumAllocationMenu 4 =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}} := by
  decide

/-- For two-unit homogeneous uses, the greatest feasible capacity at stocks
zero through four is `0, 0, 1, 1, 2`. -/
theorem finite_two_quantum_capacity_table :
    (0 / 2 : ℕ) = 0 ∧ (1 / 2 : ℕ) = 0 ∧ (2 / 2 : ℕ) = 1 ∧
    (3 / 2 : ℕ) = 1 ∧ (4 / 2 : ℕ) = 2 := by
  norm_num

/-- A two-unit stock bound is exactly the floor capacity expressed by natural
division. -/
theorem finite_two_quantum_feasible_iff_capacity
    (stock : ℕ) (S : Finset (Fin 3)) :
    2 * S.card ≤ stock ↔ S.card ≤ stock / 2 := by
  omega

/-- The two-unit technology changes the focal input requirement of every
ranked end to two; the ranked non-focal attribute remains the one used in the
unit-quantum witness. -/
def finiteTwoQuantumRankedUseEnd (r : Fin 3) : ModelEnd :=
  ModelEnd.bundle (fun m =>
    if m = (0 : Fin 3) then 2
    else if m = (1 : Fin 3) then finiteRankedEndWeight r
    else 0)

/-- Three ranked uses, each requiring exactly two units of the focal means. -/
def finiteTwoQuantumRankedTechnology :
    HomogeneousUseTechnology FiniteBranchingModel (0 : Fin 3) 3 where
  useEnd := finiteTwoQuantumRankedUseEnd
  useEnd_injective := by
    intro r s h
    have hweight : finiteRankedEndWeight r = finiteRankedEndWeight s := by
      have h' := congrArg
        (fun e : ModelEnd =>
          match e with
          | .bundle b => b (1 : Fin 3)
          | _ => 0) h
      simpa [finiteTwoQuantumRankedUseEnd] using h'
    apply Fin.ext
    dsimp [finiteRankedEndWeight] at hweight
    omega
  quantum := 2
  quantum_positive := by decide
  requirement_exact := by
    intro r
    change finite_model_requirement (finiteTwoQuantumRankedUseEnd r) 0 = 2
    simp [finiteTwoQuantumRankedUseEnd, finite_model_requirement]

/-- The end associated with a two-quantum allocation records both its actual
focal input requirement and the same ranked non-focal attributes. -/
def finiteTwoQuantumAllocationEnd (S : Finset (Fin 3)) : ModelEnd :=
  ModelEnd.bundle (fun m => S.sum fun r =>
    finite_model_requirement (finiteTwoQuantumRankedTechnology.useEnd r) m)

private theorem finiteTwoQuantumAllocationEnd_rank (S : Finset (Fin 3)) :
    end_rank (finiteTwoQuantumAllocationEnd S) =
      10 * (2 * S.card + S.sum finiteRankedEndWeight) := by
  have h0 : S.sum (fun r => finite_model_requirement
      (finiteTwoQuantumRankedTechnology.useEnd r) (0 : Fin 3)) = 2 * S.card := by
    simp [finiteTwoQuantumRankedTechnology, finiteTwoQuantumRankedUseEnd,
      finite_model_requirement, Finset.sum_const]
    omega
  have h1 : S.sum (fun r => finite_model_requirement
      (finiteTwoQuantumRankedTechnology.useEnd r) (1 : Fin 3)) =
      S.sum finiteRankedEndWeight := by
    simp [finiteTwoQuantumRankedTechnology, finiteTwoQuantumRankedUseEnd,
      finite_model_requirement]
  have h2 : S.sum (fun r => finite_model_requirement
      (finiteTwoQuantumRankedTechnology.useEnd r) (2 : Fin 3)) = 0 := by
    simp [finiteTwoQuantumRankedTechnology, finiteTwoQuantumRankedUseEnd,
      finite_model_requirement]
  change 10 * ((S.sum (fun r => finite_model_requirement
      (finiteTwoQuantumRankedTechnology.useEnd r) (0 : Fin 3)) +
    S.sum (fun r => finite_model_requirement
      (finiteTwoQuantumRankedTechnology.useEnd r) (1 : Fin 3))) +
    S.sum (fun r => finite_model_requirement
      (finiteTwoQuantumRankedTechnology.useEnd r) (2 : Fin 3))) = _
  rw [h0, h1, h2]
  simp

/-- The same local addition, replacement, and transitivity laws hold for the
two-unit ends; their focal requirement is not borrowed from the unit-use
allocation end. -/
theorem finiteTwoQuantumOrdinalLawsFor (capacity : ℕ) :
    LocalOrdinalAllocationLaws (W := FiniteBranchingModel)
      (0 : Fin 2) (0 : Fin 4) (0 : Fin 3) capacity
      finiteTwoQuantumAllocationEnd := {
  add_unused := by
    intro S _ r hr
    change end_rank (finiteTwoQuantumAllocationEnd S) <
      end_rank (finiteTwoQuantumAllocationEnd (insert r S))
    have hcard : (insert r S).card = S.card + 1 :=
      Finset.card_insert_of_notMem hr
    have hsum : (insert r S).sum finiteRankedEndWeight =
        finiteRankedEndWeight r + S.sum finiteRankedEndWeight :=
      Finset.sum_insert hr
    rw [finiteTwoQuantumAllocationEnd_rank, finiteTwoQuantumAllocationEnd_rank,
      hcard, hsum]
    have hrlt : r.val < 3 := r.isLt
    simp [finiteRankedEndWeight]
    omega
  replace_lower := by
    intro S r s hrs hr hs
    have hrErase : r ∉ S.erase s := by
      intro hmem
      exact hr (Finset.mem_of_mem_erase hmem)
    have hcard : (insert r (S.erase s)).card = S.card := by
      rw [Finset.card_insert_of_notMem hrErase, Finset.card_erase_of_mem hs]
      have hspos : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
      omega
    have hsumNew : (insert r (S.erase s)).sum finiteRankedEndWeight =
        finiteRankedEndWeight r + (S.erase s).sum finiteRankedEndWeight :=
      Finset.sum_insert hrErase
    have hsumOld : finiteRankedEndWeight s +
        (S.erase s).sum finiteRankedEndWeight = S.sum finiteRankedEndWeight :=
      Finset.add_sum_erase S finiteRankedEndWeight hs
    change end_rank (finiteTwoQuantumAllocationEnd S) <
      end_rank (finiteTwoQuantumAllocationEnd (insert r (S.erase s)))
    rw [finiteTwoQuantumAllocationEnd_rank, finiteTwoQuantumAllocationEnd_rank,
      hcard, hsumNew, ← hsumOld]
    simp [finiteRankedEndWeight]
    omega
  transitive := by
    intro e₁ e₂ e₃ h₁₂ h₂₃
    change end_rank e₂ < end_rank e₁ at h₁₂
    change end_rank e₃ < end_rank e₂ at h₂₃
    change end_rank e₃ < end_rank e₁
    omega
}

/-- Ordinally undominated selections for the two-unit technology. Feasibility
is stated as `2 * card ≤ stock`, and preferences compare the matching two-unit
allocation ends. -/
def finiteTwoQuantumUndominatedChoice (stock : ℕ) (S : Finset (Fin 3)) : Prop :=
  2 * S.card ≤ stock ∧
  (S = ∅ ∨ FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
    (finiteTwoQuantumAllocationEnd S) (finiteTwoQuantumAllocationEnd ∅)) ∧
  (∀ R : Finset (Fin 3), 2 * R.card ≤ stock →
    ¬ FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
      (finiteTwoQuantumAllocationEnd R) (finiteTwoQuantumAllocationEnd S))

/-- At stock `s`, the prefix capacity is the number of complete two-unit uses,
capped by the three uses represented in this finite technology. -/
def finiteTwoQuantumStockCapacity (stock : ℕ) : ℕ := min (stock / 2) 3

/-- The ranked prefix selected by that physical stock bound. -/
def finiteTwoQuantumStockChoice (stock : ℕ) : Finset (Fin 3) :=
  rankedPrefix (finiteTwoQuantumStockCapacity stock)
    (Nat.min_le_right (stock / 2) 3)

/-- Every stock-feasible allocation has at most the derived prefix capacity;
therefore the ranked prefix is feasible and undominated under local ordinal
laws for the matching two-unit ends. -/
theorem finite_two_quantum_ranked_prefix_is_undominated (stock : ℕ) :
    finiteTwoQuantumUndominatedChoice stock (finiteTwoQuantumStockChoice stock) := by
  let capacity := finiteTwoQuantumStockCapacity stock
  let P := finiteTwoQuantumStockChoice stock
  have hcapacity : capacity ≤ 3 := by
    dsimp [capacity, finiteTwoQuantumStockCapacity]
    exact Nat.min_le_right _ _
  have hPcard : P.card = capacity := by
    dsimp [P, finiteTwoQuantumStockChoice]
    exact rankedPrefix_card capacity hcapacity
  have hlaws := finiteTwoQuantumOrdinalLawsFor capacity
  refine ⟨?_, ?_, ?_⟩
  · change 2 * P.card ≤ stock
    rw [hPcard]
    dsimp [capacity, finiteTwoQuantumStockCapacity]
    omega
  · by_cases hEmpty : P = ∅
    · exact Or.inl hEmpty
    · right
      change end_rank (finiteTwoQuantumAllocationEnd ∅) <
        end_rank (finiteTwoQuantumAllocationEnd P)
      rw [finiteTwoQuantumAllocationEnd_rank, finiteTwoQuantumAllocationEnd_rank]
      simp only [Finset.card_empty, Finset.sum_empty]
      have hnonempty : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      have hpositive : 0 < P.card := Finset.card_pos.mpr hnonempty
      omega
  · intro R hR hbetter
    have hRcapacity : R.card ≤ stock / 2 :=
      (finite_two_quantum_feasible_iff_capacity stock R).1 hR
    have hRthree : R.card ≤ 3 := by
      calc
        R.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ R)
        _ = 3 := by simp
    have hRle : R.card ≤ capacity := by
      dsimp [capacity, finiteTwoQuantumStockCapacity]
      omega
    have hchoice := ranked_prefix_optimality hcapacity
      finiteTwoQuantumAllocationEnd hlaws R hRle
    rcases hchoice with heq | hpreferred
    · subst R
      exact FiniteBranchingModel.pref_asymm (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
        hbetter hbetter
    · exact FiniteBranchingModel.pref_asymm (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
        hpreferred hbetter

/-- The undominated allocations under two-unit requirements at stocks zero
through four have sizes `0, 0, 1, 1, 2`. -/
theorem finite_two_quantum_stock_choice_table :
    finiteTwoQuantumUndominatedChoice 0 (∅ : Finset (Fin 3)) ∧
    finiteTwoQuantumUndominatedChoice 1 (∅ : Finset (Fin 3)) ∧
    finiteTwoQuantumUndominatedChoice 2 ({0} : Finset (Fin 3)) ∧
    finiteTwoQuantumUndominatedChoice 3 ({0} : Finset (Fin 3)) ∧
    finiteTwoQuantumUndominatedChoice 4 ({0, 1} : Finset (Fin 3)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [finiteTwoQuantumStockChoice, finiteTwoQuantumStockCapacity,
      rankedPrefix] using
      finite_two_quantum_ranked_prefix_is_undominated 0
  · simpa [finiteTwoQuantumStockChoice, finiteTwoQuantumStockCapacity,
      rankedPrefix] using
      finite_two_quantum_ranked_prefix_is_undominated 1
  · have hchoice : finiteTwoQuantumStockChoice 2 = ({0} : Finset (Fin 3)) := by
      decide
    rw [← hchoice]
    exact finite_two_quantum_ranked_prefix_is_undominated 2
  · have hchoice : finiteTwoQuantumStockChoice 3 = ({0} : Finset (Fin 3)) := by
      decide
    rw [← hchoice]
    exact finite_two_quantum_ranked_prefix_is_undominated 3
  · have hchoice : finiteTwoQuantumStockChoice 4 = ({0, 1} : Finset (Fin 3)) := by
      decide
    rw [← hchoice]
    exact finite_two_quantum_ranked_prefix_is_undominated 4

/-- With the two-unit requirement, stocks two and four select one and two
ranked uses under the same technology and preference laws. The additional
marginal use at stock four is below the use selected at stock two. -/
theorem finite_two_quantum_distinct_stock_marginal_witness :
    finiteTwoQuantumUndominatedChoice 2 ({0} : Finset (Fin 3)) ∧
    finiteTwoQuantumUndominatedChoice 4 ({0, 1} : Finset (Fin 3)) ∧
    ({0, 1} : Finset (Fin 3)) \ {0} = {1} ∧
    FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
      (finiteTwoQuantumAllocationEnd {0})
      (finiteTwoQuantumAllocationEnd {1}) := by
  refine ⟨?_, ?_, by decide, ?_⟩
  · rw [← (by decide : finiteTwoQuantumStockChoice 2 = ({0} : Finset (Fin 3)))]
    exact finite_two_quantum_ranked_prefix_is_undominated 2
  · rw [← (by decide : finiteTwoQuantumStockChoice 4 = ({0, 1} : Finset (Fin 3)))]
    exact finite_two_quantum_ranked_prefix_is_undominated 4
  · exact (finiteTwoQuantumOrdinalLawsFor 2).higher_ranked_singleton_preferred
      0 1 (by decide)

/-- The capacity of a unit-use technology with three listed uses saturates at
three even when physical stock continues to grow. -/
def finiteUnitUseCapacity (stock : ℕ) : ℕ := min stock 3

/-- The selected allocation at a physical stock, capped by the three listed
uses. -/
def finiteUnitStockChoice (stock : ℕ) : Finset (Fin 3) :=
  rankedPrefix (finiteUnitUseCapacity stock) (Nat.min_le_right stock 3)

def finiteUnitStockPurposeful (stock : ℕ) : Prop :=
  finiteAllocationPurposeful (finiteUnitUseCapacity stock) (finiteUnitStockChoice stock)

theorem finite_unit_stock_choice_is_purposeful (stock : ℕ) :
    finiteUnitStockPurposeful stock := by
  exact finite_ranked_prefix_is_purposeful (finiteUnitUseCapacity stock)
    (Nat.min_le_right stock 3)

/-- The unit-use capacities for stocks zero through four. -/
theorem finite_unit_use_capacity_table :
    finiteUnitUseCapacity 0 = 0 ∧ finiteUnitUseCapacity 1 = 1 ∧
    finiteUnitUseCapacity 2 = 2 ∧ finiteUnitUseCapacity 3 = 3 ∧
    finiteUnitUseCapacity 4 = 3 := by
  norm_num [finiteUnitUseCapacity]

/-- Distinct one- and two-unit stock contexts select consecutive ranked uses
under the same three-use technology and local ordinal laws. The marginal use
at stock two is strictly below the marginal use at stock one. -/
theorem finite_distinct_stock_marginal_utility_witness :
    finiteAllocationPurposeful 1 ({0} : Finset (Fin 3)) ∧
    finiteAllocationPurposeful 2 ({0, 1} : Finset (Fin 3)) ∧
    ({0} : Finset (Fin 3)) \ ∅ = ({0} : Finset (Fin 3)) ∧
    ({0, 1} : Finset (Fin 3)) \ {0} = ({1} : Finset (Fin 3)) ∧
    FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
      (finiteRankedUseEnd 0) (finiteRankedUseEnd 1) := by
  refine ⟨finite_one_unit_stock_choice, finite_two_unit_stock_choice, ?_, ?_, ?_⟩
  · decide
  · decide
  · change end_rank (finiteRankedUseEnd 1) < end_rank (finiteRankedUseEnd 0)
    norm_num [finiteRankedUseEnd, finiteRankedEndWeight, end_rank]

/-- Additional unit stock beyond the three listed uses produces no additional
selected use: the stock-three and stock-four contexts select the same full
menu. This is satiation relative to the explicitly bounded end list. -/
theorem finite_unit_use_satiation_after_listed_uses :
    finiteUnitUseCapacity 3 = finiteUnitUseCapacity 4 ∧
    finiteUnitStockChoice 3 = Finset.univ ∧
    finiteUnitStockChoice 4 = Finset.univ ∧
    finiteUnitStockPurposeful 3 ∧ finiteUnitStockPurposeful 4 := by
  refine ⟨by norm_num [finiteUnitUseCapacity], ?_, ?_, ?_, ?_⟩
  · ext r
    simp [finiteUnitStockChoice, finiteUnitUseCapacity, rankedPrefix]
  · ext r
    simp [finiteUnitStockChoice, finiteUnitUseCapacity, rankedPrefix]
  · simpa [finiteUnitStockPurposeful, finiteUnitStockChoice,
      finiteUnitUseCapacity] using finite_ranked_prefix_is_purposeful 3 (by omega)
  · simpa [finiteUnitStockPurposeful, finiteUnitStockChoice,
      finiteUnitUseCapacity] using finite_ranked_prefix_is_purposeful 3 (by omega)

/-- A decision maker restricted to the empty and second-ranked allocations can
select the latter as undominated even though the first-ranked use is feasible
in the full menu. This countermodel shows why menu completeness is required. -/
def finiteRestrictedAllocationMenu : Finset (Finset (Fin 3)) := {∅, {1}}

def finiteRestrictedPurposeful (S : Finset (Fin 3)) : Prop :=
  S ∈ finiteRestrictedAllocationMenu ∧
  ∀ R ∈ finiteRestrictedAllocationMenu,
    ¬ FiniteBranchingModel.Preference (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
      (finiteAllocationEnd R) (finiteAllocationEnd S)

theorem missing_allocation_menu_invalidates_prefix_conclusion :
    finiteRestrictedPurposeful ({1} : Finset (Fin 3)) ∧
    ({0} : Finset (Fin 3)) ∉ finiteRestrictedAllocationMenu := by
  refine ⟨?_, by decide⟩
  constructor
  · decide
  · intro R hR
    simp only [finiteRestrictedAllocationMenu, Finset.mem_insert,
      Finset.mem_singleton] at hR
    rcases hR with rfl | rfl
    · intro h
      change end_rank (finiteAllocationEnd ({1} : Finset (Fin 3))) <
        end_rank (finiteAllocationEnd ∅) at h
      norm_num [finiteAllocationEnd, finiteModelRankedAllocationEnd_rank] at h
    · intro h
      exact FiniteBranchingModel.pref_irrefl (0 : Fin 2) (0 : Fin 4) (0 : Fin 3)
        (finiteAllocationEnd {1}) h

/-- If replacement improvements are removed, cardinality alone makes both
single-use allocations undominated. The lower-ranked use can then be selected,
so the replacement law is necessary for ranked-prefix uniqueness. -/
def finiteFlatPreference (S T : Finset (Fin 3)) : Prop := T.card < S.card

def finiteFlatUndominated (capacity : ℕ) (S : Finset (Fin 3)) : Prop :=
  S.card ≤ capacity ∧
  ∀ R, R.card ≤ capacity → ¬ finiteFlatPreference R S

theorem missing_replacement_law_permits_lower_ranked_choice :
    finiteFlatUndominated 1 ({1} : Finset (Fin 3)) ∧
    finiteFlatUndominated 1 ({0} : Finset (Fin 3)) := by
  constructor <;> constructor
  · norm_num
  · intro R hR hbetter
    dsimp [finiteFlatPreference] at hbetter
    simp at hbetter
    omega
  · norm_num
  · intro R hR hbetter
    dsimp [finiteFlatPreference] at hbetter
    simp at hbetter
    omega

/-- A heterogeneous technology in which the top-ranked use costs two units
and the other uses cost one each. -/
def finiteHeterogeneousRequirement (r : Fin 3) : ℕ :=
  if r = 0 then 2 else 1

/-- Feasibility under heterogeneous per-use requirements and a fixed stock. -/
def finiteHeterogeneousFeasible (stock : ℕ) (S : Finset (Fin 3)) : Prop :=
  S.sum finiteHeterogeneousRequirement ≤ stock

/-- Equal-cardinality allocations can have different feasibility when unit
requirements vary. With stock two, uses `{1, 2}` fit but `{0, 1}` do not.
Thus feasibility cannot be reduced to a cardinality bound without the
homogeneous-requirement premise. -/
theorem heterogeneous_requirements_break_cardinality_feasibility :
    ({1, 2} : Finset (Fin 3)).card = ({0, 1} : Finset (Fin 3)).card ∧
    finiteHeterogeneousFeasible 2 ({1, 2} : Finset (Fin 3)) ∧
    ¬ finiteHeterogeneousFeasible 2 ({0, 1} : Finset (Fin 3)) := by
  norm_num [finiteHeterogeneousFeasible, finiteHeterogeneousRequirement]

/-- Every feasible action in a stocked allocation context uses at most the
available number of homogeneous-use quanta. Below satiation the strict
remainder bound rules out another complete use; at satiation the finite menu
already bounds allocations by `N`. -/
theorem StockedAllocationContext.feasible_allocation_card_le
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {m : W.Means} {N : ℕ} {T : HomogeneousUseTechnology W m N}
    {capacity : ℕ} (C : StockedAllocationContext i t h m T capacity)
    (α : W.Action) (hα : α ∈ W.A_feas i t h) :
    (C.allocationOf α).card ≤ capacity := by
  have hfeas := (W.A_feas_coupling i t h α).mp hα
  have huse := hfeas.2 m
  rw [C.action_use_focal α hfeas.1, C.actual_stock] at huse
  have hcap_le := C.capacity_le_N
  by_cases hsat : capacity = N
  · have hcardN : (C.allocationOf α).card ≤ N :=
      by simpa using Finset.card_le_univ (C.allocationOf α)
    omega
  · have hcap_lt : capacity < N := by omega
    by_contra hnot
    have hlt : capacity + 1 ≤ (C.allocationOf α).card := by omega
    have hmul := Nat.mul_le_mul_right T.quantum hlt
    rw [Nat.succ_mul] at hmul
    have hq := T.quantum_positive
    have hrem := C.remainder_lt_quantum hcap_lt
    omega

/-- Every allocation of at most capacity ranked uses is feasible. Feasibility
follows from contemplation, the exact action cost, and the actual endowment;
surplus stock at satiation only strengthens this bound. -/
theorem StockedAllocationContext.realized_allocation_feasible
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {m : W.Means} {N : ℕ} {T : HomogeneousUseTechnology W m N}
    {capacity : ℕ} (C : StockedAllocationContext i t h m T capacity)
    (S : Finset (Fin N)) (hS : S.card ≤ capacity) :
    C.realize S ∈ W.A_feas i t h := by
  rw [W.A_feas_coupling]
  refine ⟨C.realize_contemplated S hS, ?_⟩
  intro m'
  by_cases hm : m' = m
  · subst m'
    rw [C.action_use_focal (C.realize S) (C.realize_contemplated S hS),
      C.realize_allocation S, C.actual_stock]
    have hmul := Nat.mul_le_mul_right T.quantum hS
    omega
  · rw [C.action_use_exact (C.realize S) (C.realize_contemplated S hS) m',
      C.realize_allocation S]
    exact C.other_stock_suffices S m' hm

/-- Purposeful choice selects the ranked prefix under the local add,
replacement, and transitivity laws. This derives optimality from local rules
and the complete feasible realization map; no premise states that the prefix
globally dominates every alternative. -/
theorem StockedAllocationContext.purposeful_choice_is_ranked_prefix
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {m : W.Means} {N : ℕ} {T : HomogeneousUseTechnology W m N}
    {capacity : ℕ} (C : StockedAllocationContext i t h m T capacity)
    (laws : LocalOrdinalAllocationLaws i t h capacity C.allocationEnd)
    (α : W.Action) (hPurposeful : @PurposefulAct W i t h α) :
    C.allocationOf α = rankedPrefix capacity C.capacity_le_N := by
  have hcard := C.feasible_allocation_card_le α hPurposeful.1
  rcases ranked_prefix_optimality C.capacity_le_N C.allocationEnd laws
      (C.allocationOf α) hcard with hEq | hPref
  · exact hEq
  · have hprefix_card := rankedPrefix_card capacity C.capacity_le_N
    have hprefix_feasible := C.realized_allocation_feasible
      (rankedPrefix capacity C.capacity_le_N) (by rw [hprefix_card])
    have hbetter : W.Preference i t h
        (W.End_of i (C.realize (rankedPrefix capacity C.capacity_le_N)) t h)
        (W.End_of i α t h) := by
      have hrealizeCont := C.realize_contemplated _ (by rw [hprefix_card])
      have hαCont := (W.A_feas_coupling i t h α).mp hPurposeful.1 |>.1
      rw [C.action_end (C.realize _) hrealizeCont, C.realize_allocation,
        C.action_end α hαCont]
      exact hPref
    exact False.elim (hPurposeful.2.2.2
      (C.realize (rankedPrefix capacity C.capacity_le_N)) hprefix_feasible hbetter)

/-- sigma realization supplies a history on which any feasible allocation
action is enacted. This exposes execution as a witness obligation; it does not
assume the action is purposeful. -/
theorem StockedAllocationContext.realized_action_executable
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {m : W.Means} {N : ℕ} {T : HomogeneousUseTechnology W m N}
    {capacity : ℕ} (C : StockedAllocationContext i t h m T capacity)
    (ht : W.mem_hist t h) (S : Finset (Fin N)) (hS : S.card ≤ capacity) :
    ∃ h', W.mem_hist t h' ∧ W.enacted i t h' = C.realize S := by
  have hσ := W.sigma_realization i t h h ht
    (C.realized_allocation_feasible S hS) ht
  exact ⟨W.sigma i t (C.realize S) h, hσ.1, hσ.2⟩

/-- The ranked prefix is a purposeful action on a history realized by the
frame's existing branch-selection operator. Feasibility follows from the
stock and requirement equations; preference and undominated choice follow
from the local addition, replacement, and transitivity laws. No globally
optimal allocation is assumed. -/
theorem StockedAllocationContext.ranked_prefix_has_purposeful_execution
    {W : ActionFrame} {i : W.Agent} {t : W.Moment} {h : W.History}
    {m : W.Means} {N : ℕ} {T : HomogeneousUseTechnology W m N}
    {capacity : ℕ} (C : StockedAllocationContext i t h m T capacity)
    (laws : LocalOrdinalAllocationLaws i t h capacity C.allocationEnd)
    (ht : W.mem_hist t h) :
    ∃ h', W.mem_hist t h' ∧
      W.enacted i t h' = C.realize (rankedPrefix capacity C.capacity_le_N) ∧
      @PurposefulAct W i t h' (C.realize (rankedPrefix capacity C.capacity_le_N)) := by
  let P := rankedPrefix capacity C.capacity_le_N
  have hPcard : P.card = capacity := rankedPrefix_card capacity C.capacity_le_N
  have hPfeasible : C.realize P ∈ W.A_feas i t h :=
    C.realized_allocation_feasible P (by simpa [P] using hPcard.le)
  let h' := W.sigma i t (C.realize P) h
  have hσ := W.sigma_realization i t h h ht hPfeasible ht
  have ht' : W.mem_hist t h' := by simpa [h'] using hσ.1
  have henacted : W.enacted i t h' = C.realize P := by
    simpa [h'] using hσ.2
  let C' := C.transport ht ht'
  let laws' := laws.transport ht ht'
  have hPfeasible' : C.realize P ∈ W.A_feas i t h' :=
    C'.realized_allocation_feasible P (by simpa [P] using hPcard.le)
  have hPcont : C.realize P ∈ W.A_cont i t h' :=
    C'.realize_contemplated P (by simpa [P] using hPcard.le)
  have hPallocation : C'.allocationOf (C.realize P) = P := by
    change C'.allocationOf (C'.realize P) = P
    exact C'.realize_allocation P
  have hPend : W.End_of i (C.realize P) t h' = C'.allocationEnd P := by
    rw [C'.action_end (C.realize P) hPcont, hPallocation]
  have hZeroAllocation : C'.allocationOf W.alpha_zero = ∅ := by
    rw [← C'.realize_empty_is_passive]
    exact C'.realize_allocation ∅
  have hZeroCont : W.alpha_zero ∈ W.A_cont i t h' := W.alpha_zero_cont i t h'
  have hZeroEnd : W.End_of i W.alpha_zero t h' = C'.allocationEnd ∅ := by
    rw [C'.action_end W.alpha_zero hZeroCont, hZeroAllocation]
  have hPreferredToZero :
      C.realize P = W.alpha_zero ∨
        W.Preference i t h' (W.End_of i (C.realize P) t h')
          (W.End_of i W.alpha_zero t h') := by
    by_cases hPempty : P = ∅
    · left
      rw [hPempty, C.realize_empty_is_passive]
    · right
      have hChoice := ranked_prefix_optimality C.capacity_le_N
        C'.allocationEnd laws' (∅ : Finset (Fin N)) (by simp)
      rcases hChoice with hEmptyEq | hPref
      · exact (hPempty hEmptyEq.symm).elim
      · rw [hPend, hZeroEnd]
        exact hPref
  have hUndominated : ∀ β ∈ W.A_feas i t h',
      ¬ W.Preference i t h'
        (W.End_of i β t h') (W.End_of i (C.realize P) t h') := by
    intro β hβ hβpref
    have hβcard := C'.feasible_allocation_card_le β hβ
    have hChoice := ranked_prefix_optimality C.capacity_le_N
      C'.allocationEnd laws' (C'.allocationOf β) hβcard
    have hβcont : β ∈ W.A_cont i t h' := (W.A_feas_coupling i t h' β).mp hβ |>.1
    have hβend := C'.action_end β hβcont
    rcases hChoice with hEq | hPref
    · have hEndEq : W.End_of i β t h' = W.End_of i (C.realize P) t h' := by
        rw [hβend, hPend, hEq]
      rw [hEndEq] at hβpref
      exact W.pref_irrefl i t h' _ hβpref
    · have hPrefixPrefers :
          W.Preference i t h' (W.End_of i (C.realize P) t h')
            (W.End_of i β t h') := by
        rw [hPend, hβend]
        exact hPref
      exact W.pref_asymm i t h' hPrefixPrefers hβpref
  refine ⟨h', ht', henacted, ?_⟩
  refine ⟨hPfeasible', ?_, hPreferredToZero, hUndominated⟩
  change h' ∈ ChoicePartition i t (C.realize P)
  exact ⟨ht', henacted⟩

end Praxeology
