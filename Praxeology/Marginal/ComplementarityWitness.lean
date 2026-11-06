/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame.Core
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Complementary Means: A Left/Right Shoe Witness

This finite example records a pair of shoes as an end that requires one left
shoe and one right shoe. It separates physical stock growth from expansion of
the set of attainable valued ends and makes the bounded-menu assumption in a
satiation claim explicit.
-/

@[expose] public section

namespace Praxeology

inductive ShoeMeans where
  | left
  | right
  deriving DecidableEq

instance : Fintype ShoeMeans where
  elems := {.left, .right}
  complete := by
    intro m
    cases m <;> simp

inductive ShoeEnd where
  | pairCount (pairs : ℕ)
  | walk
  deriving DecidableEq

/-- Each pair requires one left and one right shoe. Walking uses one pair. -/
def shoePairRequirement : ShoeEnd → ShoeMeans → ℕ
  | .pairCount q, _ => q
  | .walk, _ => 1

/-- Inventory of left and right shoes. -/
def shoeInventory (left right : ℕ) : ShoeMeans → ℕ
  | .left => left
  | .right => right

/-- Whether the requested number of pairs is attainable from an inventory. -/
def ShoeEndAttained (left right : ℕ) (e : ShoeEnd) : Prop :=
  AttainsEnd shoePairRequirement (shoeInventory left right) e

/-- Pair attainment requires each complementary shoe type in the requested
quantity. -/
theorem shoeEndAttained_iff (left right q : ℕ) :
    ShoeEndAttained left right (.pairCount q) ↔ q ≤ left ∧ q ≤ right := by
  constructor
  · intro h
    exact ⟨h .left, h .right⟩
  · rintro ⟨hleft, hright⟩ m
    cases m with
    | left => exact hleft
    | right => exact hright

/-- Walking is attainable exactly when the inventory contains both shoes. -/
theorem shoeWalkAttained_iff (left right : ℕ) :
    ShoeEndAttained left right .walk ↔ 1 ≤ left ∧ 1 ≤ right := by
  constructor
  · intro h
    exact ⟨h ShoeMeans.left, h ShoeMeans.right⟩
  · rintro ⟨hleft, hright⟩ m
    cases m with
    | left => exact hleft
    | right => exact hright

instance shoeEndAttainedDecidablePred (left right : ℕ) :
    DecidablePred (fun e => ShoeEndAttained left right e) := by
  intro e
  cases e with
  | pairCount q =>
    change Decidable (ShoeEndAttained left right (.pairCount q))
    rw [shoeEndAttained_iff]
    infer_instance
  | walk =>
    change Decidable (ShoeEndAttained left right .walk)
    rw [shoeWalkAttained_iff]
    infer_instance

/-- Two left shoes with no right shoe do not enable walking. -/
theorem extra_left_stock_does_not_enable_walking :
    ¬ ShoeEndAttained 2 0 .walk := by
  rw [shoeWalkAttained_iff]
  omega

/-- One left and one right shoe satisfy the modeled walking requirement. -/
theorem complementary_stock_enables_walking :
    ShoeEndAttained 1 1 .walk := by
  rw [shoeWalkAttained_iff]
  omega

/-- Raising left stock from one to two while right stock stays at zero does
not change whether walking is attainable. -/
theorem unmatched_left_inventory_does_not_change_walking :
    ShoeEndAttained 1 0 .walk ↔ ShoeEndAttained 2 0 .walk := by
  rw [shoeWalkAttained_iff, shoeWalkAttained_iff]
  omega

/-- Two left shoes without a right shoe still cannot attain one pair. -/
theorem unmatched_left_shoe_stock_does_not_attain_pair :
    ¬ ShoeEndAttained 2 0 (.pairCount 1) := by
  rw [shoeEndAttained_iff]
  omega

/-- One left and one right shoe attain one pair. -/
theorem complementary_shoes_attain_pair :
    ShoeEndAttained 1 1 (.pairCount 1) := by
  rw [shoeEndAttained_iff]
  omega

/-- Additional left shoes with no right shoe do not change which pair counts
are attainable. This is a concrete non-attainment counterexample to treating
every increase in one means as an increase in attainable ends. -/
theorem unmatched_left_inventory_same_attainable_pair_counts (q : ℕ) :
    ShoeEndAttained 1 0 (.pairCount q) ↔
      ShoeEndAttained 2 0 (.pairCount q) := by
  rw [shoeEndAttained_iff, shoeEndAttained_iff]
  omega

/-- The extra left shoe is a strict physical-bundle increase. -/
theorem unmatched_left_inventory_physically_dominates :
    PhysicalBundleDominates (shoeInventory 2 0) (shoeInventory 1 0) := by
  refine ⟨?_, ⟨ShoeMeans.left, ?_⟩⟩
  · intro m
    cases m <;> simp [shoeInventory]
  · simp [shoeInventory]

/-- Ends that are valued in the capped one-pair menu. The cap expresses the
model's limited wants; it is not a general claim about human wants. -/
def boundedShoeEndMenu : Finset ShoeEnd :=
  {.pairCount 0, .pairCount 1}

/-- Attainable valued ends in the bounded shoe menu. -/
def attainableBoundedShoeEnds (left right : ℕ) : Finset ShoeEnd :=
  boundedShoeEndMenu.filter (fun e => ShoeEndAttained left right e)

/-- Once one pair is available, doubling both stocks does not enlarge the
attainable menu when the model values at most one pair. This is a precise,
bounded-menu satiation witness. -/
theorem shoe_stock_satiation_under_one_pair_menu :
    attainableBoundedShoeEnds 1 1 = attainableBoundedShoeEnds 2 2 := by
  ext e
  cases e with
  | pairCount q =>
    simp [attainableBoundedShoeEnds, boundedShoeEndMenu, shoeEndAttained_iff]
    omega
  | walk =>
    simp [attainableBoundedShoeEnds, boundedShoeEndMenu]

/-- If the sole valued end is a completed pair, an unmatched increase in left
shoes creates no strict subjective teleological advantage over zero stock. -/
theorem unmatched_left_inventory_no_subjective_teleological_gain :
    ¬ SubjectiveTeleologicalDominates shoePairRequirement
      (fun e => e = .pairCount 1) (shoeInventory 2 0) (shoeInventory 0 0) := by
  rintro ⟨_, ⟨S, hvalued, hstock, hnot⟩⟩
  have h_empty : S = ∅ := by
    by_contra h_ne
    have h_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_ne
    obtain ⟨e, he⟩ := h_nonempty
    have he_pair : e = .pairCount 1 := hvalued e he
    subst e
    have hsum : S.sum (fun e => shoePairRequirement e ShoeMeans.right) = S.card := by
      calc
        S.sum (fun e => shoePairRequirement e ShoeMeans.right) =
            S.sum (fun _ => 1) := by
          apply Finset.sum_congr rfl
          intro e he'
          rw [hvalued e he']
          rfl
        _ = S.card := by simp
    have hbound : S.sum (fun e => shoePairRequirement e ShoeMeans.right) ≤ 0 := by
      simpa [shoeInventory] using hstock ShoeMeans.right
    rw [hsum] at hbound
    have hcardpos : 0 < S.card := Finset.card_pos.mpr ⟨.pairCount 1, he⟩
    omega
  apply hnot
  intro m
  simp [h_empty]

end Praxeology

end
