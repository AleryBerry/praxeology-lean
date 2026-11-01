/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.NormNum

/-!
# Exact balances for natural-number quantities

Economic differences are represented by a remainder together with its additive
balance. The only truncated subtraction used to construct such a remainder is
guarded by a proof that the amount used does not exceed the total.
-/

@[expose] public section

namespace Praxeology

/-- The exact amount left after using `used` from `total`. -/
structure NatRemainder (total used : ℕ) where
  remaining : ℕ
  balance : used + remaining = total

namespace NatRemainder

/-- Construct a certified remainder when the amount used is feasible. -/
def ofLE (total used : ℕ) (h : used ≤ total) : NatRemainder total used :=
  ⟨total - used, by omega⟩


/-- A total and used amount determine at most one exact remainder. -/
theorem remaining_unique {total used : ℕ}
    (r₁ r₂ : NatRemainder total used) : r₁.remaining = r₂.remaining := by
  have h₁ := r₁.balance
  have h₂ := r₂.balance
  omega

/-- No quantity remains exactly when all of the total was used. -/
theorem remaining_eq_zero_iff {total used : ℕ} (r : NatRemainder total used) :
    r.remaining = 0 ↔ used = total := by
  have h := r.balance
  omega

/-- A positive remainder is equivalent to using strictly less than the total. -/
theorem remaining_pos_iff {total used : ℕ} (r : NatRemainder total used) :
    0 < r.remaining ↔ used < total := by
  have h := r.balance
  omega

/-- Increasing the total cannot reduce a certified remainder. -/
theorem remaining_mono {total₁ total₂ used : ℕ}
    (h : total₁ ≤ total₂)
    (r₁ : NatRemainder total₁ used)
    (r₂ : NatRemainder total₂ used) :
    r₁.remaining ≤ r₂.remaining := by
  have h₁ := r₁.balance
  have h₂ := r₂.balance
  omega

end NatRemainder

end Praxeology

end
