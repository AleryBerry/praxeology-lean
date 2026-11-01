/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Mathlib.Data.Finset.Basic

/-!
# Finite Support Helpers

Small interface lemmas for filtering finite supports represented as `Finset`s.
-/

@[expose] public section

namespace Praxeology

/-- Membership in a filtered finite support. -/
theorem finsetFilter_mem {α : Type} (p : α → Prop) [DecidablePred p]
    (s : Finset α) (x : α) :
    x ∈ s.filter p ↔ x ∈ s ∧ p x :=
  Finset.mem_filter

/-- Filtering a finite support never introduces new elements. -/
theorem finsetFilter_subset {α : Type} (p : α → Prop) [DecidablePred p]
    (s : Finset α) : s.filter p ⊆ s :=
  Finset.filter_subset _ _

end Praxeology
