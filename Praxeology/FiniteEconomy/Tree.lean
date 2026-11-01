/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.Frame.Core
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max

/-!
# Finite branching-time trees

Moments are numbered in parent-before-child order.  Every non-root moment has
one strictly earlier parent, so ancestry follows a terminating parent walk.
-/

@[expose] public section

namespace Praxeology

/-- A finite rooted tree represented by a parent pointer for each moment. -/
structure FiniteTreeSpec where
  extraNodes : ℕ
  parent : Fin (extraNodes + 1) → Fin (extraNodes + 1)
  parent_root : parent 0 = 0
  parent_decreases : ∀ v, v ≠ 0 → (parent v).val < v.val

namespace FiniteTreeSpec

/-- The moments of a finite tree, including its root. -/
abbrev Node (T : FiniteTreeSpec) := Fin (T.extraNodes + 1)

/-- Parent number for the preorder concatenation of two finite trees. -/
def appendSubtreeParentVal (T U : FiniteTreeSpec) (p : T.Node)
    (v : Fin (T.extraNodes + U.extraNodes + 1 + 1)) : ℕ :=
  if hv : v.val < T.extraNodes + 1 then
    (T.parent ⟨v.val, hv⟩).val
  else if v.val - (T.extraNodes + 1) = 0 then p.val
  else
    T.extraNodes + 1 + (U.parent ⟨v.val - (T.extraNodes + 1), by
      have hvBound := v.isLt
      omega⟩).val

/-- The appended parent number is always a valid node index. -/
theorem appendSubtreeParentVal_bound (T U : FiniteTreeSpec) (p : T.Node)
    (v : Fin (T.extraNodes + U.extraNodes + 1 + 1)) :
    appendSubtreeParentVal T U p v < T.extraNodes + U.extraNodes + 1 + 1 := by
  unfold appendSubtreeParentVal
  split_ifs with hold hroot
  · have hparent := (T.parent ⟨v.val, hold⟩).isLt
    omega
  · have hp := p.isLt
    omega
  · have hparent := (U.parent ⟨v.val - (T.extraNodes + 1), by omega⟩).isLt
    omega

/-- Every appended parent still precedes its child in preorder. -/
theorem appendSubtreeParentVal_decreases (T U : FiniteTreeSpec) (p : T.Node)
    (v : Fin (T.extraNodes + U.extraNodes + 1 + 1)) (hv : v ≠ 0) :
    appendSubtreeParentVal T U p v < v.val := by
  unfold appendSubtreeParentVal
  split_ifs with hold hroot
  · have old : (⟨v.val, hold⟩ : T.Node) ≠ 0 := by
      intro heq
      have hzero : v.val = 0 := by simpa using congrArg Fin.val heq
      exact hv (Fin.ext hzero)
    exact T.parent_decreases ⟨v.val, hold⟩ old
  · have hchildEq : v.val = T.extraNodes + 1 := by omega
    have hparent : p.val < T.extraNodes + 1 := p.isLt
    omega
  · let child : U.Node := ⟨v.val - (T.extraNodes + 1), by omega⟩
    have hvEq : v.val = T.extraNodes + 1 + child.val := by
      simp [child]
      omega
    have hchildNe : child ≠ 0 := by
      intro hc
      have hcval : child.val = 0 := by simpa using congrArg Fin.val hc
      apply hroot
      simpa [child] using hcval
    have hparent := U.parent_decreases child hchildNe
    calc
      T.extraNodes + 1 + (U.parent child).val <
          T.extraNodes + 1 + child.val := Nat.add_lt_add_left hparent _
      _ = v.val := hvEq.symm

/-- Parent map for the preorder concatenation of two finite trees. -/
def appendSubtreeParent (T U : FiniteTreeSpec) (p : T.Node) :
    Fin (T.extraNodes + U.extraNodes + 1 + 1) →
      Fin (T.extraNodes + U.extraNodes + 1 + 1) := fun v =>
  ⟨appendSubtreeParentVal T U p v, appendSubtreeParentVal_bound T U p v⟩

/-- The parent map fixes the old tree's root. -/
theorem appendSubtreeParent_root (T U : FiniteTreeSpec) (p : T.Node) :
    appendSubtreeParent T U p 0 = 0 := by
  apply Fin.ext
  simp [appendSubtreeParent, appendSubtreeParentVal, T.parent_root]

/-- Every appended parent still precedes its child in preorder. -/
theorem appendSubtreeParent_decreases (T U : FiniteTreeSpec) (p : T.Node)
    (v : Fin (T.extraNodes + U.extraNodes + 1 + 1)) (hv : v ≠ 0) :
    (appendSubtreeParent T U p v).val < v.val :=
  appendSubtreeParentVal_decreases T U p v hv

/-- Append an entire finite subtree below an existing node. Old indices stay
fixed; the appended subtree's root becomes a child of `p`, and its remaining
parent indices are shifted by the old node count. This operation is the
structural primitive for preorder program compilation. -/
def appendSubtree (T U : FiniteTreeSpec) (p : T.Node) : FiniteTreeSpec where
  extraNodes := T.extraNodes + U.extraNodes + 1
  parent := appendSubtreeParent T U p
  parent_root := appendSubtreeParent_root T U p
  parent_decreases := appendSubtreeParent_decreases T U p

/-- The old subtree occupies the initial block of an appended tree. -/
theorem appendSubtree_parent_old (T U : FiniteTreeSpec) (p : T.Node)
    (v : T.Node) :
    (appendSubtree T U p).parent
        (⟨v.val, by
          change v.val < T.extraNodes + U.extraNodes + 1 + 1
          omega⟩ : (appendSubtree T U p).Node) =
      ⟨(T.parent v).val, by
        have h := (T.parent v).isLt
        change (T.parent v).val < T.extraNodes + U.extraNodes + 1 + 1
        omega⟩ := by
  apply Fin.ext
  simp [appendSubtree, appendSubtreeParent, appendSubtreeParentVal]

/-- The appended subtree root is attached to the requested old node. -/
theorem appendSubtree_parent_childRoot (T U : FiniteTreeSpec) (p : T.Node) :
    (appendSubtree T U p).parent
        (⟨T.extraNodes + 1, by
          change T.extraNodes + 1 < T.extraNodes + U.extraNodes + 1 + 1
          omega⟩ :
          (appendSubtree T U p).Node) =
      ⟨p.val, by
        have hp := p.isLt
        change p.val < T.extraNodes + U.extraNodes + 1 + 1
        omega⟩ := by
  apply Fin.ext
  simp [appendSubtree, appendSubtreeParent, appendSubtreeParentVal]

/-- An appended internal node keeps its local parent, shifted by the old
tree's node count. -/
theorem appendSubtree_parent_child (T U : FiniteTreeSpec) (p : T.Node)
    (v : U.Node) (hv : v ≠ 0) :
    (appendSubtree T U p).parent
        (⟨T.extraNodes + 1 + v.val, by
          have h := v.isLt
          change T.extraNodes + 1 + v.val < T.extraNodes + U.extraNodes + 1 + 1
          omega⟩ : (appendSubtree T U p).Node) =
      ⟨T.extraNodes + 1 + (U.parent v).val, by
        have h := (U.parent v).isLt
        change T.extraNodes + 1 + (U.parent v).val <
          T.extraNodes + U.extraNodes + 1 + 1
        omega⟩ := by
  apply Fin.ext
  simp [appendSubtree, appendSubtreeParent, appendSubtreeParentVal, hv]

/-- The one-node rooted tree is the identity for subtree assembly. -/
def rootOnly : FiniteTreeSpec where
  extraNodes := 0
  parent := fun _ => 0
  parent_root := rfl
  parent_decreases := by
    intro v hv
    apply (hv ?_).elim
    apply Fin.ext
    omega

/-- Attach a list of ordered child trees under the unchanged root of `base`. -/
def appendChildrenAux : List FiniteTreeSpec →
    (base : FiniteTreeSpec) → FiniteTreeSpec
  | [], base => base
  | child :: rest, base => appendChildrenAux rest (base.appendSubtree child 0)

/-- The assembled tree begins with a root and then contains each child tree
in the given list order. -/
def assembleChildren (children : List FiniteTreeSpec) : FiniteTreeSpec :=
  appendChildrenAux children rootOnly

/-- Appending one subtree adds its complete node count to the base tree. -/
theorem appendSubtree_size (T U : FiniteTreeSpec) (p : T.Node) :
    (appendSubtree T U p).extraNodes + 1 =
      (T.extraNodes + 1) + (U.extraNodes + 1) := by
  simp [appendSubtree]
  omega

/-- Size of preorder assembly is the root size plus every child subtree. -/
theorem appendChildrenAux_size (children : List FiniteTreeSpec)
    (base : FiniteTreeSpec) :
    (appendChildrenAux children base).extraNodes + 1 =
      (base.extraNodes + 1) + (children.map (fun child => child.extraNodes + 1)).sum := by
  induction children generalizing base with
  | nil => simp [appendChildrenAux]
  | cons child rest ih =>
      simp only [appendChildrenAux]
      rw [ih]
      have hsize := appendSubtree_size base child 0
      simp only [List.map_cons, List.sum_cons]
      omega

/-- Node count of an assembled child list, including its common root. -/
theorem assembleChildren_size (children : List FiniteTreeSpec) :
    (assembleChildren children).extraNodes + 1 =
      1 + (children.map (fun child => child.extraNodes + 1)).sum := by
  simpa [assembleChildren, rootOnly] using appendChildrenAux_size children rootOnly

/-- Boolean ancestry, evaluated by walking from the proposed descendant to its parent. -/
def ancestorB (T : FiniteTreeSpec) (a b : T.Node) : Bool :=
  if a = b then true
  else if _h0 : b.val = 0 then false
  else ancestorB T a (T.parent b)
termination_by b.val
decreasing_by
  apply T.parent_decreases b
  intro h
  subst b
  exact _h0 rfl

/-- A Boolean row with a statically checked finite width. -/
structure FiniteBoolRow (n : ℕ) where
  values : Array Bool
  values_size : values.size = n

namespace FiniteBoolRow

def ofFn {n : ℕ} (f : Fin n → Bool) : FiniteBoolRow n :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

def get {n : ℕ} (row : FiniteBoolRow n) (i : Fin n) : Bool :=
  row.values[i.val]'(by rw [row.values_size]; exact i.isLt)

def set {n : ℕ} (row : FiniteBoolRow n) (i : Fin n) (value : Bool) :
    FiniteBoolRow n :=
  ⟨row.values.set i.val value (by rw [row.values_size]; exact i.isLt), by
    rw [Array.size_set, row.values_size]⟩

@[simp] theorem get_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (FiniteBoolRow.ofFn f).get i = f i := by
  simp [FiniteBoolRow.get, FiniteBoolRow.ofFn, Array.getElem_ofFn]

theorem get_set {n : ℕ} (row : FiniteBoolRow n) (i j : Fin n) (value : Bool) :
    (row.set i value).get j = if i = j then value else row.get j := by
  by_cases hij : i = j
  · subst j
    simp [FiniteBoolRow.get, FiniteBoolRow.set, Array.getElem_set_self]
  · have hval : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
    simp [FiniteBoolRow.get, FiniteBoolRow.set, Array.getElem_set, hij, hval]

end FiniteBoolRow

/-- A finite table of fixed-width Boolean rows. -/
structure FiniteBoolTable (n : ℕ) where
  rows : Array (FiniteBoolRow n)
  rows_size : rows.size = n

namespace FiniteBoolTable

def ofFn {n : ℕ} (f : Fin n → FiniteBoolRow n) : FiniteBoolTable n :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

def get {n : ℕ} (table : FiniteBoolTable n) (i : Fin n) : FiniteBoolRow n :=
  table.rows[i.val]'(by rw [table.rows_size]; exact i.isLt)

@[simp] theorem get_ofFn {n : ℕ} (f : Fin n → FiniteBoolRow n) (i : Fin n) :
    (FiniteBoolTable.ofFn f).get i = f i := by
  simp [FiniteBoolTable.get, FiniteBoolTable.ofFn, Array.getElem_ofFn]

end FiniteBoolTable

/-- A cached ancestry row for one descendant. Each non-root row is copied
from its already earlier parent and sets the descendant's own bit. Evaluating
all rows costs O(N²) in the worst case because every row follows at most N
parent links. Lookups use statically bounded array indices. -/
def ancestorCacheRow (T : FiniteTreeSpec) :
    (b : T.Node) → FiniteBoolRow (T.extraNodes + 1)
  | b =>
      if _hb : b = 0 then
        FiniteBoolRow.ofFn fun a : T.Node => decide (a = 0)
      else
        (ancestorCacheRow T (T.parent b)).set b true
termination_by b => b.val
decreasing_by
  exact T.parent_decreases b _hb

/-- The complete ancestry table, indexed first by descendant and then by
candidate ancestor. -/
def ancestorCache (T : FiniteTreeSpec) : FiniteBoolTable (T.extraNodes + 1) :=
  FiniteBoolTable.ofFn fun b : T.Node => T.ancestorCacheRow b

/-- Constant-time lookup in the generated ancestry table. -/
def cachedAncestorB (T : FiniteTreeSpec) (a b : T.Node) : Bool :=
  (T.ancestorCache.get b).get a

/-- A cache row agrees with the recursive ancestor predicate. -/
theorem ancestorCacheRow_get_eq_ancestorB (T : FiniteTreeSpec)
    (a b : T.Node) : (T.ancestorCacheRow b).get a = T.ancestorB a b := by
  have haux : ∀ n, ∀ b : T.Node, b.val = n → ∀ a,
      (T.ancestorCacheRow b).get a = T.ancestorB a b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro b hb a
        by_cases hb0 : b = 0
        · subst b
          simp [ancestorCacheRow, ancestorB]
        · have hp_lt : (T.parent b).val < n := by
            rw [← hb]
            exact T.parent_decreases b hb0
          have hparent := ih (T.parent b).val hp_lt (T.parent b) rfl a
          have hrow : T.ancestorCacheRow b =
              (T.ancestorCacheRow (T.parent b)).set b true := by
            rw [ancestorCacheRow]
            exact dite_eq_right hb0
          by_cases hEq : a = b
          · subst a
            rw [hrow]
            simp [FiniteBoolRow.get_set, ancestorB]
          · rw [hrow, FiniteBoolRow.get_set, hparent]
            conv_rhs => rw [ancestorB]
            have hEq' : b ≠ a := Ne.symm hEq
            simp [hEq, hEq', hb0]
  exact haux b.val b rfl a

/-- The whole table agrees with `ancestorB` at every bounded pair. -/
theorem cachedAncestorB_eq_ancestorB (T : FiniteTreeSpec) (a b : T.Node) :
    T.cachedAncestorB a b = T.ancestorB a b := by
  simp [cachedAncestorB, ancestorCache, FiniteBoolTable.get_ofFn,
    ancestorCacheRow_get_eq_ancestorB]

/-- A compiled finite-tree index stores the generated Boolean ancestry table
once so execution code can reuse it for repeated membership queries. -/
structure FiniteTreeIndex (T : FiniteTreeSpec) where
  table : FiniteBoolTable (T.extraNodes + 1)
  table_correct : ∀ a b, (table.get b).get a = T.ancestorB a b

/-- Generate and validate the ancestry matrix from parent pointers. -/
def compileIndex (T : FiniteTreeSpec) : FiniteTreeIndex T :=
  ⟨T.ancestorCache, fun a b => by
    simpa [cachedAncestorB] using T.cachedAncestorB_eq_ancestorB a b⟩

/-- Propositional ancestry corresponding to the recursive `ancestorB`. -/
def Ancestor (T : FiniteTreeSpec) (a b : T.Node) : Prop :=
  T.ancestorB a b = true

/-- Strict temporal precedence in the tree. -/
def Precedence (T : FiniteTreeSpec) (a b : T.Node) : Prop :=
  a ≠ b ∧ T.Ancestor a b

/-- A node is a leaf when no non-root node points to it as parent. -/
def IsLeaf (T : FiniteTreeSpec) (l : T.Node) : Prop :=
  ∀ v, v ≠ 0 → T.parent v ≠ l

/-- A history is identified with its terminal leaf. -/
abbrev History (T : FiniteTreeSpec) := {l : T.Node // T.IsLeaf l}

/-- A moment belongs to a history when it is an ancestor of that history's leaf. -/
def MemHist (T : FiniteTreeSpec) (t : T.Node) (h : T.History) : Prop :=
  T.Ancestor t h.1

namespace FiniteTreeIndex

/-- Read ancestry from the stored finite matrix. -/
def ancestorB {T : FiniteTreeSpec} (I : FiniteTreeIndex T)
    (a b : T.Node) : Bool := (I.table.get b).get a

/-- The compiled lookup agrees with the recursive tree definition. -/
theorem ancestorB_eq {T : FiniteTreeSpec} (I : FiniteTreeIndex T)
    (a b : T.Node) : I.ancestorB a b = T.ancestorB a b :=
  I.table_correct a b

/-- Cached ancestry as a proposition. -/
def Ancestor {T : FiniteTreeSpec} (I : FiniteTreeIndex T)
    (a b : T.Node) : Prop := I.ancestorB a b = true

/-- A cached history incidence query. -/
def MemHist {T : FiniteTreeSpec} (I : FiniteTreeIndex T)
    (t : T.Node) (h : T.History) : Prop := I.Ancestor t h.1

theorem ancestor_iff {T : FiniteTreeSpec} (I : FiniteTreeIndex T)
    (a b : T.Node) : I.Ancestor a b ↔ T.Ancestor a b := by
  change I.ancestorB a b = true ↔ T.ancestorB a b = true
  rw [I.ancestorB_eq]

theorem memHist_iff {T : FiniteTreeSpec} (I : FiniteTreeIndex T)
    (t : T.Node) (h : T.History) : I.MemHist t h ↔ T.MemHist t h :=
  I.ancestor_iff t h.1

end FiniteTreeIndex

theorem ancestorB_self (T : FiniteTreeSpec) (a : T.Node) :
    T.ancestorB a a = true := by
  simp [ancestorB]

theorem ancestor_refl (T : FiniteTreeSpec) (a : T.Node) : T.Ancestor a a :=
  T.ancestorB_self a

theorem ancestorB_parent (T : FiniteTreeSpec) {a b : T.Node} (hb : b ≠ 0) :
    T.ancestorB a b = true ↔ a = b ∨ T.Ancestor a (T.parent b) := by
  rw [ancestorB]
  by_cases hEq : a = b
  · simp [hEq, Ancestor]
  · have hzero : b.val ≠ 0 := by
      intro h
      apply hb
      exact Fin.ext h
    simp [hEq, hzero, Ancestor]

theorem ancestor_of_parent (T : FiniteTreeSpec) {a b : T.Node} (hb : b ≠ 0)
    (h : T.Ancestor a (T.parent b)) : T.Ancestor a b := by
  exact (T.ancestorB_parent hb).mpr (Or.inr h)

/-- The distinguished node zero lies on every history of the rooted tree. -/
theorem root_ancestor (T : FiniteTreeSpec) (t : T.Node) : T.Ancestor 0 t := by
  have h : ∀ n, ∀ t : T.Node, t.val = n → T.Ancestor 0 t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        exact T.ancestor_refl 0
      · have hp_lt : (T.parent t).val < n := by
          rw [← ht]
          exact T.parent_decreases t ht0
        exact T.ancestor_of_parent ht0 (ih _ hp_lt (T.parent t) rfl)
  exact h t.val t rfl

theorem root_mem_history (T : FiniteTreeSpec) (h : T.History) : T.MemHist 0 h :=
  T.root_ancestor h.1

theorem ancestor_parent_of_ne (T : FiniteTreeSpec) {a b : T.Node} (hb : b ≠ 0)
    (hab : T.Ancestor a b) (hne : a ≠ b) : T.Ancestor a (T.parent b) := by
  rcases (T.ancestorB_parent hb).mp hab with h | h
  · exact (hne h).elim
  · exact h

theorem ancestor_rank_le (T : FiniteTreeSpec) {a b : T.Node}
    (hab : T.Ancestor a b) : a.val ≤ b.val := by
  have h : ∀ n, ∀ b : T.Node, b.val = n → ∀ a, T.Ancestor a b → a.val ≤ b.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hb a hab
      by_cases hEq : a = b
      · subst a
        omega
      · by_cases hb0 : b = 0
        · subst b
          have ha0 : a = 0 := by
            by_contra hne
            change T.ancestorB a 0 = true at hab
            rw [ancestorB] at hab
            simp [hne] at hab
          subst a
          simp
        · have hParent := T.ancestor_parent_of_ne hb0 hab hEq
          have hlt : (T.parent b).val < n := by
            rw [← hb]
            exact T.parent_decreases b hb0
          have hrec := ih (T.parent b).val hlt (T.parent b) rfl a hParent
          omega
  exact h b.val b rfl a hab

theorem ancestor_trans (T : FiniteTreeSpec) {a b c : T.Node}
    (hab : T.Ancestor a b) (hbc : T.Ancestor b c) : T.Ancestor a c := by
  have h : ∀ n, ∀ c : T.Node, c.val = n → ∀ a b,
      T.Ancestor a b → T.Ancestor b c → T.Ancestor a c := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc a b hab hbc
      by_cases hbcEq : b = c
      · simpa [hbcEq] using hab
      · by_cases hc0 : c = 0
        · subst c
          have : b = 0 := by
            have hle := T.ancestor_rank_le hbc
            exact Fin.ext (by simpa using Nat.le_zero.mp hle)
          subst b
          simpa using hab
        · have hParent := T.ancestor_parent_of_ne hc0 hbc hbcEq
          have hlt : (T.parent c).val < n := by
            rw [← hc]
            exact T.parent_decreases c hc0
          have hrec := ih (T.parent c).val hlt (T.parent c) rfl a b hab hParent
          exact T.ancestor_of_parent hc0 hrec
  exact h c.val c rfl a b hab hbc

theorem ancestor_backward_linear (T : FiniteTreeSpec) {a b c : T.Node}
    (hac : T.Ancestor a c) (hbc : T.Ancestor b c) :
    T.Ancestor a b ∨ a = b ∨ T.Ancestor b a := by
  have h : ∀ n, ∀ c : T.Node, c.val = n → ∀ a b,
      T.Ancestor a c → T.Ancestor b c →
      T.Ancestor a b ∨ a = b ∨ T.Ancestor b a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc a b hac hbc
      by_cases hacEq : a = c
      · subst a
        by_cases hbcEq : b = c
        · exact Or.inr (Or.inl hbcEq.symm)
        · exact Or.inr (Or.inr hbc)
      · by_cases hbcEq : b = c
        · subst b
          exact Or.inl hac
        · by_cases hc0 : c = 0
          · subst c
            have ha0 : a = 0 := by
              have hle := T.ancestor_rank_le hac
              exact Fin.ext (by simpa using Nat.le_zero.mp hle)
            have hb0 : b = 0 := by
              have hle := T.ancestor_rank_le hbc
              exact Fin.ext (by simpa using Nat.le_zero.mp hle)
            exact Or.inr (Or.inl (ha0.trans hb0.symm))
          · have hpa := T.ancestor_parent_of_ne hc0 hac hacEq
            have hpb := T.ancestor_parent_of_ne hc0 hbc hbcEq
            have hlt : (T.parent c).val < n := by
              rw [← hc]
              exact T.parent_decreases c hc0
            rcases ih (T.parent c).val hlt (T.parent c) rfl a b hpa hpb with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h)
  exact h c.val c rfl a b hac hbc

theorem ancestor_rank_lt (T : FiniteTreeSpec) {a b : T.Node}
    (hab : T.Ancestor a b) (hne : a ≠ b) : a.val < b.val := by
  have hle := T.ancestor_rank_le hab
  have hval : a.val ≠ b.val := by
    intro heq
    exact hne (Fin.ext heq)
  omega

instance (T : FiniteTreeSpec) : DecidableRel T.Ancestor := by
  intro a b
  unfold Ancestor
  infer_instance

instance (T : FiniteTreeSpec) : DecidableRel T.Precedence := by
  intro a b
  unfold Precedence
  infer_instance

instance (T : FiniteTreeSpec) : DecidablePred T.IsLeaf := by
  intro l
  unfold IsLeaf
  infer_instance

/-- Finite histories inherit a computable finite enumeration from their leaf
predicate; generated models do not need a separately maintained list. -/
instance (T : FiniteTreeSpec) : Fintype T.History := by
  infer_instance

/-- All descendants of a node, including the node itself. -/
def descendants (T : FiniteTreeSpec) (t : T.Node) : Finset T.Node :=
  Finset.univ.filter (fun l => T.Ancestor t l)

theorem mem_descendants (T : FiniteTreeSpec) {t l : T.Node} :
    l ∈ T.descendants t ↔ T.Ancestor t l := by
  simp [descendants]

theorem descendants_nonempty (T : FiniteTreeSpec) (t : T.Node) :
    (T.descendants t).Nonempty := by
  exact ⟨t, (T.mem_descendants).2 (T.ancestor_refl t)⟩

/-- A computably selected maximum-rank descendant of `t`. -/
def canonicalLeafNode (T : FiniteTreeSpec) (t : T.Node) : T.Node :=
  (T.descendants t).max' (T.descendants_nonempty t)

theorem leaf_ancestor_eq (T : FiniteTreeSpec) {l b : T.Node}
    (hl : T.IsLeaf l) (hlb : T.Ancestor l b) : l = b := by
  have h : ∀ n, ∀ b : T.Node, b.val = n → T.Ancestor l b → l = b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro b hb hlb
      by_cases hEq : l = b
      · exact hEq
      · by_cases hb0 : b = 0
        · subst b
          have hle := T.ancestor_rank_le hlb
          exact Fin.ext (by simpa using Nat.le_zero.mp hle)
        · have hParent := T.ancestor_parent_of_ne hb0 hlb hEq
          have hlt : (T.parent b).val < n := by
            rw [← hb]
            exact T.parent_decreases b hb0
          have hleaves : l = T.parent b :=
            ih (T.parent b).val hlt (T.parent b) rfl hParent
          have hbad := hl b hb0
          exact (hbad hleaves.symm).elim
  exact h b.val b rfl hlb

theorem canonicalLeafNode_isLeaf (T : FiniteTreeSpec) (t : T.Node) :
    T.IsLeaf (T.canonicalLeafNode t) := by
  intro v hv hparent
  let l := T.canonicalLeafNode t
  have htl : T.Ancestor t l :=
    (T.mem_descendants).1 (Finset.max'_mem (T.descendants t) (T.descendants_nonempty t))
  have hlv : T.Ancestor l v := by
    apply (T.ancestorB_parent hv).2
    right
    rw [hparent]
    exact T.ancestor_refl l
  have htv := T.ancestor_trans htl hlv
  have hvMem : v ∈ T.descendants t := (T.mem_descendants).2 htv
  have hvLe : v ≤ l := Finset.le_max' (T.descendants t) v hvMem
  have hlt : l.val < v.val := by
    have h := T.parent_decreases v hv
    rw [hparent] at h
    simpa [l] using h
  change v.val ≤ l.val at hvLe
  omega

/-- The finite history space is the subtype of terminal nodes. -/
abbrev HistorySpace (T : FiniteTreeSpec) := T.History

def canonicalHistory (T : FiniteTreeSpec) (t : T.Node) : T.History :=
  ⟨T.canonicalLeafNode t, T.canonicalLeafNode_isLeaf t⟩

theorem moment_in_history (T : FiniteTreeSpec) (t : T.Node) :
    ∃ h : T.History, T.MemHist t h :=
  ⟨T.canonicalHistory t,
    (T.mem_descendants).1 (Finset.max'_mem (T.descendants t) (T.descendants_nonempty t))⟩

theorem histories_extensional (T : FiniteTreeSpec) (h1 h2 : T.History)
    (h : ∀ t : T.Node, T.MemHist t h1 ↔ T.MemHist t h2) : h1 = h2 := by
  apply Subtype.ext
  exact T.leaf_ancestor_eq h1.property ((h h1.1).mp (T.ancestor_refl h1.1))

theorem histories_linear (T : FiniteTreeSpec) (h : T.History) :
    IsLinearChain T.Precedence {t | T.MemHist t h} := by
  intro t u ht hu
  by_cases hEq : t = u
  · exact Or.inr (Or.inl hEq)
  · rcases T.ancestor_backward_linear ht hu with htu | hEq' | hut
    · exact Or.inl ⟨hEq, htu⟩
    · exact (hEq hEq').elim
    · exact Or.inr (Or.inr ⟨Ne.symm hEq, hut⟩)

theorem histories_maximal_linear (T : FiniteTreeSpec) (h : T.History) :
    IsMaximalLinearChain T.Precedence {t | T.MemHist t h} := by
  refine ⟨T.histories_linear h, ?_⟩
  intro s hs hsub t ht
  have hleaf : h.1 ∈ s := hsub ((T.ancestor_refl h.1))
  rcases hs ht hleaf with htl | hEq | hlt
  · exact htl.2
  · subst t
    exact T.ancestor_refl h.1
  · have heq := T.leaf_ancestor_eq h.property hlt.2
    subst t
    exact T.ancestor_refl h.1

theorem divergent_futures_witness (T : FiniteTreeSpec) {t : T.Node}
    (h1 h2 : T.History) (ht1 : T.MemHist t h1) (ht2 : T.MemHist t h2)
    (hne : h1 ≠ h2) :
    ∃ u v : T.Node,
      T.MemHist u h1 ∧ T.MemHist v h2 ∧
      T.Precedence t u ∧ T.Precedence t v ∧
      ¬ T.Precedence u v ∧ u ≠ v ∧ ¬ T.Precedence v u := by
  refine ⟨h1.1, h2.1, T.ancestor_refl _, T.ancestor_refl _, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by
      intro heq
      have hleaf := T.leaf_ancestor_eq h1.property (by simpa [MemHist, heq] using ht2)
      exact hne (Subtype.ext hleaf), ht1⟩
  · exact ⟨by
      intro heq
      have hleaf := T.leaf_ancestor_eq h2.property (by simpa [MemHist, heq] using ht1)
      exact hne (Subtype.ext hleaf.symm), ht2⟩
  · intro huv
    exact hne (Subtype.ext (T.leaf_ancestor_eq h1.property huv.2))
  · intro heq
    exact hne (Subtype.ext heq)
  · intro hvu
    exact hne (Subtype.ext (T.leaf_ancestor_eq h2.property hvu.2).symm)

theorem isNextMoment_iff_parent (T : FiniteTreeSpec) (t u : T.Node) (h : T.History) :
    IsNextMoment T.Precedence T.MemHist t u h ↔
      T.MemHist u h ∧ u ≠ 0 ∧ T.parent u = t := by
  constructor
  · rintro ⟨_, hu, htu, hno⟩
    have hu0 : u ≠ 0 := by
      intro hu0
      subst u
      have hle := T.ancestor_rank_le htu.2
      have ht0 : t = 0 := Fin.ext (Nat.eq_zero_of_le_zero hle)
      exact htu.1 ht0
    have hpar : T.Ancestor t (T.parent u) :=
      T.ancestor_parent_of_ne hu0 htu.2 htu.1
    have hparAnc : T.Ancestor (T.parent u) u := by
      apply (T.ancestorB_parent hu0).2
      exact Or.inr (T.ancestor_refl _)
    have hparMem : T.MemHist (T.parent u) h := T.ancestor_trans hparAnc hu
    have hparNe : T.parent u ≠ u := by
      intro heq
      have hlt := T.parent_decreases u hu0
      rw [heq] at hlt
      omega
    have hparentEq : T.parent u = t := by
      by_contra hneq
      have htpar : T.Precedence t (T.parent u) := ⟨Ne.symm hneq, hpar⟩
      have hparNext : T.Precedence (T.parent u) u := ⟨hparNe, hparAnc⟩
      exact (hno (T.parent u) hparMem ⟨htpar, hparNext⟩).elim
    exact ⟨hu, hu0, hparentEq⟩
  · rintro ⟨hu, hu0, hparent⟩
    have htuAnc : T.Ancestor t u := by
      rw [← hparent]
      exact T.ancestor_of_parent hu0 (T.ancestor_refl (T.parent u))
    have htuNe : t ≠ u := by
      intro hEq
      have hParentEq : T.parent u = u := hparent.trans hEq
      have hlt := T.parent_decreases u hu0
      rw [hParentEq] at hlt
      omega
    refine ⟨?_, hu, ⟨htuNe, htuAnc⟩, ?_⟩
    · exact T.ancestor_trans htuAnc hu
    · intro τ hτ ⟨htτ, hτu⟩
      have hτne : τ ≠ u := hτu.1
      have hτpar : T.Ancestor τ (T.parent u) :=
        T.ancestor_parent_of_ne hu0 hτu.2 hτne
      have hτt : T.Ancestor τ t := by simpa [hparent] using hτpar
      have hlt := T.ancestor_rank_lt htτ.2 htτ.1
      have hback := T.ancestor_rank_le hτt
      omega

/-- A presentation embeds a finite parent tree into an existing ActionFrame.
It supplies only temporal and incidence evidence: inventories, enacted
actions, preferences, and doxastic principles remain those of `W`. -/
structure FiniteTreePresentation (W : ActionFrame) (T : FiniteTreeSpec) where
  moment : T.Node → W.Moment
  history : T.History → W.History
  moment_injective : Function.Injective moment
  moment_surjective : Function.Surjective moment
  history_injective : Function.Injective history
  history_surjective : Function.Surjective history
  precedence_iff : ∀ a b,
    W.Precedence (moment a) (moment b) ↔ T.Precedence a b
  incidence_iff : ∀ a h,
    W.mem_hist (moment a) (history h) ↔ T.MemHist a h

/-- Immediate succession in the finite tree remains immediate after embedding
it into an ActionFrame. -/
theorem FiniteTreePresentation.map_next_moment
    {W : ActionFrame} {T : FiniteTreeSpec}
    (P : FiniteTreePresentation W T) {a b : T.Node} {h : T.History}
    (hab : IsNextMoment T.Precedence T.MemHist a b h) :
    IsNextMoment W.Precedence W.mem_hist (P.moment a) (P.moment b) (P.history h) := by
  rcases hab with ⟨ha, hb, hab, hno⟩
  refine ⟨(P.incidence_iff a h).2 ha, (P.incidence_iff b h).2 hb,
    (P.precedence_iff a b).2 hab, ?_⟩
  intro τ hτ hsplit
  obtain ⟨u, rfl⟩ := P.moment_surjective τ
  apply hno u ((P.incidence_iff u h).1 hτ)
  exact ⟨(P.precedence_iff a u).1 hsplit.1,
    (P.precedence_iff u b).1 hsplit.2⟩

end FiniteTreeSpec

end Praxeology

end
