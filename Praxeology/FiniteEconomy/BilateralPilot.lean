/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Execution
public import Praxeology.Frame.Witnesses

/-!
# Bilateral finite-tree compiler pilot

The existing bilateral `ActionFrame` is presented through the parent-pointer
tree compiler. Its preference and doxastic laws remain those of the frame;
this module checks the tree and execution-table bridge.
-/

@[expose] public section

namespace Praxeology

/-- Root with four terminal branches, indexed in parallel with the bilateral
trade witness's history type. -/
def bilateralFiniteTree : FiniteTreeSpec where
  extraNodes := 4
  parent := fun _ => 0
  parent_root := rfl
  parent_decreases := by
    intro v hv
    have hvpos : 0 < v.val := by
      by_contra hn
      have hz : v.val = 0 := Nat.eq_zero_of_not_pos hn
      apply hv
      exact Fin.ext hz
    exact hvpos

namespace bilateralFiniteTree

abbrev Node := Fin 5
abbrev History := {l : Node // FiniteTreeSpec.IsLeaf bilateralFiniteTree l}

def momentOfNode (t : Node) : BilateralMoment :=
  match t.val with
  | 0 => .root
  | 1 => .leaf0
  | 2 => .leaf1
  | 3 => .leaf2
  | _ => .leaf3

def nodeOfMoment : BilateralMoment → Node
  | .root => 0
  | .leaf0 => 1
  | .leaf1 => 2
  | .leaf2 => 3
  | .leaf3 => 4

private theorem history_node_ne_root (h : History) : h.val.val ≠ 0 := by
  intro hzero
  have hval : h.val = (0 : Node) := Fin.ext hzero
  have hOne : (1 : Node) ≠ 0 := by decide
  have hleaf := h.property 1 hOne
  apply hleaf
  simpa [bilateralFiniteTree] using hval.symm

def historyOfIndex (h : Fin 4) : History :=
  ⟨⟨h.val + 1, by omega⟩, by
    intro v hv heq
    have heqVal := congrArg Fin.val heq
    have hparent_zero : (bilateralFiniteTree.parent v).val = 0 := by
      simp [bilateralFiniteTree]
    have hbad : 0 = h.val + 1 := by
      simp [hparent_zero] at heqVal
    omega⟩

def historyIndex (h : History) : Fin 4 :=
  ⟨h.val.val - 1, by
    have hne := history_node_ne_root h
    have hlt := h.val.isLt
    omega⟩

theorem historyIndex_historyOfIndex (h : Fin 4) :
    historyIndex (historyOfIndex h) = h := by
  apply Fin.ext
  simp [historyIndex, historyOfIndex]

theorem historyOfIndex_historyIndex (h : History) :
    historyOfIndex (historyIndex h) = h := by
  apply Subtype.ext
  apply Fin.ext
  have hne := history_node_ne_root h
  simp only [historyIndex, historyOfIndex]
  omega

def presentation : FiniteTreeSpec.FiniteTreePresentation
    BilateralTradeActionFrame bilateralFiniteTree where
  moment := momentOfNode
  history := historyIndex
  moment_injective := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp [momentOfNode] at hab ⊢
  moment_surjective := by
    intro t
    cases t with
    | root => exact ⟨(0 : Node), by simp [momentOfNode]⟩
    | leaf0 => exact ⟨(1 : Node), by simp [momentOfNode]⟩
    | leaf1 => exact ⟨(2 : Node), by simp [momentOfNode]⟩
    | leaf2 => exact ⟨(3 : Node), by simp [momentOfNode]⟩
    | leaf3 => exact ⟨(4 : Node), by simp [momentOfNode]⟩
  history_injective := by
    intro h1 h2 heq
    have h := congrArg historyOfIndex heq
    rw [historyOfIndex_historyIndex h1, historyOfIndex_historyIndex h2] at h
    exact h
  history_surjective := by
    intro h
    exact ⟨historyOfIndex h, historyIndex_historyOfIndex h⟩
  precedence_iff := by
    intro a b
    change bilateral_prec (momentOfNode a) (momentOfNode b) ↔
      FiniteTreeSpec.Precedence bilateralFiniteTree a b
    fin_cases a <;> fin_cases b <;>
      simp [FiniteTreeSpec.Precedence, FiniteTreeSpec.Ancestor,
        FiniteTreeSpec.ancestorB, bilateralFiniteTree, momentOfNode,
        bilateral_prec]
  incidence_iff := by
    intro a h
    rcases h with ⟨hleafNode, hleaf⟩
    have hnodeNe : hleafNode ≠ (0 : Node) := by
      intro hz
      subst hleafNode
      have hOne : (1 : Node) ≠ 0 := by decide
      exact hleaf 1 hOne (by simp [bilateralFiniteTree])
    change bilateral_mem_hist (momentOfNode a) (historyIndex ⟨hleafNode, hleaf⟩) ↔
      FiniteTreeSpec.MemHist bilateralFiniteTree a ⟨hleafNode, hleaf⟩
    fin_cases a <;> fin_cases hleafNode <;>
      simp [FiniteTreeSpec.MemHist, FiniteTreeSpec.Ancestor,
        FiniteTreeSpec.ancestorB, bilateralFiniteTree, momentOfNode,
        historyIndex, bilateral_mem_hist] at *

end bilateralFiniteTree

end Praxeology

end
