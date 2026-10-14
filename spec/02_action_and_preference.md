# 02_action_and_preference.md
# Mathematical Formalization Spec for Antigravity (Lean 4)
# Axioms of Action, Demonstrated Preference, and Opportunity Cost

## 1. Axiom 1' (Axiom of Purposeful Human Action)

### Local Predicates
- ChoiceNode(i, t, h) ≡ |A_i^feas(t, h)| ≥ 2 ∧ 
    ∃ α ∈ A_i^feas(t, h) \ {α₀}, B_i([α₀] F φ_{e₀} ∧ [α] F φ_{e_α} ∧ (e_α ≻_{i,t,h} e₀))

- Act_i(t, h, α*) ≡
    B_i([α₀] F φ_{e₀} ∧ [α*] F φ_{e*} ∧ (e* ≻_{i,t,h} e₀)) ∧
    [ :i dstit: ] Exec(α*) ∧
    B_i(∀ β ∈ A_i^feas(t, h) \ {α*}, [β] F φ_{e_β} → (e* ≻_{i,t,h} e_β))

- PA_i(t, h) ≡ ChoiceNode(i, t, h) → ∃! α* ∈ A_i^feas(t, h), Act_i(t, h, α*)

### Axiom Statement
- Axiom 1': ∀ i ∈ I, ∀ t ∈ T, ∀ h ∈ H(t), PA_i(t, h)

---

## 2. Axiom 2(3)' (Demonstrated Preference - Scope Repaired)

Preference ≻_{i,t,h} over ends is a strict partial order (irreflexive, asymmetric, transitive), strictly linear over finite feasible ends.

### Prenex Quantifier Scope Fix:
Quantifier over alternatives β must be placed INSIDE the right-hand side of the biconditional:
```lean
axiom demonstrated_preference (i : Agent) (t : Moment) (h : History) (α_star : Action)
    (h_feas : α_star ∈ A_feas i t h) :
    [ :i dstit: ] Exec(α_star) ↔
      ∀ β ∈ (A_feas i t h \ {α_star}), End_of i α_star t h ≻_{i,t,h} End_of i β t h
