# 01_ontology_and_frames.md
# Mathematical Formalization Spec for Antigravity (Lean 4)
# Sorts, Frame Conditions, Semantics of Time, Agency, and Belief

## 1. Multi-Sorted Signature (Σ_prx)

The foundational language L_prx operates over the following discrete sorts:
- `Agent` (I): Finite, non-empty set of discrete acting entities.
- `Moment` (T): Discrete points in time equipped with a strict order (<).
- `Action` (A): Finite set of elementary intentional choices.
- `Means` (M): Discrete physical goods/resources measured in units of ℕ₀.
- `Ends` (E): Discrete teleological goals/states of affairs.
- `History` (H): Maximal chains in (T, <).
  - H(t) := { h : History | t ∈ h }, the history bundle passing through moment t.

### Functional & Relational Signatures
- `ω : Agent → Moment → History → Means → ℕ₀`: Physical endowment function.
- `ρ : Ends → Means → ℕ₀`: Production requirement function (minimum discrete units of means m required to instantiate end e).
- `Scarce : Agent → Moment → History → Means → Prop`: Scarcity predicate.
- `Precedes (≺) : Ends → Ends → Agent → Moment → History → Prop`: Strict ordinal preference.

---

## 2. Kripke-Tree Temporal Frame (CTL* Branching Time)

The structure (T, <) satisfies the following axioms:
1. Strict Order:
   - Irreflexive: ∀ t, ¬(t < t)
   - Asymmetric: ∀ t1 t2, t1 < t2 → ¬(t2 < t1)
   - Transitive: ∀ t1 t2 t3, t1 < t2 ∧ t2 < t3 → t1 < t3
2. Backward Linearity (Historical Determinism / Fixed Past):
   ∀ t t1 t2, (t1 < t ∧ t2 < t) → (t1 < t2 ∨ t1 = t2 ∨ t2 < t1)
3. Forward Branching (Open Future):
   ∀ t, ∃ t1 t2, (t < t1 ∧ t < t2 ∧ t1 ≠ t2)
4. Discrete Successors:
   ∀ t h, t ∈ h → ∃! t_succ ∈ h, (t < t_succ ∧ ¬∃ τ ∈ h, t < τ ∧ τ < t_succ)

---

## 3. Agency and Choice Partitions (STIT / PDL)

For every agent i ∈ I and moment t ∈ T:
- Feasible Menu: A_i(t) ⊆ A is a non-empty finite set.
- A_i(t) contains a distinguished element α₀ (the passive/inertial baseline).
- Choice Partition: Π_i(t) = { π_i(t, α) | α ∈ A_i(t) } partitions H(t):
  1. ⋃_{α ∈ A_i(t)} π_i(t, α) = H(t)
  2. ∀ α β ∈ A_i(t), α ≠ β → π_i(t, α) ∩ π_i(t, β) = ∅
  3. ∀ α ∈ A_i(t), π_i(t, α) ≠ ∅
  4. Independence of Agency: ∀ (α_i)_{i ∈ I} ∈ ∏_i A_i(t), ⋂_{i ∈ I} π_i(t, α_i) ≠ ∅

### Definition 1.2' (Repaired Model-Theoretic Truth Conditions)
Let M be a model, t ∈ T, h ∈ H(t).
1. Execution Predicate:
   M, ⟨t, h⟩ ⊨ Exec(α_i) ↔ h ∈ π_i(t, α_i)
2. Dynamic Modality ([α_i]ψ):
   M, ⟨t, h⟩ ⊨ [α_i]ψ ↔ ∀ h' ∈ π_i(t, α_i), M, ⟨t, h'⟩ ⊨ ψ
   (Note: Counterfactual jumping: non-vacuous even if h ∉ π_i(t, α_i)).
3. Deliberative STIT ([ :i dstit: ]ψ):
   M, ⟨t, h⟩ ⊨ [ :i dstit: ]ψ ↔ 
     (∀ h' ∈ Π_i(t, h), M, ⟨t, h'⟩ ⊨ ψ) ∧ (∃ h'' ∈ H(t), M, ⟨t, h''⟩ ⊭ ψ)

---

## 4. Doxastic Epistemic Logic (DEL)

- Information Partition: Equivalence relation ~_{i,t} over T × H, inducing equivalence classes K_i(t, h).
- Plausibility Order: Well-founded preorder ⪯_{i,t}^B on K_i(t, h).
- Minimal Plausibility Worlds: Min_{⪯_{i,t}^B}(K_i(t, h)).
- Subjective Belief (B_i ψ):
  M, ⟨t, h⟩ ⊨ B_i ψ ↔ ∀ ⟨t', h'⟩ ∈ Min_{⪯_{i,t}^B}(K_i(t, h)), M, ⟨t', h'⟩ ⊨ ψ
- Dynamic Epistemic Event Update ([!ε]ψ): Plausibility update restricting K_i to worlds satisfying ε.
