---
# 03_intertemporal_marginal.md
# Mathematical Formalization Spec for Antigravity (Lean 4)
# Law of Marginal Utility, Time Preference, and Originary Interest

## 1. Ordinal Marginal Utility

### Definitions and Sort Disciplines
- Let m ∈ M be a scarce good, endowment ω_i(t, h, m) = k ∈ ℕ⁺.
- Standard Atomic Regime: E₁(m) = { e₁, ..., e_N } (N > k) where ∀ r, ρ(e_r, m) = 1.
- Ranked: e₁ ≻_{i,t,h} e₂ ≻ ... ≻ e_N.
- Optimal allocation set S*(k) = { e₁, ..., e_k }.
- Definite Description Formulation (ensuring type E, not P(E)):
  MU_{i,t,h}(m, k) := ι e ∈ E₁(m), (e ∈ S*(k) \ S*(k - 1))

### Axiom 4 (Sub-Menu Monotonicity)
Given S, S' ⊆ E₁(m), |S| = |S'| = k, if ∃ bijection σ : S \ S' → S' \ S such that 
∀ e ∈ S \ S', e ≻_{i,t,h} σ(e), then S ≻_{i,t,h}^P S'.

### Theorem 2.1 (Law of Purely Ordinal Diminishing Marginal Utility)
1. S*(k) = { e₁, ..., e_k } uniquely solves max_{≻^P}.
2. MU_{i,t,h}(m, k) = e_k.
3. Diminishing Marginal Utility:
   ∀ k₁ k₂ ∈ {1, ..., N}, k₁ < k₂ → MU_{i,t,h}(m, k₁) ≻_{i,t,h} MU_{i,t,h}(m, k₂).
Proof: Direct consequence of transitivity on the underlying ordering of E₁(m).

---

## 2. Temporal Horizon and Axiom of Time Preference

### Definition 2.3' (Repaired Boundary Conditions)
1. Post-Horizon Degenerate Menu:
   Beyond lifespan T_max(i, h), action menu becomes singleton:
   ∀ t > T_max(i, h), A_i(t) = { α₀ } with π_i(t, α₀) = H(t).
2. Open Epistemic Horizon:
   ∀ ⟨τ', h'⟩ ∈ Min_{⪯_{i,τ}^B}(K_i(τ, h)), (τ'^{+h'})^{+h'} ≤ T_max(i, h').

### Axiom 5 (Positive Time Preference)
Holding end quality and epistemic conditions constant:
∀ e ∈ E_i^+(t, h), ∀ τ₁ τ₂ ∈ h, (t ≤ τ₁ < τ₂) → (⟨e, τ₁⟩ ≻_{i,t,h} ⟨e, τ₂⟩)

### Theorem 2.3' (Action Impossibility Under Non-Positive Time Preference)
If an agent holds universal negative time preference (∀ τ₁ < τ₂, ⟨e, τ₂⟩ ≻ ⟨e, τ₁⟩) under an Open Epistemic Horizon, then:
∀ τ ∈ [t₀, T_max(i, h)]_h, M, ⟨τ, h⟩ ⊨ ¬Exec(α_e(τ))
Proof: At every node, deferral strictly dominates realization, preventing execution prior to death.

### Theorem 2.4' (Positive Originary Interest - With Stationarity Condition)
- Hypothesis: Baseline endowment stationarity ω_i(τ₁, h, m) = ω_i(τ₂, h, m) and preference invariance.
- Let ⟨q, τ⟩ denote q units of m available at τ.
1. Unit-for-unit exchange is rejected: ⟨q, τ₁⟩ ≻_{i,t,h} ⟨q, τ₂⟩.
2. Intertemporal voluntary exchange yielding ⟨q', τ₂⟩ for ⟨q, τ₁⟩ requires q' = q + δ with δ ∈ ℕ⁺.
3. Originary Interest Rate:
   ι_{i,t,h}(q, τ₁, τ₂) := (q' - q) / q = δ / q > 0, where ι ∈ ℚ⁺.
Proof: Follows from Axiom 4 and Axiom 5 over discrete unit bundles.
