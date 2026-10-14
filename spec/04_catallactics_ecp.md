# 04_catallactics_ecp.md
# Mathematical Formalization Spec for Antigravity (Lean 4)
# Exchange, Money Emergence (Bourbaki-Witt), Prices, and ECP

## 1. Bilateral Exchange and Money Emergence

### Axiom 6 (Voluntary Bilateral Consent)
Bilateral exchange χ(i, j, q_A m_A, q_B m_B) executes iff:
[ :i dstit: ] Offer(...) ∧ [ :j dstit: ] Accept(...)
Yields Theorem 3.1: Double inequality of subjective valuations (both agents expect gain).

### Theorem 3.2' (Mengerian Emergence of Money via Bourbaki-Witt)
Let L = ⟨P(I)^M, ⊑⟩ be the poset of acceptance profiles, ordered by inclusion Γ ⊑ Γ'.
Transition operator Φ : L → L:
  Φ(Γ)_m = Γ(m) ∪ { i ∈ I | m ∈ argmax_{m'} |Γ(m')| ∧ Feas_indirect(i, m, d_i) }
1. Φ is NOT globally monotone on (P(I)^M, ⊆). (Knaster-Tarski fails).
2. Φ is Inflationary: ∀ Γ, Γ ⊑ Φ(Γ).
3. Convergence: By the Bourbaki-Witt Theorem, iteration from any initial Γ₀ in a finite chain-complete poset reaches a fixed point Γ* = Φ(Γ*) in finite steps.
4. If unique initial highest marketability good m* exists, Γ*(m*) = I (Universal Money).

---

## 2. Discrete Marginal Pairs and Catallactic Pricing

### Theorem 3.3' (Marginal Pairs on Discrete Currency Grid M_D)
Let grid be M_D = { k / D | k ∈ ℕ⁺ }.
Buyers sorted v_1^b > v_2^b > ... > v_r^b; sellers sorted v_1^s < v_2^s < ... < v_r^s.
Let r* be the marginal clearing pair: v_{r*}^b ≥ v_{r*}^s and v_{r*+1}^b < v_{r*+1}^s.
Price bounds:
  max(v_{r*}^s, v_{r*+1}^b + 1/D) ≤ P_t(m) ≤ min(v_{r*}^b, v_{r*+1}^s - 1/D)
- Width: W_t(m) = P_max - P_min ≥ 0.
- Guarantees extra-marginal deterrence without tie ambiguity.

---

## 3. The Economic Calculation Problem (ECP)

### Structure of Production
Production DAG G = (V, E_edges). Nodes are capital goods m_cap ∈ M_cap maturing to consumer goods c ∈ M_1.
Input vector x(ω) ∈ ℕ₀^d for method ω ∈ Ω(c).

### Lemma 4.1 (Non-Existence of Capital Prices under Socialism)
Under regime R_soc, property in capital goods is abolished, suppressing market exchange:
∀ m ∈ M_cap, A^exchange(m) = ∅.
By Theorem 3.3', without exchange, reservation bounds do not exist, and P_t(m) is undefined.

### Theorem 4.2 (Undefinedness of Cost Minimization over Antichains)
Let ω₁, ω₂ ∈ Ω(c) such that input vectors form an antichain in (ℕ₀^d, ≤_phys)
(i.e., x_a(ω₁) > x_a(ω₂) while x_b(ω₁) < x_b(ω₂)):
1. Under Catallactics (R_cat):
   Cost functional C_t(x) = ∑_{r=1}^d P_t(m_r) x_r maps to ℚ⁺, inducing a total linear order.
2. Under Socialism (R_soc):
   - Addition across heterogeneous physical types (e.g. steel + electricity) is ill-typed.
   - Any cost-ranking relation ⪯_cost derived from ordinal preferences over final consumer goods M_1 is invariant under order-automorphisms Aut(M_1, ≻).
   - Cardinal sums of rank differences change arbitrarily under order-preserving transformations.
   - Conclusion: argmin_{ω ∈ Ω(c)} Cost(ω) is mathematically undefined in R_soc.

### Theorem 4.3 (Semantic Incommensurability vs. Algorithmic Complexity)
The failure of central economic calculation is not an NP-hardness / Turing time-complexity barrier on known inputs, but an epistemic undefinedness: the objective function does not exist within the relational model.
