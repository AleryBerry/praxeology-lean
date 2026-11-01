# Praxeological Critique of Decision Theory

## 1. Foundations and Formal Definitions

Decision theory—formalized by John von Neumann and Oskar Morgenstern (vNM) for objective risk, and extended by Leonard Savage to subjective uncertainty—is the normative and positive foundation of neoclassical choice under uncertainty. The core doctrine asserts that a rational agent's choices over lotteries or uncertain prospects can be uniquely represented by maximizing expected cardinal utility.

### Definition 1 (von Neumann-Morgenstern Expected Utility)
Let $\mathcal{X}$ be a set of prizes and $\mathcal{L}$ the set of simple probability distributions (lotteries) over $\mathcal{X}$. The vNM framework assumes an agent's preference relation $\succsim$ over $\mathcal{L}$ satisfies four axioms:
1. **Completeness & Transitivity:** $\succsim$ is a complete and transitive weak order.
2. **Continuity:** For all $p, q, r \in \mathcal{L}$ with $p \succ q \succ r$, there exists $\alpha, \beta \in (0,1)$ such that $\alpha p + (1-\alpha) r \succ q \succ \beta p + (1-\beta) r$.
3. **Independence:** For all $p, q, r \in \mathcal{L}$ and $\alpha \in (0, 1]$, $p \succsim q \iff \alpha p + (1-\alpha) r \succsim \alpha q + (1-\alpha) r$.

Under these axioms, there exists a cardinal utility function $u : \mathcal{X} \to \mathbb{R}$, unique up to positive affine transformation ($u' = a u + b$, $a > 0$), such that:

$$
p \succsim q \iff \mathbb{E}_p[u] = \sum_{x \in \mathcal{X}} p(x) u(x) \ge \sum_{x \in \mathcal{X}} q(x) u(x) = \mathbb{E}_q[u]
$$

### Definition 2 (Savage's Subjective Expected Utility)
Savage extends the model to states of the world $\mathcal{S}$ and acts $f : \mathcal{S} \to \mathcal{X}$, postulating the "Sure-Thing Principle" (Postulate P2) to derive both a unique subjective probability measure $\mu$ on $\mathcal{S}$ and a cardinal utility function $u$ satisfying:

$$
f \succsim g \iff \int_{\mathcal{S}} u(f(s)) \, d\mu(s) \ge \int_{\mathcal{S}} u(g(s)) \, d\mu(s)
$$

---

## 2. Catallactic Breakdown & Mathematical Critiques

### 2.1 The Category Error of Probability-Weighted Utility Sums
Expected utility theory rests on multiplying utility numbers by probabilities and summing the products: $\sum p_i u(x_i)$.

Praxeologically, this operation is mathematically invalid:
1. Subjective utility is strictly ordinal (Chapter 3, Assumption 3.3). An ordinal ranking expresses relative priority ($A \succ B$); it has no mathematical scale, zero-point, or unit of measurement.
2. Multiplying an ordinal rank by a probability number and adding them is a mathematical category mistake: ordinal ranks cannot be added or multiplied ($u_1 \times p_1 + u_2 \times p_2$ is meaningless). 
3. The vNM "cardinal utility" derived from lottery choices is not a measure of psychic satisfaction or felt unease; it is merely an algebraic scaling factor concocted to make the expectation formula hold by construction.

### 2.2 Class Probability vs. Case Probability
Neoclassical decision theory treats all uncertainty as reducible to probability distributions over a known state space $\mathcal{S}$.

Ludwig von Mises demonstrated that this conflates two fundamentally distinct categories of knowledge:
1. **Class Probability (Risk):** Applies to situations where we know everything about the behavior of an entire homogeneous class of events, but nothing about the specific outcome of any individual instance (e.g., mortality tables in life insurance, dice rolls, or coin flips). Here, actuarial risk pooling is possible.
2. **Case Probability (Knightian Uncertainty):** Applies to unique, non-repeatable historical events where each instance is unique (e.g., an entrepreneurial business investment, the outcome of a political election, or a technological innovation). Here, the actor knows some factors affecting the case, but is ignorant of others. 
3. Applying calculus-based probability distributions to unique entrepreneurial choices commits an ontological category error: human action takes place in open, historical time where the space of future events cannot be exhaustively enumerated in advance.

### 2.3 The Independence Axiom and the Falsehood of Isolated Evaluation
The Independence Axiom (and Savage's Sure-Thing Principle) asserts that an agent's preference between two prospects in state $s_1$ is completely independent of what would have occurred in state $s_2$.

Praxeologically, this axiom misrepresents human deliberation under uncertainty (Chapter 5):
1. A human being choosing a plan of action evaluates the prospective plan as an integrated, holistic end at decision node $\langle t, h \rangle$.
2. The psychological reality of relief from felt unease depends on the entire contingency tree. As the Allais and Ellsberg paradoxes empirically demonstrated, real human beings systematically violate the independence axiom because certainty and ambiguity carry distinct qualitative meaning that cannot be parsed into additive probabilities.

---

## 3. Formal Theorems

### Theorem 1 (Discrete Plausibility Strata vs. Continuous Probability)
In an action frame, an agent's epistemic state over historical branches $h \in \mathcal{H}$ is characterized by a discrete finite ranking of plausibility strata:

$$
\mathcal{P}_{\text{plaus}}(i, t, h) = \langle \Pi_1 \succ_{\text{plaus}} \Pi_2 \succ_{\text{plaus}} \dots \succ_{\text{plaus}} \Pi_k \rangle
$$

rather than a real-valued probability measure $\mu : \mathcal{F} \to [0, 1]$. Purposeful action requires selecting an undominated action across the most plausible branches, without requiring cardinal probability weighting.

**Proof.** Direct from Chapter 5 (Epistemic Strata and Uncertainty). Human actors deliberate over finite partitions of possibilities $\Pi_k \subseteq H(t)$. An action $\alpha$ is purposeful when its outcome relieves unease over the passive baseline on the agent's primary plausibility stratum and is undominated by feasible alternatives (Chapter 5, Proposition 5.2). This choice rule is strictly ordinal and requires zero probability integration. $\blacksquare$

### Theorem 2 (The Epistemic Validity of the Allais and Ellsberg Choices)
Let an agent face the choice between a guaranteed certain outcome $A$ and a risky lottery $B$. If the agent strictly prefers $A \succ B$, and in a compound lottery strictly prefers the corresponding alternative that violates the vNM independence axiom:

$$
A \succ B \quad \wedge \quad \text{Lottery}_1 \prec \text{Lottery}_2
$$

this choice profile satisfies all conditions of purposeful action:

$$
\exists P : \text{StrictPoset}(\text{Ends}), \quad \mathsf{P}(i, t, h, \alpha_A) \wedge \mathsf{P}(i, t', h', \alpha_{\text{Lottery}_2})
$$

**Proof.** The two decisions occur at distinct decision nodes $\langle t, h \rangle$ and $\langle t', h' \rangle$. By Chapter 3 (Proposition 3.32), preference rankings across distinct decision nodes or contexts do not violate asymmetry or transitivity. The Allais choices reflect a genuine ordinal preference for certainty (relief of doubt) that is fully consistent with the Action Axiom. $\blacksquare$

### Theorem 3 (Non-Identifiability of Counterfactual Expected Utility)
Let historical observations record the enacted action $\alpha = \text{enacted}(i, t, h)$ and its realized outcome. No econometric estimator can identify the agent's subjective probability distribution $\mu$ or counterfactual expected utility over unchosen branches:

$$
\text{outcome}(i, \alpha^{\ast}, t, h) = \text{outcome}'(i, \alpha^{\ast}, t, h) \implies \text{est}(\mathcal{O}_{\text{obs}}) = \text{est}(\mathcal{O}'_{\text{obs}})
$$

even when the unchosen lottery payoffs diverge arbitrarily: $`\mathbb{E}_{\mu}[\beta] \neq \mathbb{E}_{\mu'}[\beta]`$.

**Proof.** Direct from Chapter 14, Theorem 14.1 (Econometric Non-Identifiability). Econometric data record realized history branches, not subjective probability weights assigned to counterfactual paths. Multiple mutually contradictory probability structures generate identical historical actions. $\blacksquare$

---

## 4. Decision-Theoretic Fallacies

### 4.1 The "Irrationality" of Ambiguity Aversion
Decision theorists label Ellsberg's ambiguity aversion (preferring an urn with known 50/50 red/black balls over an urn with unknown ball composition) as an "irrational behavioral bias" because it cannot be reconciled with Savage's subjective probability axioms.

Praxeologically, this accusation is a category error:
- It is entirely purposeful and rational for an acting human being to prefer operating under known physical parameters rather than unknown, unquantifiable uncertainty.
- Labeling an actor "irrational" simply because their subjective preference does not fit a theorist's preferred mathematical formula reflects normative academic arrogance, not empirical science.

### 4.2 The Mechanical Reduction of Entrepreneurship
Neoclassical decision theory models the business entrepreneur as a computer solving an expected utility maximization problem over an existing, static probability distribution.

Praxeologically, this erases the essence of entrepreneurship:
- In the real world of dynamic change, the future is not a known roulette wheel with predetermined probabilities; it is an unwritten book (Chapter 10).
- The entrepreneur does not compute expected values; the entrepreneur exercises judgment, creates new production processes, and bears irreducible uncertainty under the prospect of profit or loss (Chapter 10, Definition 10.1).

---

## 5. Praxeological Reconstruction

Decision theory attempted to reduce the deep, qualitative reality of human choice under uncertainty to mechanical calculus, creating artificial "paradoxes" whenever human beings act like thinking agents rather than computing machines.

Praxeology reconstructs decision-making under uncertainty on apodictic foundations:
1. **Ordinal Action in Open Time:** All human choice is an attempt to exchange a less satisfactory future state for a more satisfactory future state in an open, uncertain world (Chapter 1; Chapter 3).
2. **Plausibility and Epistemic Strata:** Deliberation operates through discrete plausibility strata over possible historical paths, updating beliefs through observable physical signals rather than mathematical integration over unmeasurable probabilities (Chapter 5).
3. **The Centrality of Judgment:** Where class probabilities are absent, human actors rely on case judgment and entrepreneurial appraisal. The success of an action is judged not by whether it satisfied mathematical independence axioms, but by whether it successfully attained the actor's purposeful end (Chapter 10).
