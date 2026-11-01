# Specification 09: Poset-Theoretic Behavioral Equivalence and Anomaly Invariance

Formal mathematical specification for [`Praxeology/BehavioralPoset.lean`](../Praxeology/BehavioralPoset.lean).

---

## 1. Poset-Theoretic Behavioral Embedding

Behavioral economics (Kahneman, Tversky, Thaler) purports to refute neoclassical rationality—and by extension praxeological deduction—by documenting empirical "anomalies": framing effects, loss aversion, status-quo bias, and hyperbolic discounting. Praxeology proves that these phenomena do not violate human action, but are mathematically isomorphic to context- and time-dependent strict partial orders on $`\text{Ends}`$:

* **Contextual Framing Structure:** A mapping $`F : \text{Context} \to (\text{Ends} \to \text{Ends} \to \text{Prop})`$ that is asymmetric and transitive within each context $`c \in \text{Context}`$ ([`ContextualFrame`](../Praxeology/BehavioralPoset.lean#L34)).
* **Poset Embedding Theorem:** For every framing context $`c`$, $`F`$ induces a mathematically valid strict partially ordered set $`\langle \text{Ends}, <_c \rangle`$:
```math
  \forall c \in \text{Context}, \quad \text{contextualToPoset}(F, c) \in \text{StrictPoset}(\text{Ends})
```
  ([`contextual_to_poset`](../Praxeology/BehavioralPoset.lean#L53)).

---

## 2. Cross-Frame Preference Reversals Consistent with Asymmetry

A famous empirical finding is that presenting the exact same physical dilemma in positive ("lives saved") versus negative ("lives lost") frames flips agents' stated choices ($`e_1 \succ e_2`$ in frame $`c_1`$, but $`e_2 \succ e_1`$ in frame $`c_2`$):

* **Neoclassical Breakdown:** This falsifies the neoclassical assumption of an invariant, context-free objective utility function $`U : X \to \mathbb{R}`$.
* **Praxeological Consistency:** Praxeological preference is strictly ordinal and situated at the moment of choice. Because $`c_1 \neq c_2`$, the two relations $`\succ_{c_1}`$ and $`\succ_{c_2}`$ represent distinct indexed relations:
```math
  e_1 \succ_{c_1} e_2 \quad \wedge \quad e_2 \succ_{c_2} e_1
```
  does not violate asymmetry within either frame ([`framing_reversal_consistent_with_asymmetry`](../Praxeology/BehavioralPoset.lean#L61)).
* **Purposeful Action Invariance:** Under any contextual frame $`c`$, the agent's choice satisfies all conditions of purposeful action ([`purposeful_act_invariant_under_framing`](../Praxeology/BehavioralPoset.lean#L162)).

---

## 3. Hyperbolic Discounting and Dynamic Inconsistency

Behavioral economists argue that hyperbolic discounting (preferring 100 monetary units today over 110 units tomorrow, but preferring 110 units in 31 days over 100 units in 30 days) proves irrationality:

* **Temporal Poset Re-Ordering:** At moment $`t_1`$, the agent ranks the delayed larger reward higher; at moment $`t_2`$, as the prize enters the immediate present, the subjective ranking flips:
```math
  \text{pref}_{t_1}(e_{\text{delayed}}, e_{\text{immediate}}) \quad \wedge \quad \text{pref}_{t_2}(e_{\text{immediate}}, e_{\text{delayed}})
```
* **Praxeological Theorem:** The agent acts purposefully at *both* moments $`t_1`$ and $`t_2`$. Dynamic preference evolution across time does not violate the Action Axiom, which requires only that action at node $`\langle t, h \rangle`$ be directed toward relieving the most urgent felt unease experienced at *that* moment ([`hyperbolic_reversal_consistent_with_action_axiom`](../Praxeology/BehavioralPoset.lean#L197)).

---

## 4. Loss Aversion and Reference-Dependent Choice

Loss aversion (Kahneman & Tversky's Prospect Theory) observes that individuals weight losses more heavily than equivalent gains relative to a status-quo reference point $`e_{\text{ref}}`$:

* Our codebase formalizes reference-dependent choice as a valid asymmetric relation $`L`$ on $`\text{Ends}`$.
* We prove that an acting agent exhibiting loss aversion satisfies the Praxeological Action Axiom: the agent acts to attain an undominated end relative to their perceived baseline ([`loss_aversion_instantiates_purposeful_act`](../Praxeology/BehavioralPoset.lean#L317)).

---

## 5. The Behavioral Anomaly Fallacy Refuted

The widespread claim that experimental psychology has refuted the deductive foundation of Austrian economics rests on a category mistake:

```math
\forall F : \text{ContextualFrame}, \forall c : \text{Context}, \quad \exists P : \text{StrictPoset}(\text{Ends}), \quad P.{<} = F.\text{framePref}(c)
```
([`contextual_frame_induces_strict_poset`](../Praxeology/BehavioralPoset.lean#L351)).

Behavioral anomalies demonstrate that psychological preferences are complex, mutable, and frame-sensitive; but whenever a human being acts, they deliberately employ means to achieve what they subjectively rank as their most urgent end at that historical juncture. The Praxeological Action Axiom remains categorical and universally valid.

---

## 6. Bounded Contemplation and Purposeful Action

Herbert Simon's concept of "bounded rationality" posits that agents do not evaluate all conceivable options. In our formalization:
* Contemplated actions are finite: $`\mathcal{A}_{\text{cont}}(i, t, h)`$.
* Feasible actions require contemplation: $`\alpha \in \mathcal{A}_{\text{feas}}(i, t, h) \iff \alpha \in \mathcal{A}_{\text{cont}}(i, t, h) \wedge \forall m, \text{use}(m) \le \omega(m)`$.
* An uncontemplated option $`\gamma \notin \mathcal{A}_{\text{cont}}`$ is strictly infeasible ($`\gamma \notin \mathcal{A}_{\text{feas}}`$), and purposeful action $`\mathsf{P}(i, t, h, \alpha)`$ requires undominatedness only over feasible actions:
```math
\mathsf{P}(i, t, h, \alpha) \wedge \gamma \notin \mathcal{A}_{\text{cont}}(i, t, h) \implies \gamma \notin \mathcal{A}_{\text{feas}}(i, t, h) \wedge \forall \beta \in \mathcal{A}_{\text{feas}}, \neg(\text{outcome}(\beta) \succ \text{outcome}(\alpha))
```
([`bounded_contemplation_purposeful_act`](../Praxeology/BehavioralPoset.lean#L146)).

---

## 7. Condorcet Paradox: Aggregation Cycles from Strict Posets

Social choice theory (Arrow, Condorcet) shows that collective preference cannot be consistently derived from individual preferences:
* In [`condorcet_majority_cycle_of_strict_posets`](../Praxeology/BehavioralPoset.lean#L211), three agents each have strict posets (linear orderings) over $`\{0, 1, 2\}`$:
  * Agent 1: $`0 \succ 1 \succ 2`$
  * Agent 2: $`1 \succ 2 \succ 0`$
  * Agent 3: $`2 \succ 0 \succ 1`$
* Pairwise majority rule generates the cyclical preference:
```math
0 \succ_{\text{maj}} 1 \succ_{\text{maj}} 2 \succ_{\text{maj}} 0
```
* Praxeological implication: Society has no mind, no ends, and no action. Voting aggregation does not produce an acting subject or an ordinal preference ranking.

---

## 8. Self-Precommitment vs. External Coercive Menu Stripping

* An agent purposefully executing self-binding at $`t_1`$ eliminates temptation from their own downstream menu $`\mathcal{A}_{\text{feas}}(i, t_2, h_{\text{commit}})`$ while acting purposefully at both nodes ([`precommitment_prunes_feasible_menu`](../Praxeology/BehavioralPoset.lean#L254)).
* External coercive regulation or nudges physically strip options by contracting stocks without consent ($`\text{EndogenouslyInvasiveJ}`$, [`FeasibleMenuStripped`](../Praxeology/Frame/Production.lean#L475)), categorizing the act as political extraction rather than voluntary coordination.
