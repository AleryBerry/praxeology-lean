# Comparative Architectural Analysis: `praxeology-lean` vs. *A Formalization of Austrian Economics* ($`T_{\text{prx}}`$)

The treatise ***A Formalization of Austrian Economics — Praxeological Foundations: The Base System and Its Derived Theorems*** by Rafał Komendarczyk, Walter E. Block, John Levendis, and Frank J. Tipler (June 30, 2026; [`arXiv:2606.18292v3 [econ.TH]`](https://arxiv.org/abs/2606.18292)) establishes a foundational benchmark in mathematical economics. It encodes the core verbal deductions of Ludwig von Mises's *Human Action* and Murray N. Rothbard's *Man, Economy, and State* into a Hilbert-style many-sorted first-order theory $`T_{\text{prx}}`$ over the formal language $`\mathcal{L}_{\text{prx}}`$, accompanied by a single-file Lean 4 companion (`Praxeology.lean`).

This document provides a direct architectural and mathematical comparison between the original $`T_{\text{prx}}`$ formalization in *A Formalization of Austrian Economics* (Komendarczyk et al., 2026) and the current 17-module proof system of `praxeology-lean`. It outlines the formal motivations behind our structural generalizations, the relaxation of auxiliary premises, and the expansion into multi-agent catallactics and macroeconomics, highlighting the core mathematical breakthroughs established in the library.

---

## 1. The Base System $`T_{\text{prx}}`$ in *A Formalization of Austrian Economics*

In *A Formalization of Austrian Economics* (Komendarczyk et al., 2026), the base theory $`T_{\text{prx}}`$ isolates the foundational layer of single-actor purposeful action in classical many-sorted first-order logic with equality.

### 1.1 Signature: Sorts and Primitive Relations ($`\mathcal{L}_{\text{prx}}`$)

The formal language $`\mathcal{L}_{\text{prx}}`$ is defined over five sorts:
1. $`\text{Actors}`$ ($`a, b, p, \dots`$): purposeful human agents.
2. $`\text{Actions}`$ ($`\alpha, \beta, \gamma, \dots`$): conscious, purposeful acts (excluding involuntary reflexes; Remark 2.1).
3. $`\text{Ends}`$ ($`E, F, G, \dots`$): goals or states of affairs toward which actions are directed (atomic or composite bundles; Remark 2.10).
4. $`\text{Things}`$ ($`x, y, z, \dots`$): physical objects that become economic means only when employed in action via `Use` (Remark 2.4).
5. $`\text{Times}`$ ($`t, s, r, \dots`$): discrete moments at which actions occur (Remark 2.7).

The signature specifies six primitive relations:
* $`\text{Acts}(a, \alpha, t)`$: actor $`a`$ performs action $`\alpha`$ at time $`t`$.
* $`\text{Avail}(a, \alpha, t)`$: action $`\alpha`$ is available to actor $`a`$ in their choice menu $`\mathsf{E}_{a,t} := \{\alpha \in \text{Actions} \mid \text{Avail}(a, \alpha, t)\}`$ at time $`t`$.
* $`\text{EndOf}(\alpha, E)`$: action $`\alpha`$ is directed toward intended end $`E`$ (individuated by meaning; Remarks 2.2–2.3).
* $`\text{Use}(\alpha, x)`$: action $`\alpha`$ employs thing $`x`$ as a means.
* $`E \succ_a^t F`$: actor $`a`$ at time $`t`$ strictly prefers end $`E`$ to end $`F`$ on their subjective ordinal scale of values.
* $`t < s`$: time $`t`$ strictly precedes time $`s`$.

### 1.2 Three-Layer Axiom Architecture of $`T_{\text{prx}}`$

The base theory $`T_{\text{prx}}`$ is organized into three axiomatic layers, supplemented by an enrichment layer for marginal utility:

#### Layer 1: Action and Time Structure
* **Time-Order Axioms (T0–T6):** First time (T0: $`\exists t_0 \forall t (t_0 \le t)`$), Irreflexivity (T1), Transitivity (T2), Trichotomy (T3: $`\forall t s (t < s \lor t = s \lor s < t)`$), Nontriviality (T4), Irreversibility (T5), and Discreteness (T6: $`\forall t \exists s (t < s \land \neg \exists r (t < r \land r < s))`$). Time is a single linear discrete chain with no finite models.
* **Incidence Axioms (P1–P6):**
  - (P1) Non-empty choice menu: $`\forall a t \exists \alpha \, \text{Avail}(a, \alpha, t)`$.
  - (P2) Performance requires availability: $`\forall a \alpha t (\text{Acts}(a, \alpha, t) \implies \text{Avail}(a, \alpha, t))`$.
  - (P3) Every action has an end: $`\forall \alpha \exists E \, \text{EndOf}(\alpha, E)`$.
  - (P4) Functionality of ends: $`\forall \alpha E F (\text{EndOf}(\alpha, E) \land \text{EndOf}(\alpha, F) \implies E = F)`$.
  - (P5) Nonsynchronism: $`\forall a \alpha \beta t s (\text{Acts}(a, \alpha, t) \land \text{Acts}(a, \beta, s) \land \alpha \neq \beta \implies t \neq s)`$.
  - (P6) Free-good exclusion: $`\forall a t \alpha x (\text{Acts}(a, \alpha, t) \land \text{Use}(\alpha, x) \implies \exists \beta s (\text{Avail}(a, \beta, s) \land \text{Use}(\beta, x) \land \neg \text{Acts}(a, \beta, s)))`$.
* **Action Choice Axiom (C1):** $`\forall a t \alpha \beta (\text{Acts}(a, \alpha, t) \land \text{Acts}(a, \beta, t) \implies \alpha = \beta)`$.

#### Layer 2: Preference and Demonstration in Choice
* **Demonstrated Preference Record (Def 2.11):** Actor $`a`$ demonstrates a preference for end $`E`$ over end $`F`$ at time $`t`$ ($`E \triangleright_a^t F`$) iff:
```math
  E \neq F \land \exists \alpha \beta \left(\text{Acts}(a, \alpha, t) \land \text{Avail}(a, \beta, t) \land \alpha \neq \beta \land \text{EndOf}(\alpha, E) \land \text{EndOf}(\beta, F)\right)
```
* **Grounding (O0):** $`\forall a t E F (E \triangleright_a^t F \implies E \succ_a^t F)`$.
* **Always-Acting (O1):** $`\forall a t \exists \alpha \, \text{Acts}(a, \alpha, t)`$.
* **Menu-Comparability (O2):** $`\forall a t E F (E \neq F \land \text{EndAt}(a, t, E) \land \text{EndAt}(a, t, F) \implies (E \succ_a^t F \lor F \succ_a^t E))`$, where $`\text{EndAt}(a, t)`$ is the image of $`\mathsf{E}_{a,t}`$ under $`\text{EndOf}`$.
* **Transitivity (O3) and Asymmetry (O4):** Strict total order axioms on $`\text{EndAt}(a, t)`$ at each fixed time $`t`$.

#### Layer 3 & Marginal-Utility Enrichment: Scarcity and Allocation
* **Existence of Scarcity (S1):** $`\exists a t \alpha \beta x (\alpha \neq \beta \land \text{Avail}(a, \alpha, t) \land \text{Avail}(a, \beta, t) \land \text{Use}(\alpha, x) \land \text{Use}(\beta, x))`$.
* **Marginal Utility Schedule (MU0–MU4 & LB1):** Introduces a sort `Goods`, predicates `UnitOf(x, g)` and `Allot(a, t, x, E)` (an allocation schedule distinct from `Acts`), and five auxiliary premises—Functionality (MU0), Feasibility (MU1), Homogeneity of units (MU2), Cardinal-free scarcity (MU3), and Top-segment coherence (MU4)—plus `Labor` means-only (LB1).

### 1.3 Scope and Explicit Boundaries of the Original Lean 4 Companion
In Appendix A of *A Formalization of Austrian Economics*, the companion file `Praxeology.lean` proves:
1. Asymmetry of demonstrated preference (Theorem 4.1), unique maximality of the chosen end $`\hat{E}`$ (Proposition 4.2), existence and singleton uniqueness of opportunity cost $`\text{Cost}(a, t) := \max_{\succ_a^t}(\text{EndAt}(a, t) \setminus \{\hat{E}\})`$ (Theorem 4.3 & Corollary 4.5), structural scarcity of time (Theorem 4.6), Diminishing Marginal Utility (Theorem A & Corollary 4.18), and Increasing Marginal Disutility of Labor (Theorem B).
2. Consistency via a 3-period Crusoe snapshot $`\{0, 1, 2\}`$ and an infinite-time Crusoe model over $`\mathbb{N}`$.

As the authors explicitly note in Section 1.2 (p. 5), Remarks 2.2, 2.5, 2.14, and Section 5 ("Future research", pp. 49–50), $`T_{\text{prx}}`$ deliberately leaves outside its formalization:
* Counterfactual branching histories, epistemic uncertainty, and the divergence between intended ends and realized outcomes (profit, loss, and regret).
* Endogenous physical transition laws mapping resource endowments and capital formation across periods (`Avail` is specified externally by inspection; Remark 2.14).
* Multi-agent bilateral exchange, comparative advantage (the Mises-Ricardo Law of Association), and coercion vs. voluntary trade.
* Mengerian money emergence, discrete marginal-pair pricing brackets, and Gresham's Law.
* The Economic Calculation Problem (`CALC`), Coasean firm boundaries, and Austrian Business Cycle Theory (ABCT).

---

## 2. Architectural Generalizations and Core Breakthroughs

`praxeology-lean` builds upon the foundational groundwork established by Komendarczyk et al. (2026). By generalizing several primitive axioms, our framework broadens the base theory to handle edge cases (such as preference ties and branching timelines), removes extraneous ordering constraints, and extends the formalization from single-actor choice into multi-agent exchange, monetary calculation, and macroeconomic dynamics.

```
   A Formalization of Austrian Economics (T_prx)               praxeology-lean Proof System
===================================================     ===================================================
1. Linear Discrete Time (Times = ℕ, T0–T6)          --> Kripke-STIT Branching History Trees & Finite Models
2. Total Order on End Menus via (O2) & (O3)         --> Minimal Asymmetric Posets & Undominated Choice
3. Singleton Cost max(EndAt \ {Ê}) under (O2)       --> Dual Set-Valued Poset Frontiers (Action/StrictOCSet)
4. Unconstrained Always-Acting (O1)                 --> Distinguished Inertial Baseline α₀ (Refraining)
5. Decoupled Allot(a,t,x,E) vs. Acts(a,α,t)         --> Action-Forced Bundle Menus & Teleological Quanta
6. External Avail(a,α,t) & Static Use(α,x)          --> Endogenous Feasibility & Causal Transition Laws
7. Single-Actor Crusoe Scope (Sec. 5 Future Work)   --> Complete 17-Module Catallactic & Macroeconomic Suite
```

### 2.1 From Linear Time (T0–T6) to Branching Kripke-STIT History Trees (`Frame/Core.lean`, `Action.lean`)

* Limitation in $`T_{\text{prx}}`$: Axioms (T3) (Trichotomy) and (T6) (Discreteness) lock the model into a single linear, infinite timeline ($`\text{Times} \cong \mathbb{N}`$). In a single-path universe, there are no counterfactual branches at moment $`t`$ representing what *would* have transpired had the actor chosen $`\beta`$ instead of $`\alpha`$. Furthermore, because `EndOf` is unindexed by history branches, ex-ante intended ends cannot diverge from ex-post realized outcomes (Remark 2.2), and (T6) prohibits any finite model of the full axiom system (Appendix A, p. 51).
* **`praxeology-lean` Modification:** Replaces linear trichotomy (T3) and infinite successors (T6) with a **forward-branching Kripke-tree ontology** ([`ActionFrame`](../Praxeology/Frame/Core.lean#L276)) governed by strict precedence irreflexivity ([`moment_lt_irrefl`](../Praxeology/Frame/Core.lean#L1359)), transitivity ([`moment_lt_trans`](../Praxeology/Frame/Core.lean#L1363)), and **backward linearity** ([`backward_linearity`](../Praxeology/Frame/Core.lean#L1371)) over the moment-history incidence relation [`mem_hist`](../Praxeology/Frame/Core.lean#L1556). Agency is grounded in the trajectory function [`enacted`](../Praxeology/Frame/Core.lean#L1451):
  ```lean
  enacted : Agent → Moment → History → Action
  ```
* **Key Formal Advances and Breakthroughs:**
  1. **Constructive STIT Partitions & Counterfactual Refrainability:** Rather than postulating modal operators by fiat, STIT choice cells ([`ChoicePartition`](../Praxeology/Frame/Core.lean#L1460)) and modal dynamic boxes ([`DynamicBox`](../Praxeology/Frame/Core.lean#L1504)) are derived as kernel-checked theorems from `enacted`. By [`choice_partition_nonempty`](../Praxeology/Frame/Core.lean#L1482), every feasible action $`\alpha \in A_{\text{feas}}(i, t, h)`$—and in particular passive refraining $`\alpha_0`$—is enacted along at least one genuine counterfactual history branch $`h' \in H(t)`$.
  2. **Proof that Action Requires Branching Time:** Theorem [`global_purposeful_act_branches_history`](../Praxeology/Action.lean#L414) and Theorem [`action_implies_branching_universe`](../Praxeology/Action.lean#L1339) formally prove that purposeful action is mathematically impossible in a single-history deterministic universe: active choice strictly forces at least two distinct histories $`h_1 \neq h_2`$ passing through decision moment $`t`$.
  3. **Ex-Ante Deliberation vs. Contextual Regret:** Rather than assuming static end evaluation, `ActionFrame` couples deliberate choice with epistemic belief structures ([`DoxasticActionFrame`](../Praxeology/Action.lean#L1185)). When realized history outcomes diverge from anticipated counterfactuals, contextual regret is rigorously derived without arbitrary preference shifts via context-matched regret ([`GuaranteedContextRegret`](../Praxeology/Action.lean#L1225)) and entrepreneurial malinvestment theorems ([`entrepreneurial_cycle_regret_from_evidence`](../Praxeology/Entrepreneurship.lean#L454)), resolving Mises's distinction between ex-ante purpose and ex-post error.
  4. **Decidable Finite Consistency Models:** Because `ActionFrame` does not impose (T6), its consistency is certified on compact, fully computable finite branching models ([`BranchingMarketabilityModel`](../Praxeology/Frame/Witnesses.lean#L61), [`action_frame_consistent`](../Praxeology/Frame/Witnesses.lean#L529)).

---

### 2.2 From Menu-Comparability (O2) & Total Orders to Minimal Asymmetric Posets (`Action.lean`)

* Limitation in $`T_{\text{prx}}`$: Layer 2 of $`T_{\text{prx}}`$ imposes Menu-Comparability (O2: $`E \neq F \implies E \succ_a^t F \lor F \succ_a^t E`$) and Transitivity (O3) across the entire end menu $`\text{EndAt}(a, t)`$. As the authors note (Section 2.2, p. 17), completeness over never-chosen alternatives is an idealization that no finite choice history can observationally certify. More critically, baking (O2) into the foundational preference layer rules out:
  - **Incomparable Ends (Antichains):** Two distinct unchosen ends (or multi-dimensional physical factor bundles) that the actor has never needed to rank against one another.
  - **Distinct-End Buridan Ties:** Two available actions aiming at distinct ends $`E_{\text{left}} \neq E_{\text{right}}`$ between which the actor has no strict preference ( $`\neg(E_{\text{left}} \succ E_{\text{right}}) \land \neg(E_{\text{right}} \succ E_{\text{left}})`$ ), where (O0) + (O2) forces a strict ranking or logical paralysis.
* **`praxeology-lean` Modification:** Imposes **strict asymmetry alone** ([`pref_asymm`](../Praxeology/Action.lean#L201), from which irreflexivity [`pref_irrefl`](../Praxeology/Action.lean#L206) follows immediately) as the sole global preference axiom in [`ActionFrame`](../Praxeology/Frame/Core.lean#L276), and defines [`PurposefulAct`](../Praxeology/Action.lean#L222) via **undominated choice** over strict partial orders:
  ```lean
  def PurposefulAct (i : Agent) (t : Moment) (h : History) (α_star : Action) : Prop :=
    α_star ∈ A_feas i t h ∧
    Exec i t α_star h ∧
    (α_star = α₀ ∨ Preference i t h (End_of i α_star t h) (End_of i α₀ t h)) ∧
    ∀ β ∈ A_feas i t h, ¬ Preference i t h (End_of i β t h) (End_of i α_star t h)
  ```
* **Key Formal Advances and Breakthroughs:**
  1. **Machine-Checked Resolution of Buridan Paradoxes:** Theorems [`buridan_tie_refutes_strict_demonstrated_pref`](../Praxeology/Action.lean#L989) and [`buridan_distinct_ends_tie_refutes_strict_grounding`](../Praxeology/Action.lean#L1016) constructively prove that requiring strict preference dominance over all foregone alternatives fails under both same-end ties ($`E_1 = E_2`$) and distinct-end Buridan ties ($`E_1 \neq E_2`$). In contrast, undominated [`PurposefulAct`](../Praxeology/Action.lean#L222) is proved fully compatible with ties ([`buridan_tie_compatible_with_purposeful_act`](../Praxeology/Action.lean#L504)) and guaranteed to exist on any non-empty finite poset by strong induction ([`exists_undominated_ends`](../Praxeology/Action.lean#L627)).
  2. **Equivalence under Local Menu Comparability:** Rather than assuming (O2) globally, [`MenuComparable`](../Praxeology/Marginal.lean#L1094) is defined locally and direction-symmetrically. Theorem [`purposeful_act_and_comparable_iff_distinct_dominant`](../Praxeology/Marginal.lean#L1108) proves that $`T_{\text{prx}}`$'s unique maximum property (Proposition 4.2, formalized as [`DistinctEndDominantAct`](../Praxeology/Marginal.lean#L1100)) is logically equivalent to `ActivePurposefulAct ∧ MenuComparable`.

---

### 2.3 From Singleton `Cost(a, t)` to Dual Set-Valued Opportunity Cost Frontiers (`Action.lean`)

* Limitation in $`T_{\text{prx}}`$: Definition 4.4 and Corollary 4.5 define opportunity cost as the unique maximum $`\text{Cost}(a, t) := \max_{\succ_a^t}(\text{EndAt}(a, t) \setminus \{\hat{E}\})`$, which depends on menu completeness (O2). Furthermore, Remark 3.2 identifies a fundamental split between two readings of opportunity cost when distinct actions share an end (means-ends multiplicity):
  1. *Means lost* (foregone actions, where an unchosen rival action $`\beta \neq \alpha^{\ast}`$ also yields $`\text{End}(\beta) = \hat{E}`$).
  2. *Foregone ends unattained* (foregone ends strictly distinct from $`\hat{E}`$).
  However, $`T_{\text{prx}}`$ only formalizes the second reading (`EndAt(a, t) \ {Ê}`), which causes a discontinuity at tie boundaries: if Sector A yields 100 units and Sector B yields 99 units, the opportunity cost is 99 units, but if Sector B also yields 100 units ($`E_A = E_B = \hat{E}`$), erasing $`\hat{E}`$ deletes Sector B from the cost set.
* **`praxeology-lean` Modification:** Formalizes *both* readings of Remark 3.2 as set-valued undominated frontiers on finite posets without assuming (O2):
  1. **[`ForegoneActionEnds`](../Praxeology/Action.lean#L652) & [`ActionOCSet`](../Praxeology/Action.lean#L703):** Takes the image of all foregone actions $`\text{ForegoneActions} = A_{\text{feas}} \setminus \{\alpha^{\ast}\}`$ under `End_of`, including those sharing $`\hat{E}`$, and filters for undominated ends.
  2. **[`StrictForegoneEnds`](../Praxeology/Action.lean#L657) & [`StrictOCSet`](../Praxeology/Action.lean#L709):** Erases the realized end $`\hat{E}`$ (`(ForegoneActionEnds).erase (End_of α*)`) and filters for undominated ends, matching Definition 4.4 of *A Formalization of Austrian Economics*.
* **Key Formal Advances and Breakthroughs:**
  1. **Continuity Across Tie Boundaries:** Theorems [`end_of_mem_action_ocset_of_tie`](../Praxeology/Action.lean#L731) and [`buridan_same_end_tie_action_ocset_continuity`](../Praxeology/Action.lean#L1026) prove that when rival actions tie at the optimal end $`e^{\ast} = \hat{E}`$, $`e^{\ast} \in \text{ActionOCSet}`$, eliminating the tie-boundary discontinuity.
  2. **Bridge & Generalization Theorems:** When no unchosen action shares the realized end, [`action_ocset_eq_strict_ocset`](../Praxeology/Action.lean#L715) proves that `ActionOCSet` and `StrictOCSet` coincide identically. Both sets are proved non-empty on any finite transitive poset ([`strict_ocset_nonempty_of_trans`](../Praxeology/Action.lean#L764), [`action_ocset_nonempty_of_trans`](../Praxeology/Action.lean#L811)) and on non-transitive star orders ([`strict_ocset_nonempty_of_star_order`](../Praxeology/Action.lean#L746)), and both contract to $`T_{\text{prx}}`$'s unique singleton when local connectedness holds ([`strict_ocset_singleton_of_connected`](../Praxeology/Action.lean#L795), [`action_ocset_singleton_of_connected`](../Praxeology/Action.lean#L842)).

---

### 2.4 Explicit Inertial Baseline ($`\alpha_0`$), Felt Uneasiness, and Non-Circular Performative Grounding (`Action.lean`)

* Limitation in $`T_{\text{prx}}`$: In Section 1.1 (p. 4) of *A Formalization of Austrian Economics* (Komendarczyk et al., [arXiv:2606.18292](https://arxiv.org/abs/2606.18292)), Mises's three prerequisites of action—(i) *felt uneasiness*, (ii) *an imagined better state*, and (iii) *expectation of efficacy*—as well as the performative self-refutation of denying the Action Axiom are recorded only verbally. Formally, $`T_{\text{prx}}`$ uses Always-Acting (O1: $`\forall a t \exists \alpha \, \text{Acts}(a, \alpha, t)`$) without distinguishing active intervention from passive refraining/inertia.
* **`praxeology-lean` Modification:**
  1. Distinguishes a passive/inertial baseline action $`\alpha_0`$ ([`alpha_zero`](../Praxeology/Frame/Core.lean#L1345)) always present in $`A_{\text{feas}}`$ ([`alpha_zero_feasible`](../Praxeology/Frame/Core.lean#L1436)).
  2. Formalizes [`ActivePurposefulAct`](../Praxeology/Action.lean#L344) where the actor strictly prefers the intended end over the passive baseline: $`\text{End}(\alpha^{\ast}) \succ \text{End}(\alpha_0)`$.
  3. Formalizes the epistemic and deliberative structure of asserting propositions via [`EpistemicAssertionNorm`](../Praxeology/Action.lean#L998), [`DeliberativeEpistemicAssertion`](../Praxeology/Action.lean#L910), and [`DoxasticDeliberativeEpistemicAssertion`](../Praxeology/Action.lean#L1352).
* **Key Formal Advances and Breakthroughs:**
  1. **Formal Equivalence of Active Agency and Felt Uneasiness:** Theorem [`active_purposeful_act_iff_ne_alpha_zero`](../Praxeology/Action.lean#L382) proves that under `PurposefulAct`, executing an active intervention ($`\alpha^{\ast} \neq \alpha_0`$) is logically equivalent to possessing positive felt uneasiness over the passive baseline ( $`\text{End}(\alpha^{\ast}) \succ \text{End}(\alpha_0)`$ ). Conversely, when coercive interventions make production or active trade worse than autarky or status quo retention, `PurposefulAct` constructively forces the actor to refrain or shut down production ([`production_shutdown_boundary`](../Praxeology/StateMonopoly.lean#L434), [`BinaryFiscalDecision.baseline_purposeful_iff`](../Praxeology/StateMonopoly.lean#L416)).
  2. **Non-Question-Begging Performative Self-Falsification:** Rather than assuming that speech is automatically purposeful, [`DeliberativeEpistemicAssertion`](../Praxeology/Action.lean#L910) models assertion via DEL belief, felt unease over unexpressed error, and counterfactual reason-responsiveness on a falsifying branch $`h_f`$ ( $`\neg P(h_f) \implies \text{enacted}(i, t, h_f) = \alpha_0`$ ). Theorems [`deliberative_epistemic_assertion_refraining_witness`](../Praxeology/Action.lean#L916), [`purposeful_act_and_refraining_of_deliberative_epistemic_assertion`](../Praxeology/Action.lean#L930), and [`dialectical_self_falsification_under_deliberative_norms`](../Praxeology/Action.lean#L965) constructively deduce both `PurposefulAct` and the non-emptiness of the passive refraining cell, proving that denying purposeful action (`NoPurposefulActionProp`) is dialectically self-falsifying.

---

### 2.5 Action-Forced Bundle Allocation, Teleological Quanta, and Originary Interest (`Marginal.lean`)

* Limitation in $`T_{\text{prx}}`$: In Section 4.2 of *A Formalization of Austrian Economics* (Komendarczyk et al., [arXiv:2606.18292](https://arxiv.org/abs/2606.18292)), the allocation relation `Allot(a, t, x, E)` is introduced as a separate valuation schedule parallel to `Acts(a, α, t)`, governed by five auxiliary axioms (MU0)–(MU4). The authors note in Footnote 35 (p. 41) that counting below Rothbard's technological unit (e.g., removing 1 log from a 30-log cabin) misfires if not properly scoped, and defer intertemporal time preference, originary interest, and backward factor value imputation to future work.
* **`praxeology-lean` Modification:**
  1. Connects means-ends bundle allocation directly to `PurposefulAct` via [`UnitRequirementSchedule`](../Praxeology/Marginal.lean#L154) and [`BundleAllocationMenu`](../Praxeology/Marginal.lean#L286).
  2. Formalizes Rothbard's technological unit and Misesian complementarity via [`TeleologicalQuantumRegime`](../Praxeology/Marginal.lean#L756) ($`q_{\min} \ge 1`$) and [`TeleologicalBundleSystem`](../Praxeology/Marginal.lean#L869).
  3. Formalizes intertemporal action over [`TimedEnd`](../Praxeology/Marginal.lean) and [`CausalDoxasticOpenHorizon`](../Praxeology/Marginal.lean).
* **Key Formal Advances and Breakthroughs:**
  1. Action Axiom Forces Optimal Prefix Allocation $`S_{\text{opt}}(k)`$: Theorem [`purposeful_act_forces_S_opt_from_physical_endowment`](../Praxeology/Marginal.lean) proves that `PurposefulAct` over a `BundleAllocationMenu` bounded by physical endowment $`\omega = k`$ *forces* the agent to select the exact top-segment prefix $`S_{\text{opt}}(k) = \{0, \dots, k-1\}`$ (deriving $`T_{\text{prx}}`$'s (MU4) top-segment coherence from undominated choice), and proves [`purposeful_diminishing_marginal_utility`](../Praxeology/Marginal.lean).
  2. **Exact Resolution of Complementarity ("Odd Shoe" / 30-Log Cabin):** Proves that across full teleological quanta $`q_{\min}`$, DMU holds strictly ([`purposeful_teleological_diminishing_marginal_utility`](../Praxeology/Marginal.lean)), whereas sub-quantum physical remainders $`r < q_{\min}`$ cannot expand the set of achieved ends and are economically sterile ([`teleological_sub_quantum_remainder_sterile`](../Praxeology/Marginal.lean), [`dmu_fails_under_complementarity`](../Praxeology/Marginal.lean)).
  3. **Sunk-Cost Sterility, Backward Imputation & Positive Originary Interest:** Formalizes Remark 2.18 as [`sunk_cost_irrelevant_to_purposeful_act`](../Praxeology/Marginal.lean); proves Mengerian backward value imputation ([`mengerian_backward_value_imputation`](../Praxeology/Marginal.lean)), intertemporal capital imputation ([`intertemporal_capital_value_imputation`](../Praxeology/Marginal.lean)), and factor specificity ([`mengerian_factor_specificity_dichotomy`](../Praxeology/Marginal.lean)); and constructively derives positive time preference ([`causal_enacted_consumption_demonstrates_strict_time_pref`](../Praxeology/Marginal.lean)), positive originary interest $`\iota > 0`$ ([`purposeful_positive_originary_interest`](../Praxeology/Marginal.lean)), Böhm-Bawerk's roundabout productivity ([`bohm_bawerk_roundabout_productivity_necessity`](../Praxeology/Marginal.lean)), and the Crusoe capital epochs $`Q_0 \subsetneq Q_1 \subsetneq Q_2`$ of Table 1 ([`capital_accumulation_unlocks_action_menu_epoch`](../Praxeology/Marginal.lean)).

---

### 2.6 Endogenous Feasibility and Causal Transition Laws vs. External `Avail` (`Frame/Core.lean`, `FirmBoundary.lean`)

* Limitation in $`T_{\text{prx}}`$: As explained in Remark 2.14 (p. 16) of *A Formalization of Austrian Economics* (Komendarczyk et al., [arXiv:2606.18292](https://arxiv.org/abs/2606.18292)), `Avail(a, α, t)` cannot be computed from `Use(α, x)` and `Things` at the base level because `Use` is static, actor-blind, and history-independent; therefore, `Avail` must be specified externally by the modeler by inspection.
* **`praxeology-lean` Modification:**
  1. Introduces causal transition laws directly in [`ActionFrame`](../Praxeology/Frame/Core.lean#L276) via immediate successor relation [`IsNextMoment`](../Praxeology/Frame/Core.lean#L37) and physical conservation/production laws:
     ```lean
     law_in_re_transition : ∀ i t t' h α m,
       ¬ IsTradeAction α →
       enacted i t h = α →
       IsNextMoment Precedence mem_hist t t' h →
       omega i t' h m + use_means α m = omega i t h m + yield_means α m
     ```
  2. Defines endogenous feasibility by intersecting the agent's contemplated repertoire $`A_{\text{cont}}(i, t, h)`$ with physical endowment sufficiency ( $`\forall m, \text{use\_means}(\alpha, m) \le \omega(i, t, h, m)`$ ) via `A_feas_coupling`, embedded directly into [`ActionFrame`](../Praxeology/Frame/Core.lean#L276) and [`ActionFrame.OutcomesGroundedInEndowments`](../Praxeology/Frame/Core.lean#L961).
* **Key Formal Advances and Breakthroughs:**
  1. **Endogenous Path-Dependent Menus:** Feasibility at $`t'`$ is no longer stipulated by external inspection; it is causally determined by prior actions enacted at $`t`$ along branch $`h`$, enabling machine-checked proofs of Hülsmann's path-dependent capital availability ([`hulsmann_path_dependent_availability`](../Praxeology/Frame/Core.lean#L1839)) and capital starvation when complementary factors are depleted ([`infeasible_of_insufficient_endowment`](../Praxeology/Frame/Core.lean#L1830)).
  2. **Kirznerian Bounded Contemplation & Discovery:** Separating physical feasibility ($`\text{use\_means} \le \omega`$) from epistemic contemplation ($`A_{\text{cont}}`$) allows formalizing Kirznerian entrepreneurial alertness ([`KirznerAlertnessOperator`](../Praxeology/FirmBoundary.lean#L292), [`bounded_contemplation_purposeful_act`](../Praxeology/BehavioralPoset.lean#L146)) and distinguishing catallactic regret from discovery regret ([`discovery_regret_of_overlooked_opportunity`](../Praxeology/FirmBoundary.lean#L354)).

---

### 2.7 Full Realization of the Section 5 "Future Research" Programme (Modules 4–17)

Section 5 of *A Formalization of Austrian Economics* (Komendarczyk et al., [arXiv:2606.18292](https://arxiv.org/abs/2606.18292)) (pp. 49–50) outlines the major open problems for extending formal praxeology: bilateral exchange, property/coercion, money, Coasean firm boundaries, and the Economic Calculation Problem (`CALC`). `praxeology-lean` completes all of these extensions and adds ABCT macroeconomics, econometric non-identifiability, and poset behavioral economics:

1. **Catallactics, Comparative Advantage & Voluntary vs. Coercive Interaction ([`Catallactics.lean`](../Praxeology/Catallactics.lean)):**
   - Proves the double inequality of exchange ([`double_inequality_of_exchange`](../Praxeology/Catallactics.lean#L917)) and formalizes Megger's (2024) separation between voluntary catallactic exchange and coercive extortion ([`highwayman_is_purposeful_but_not_catallactic`](../Praxeology/Catallactics.lean#L138), [`rothbard_demonstrated_welfare_dichotomy`](../Praxeology/Catallactics.lean#L148)).
   - Proves the Mises-Ricardo Law of Association on [`RicardianEconomy`](../Praxeology/Catallactics.lean#L234) from integer labor budgets and relative opportunity-cost ratios without cardinal utility ([`ricardian_surplus_of_any_positive_autarky`](../Praxeology/Catallactics.lean#L580), [`ricardian_terms_of_trade_interval`](../Praxeology/Catallactics.lean#L717), [`ricardian_bilateral_exchange_of_pareto_gain`](../Praxeology/Catallactics.lean#L974)), while proving that equal opportunity costs ($`a_{i0} a_{j1} = a_{j0} a_{i1}`$) mathematically preclude surplus ([`no_ricardian_surplus_of_equal_opportunity_costs`](../Praxeology/Catallactics.lean#L517)).
2. **Bourbaki-Witt Network Money Emergence, Two-Tier Banking Architecture & Ordinal Gresham's Law ([`Catallactics.lean`](../Praxeology/Catallactics.lean), [`Catallactics/Credit.lean`](../Praxeology/Catallactics/Credit.lean)):**
   - Proves that because marketability argmax transitions $`\Phi`$ are inflationary ([`phi_inflationary`](../Praxeology/Catallactics.lean#L1339)) rather than globally monotone ([`phi_not_globally_monotone`](../Praxeology/Catallactics.lean#L1346)), Mengerian money emergence is governed by Bourbaki-Witt fixed-point convergence ([`bourbaki_witt_finite_fixed_point`](../Praxeology/Catallactics.lean#L1649), [`network_universal_money_emergence`](../Praxeology/Catallactics.lean#L1871)), certified on both symmetric and asymmetric multi-hop trading networks ([`three_agent_network_money_emergence_witness`](../Praxeology/Catallactics.lean#L2048), [`asymmetric_unique_network_money_emergence_witness`](../Praxeology/Catallactics.lean#L2149)).
   - Formalizes the disaggregated monetary state via the Endowment Matrix $\boldsymbol{\Omega}$ ([`EndowmentMatrix`](../Praxeology/Catallactics/Credit.lean#L993)) and proves that macro-sum aggregates underdetermine individual feasibility and purposefulness ([`macro_sum_underdetermines_spot_feasibility`](../Praxeology/Catallactics/Credit.lean#L998)).
   - Derives the three-sector base money partition ([`totalBaseMoney_eq_three_sector_partition`](../Praxeology/Catallactics/Credit.lean#L1061)), bank-tier coverage divergence ([`asymmetric_tier_coverage_divergence`](../Praxeology/Catallactics/Credit.lean#L1117)), and the automated sweep freeze dichotomy ([`automated_sweep_two_step_vs_freeze_dichotomy`](../Praxeology/Catallactics/Credit.lean#L1149)).
   - Derives Gresham's Law circulation collapse purely from ordinal Mengerian bundle preferences with zero cardinal multiplications ([`mengerian_greshams_tender_dominance`](../Praxeology/Catallactics.lean#L2381), [`ordinal_par_pricing_from_mengerian_bundle_pref`](../Praxeology/Catallactics.lean#L3418), [`greshams_law_circulation_collapse`](../Praxeology/Catallactics.lean#L3464)).
3. **The Economic Calculation Problem (`CALC`) ([`Catallactics.lean`](../Praxeology/Catallactics.lean)):**
   - Directly realizes Section 5's `CALC` impossibility by proving [`socialist_calculation_incommensurability`](../Praxeology/Catallactics.lean#L3544), [`semantic_incommensurability_barrier`](../Praxeology/Catallactics.lean#L3576), and [`ecp_epistemic_measurability_impossibility`](../Praxeology/Catallactics.lean#L3560): in the absence of catallactic market prices over `PhysicalAntichain` factor vectors, every measurable planner rule violates Mengerian economizing in at least one economy.
4. **Coasean-Misesian Firm Boundaries & Price-Box Cones ([`FirmBoundary.lean`](../Praxeology/FirmBoundary.lean)):**
   - Formalizes price-box indeterminacy cones ([`price_box_indeterminacy_cone_exists`](../Praxeology/FirmBoundary.lean#L152)), robust cost comparison ([`hayekian_epistemic_compression`](../Praxeology/FirmBoundary.lean#L85)), arithmetic integration trade-offs ([`firm_boundary_tradeoff`](../Praxeology/FirmBoundary.lean#L514), [`ordinal_firm_boundary_tradeoff`](../Praxeology/FirmBoundary.lean#L1891)), and positive-price cost and ordinal rank-sum results ([`positive_prices_and_ordinal_rank_sum_reversal`](../Praxeology/FirmBoundary.lean#L538)).
5. **Austrian Business Cycle Theory & Multi-Stage Supply Cascades ([`BusinessCycle.lean`](../Praxeology/BusinessCycle.lean), [`Clusters.lean`](../Praxeology/BusinessCycle/Clusters.lean), [`FiveStageSupplyChain.lean`](../Praxeology/FiniteEconomy/FiveStageSupplyChain.lean)):**
   - Proves the unified ABCT Master Theorem ([`abct_action_frame_master`](../Praxeology/BusinessCycle.lean#L440)), Böhm-Bawerk marginal-pair factor price squeezes ([`cantillon_marginal_pair_price_box_abct_squeeze`](../Praxeology/BusinessCycle.lean#L928)), midstream bailout impossibility ([`bailout_impossibility_dichotomy`](../Praxeology/BusinessCycle.lean#L636)), full execution of a multi-stage production structure to its terminal completion ([`fiveStageSupplyChain_reaches_terminal`](../Praxeology/FiniteEconomy/FiveStageSupplyChain.lean#L204)), and entrepreneurial malinvestment clustering under counterfactual interest shifts ([`contextual_regret_cluster`](../Praxeology/BusinessCycle/Clusters.lean#L1080)).
6. **Econometric Non-Identifiability & Behavioral Posets ([`EconometricLimits.lean`](../Praxeology/EconometricLimits.lean), [`BehavioralPoset.lean`](../Praxeology/BehavioralPoset.lean)):**
   - Machine-checks the methodological thesis of Section 1.3 (p. 6) that synthetic-a-priori praxeological propositions cannot be falsified by empirical regressions ([`causal_econometric_non_identifiability`](../Praxeology/EconometricLimits.lean#L102), [`lucas_critique_policy_invariance_failure`](../Praxeology/EconometricLimits.lean#L137), [`duhem_quine_underdetermination`](../Praxeology/EconometricLimits.lean#L208)).
   - Generalizes Remark 3.3 (preference variation vs. consistency) into poset-theoretic behavioral economics, proving DEL epistemic grounding of framing reversals ([`framing_reversal_implies_del_or_endowment_shift`](../Praxeology/BehavioralPoset.lean#L143)) and Ulysses pre-commitment menu pruning ([`precommitment_prunes_temptation`](../Praxeology/BehavioralPoset.lean#L92), [`hyperbolic_naive_agent_cross_branch_regret`](../Praxeology/BehavioralPoset.lean#L462)).

---

## 3. Comprehensive Architectural Comparison Matrix

| Analytical Dimension | *A Formalization of Austrian Economics* ($`T_{\text{prx}}`$, 2026) | `praxeology-lean` Proof System |
| :--- | :--- | :--- |
| **Foundational Architecture** | Single-file Lean 4 companion (`Praxeology.lean`) encoding 3-layer FOL axioms (T0–T6, P1–P6, C1, O0–O4, S1) + (MU0–MU4, LB1) | 17-module Lean 4 library parameterized by [`ActionFrame`](../Praxeology/Frame/Core.lean#L276) with zero global axioms |
| **Temporal Topology** | Linear discrete chain $`(\text{Times}, <)`$ with Trichotomy (T3) and Discreteness (T6); no finite models of full theory | Forward-branching Kripke tree with [`backward_linearity`](../Praxeology/Frame/Core.lean#L1371) and history bundles $`H(t)`$; admits compact finite models |
| **Agency & Counterfactuals** | Primitive relation $`\text{Acts}(a, \alpha, t)`$ on a single timeline; counterfactual roads not taken are unmodeled | Trajectory primitive [`enacted`](../Praxeology/Frame/Core.lean#L1451) deriving [`ChoicePartition`](../Praxeology/Frame/Core.lean#L1460), [`DynamicBox`](../Praxeology/Frame/Core.lean#L1504), and counterfactual refrainability |
| **Preference Assumptions** | Strict total order on $`\text{EndAt}(a, t)`$ via exposed Menu-Comparability (O2) and Transitivity (O3) | Strict asymmetry ([`pref_asymm`](../Praxeology/Action.lean#L201)) alone at base level; local comparability ([`MenuComparable`](../Praxeology/Marginal.lean#L1094)) isolated where needed |
| **Choice Optimality & Ties** | Unique strict maximum $`\hat{E}`$ of $`\text{EndAt}(a, t)`$ (Prop. 4.2); $`E \neq F`$ guard in Def. 2.11 | Undominated choice ([`PurposefulAct`](../Praxeology/Action.lean#L222)); resolves both same-end and distinct-end Buridan ties ([`buridan_tie_compatible_with_purposeful_act`](../Praxeology/Action.lean#L504)) |
| **Opportunity Cost** | Singleton maximum $`\text{Cost}(a, t) := \max_{\succ_a^t}(\text{EndAt}(a, t) \setminus \{\hat{E}\})`$ under (O2) | Dual set-valued poset frontiers [`ActionOCSet`](../Praxeology/Action.lean#L703) (continuous across ties) and [`StrictOCSet`](../Praxeology/Action.lean#L709) |
| **Inaction & Felt Unease** | Recorded verbally (Sec. 1.1); Always-Acting (O1) treats steady state as an ordinary action token | Distinguished inertial baseline $`\alpha_0`$ ([`alpha_zero`](../Praxeology/Frame/Core.lean#L1345)); active action proved equivalent to felt unease ([`active_purposeful_act_iff_ne_alpha_zero`](../Praxeology/Action.lean#L382)) |
| **Performative Grounding** | Apodictic certainty of Action Axiom discussed verbally (Sec. 1.1, p. 4) | Machine-checked dialectical self-falsification via [`DeliberativeEpistemicAssertion`](../Praxeology/Action.lean#L910) and refraining witness |
| **Marginal Utility & Quanta** | Separate `Allot(a, t, x, E)` predicate under (MU0)–(MU4); technological unit noted in Footnote 35 | Action-forced prefix $`S_{\text{opt}}(k)`$ ([`purposeful_act_forces_S_opt_from_physical_endowment`](../Praxeology/Marginal.lean#L332)) & [`TeleologicalQuantumRegime`](../Praxeology/Marginal.lean#L756) |
| **Feasibility & Transitions** | `Avail(a, α, t)` specified externally by inspection; `Use(α, x)` is static (Remark 2.14) | Endogenous feasibility [`A_feas`](../Praxeology/Frame/Core.lean#L1420) coupled with causal transition laws ([`law_in_re_transition`](../Praxeology/Frame/Core.lean#L414), [`IsNextMoment`](../Praxeology/Frame/Core.lean#L37)) |
| **Catallactics & Macro Scope** | Sketched as open problems in Section 5 ("Future research", pp. 49–50) | Fully proved: Law of Association, Bourbaki-Witt money, ordinal Gresham's Law, ECP, Coasean firm boundaries, ABCT, econometrics, and behavioral posets |
