# Comparative Architectural Analysis: `praxeology-lean` vs. Komendarczyk et al. ($T_{\text{prx}}$)

## Overview

In 2026, Rafał Komendarczyk, Walter E. Block, John Levendis, and Frank J. Tipler published ***A Formalization of Austrian Economics — Praxeological Foundations: The Base System and Its Derived Theorems*** ([arXiv:2606.18292](https://arxiv.org/abs/2606.18292)), accompanied by a Lean 4 companion repository (`rafkom72/praxeology-lean`). Their work formalizes the core verbal deductions of Ludwig von Mises and Murray Rothbard as an axiomatic first-order theory ($T_{\text{prx}}$).

Both projects share the goal of formalizing Austrian economics in Lean 4. However, they pursue distinct architectures and design goals:

* **Komendarczyk et al.** ($T_{\text{prx}}$): A formalization of an academic paper's axiomatic signature in Lean 4 core, focusing on the foundational logic of single-actor (Crusoe) purposeful action and verifying its consistency with concrete static models.
* **`praxeology-lean`:** A dynamic, physics-and-choice-coupled framework built on [`ActionFrame`](../Praxeology/Frame/Core.lean#L276). It generalizes single-actor choice to handle branching time, preference ties, and physical causality, and scales constructively into multi-agent catallactics, monetary calculation, and macroeconomic cycles.

This note focuses on the **fundamental conceptual and structural differences** between the two approaches.

---

## 1. Summary of Fundamental Differences

| Dimension | Komendarczyk et al. ($T_{\text{prx}}$) | `praxeology-lean` (`ActionFrame`) | Why It Matters |
| :--- | :--- | :--- | :--- |
| **Temporal Structure** | Single linear chain (like $\mathbb{N}$ ) | Forward-branching Kripke tree | Human action is counterfactual: choosing one action leaves alternate branches unchosen. Branching time also enables modeling uncertainty, error, and regret. |
| **Preference & Choice** | Strict total order (Menu-Comparability) | Strict partial order (minimal asymmetric poset) | Does not assume agents can rank every unchosen alternative; resolves Buridan ties naturally via undominated choice without indifference curves. |
| **Opportunity Cost** | Scalar maximum after erasing the chosen end | Dual set-valued frontiers ([`ActionOCSet`](../Praxeology/Action.lean#L742) & [`StrictOCSet`](../Praxeology/Action.lean#L748)) | Prevents unnatural discontinuities when multiple foregone actions achieve the same top end. |
| **Inaction & Felt Unease** | Always-acting (inaction is not distinguished) | Distinguished baseline inaction ( $\alpha_0$ ) | Directly formalizes Mises's "felt unease": active action must strictly improve over doing nothing: $\text{End}(\alpha^{\ast}) \succ \text{End}(\alpha_0)$. |
| **Feasibility & Transitions** | Externally stipulated availability (`Avail`) | Endogenous physical conservation and causal transitions | Physical means are tracked across time; actions consume and produce goods, determining what is feasible at future moments. |
| **Marginal Utility (DMU)** | Postulated allotment schedule parallel to action | Discrete economizing on homogeneous means units | Derives DMU directly from purposeful allocation; accounts for Rothbard's discrete technological quantum (complementarity / 30-log cabin). |
| **Economic Scope** | Single-actor Crusoe base system | Multi-agent catallactics, money, restricted-record calculation, & macroeconomics | Proves conditional exchange and monetary results; the ECP result assumes identical records with conflicting preferences and does not establish a general planning impossibility. |
| **Dependencies** | Lean 4 core only (single file, no Mathlib) | Lean 4 + Mathlib | Mathlib provides standard finite sets and order theory; both systems rely on standard kernel verification. |

---

## 2. Fundamental Architectural Differences Explained

### 2.1 Linear Time vs. Forward-Branching Time

* **Komendarczyk et al.:** Time is formalized as a single discrete line. Every moment has an immediate successor, forming a single unbroken timeline. Counterfactual alternatives—what *would* have happened if another action had been chosen—are not part of the timeline.
* **`praxeology-lean`:** Time is modeled as a **forward-branching tree**. The past is linear (what has occurred is fixed), but the future branches into multiple possible histories.
* **The Core Insight:** Purposeful action is inherently counterfactual. When an actor chooses action $A$ over action $B$, action $B$ must have been genuinely feasible along an alternate branch. The library formally proves that purposeful action mathematically requires a branching universe. Furthermore, branching time makes it possible to formalize Mises's distinction between ex-ante intention and ex-post error (entrepreneurial regret when an uncertain branch turns out poorly).

### 2.2 Total Orders vs. Partial Orders and Buridan Ties

* **Komendarczyk et al.:** Imposes Menu-Comparability, meaning an agent must possess a complete, strict ranking over all available ends. Every pair of ends must be comparable, forcing a single unique winner.
* **`praxeology-lean`:** Requires only **strict asymmetry** (if $A \succ B$, then $\neg(B \succ A)$ holds). Preferences form a partial order. Purposeful choice is defined as **undominated choice**: an actor selects an action whose intended end is not strictly dominated by any feasible alternative.
* **The Core Insight:** Real actors often face alternatives they have never needed to rank against each other (incomparable goods or factor bundles). More importantly, this resolves **Buridan ties** (e.g., choosing between two identical bales of hay, or two equally attractive distinct options):
  * Under strict total orders, ties cause paralysis or require neoclassical indifference curves.
  * Under undominated choice, selecting either option is purposeful because neither dominates the other, and both strictly beat inaction (starvation). Action demonstrates preference over inaction, not indifference.

### 2.3 Opportunity Cost: Singleton Erasure vs. Set-Valued Frontiers

* **Komendarczyk et al.:** Opportunity cost is defined as the single best end among the unchosen options, computed by erasing the chosen end from the menu and finding the maximum of the remainder.
* **`praxeology-lean`:** Distinguishes between foregone *actions* (means lost) and foregone *ends*, formalizing both as set-valued undominated frontiers:
  1. [`ActionOCSet`](../Praxeology/Action.lean#L742): The undominated ends among all unchosen actions.
  2. [`StrictOCSet`](../Praxeology/Action.lean#L748): The undominated ends among foregone ends strictly distinct from the chosen end.
* **The Core Insight:** If two distinct actions yield the same top end (e.g., hunting in Sector A vs. Sector B both yield 10 deer), erasing that end completely deletes Sector B from the cost set, creating an unnatural mathematical discontinuity. `ActionOCSet` retains the shared end, ensuring continuity across tie boundaries while still matching the traditional definition whenever ends are distinct.

### 2.4 Inaction, "Felt Uneasiness", and Refraining

* **Komendarczyk et al.:** Uses an "Always-Acting" axiom. The actor is always performing some action, but the formal language does not distinguish between actively intervening in the world and passively doing nothing.
* **`praxeology-lean`:** Designates an explicit **inertial baseline action** ($\alpha_0$) representing inaction or passive refraining, which is always feasible. Active action is defined as strictly improving upon doing nothing: $\text{ActiveAction}(\alpha^{\ast}) \iff \text{Purposeful}(\alpha^{\ast}) \land \text{End}(\alpha^{\ast}) \succ \text{End}(\alpha_0)$.
* **The Core Insight:** This directly formalizes Ludwig von Mises's foundational axiom: *action is the purposeful striving to relieve felt uneasiness*. If an actor does not expect an active choice to yield a state better than inaction, they simply do not act. This structure is essential for modeling:
  * **Shutdown boundaries:** An entrepreneur stops production when intervention or taxes make inactivity preferable to active trade.
  * **Performative self-falsification:** Proving that asserting that human action does not exist requires purposeful refraining and reason-responsiveness, refuting the denial of action.

### 2.5 Endogenous Physical Transitions vs. External Menus

* **Komendarczyk et al.:** The availability of actions (`Avail`) is an uninterpreted primitive specified from the outside by the modeler by inspection. Physical means and things are static.
* **`praxeology-lean`:** Menus are **endogenous**. The system tracks physical endowments and inventories across time. Actions consume specific input means and yield output goods according to physical conservation laws: $\text{Inventory}(t') = \text{Inventory}(t) - \text{UsedMeans}(\alpha) + \text{YieldMeans}(\alpha)$.
* **The Core Insight:** What an agent can do tomorrow is causally determined by what they produced or consumed today. This enables machine-checked proofs of capital accumulation, roundabout production, and complementary factor starvation (a project halts when a required input runs out).

### 2.6 Marginal Utility: Homogeneous Units and Complementarity

* **Komendarczyk et al.:** Formalizes Diminishing Marginal Utility (DMU) via a separate allotment relation parallel to action, governed by auxiliary axioms including a top-segment coherence rule.
* **`praxeology-lean`:** Derives DMU constructively from the allocation of discrete homogeneous units of means across ranked ends. An economizing actor purposefully allocates earlier units to more urgent ends, proving that each additional unit necessarily satisfies a lower-ranked end.
* **The Core Insight:** It also formalizes Murray Rothbard's **technological unit** (complementarity):
  * For goods that require a minimum physical quantum (e.g., an odd shoe, or Rothbard's 30-log cabin example), sub-quantum physical remainders are economically sterile. DMU holds across complete productive units, but correctly does not apply to non-functional fragments.

### 2.7 Economic Scope: Single-Agent Choice vs. Multi-Agent Catallactics

* **Komendarczyk et al.:** Explicitly designed as a foundational base system for a single Crusoe actor. Multi-agent exchange, property rights, money, and macroeconomic coordination are identified as open areas for future research.
* **`praxeology-lean`:** Completes the deduction from single-actor choice into full multi-agent catallactics and macroeconomics:
  * **Bilateral Exchange & Association:** Proves the double inequality of exchange, distinguishes voluntary trade from extortion, and proves the Ricardian Law of Association without cardinal utility.
  * **Money Emergence & Gresham's Law:** Models Mengerian indirect exchange converging to a medium of exchange via Bourbaki-Witt fixed points on trading networks, and derives Gresham's Law.
  * **Economic Calculation Problem (ECP):** Proves a rank-sum counterexample and a conditional two-record information result. It does not derive missing information from the absence of factor markets.
  * **Austrian Business Cycle Theory (ABCT):** Formalizes multi-stage production structures, credit expansion, and factor starvation during the credit cycle.
  * **Econometric Limits:** Proves that empirical regression data cannot identify unchosen counterfactuals (the Lucas critique and Duhem-Quine underdetermination).

---

## 3. Engineering and Proof Foundations

* **Dependency Strategy:**
  * Komendarczyk et al. chose a self-contained, single-file implementation using **Lean 4 core only**. This provides a lightweight, dependency-free verification of their paper.
  * `praxeology-lean` utilizes **Lean 4 plus Mathlib** to take advantage of established libraries for finite sets, order theory, and algebraic structures, which are essential for scaling up to multi-agent networks and multi-stage capital structures.
* **Kernel Soundness:**
  * Both formalizations rely on the exact same foundational logic: Lean 4 dependent type theory with standard axioms (`Classical.choice`, `propext`, `Quot.sound`). Neither library introduces custom unverified axioms or unfinished proofs.

---

## References

- Komendarczyk, R., Block, W. E., Levendis, J., & Tipler, F. J. (2026). *A Formalization of Austrian Economics — Praxeological Foundations: The Base System and Its Derived Theorems*. [arXiv:2606.18292 [econ.TH]](https://arxiv.org/abs/2606.18292).
- Komendarczyk et al. companion repository: [`rafkom72/praxeology-lean`](https://github.com/rafkom72/praxeology-lean).
- `praxeology-lean` project overview and architecture: [README.md](../README.md).
- Companion treatises and natural language derivations: [`natural_language/`](../natural_language/).
