# Specification 01: Multi-Sorted Ontology, Branching Frames, and Constructive Agency

Formal mathematical specification for [`Praxeology/Frame.lean`](../Praxeology/Frame.lean).

---

## 1. Multi-Sorted Ontological Signature ($`\Sigma_{\text{prx}}`$)

The foundational language $`\mathcal{L}_{\text{prx}}`$ operates over six sorts and a distinguished passive action, encapsulated in the zero-axiom typeclass [`ActionFrame`](../Praxeology/Core.lean#L276):

* **`Agent` ($`I`$):** Finite, non-empty sort of discrete acting entities ([`instFintypeAgent`](../Praxeology/Frame.lean#L53), [`instNonemptyAgent`](../Praxeology/Frame.lean#L52)).
* **`Moment` ($`T`$):** Discrete temporal points equipped with strict precedence ($`\prec`$ / `<`) and backward linearity.
* **`History` ($`H`$):** Maximal chains in $`(T, \prec)`$. The history bundle passing through moment $`t`$ is defined by:
```math
  H(t) := \{ h : \text{History} \mid t \in h \}
```
  Incidence is formalized by the predicate `mem_hist : Moment → History → Prop` ([`mem_hist`](../Praxeology/Core.lean#L1556)). Every moment belongs to at least one history branch ([`moment_in_history`](../Praxeology/Core.lean#L1388)).
* **`Action` ($`A`$):** Discrete sort of elementary intentional choices, containing a distinguished passive/inertial baseline $`\alpha_0`$ ([`alpha_zero`](../Praxeology/Core.lean#L1345), refraining from intervention).
* **`Means` ($`M`$):** Discrete physical goods/resources measured in discrete non-negative integer units ($`\mathbb{N}`$).
* **`Ends` ($`E`$):** Discrete teleological goals/states of affairs.

### Relational and Teleological Signatures

* **Endowment:** $`\omega : I \times T \times H \times M \to \mathbb{N}`$ ([`endowment`](../Praxeology/Core.lean#L1408)), specifying physical quantities held by agent $`i`$ at node $`\langle t, h \rangle`$.
* **End requirement and subjective valuation:** $`\rho : E \times M \to \mathbb{N}`$ (`requirement`) gives the means needed to realize end $`e`$. `ValuedEnd : Agent → Moment → History → Ends → Prop` selects the ends relevant to an actor at a decision node; subjective bundle dominance ranges over finite sets of these valued ends and uses the same requirement function.
* **Service accounting:** Service kinds and action-level yields are supplied outside `ActionFrame` by `ServiceAccounting`. `InventoryRun.totalService` sums those yields along an execution trace, so realized service flows do not add a primitive sort or ledger state to the frame.
* **Teleological Mapping:** $`\text{End} : I \times A \times T \times H \to E`$ ([`End_of`](../Praxeology/Action.lean#L193)), mapping each action to its intended teleological end.
* **Ordinal Preference:** $`(\succ_{i,t,h}) \subseteq E \times E`$ ([`Preference`](../Praxeology/Action.lean#L197)), subject solely to the structural law of strict asymmetry ([`pref_asymm`](../Praxeology/Action.lean#L201)):
```math
  \forall e_1, e_2 \in E, \quad e_1 \succ_{i,t,h} e_2 \implies \neg (e_2 \succ_{i,t,h} e_1)
```

---

## 2. Kripke-Tree Temporal Frame (Branching Time)

Temporal precedence $`\prec`$ on $`T`$ satisfies:

1. **Irreflexivity:** $`\forall t \in T, \neg(t \prec t)`$ ([`moment_lt_irrefl`](../Praxeology/Core.lean#L1359)).
2. **Transitivity:** $`\forall t_1, t_2, t_3 \in T, (t_1 \prec t_2 \wedge t_2 \prec t_3) \implies t_1 \prec t_3`$ ([`moment_lt_trans`](../Praxeology/Core.lean#L1363)).
3. **Derived Asymmetry:** $`\forall t_1, t_2 \in T, (t_1 \prec t_2 \wedge t_2 \prec t_1) \implies \bot`$ ([`moment_lt_asymm`](../Praxeology/Core.lean#L1367)).
4. **Backward Linearity (Historical Determinism / Fixed Past):**
```math
   \forall t_1, t_2, t_3 \in T, \quad (t_1 \prec t_3 \wedge t_2 \prec t_3) \implies (t_1 \prec t_2 \vee t_1 = t_2 \vee t_2 \prec t_1)
```
   ([`backward_linearity`](../Praxeology/Core.lean#L1371)).

---

## 3. Constructive Agency via Trajectory Primitive `enacted`

Rather than stipulating STIT choice partitions by global fiat, our codebase roots agency in a constructive trajectory function:

```lean
enacted : Agent → Moment → History → Action
```
([`enacted`](../Praxeology/Credit.lean#L340)).

### Menu Invariance and Counterfactual Refrainability

* **Feasible Menu:** $`\mathcal{A}_i(t, h) \subseteq A`$ is a finite set ([`A_feas`](../Praxeology/Core.lean#L1420)).
* **STIT No-Foreknowledge:** The feasible menu at moment $`t`$ is history-bundle invariant:
```math
  \forall h_1, h_2 \in H(t), \quad \mathcal{A}_i(t, h_1) = \mathcal{A}_i(t, h_2)
```
  ([`A_feas_bundle_invariant`](../Praxeology/Core.lean#L1424)).
* **Passive Baseline Feasibility:** $`\alpha_0 \in \mathcal{A}_i(t, h)`$ for all $`i, t, h`$ ([`alpha_zero_feasible`](../Praxeology/Core.lean#L1436)).
* **Enacted Feasibility:** $`t \in h \implies \text{enacted}(i, t, h) \in \mathcal{A}_i(t, h)`$ ([`enacted_in_A_feas`](../Praxeology/Core.lean#L1455)).
* **Counterfactual Realizability:** For every feasible action $`\alpha \in \mathcal{A}_i(t, h)`$, there exists a history branch $`h' \in H(t)`$ along which $`\text{enacted}(i, t, h') = \alpha`$ ([`choice_partition_nonempty`](../Praxeology/Core.lean#L1482)).

---

## 4. Zero-Axiom Derivation of STIT and PDL Operators

From the trajectory primitive [`enacted`](../Praxeology/Credit.lean#L340), the entire STIT and modal structure is derived as kernel-checked theorems:

### 1. Choice Partition Cell
```lean
def ChoicePartition (i : Agent) (t : Moment) (α : Action) : Set History :=
  { h : History | t ∈ h ∧ enacted i t h = α }
```
([`ChoicePartition`](../Praxeology/Core.lean#L1460)).

* **Covering Theorem:** Every history in $`H(t)`$ belongs to some choice cell:
```math
  \forall h \in H(t), \exists \alpha \in \mathcal{A}_i(t, h), h \in \text{ChoicePartition}(i, t, \alpha)
```
  ([`choice_partition_cover`](../Praxeology/Core.lean#L1469)).
* **Disjointness Theorem:** For $`\alpha \neq \beta`$, $`\text{ChoicePartition}(i, t, \alpha) \cap \text{ChoicePartition}(i, t, \beta) = \emptyset`$ ([`choice_partition_disjoint`](../Praxeology/Core.lean#L1474)).

### 2. Execution Predicate
```lean
def Exec (i : Agent) (t : Moment) (α : Action) : History → Prop :=
  fun h => h ∈ ChoicePartition i t α
```
([`Exec`](../Praxeology/Core.lean#L1500)).

### 3. Dynamic Box Modality ($`[\alpha]\psi`$)
To prevent the counterfactual vacuity of material implication on unchosen branches, $`[\alpha]\psi`$ quantifies strictly over the choice partition cell of $`\alpha`$:
```lean
def DynamicBox (i : Agent) (t : Moment) (α : Action) (ψ : History → Prop) : Prop :=
  ∀ h' : History, h' ∈ ChoicePartition i t α → ψ h'
```
([`DynamicBox`](../Praxeology/Core.lean#L1504)). This provides genuine counterfactual truth conditions even if the actual world executes $`\beta \neq \alpha`$.

### 4. Deliberative STIT ($`[\text{:}i\text{ dstit:}]\psi`$)
```lean
def STITChoiceCell (i : Agent) (t : Moment) (h : History) : Set History :=
  { h' : History | ∃ α ∈ A_feas i t h, h ∈ ChoicePartition i t α ∧ h' ∈ ChoicePartition i t α }

def dstit (i : Agent) (t : Moment) (ψ : History → Prop) (h : History) : Prop :=
  (∀ h' ∈ STITChoiceCell i t h, ψ h') ∧
  (∃ h'' : History, t ∈ h'' ∧ ¬ ψ h'')
```
([`STITChoiceCell`](../Praxeology/Core.lean#L1508), [`dstit`](../Praxeology/Core.lean#L1512)).

---

## 5. Physical Laws in Re, Bilateral Trade Guards, and Grove Spheres

* **Physical Transition Guard (`¬ IsTradeAction α`):** In `ActionFrame`, physical transformation conservation (`law_in_re_transition`) is guarded by `¬ IsTradeAction α`. Production and consumption actions obey physical conversion ( $`\omega(t') + \text{use} = \omega(t) + \text{yield}`$ ), while matched bilateral market exchanges (`Offer` and `Accept`) are governed by coupled transfer laws ([`bilateral_transfer_law`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Core.lean#L434)).
* **Unilateral Trade Invariance:** Unilateral offers or accepts without a matching counterpart execute nothing ( $`\omega(t') = \omega(t)`$ ) ([`unilateral_offer_noop`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Core.lean#L420), [`unilateral_accept_noop`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Core.lean#L427)).
* **Grove-Sphere Priority Revision:** Epistemic updates under surprising shocks are governed by concentric plausibility spheres rather than flat set intersections, eliminating doxastic collapse into vacuity ([`PriorityDELUpdate`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Core.lean#L1160), [`priority_del_update_nonempty`](file:///home/aleryberry/Projects/praxeology_lean/Praxeology/Core.lean#L1169)).

---

## 6. Model-Theoretic Consistency Witness (`FiniteBranchingModel`)

The non-vacuity and mathematical consistency of the entire praxeological ontology is certified by a concrete finite model witness:

* [`FiniteBranchingModel`](../Praxeology/Witnesses.lean#L277): A computable, 2-agent, 4-moment branching tree structure with a shared root and a separate successor for each of `idle`, `consume`, and `defer`.
* [`action_frame_consistent`](../Praxeology/Witnesses.lean#L529) (Theorem 0.2): Proves `Nonempty ActionFrame` without introducing a single axiom or unproven hypothesis into Lean's kernel.

The abstract `History` sort represents maximal moment chains faithfully: `histories_extensional` identifies histories with identical moment incidence. `no_choice_between_undivided` requires an agent to enact the same action on histories that share a later moment. These independent conditions make distinct choice cells represent genuine divergence at the decision moment. The bilateral witness has four distinct successor moments for its four joint action profiles, including profiles with identical physical endowments.

