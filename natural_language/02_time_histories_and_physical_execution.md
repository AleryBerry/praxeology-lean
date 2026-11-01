# Chapter 2: Time, Histories, and Physical Execution

Chapter 1 told us what agents have and what actions require. We now add temporal order and histories, so we can distinguish what is already settled from what remains open. Once histories are in place, we can also define which action is enacted and how inventories change from one moment to the next.

## Time, Histories, and the Open Future

We need a temporal structure before we can describe an action's later effects. Let moments be related by a precedence relation: $t_1 \prec t_2$ means that $t_1$ occurs before $t_2$. We first require that no moment precedes itself and that precedence is transitive. These two conditions rule out cycles. They still allow some pairs of moments to be incomparable, which is necessary if the future is to branch.

Irreflexivity and transitivity give us a strict order, but they do not determine whether branches may later rejoin. We choose a tree-shaped time structure: whenever two moments precede the same later moment, they must be comparable. This additional condition makes each moment's past a single ordered chain. It rules out a later moment with two incomparable pasts, so every history leading to that moment describes the same ordered past. We call the condition **backward linearity**. We impose it as part of the model because the histories in this account represent alternative continuations of one past; it is not a consequence of the strict-order laws, nor a claim that every possible temporal model must have this shape.

For example, suppose $r\prec a$ and $r\prec b$, while neither $a\prec b$ nor $b\prec a$. We may treat $a$ and $b$ as separate continuations of $r$. Backward linearity rules out a moment $c$ with both $a\prec c$ and $b\prec c$: such a $c$ would have two incomparable predecessors. We use this example to distinguish branching, which the model allows, from later rejoining, which its chosen temporal structure excludes.

### Definition 2.1 (Strict Temporal Precedence)
Let $\prec$ be a binary relation on moments $\mathcal{T}$. The relational structure $\langle \mathcal{T}, \prec \rangle$ is a **strict temporal precedence frame** if it satisfies the following three structural laws:
1. **Irreflexivity**: No moment precedes itself:

$$
\forall t\in\mathcal{T},\quad \neg(t \prec t)
$$

2. **Transitivity**: If one moment precedes a second and the second precedes a third, the first precedes the third:

$$
\forall t_1,t_2,t_3\in\mathcal{T},\quad
(t_1 \prec t_2 \wedge t_2 \prec t_3) \implies t_1 \prec t_3
$$

3. **Backward Linearity**: Any two moments preceding a common later moment are comparable:

$$
\forall t_1,t_2,t_3\in\mathcal{T},\quad
(t_1 \prec t_3 \wedge t_2 \prec t_3) \implies (t_1 \prec t_2 \vee t_1 = t_2 \vee t_2 \prec t_1)
$$

Backward linearity makes each moment's past linearly ordered. It does not make the future unique. To represent alternative futures, we allow incomparable later moments and collect moments into histories.

### Proposition 2.2 (Precedence Cannot Run Both Ways)
Let the moments $\mathcal{T}$ carry the strict temporal precedence relation from Definition 2.1. Then precedence is asymmetric:

$$
\forall t_1, t_2 \in \mathcal{T}, \quad t_1 \prec t_2 \implies \neg(t_2 \prec t_1).
$$

**Proof.** Suppose $t_1 \prec t_2$ and $t_2 \prec t_1$. By transitivity, $t_1 \prec t_1$, which directly contradicts strict irreflexivity. Thus $\neg(t_2 \prec t_1)$. $\blacksquare$

We define a history as a maximal linearly ordered course through time. “Maximal” means that we cannot add another moment while keeping every pair on the course comparable. We also require each represented moment to belong to some history, and we identify histories by the moments they contain.

### Definition 2.3 (Histories as Maximal Chains)
Let $\langle \mathcal{T}, \prec \rangle$ be a strict temporal precedence frame, and let $\in$ be an incidence relation between moments $\mathcal{T}$ and histories $\mathcal{H}$, written $t \in h$.
1. A subset of moments $s \subseteq \mathcal{T}$ is a **linear chain** if all elements of $s$ are pairwise comparable under $\prec$:

$$
\text{linearChain}(s) \iff \forall t_1, t_2 \in s, \quad (t_1 \prec t_2 \vee t_1 = t_2 \vee t_2 \prec t_1)
$$

2. A linear chain $s \subseteq \mathcal{T}$ is a **maximal linear chain** if it admits no proper linear extension:

$$
\text{maximalChain}(s) \iff \text{linearChain}(s) \wedge \forall s' \subseteq \mathcal{T}, (\text{linearChain}(s') \wedge s \subseteq s' \implies s = s')
$$

3. The historical incidence structure satisfies:
   - **Moment Coverage**: Every moment belongs to at least one history: $\forall t \in \mathcal{T}, \quad \exists h \in \mathcal{H}, \quad t \in h$

   - **Maximality of Histories**: For every history $h \in \mathcal{H}$, the set of moments incident to $h$, denoted $`\mathcal{T}(h) \equiv \{ t \in \mathcal{T} \mid t \in h \}`$, is a maximal linear chain: $\forall h \in \mathcal{H}, \quad \text{maximalChain}(\mathcal{T}(h))$

   - **History Extensionality**: The abstract history sort contains one token for each represented maximal chain: $\bigl(\forall t\in\mathcal{T},\ t\in h_1\leftrightarrow t\in h_2\bigr)\implies h_1=h_2.$

   - **Distinct histories separate**: If two distinct histories contain the same moment $t$, there are later moments on the two histories that are incomparable: $\forall h_1,h_2\in\mathcal{H},\ \forall t\in\mathcal{T},\quad (h_1\ne h_2\ \wedge\ t\in h_1\ \wedge\ t\in h_2) \quad\Longrightarrow\quad \exists u,v,\quad u\in h_1\ \wedge\ v\in h_2\ \wedge\ t\prec u\ \wedge\ t\prec v \ \wedge\ u\ne v\ \wedge\ \neg(u\prec v)\ \wedge\ \neg(v\prec u).$

We impose this condition so that distinct histories through a shared present represent genuinely different continuations.

We include extensionality because maximality specifies what each history contains but does not prevent two labels from representing the very same set of moments. Extensionality makes a history identifiable by its moments. Moment coverage and separation serve different purposes: coverage ensures that no moment is left out, while separation ensures that distinct histories through a moment do branch later.

### Definition 2.4 (History Bundles)
For each moment $t$, we gather the histories containing it into the set $H(t)$:

$$
H(t) \equiv \{ h \in \mathcal{H} \mid t \in h \}
$$

Moment coverage ensures that this set is never empty. We will use it to state what must agree while the future remains unresolved.

If two histories both contain $t$ and also contain a common later moment $u$, then they have not separated between $t$ and $u$. We require the action enacted at $t$ to be the same on those two histories. This expresses that an agent cannot choose between continuations that still share a later course. It is separate from history extensionality: the latter identifies histories with the same moments, while this condition constrains choices on histories with a common future.

In symbols, for each agent $i$ we impose

$$
\forall i\in\mathcal{I},\ \forall t,u\in\mathcal{T},\ \forall h_1,h_2\in\mathcal{H},\quad
(t\in h_1\ \wedge\ t\in h_2\ \wedge\ t\prec u\ \wedge\ u\in h_1\ \wedge\ u\in h_2)
\quad\Longrightarrow\quad
\text{enacted}(i,t,h_1)=\text{enacted}(i,t,h_2).
$$

### Physical Invariance at a Decision Moment

We can now express the information available at a shared decision point. If two histories both contain $t$, the stock and contemplated menu at $t$ are the same on each:

$$
\begin{aligned}
&\forall i\in\mathcal{I},\ \forall t\in\mathcal{T},\ \forall m\in\mathcal{M},\ \forall h_1,h_2\in\mathcal{H},\\
&\qquad t\in h_1\wedge t\in h_2\ \Longrightarrow\ \omega(i,t,h_1,m)=\omega(i,t,h_2,m),\\
&\forall i\in\mathcal{I},\ \forall t\in\mathcal{T},\ \forall h_1,h_2\in\mathcal{H},\\
&\qquad t\in h_1\wedge t\in h_2\ \Longrightarrow\ \mathcal{A}_{\text{cont}}(i,t,h_1)=\mathcal{A}_{\text{cont}}(i,t,h_2).
\end{aligned}
$$

This lets us reason about a choice using facts at the decision moment rather than facts that depend on which later branch occurs. These equalities are modeling conditions: they encode that later branch resolution does not retroactively change the stock or menu available at the shared decision moment.

### Definition 2.5 (Immediate Temporal Successors)
For inventory accounting, we need to identify consecutive moments along one history. We say $t'$ immediately follows $t$ along $h$ when both lie on $h$, $t$ precedes $t'$, and no moment of $h$ lies strictly between them:

$$
\text{succ}(t, t', h) \iff (t \in h \wedge t' \in h \wedge t \prec t' \wedge \forall \tau \in h, \neg(t \prec \tau \wedge \tau \prec t'))
$$

---

## Enacted Choice and Choice Cells

Having described the available branches, we can record the agent's actual action on each branch. This record groups histories according to the action chosen at a moment. We will use these groups later to compare the realized course with feasible alternatives; we separately assume that each feasible action can be represented on some history.

### Definition 2.6 (Intended Ends of Actions)
We assign an intended end to each agent-action pair at a decision situation:

$$
\text{outcome} : \mathcal{I} \times \mathcal{A} \times \mathcal{T} \times \mathcal{H} \to \mathcal{E}
$$

The value of this function is the end an agent associates with an action, not necessarily the later physical outcome. We impose that, at a fixed moment, the intended end is the same on every history through the moment:

$$
t \in h_1 \wedge t \in h_2 \implies \text{outcome}(i, \alpha, t, h_1)=\text{outcome}(i, \alpha, t, h_2)
$$

The end assigned to an action at $t$ does not change merely because we consider another history through $t$. Its later physical consequences may differ across histories; Chapter 5 will distinguish those realized outcomes from the end the action aims at.

### Definition 2.7 (Enacted Actions)
We record the action agent $i$ enacts at each moment-history pair by the function

$$
\text{enacted} : \mathcal{I} \times \mathcal{T} \times \mathcal{H} \to \mathcal{A}
$$

where $\text{enacted}(i, t, h)$ denotes the action enacted by agent $i$ at decision node $\langle t, h \rangle$.

An action recorded as enacted must be feasible whenever the moment lies on that history:

$$
\forall i \in \mathcal{I}, \forall t \in \mathcal{T}, \forall h \in \mathcal{H}, \quad t \in h \implies \text{enacted}(i, t, h) \in \mathcal{A}_{\text{feas}}(i, t, h)
$$

### Definition 2.8 (Choice Cells)
For each agent $i \in \mathcal{I}$, moment $t \in \mathcal{T}$, and action $\alpha \in \mathcal{A}$, the **choice partition cell** $\pi_i(t, \alpha)$ is the set of histories passing through $t$ along which agent $i$ enacts action $\alpha$:

$$
\pi_i(t, \alpha) \equiv \{ h \in \mathcal{H} \mid t \in h \wedge \text{enacted}(i, t, h) = \alpha \}
$$

### Theorem 2.9 (Choice Cells Cover and Separate Histories through a Moment)
Let $\pi_i(t, \alpha)$ be the choice cells derived from the enacted actions. Then:
1. **Bundle Inclusion**: Every history in $\pi_i(t, \alpha)$ passes through $t$: $\pi_i(t, \alpha) \subseteq H(t)$.
2. **Covering**: The choice cells cover the entire history bundle $H(t)$:

$$
\forall h \in H(t), \quad \exists \alpha \in \mathcal{A}_{\text{feas}}(i, t, h), \quad h \in \pi_i(t, \alpha)
$$

3. **Pairwise Disjointness**: *Distinct actions generate mutually disjoint choice cells:*

$$
\forall \alpha, \beta \in \mathcal{A}, \quad \alpha \neq \beta \implies \pi_i(t, \alpha) \cap \pi_i(t, \beta) = \emptyset
$$

**Proof.**
1. Immediate from the definition of $\pi_i(t, \alpha)$, where $h \in \pi_i(t, \alpha)$ implies $t \in h$.
2. Let $h \in H(t)$. By the feasibility condition on enacted actions, $\alpha = \text{enacted}(i, t, h)$ belongs to $`\mathcal{A}_{\text{feas}}(i, t, h)`$. By construction, $h \in \pi_i(t, \alpha)$.
3. If a history belonged to both cells, the enacted action on it would equal both $\alpha$ and $\beta$. Hence $\alpha=\beta$, contrary to the assumption that they are distinct. $\blacksquare$

The theorem follows from how we define enacted actions and their cells. It does not say that every action passing the resource test occurs on some history. The model adds that requirement separately, so that feasible alternatives can be compared through represented branches.

### Assumption 2.10 (Feasible Actions Have Corresponding Branches)
For every history $h$ containing $t$ and every action $\alpha$ feasible for agent $i$ there, the model supplies a selected history
$\sigma(i,t,\alpha,h)$ through $t$ on which $i$ enacts $\alpha$:

$$
t\in h\ \wedge\ \alpha\in\mathcal{A}_{\text{feas}}(i,t,h)
\quad\Longrightarrow\quad
t\in\sigma(i,t,\alpha,h)\ \wedge\
\text{enacted}(i,t,\sigma(i,t,\alpha,h))=\alpha.
$$

The selector obeys two further conditions. If $h$ already enacts $\alpha$ for $i$ at $t$, then $\sigma(i,t,\alpha,h)=h$. If $j\ne i$, then the selected history preserves $j$'s action at $t$:

$$
\text{enacted}(j,t,\sigma(i,t,\alpha,h))
=\text{enacted}(j,t,h).
$$

These are structural assumptions, not consequences of the resource test for feasibility. Branch realization lets us compare feasible actions; preservation lets us vary one agent's action while holding the other agents' present choices fixed.

### Definition 2.11 (Physical Execution and Guarantees)
1. **Physical Execution Predicate**: Agent $i$ physically executes action $\alpha$ along history $h$ at moment $t$:

$$
\mathsf{Exec}(i, t, \alpha)(h) \iff h \in \pi_i(t, \alpha) \iff (t \in h \wedge \text{enacted}(i, t, h) = \alpha)
$$

2. Action Guarantee ( $`[\alpha]_i^t \psi`$ ): Proposition $\psi$ holds on every history in the choice cell for $\alpha$:

$$
[\alpha]_i^t \psi \iff \forall h' \in \pi_i(t, \alpha), \quad \psi(h')
$$

The branch-realization condition ensures that this universal statement is not vacuously true when $\alpha$ is feasible: without it, the choice cell could be empty, and a statement about every history in that cell would hold merely because there are no such histories. We can now distinguish an action's guarantee from what happens on one realized history.

3. Deliberative Agency ( $`\text{Does}_i^t(\psi)`$ ): At a decision node with $t\in h$, agent $i$'s enacted choice guarantees $\psi$, while some history through $t$ does not satisfy $\psi$:

$$
\text{Does}_i^t(\psi)(h) \iff \left( \forall h' \in \Pi_i(t, h), \psi(h') \right) \wedge \left( \exists h'' \in H(t), \neg \psi(h'') \right)
$$

where $\Pi_i(t, h)$ is the choice cell containing history $h$:

$$
\Pi_i(t, h) \equiv \{ h' \in \mathcal{H} \mid \exists \alpha \in \mathcal{A}_{\text{feas}}(i, t, h), h \in \pi_i(t, \alpha) \wedge h' \in \pi_i(t, \alpha) \}
$$

This condition has two parts. The first says that $\psi$ holds throughout the choice cell containing $h$; the second says that $\psi$ does not hold on every history through $t$. Thus the agent's choice secures $\psi$ in the selected cell, although $\psi$ was not inevitable before that choice.

## From Actions to Inventory Changes

The final foundation connects action to subsequent physical states. Inputs deplete endowments and outputs augment them along an immediate successor. Inaction leaves stocks unchanged because its input and output schedules are zero.

### Definition 2.12 (The Inventory Transition Rule)
For a non-trade action accounted for by one agent's input and output schedules, physical endowments evolve across immediate temporal successors according to those flows. We state the law additively so that accounting does not hide the truncation of natural-number subtraction; feasibility supplies the required input. When we introduce trade in Chapter 8, we will give a paired transfer equation because one transaction changes two agents' stocks together.

$$
\text{enacted}(i, t, h) = \alpha \wedge \text{succ}(t, t', h) \implies \omega(i, t', h, m) + u(\alpha, m) = \omega(i, t, h, m) + y(\alpha, m)
$$

The balance states that the next stock plus the units used equals the current stock plus the units produced. It accounts exactly for the action's physical inputs and outputs. Because quantities are natural numbers, this additive form avoids subtracting more than the current stock; the feasibility condition ensures that the required input is available.

### Theorem 2.13 (Inaction Leaves Inventory Unchanged)
*The passive baseline action leaves physical endowments strictly unchanged across temporal transitions:*

$$
\text{enacted}(i, t, h) = \alpha_0 \wedge \text{succ}(t, t', h) \implies \forall m \in \mathcal{M}, \quad \omega(i, t', h, m) = \omega(i, t, h, m)
$$

**Proof.** The passive action uses and yields zero units of every means. Substituting those values into the transition balance gives, for each means $m$:

$$
\omega(i,t',h,m)+0=\omega(i,t,h,m)+0.
$$

Equality after adding zero gives $\omega(i,t',h,m)=\omega(i,t,h,m)$ for every means. $\blacksquare$

### Proposition 2.14 (Inventory Changes Reflect Inputs and Outputs)
Let $t'$ be an immediate successor of $t$ along history $h$, with $\text{enacted}(i, t, h) = \alpha$.
1. **Pure Production**: If action $\alpha$ consumes zero units of commodity $m$ ( $u(\alpha, m) = 0$ ), the stock of $m$ cannot decrease:

$$
\omega(i, t', h, m) = \omega(i, t, h, m) + y(\alpha, m) \ge \omega(i, t, h, m)
$$

2. **Pure Consumption**: If action $\alpha$ yields zero units of commodity $m$ ( $y(\alpha, m) = 0$ ), the stock of $m$ cannot increase:

$$
\omega(i, t', h, m) + u(\alpha, m) = \omega(i, t, h, m)
$$

**Proof.** If $u(\alpha,m)=0$, the balance reads $\omega(i,t',h,m)=\omega(i,t,h,m)+y(\alpha,m)$, so stock cannot decrease. If $y(\alpha,m)=0$, the balance reads $\omega(i,t',h,m)+u(\alpha,m)=\omega(i,t,h,m)$. Since use is nonnegative, the next stock cannot exceed the current stock. Feasibility also ensures that the consumed amount is covered. $\blacksquare$

## Multi-Step Operational Traces

A single transition is only one part of an operation that may span several moments. We represent each step as non-trade production, a matched offer or acceptance that transfers goods, or an unmatched offer or acceptance that leaves inventories unchanged. At each step, physical yield splits into production output plus goods received through matched trade; unmatched offers and acceptances contribute neither. A finite **inventory run** chains these steps along one history. For a run $r$ from $t$ to $u$, let $U_r(m)$ be the total amount of means $m$ used and $Y_r(m)$ the total amount yielded, including production and matched trade. Repeated application of the one-step law gives the exact balance

$$
\omega(i,u,h,m)+U_r(m)=\omega(i,t,h,m)+Y_r(m).
$$

If two runs are concatenated, their total uses and total yields add. Thus the balance can be checked stage by stage or over the whole run; intermediate stocks cancel from the final equality.

The same accounting applies to projected outcomes in ex-ante deliberation. A **projected inventory trace** follows a feasible action from the projected decision node along the history selected for that action until its expected maturation moment. For two feasible actions considered at the same projected node, the starting stock is identical. Each trace's additive balance uniquely determines its terminal stock from that common starting stock, total use, and total yield. The projected end is therefore grounded in the physical stock path, while preferences over those ends remain a separate premise.

## Conclusion

We have used histories to represent alternative continuations, choice cells to describe which histories an action selects, and an inventory equation to track physical change. This account specifies what is enacted and what follows materially, but it does not explain why an agent selects one feasible action rather than another. We now introduce preference and the conditions under which an enacted action counts as purposeful.
