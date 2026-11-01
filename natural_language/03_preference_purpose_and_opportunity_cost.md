# Chapter 3: Preference, Purpose, and Opportunity Cost

We now add a relation that ranks ends from the agent's point of view. Combined with the feasible menu and the enacted action from the first two chapters, this relation lets us state exactly when a choice is purposeful.

> *Prerequisites and scope:* Chapters 1 and 2. We use feasibility, histories, and enacted choice to define purposeful action, then study what a choice reveals about foregone options and context-dependent preference.

We proceed in stages. First we state the minimal consistency condition on preference and connect physical bundles to ends. Next we combine preference with feasibility and execution. Only then can we ask what an observed choice rules out and how to describe the opportunities it leaves behind.

## Scarcity and Preference

We distinguish scarcity from valuation. A short stock can limit which ends are attainable, but it cannot tell us which of those ends the agent ranks higher. We therefore define preference separately, beginning with asymmetry; when a later result needs transitivity, we will add it explicitly.

### Definition 3.1 (Physical Scarcity Predicate)
A means $m$ is scarce for agent $i$ at $(t,h)$ when the available stock falls short of the requirement for at least one end:

$$
\text{Scarce}(i, t, h, m) \iff \exists e \in \mathcal{E}, \quad \omega(i, t, h, m) < \rho(e, m)
$$

This definition records a physical shortfall. It makes no claim yet about which action the agent will choose; that conclusion also requires a menu and a preference relation.

### Definition 3.2 (Subjective Ordinal Preference)
At each decision situation, we represent the agent's strict ranking by a binary relation on ends:

$$
\succ_{i,t,h} \; \subseteq \mathcal{E} \times \mathcal{E}
$$

We write $e_1\succ_{i,t,h}e_2$ when the agent ranks $e_1$ strictly above $e_2$ at that situation. The relation records order only, so its comparisons do not depend on numerical labels assigned to ends.

### Assumption 3.3 (Strict Asymmetry of Preference)
We require preference to be asymmetric:

$$
\forall e_1, e_2 \in \mathcal{E}, \quad e_1 \succ_{i,t,h} e_2 \implies \neg(e_2 \succ_{i,t,h} e_1)
$$

This condition prevents opposite strict rankings from holding at the same decision situation. We use it immediately to rule out strict preference of an end over itself.

### Proposition 3.4 (Derived Strict Irreflexivity of Preference)
*Subjective ordinal preference is strictly irreflexive:*

$$
\forall e \in \mathcal{E}, \quad \neg(e \succ_{i,t,h} e)
$$

**Proof.** If $e\succ_{i,t,h}e$ held, asymmetry applied to this same pair would give its negation. Hence it cannot hold. $\blacksquare$

### Definition 3.5 (Bundle Invariance of Subjective Preference)
We also require the ranking at moment $t$ to agree across histories containing $t$. The future branch may differ, but the preference relation used at this shared decision point is the same:

$$
\forall h_1, h_2 \in H(t), \quad \succ_{i,t,h_1} \; = \; \succ_{i,t,h_2}
$$

---

### Valuation of Feasible Ends

Chapter 1 defined a comparison between bundles by the ends they can attain. We now state how that comparison constrains preference: a bundle that supports every attainable end set of another, and at least one additional set, is ranked strictly higher when bundles are represented as ends.

### Assumption 3.6 (Preference for a Bundle That Attains More Ends)
We represent bundles by ends through a map

$$
\text{bundle} : (\mathcal{M} \to \mathbb{N}) \to \mathcal{E}
$$

and require attainability-based dominance to imply strict preference:

$$
\forall i \in \mathcal{I}, \forall t \in \mathcal{T}, \forall h \in \mathcal{H}, \forall b_1, b_2 \in \mathcal{M} \to \mathbb{N}, \quad \triangleright_{\mathrm{T}}(\rho, b_1, b_2) \implies \succ_{i,t,h}(\text{bundle}(b_1), \text{bundle}(b_2))
$$

This condition connects physical possibilities to valuation. We will use it only where the model includes the stated bundle representation and implication; it does not follow from quantity comparisons alone.

---

### Theorem 3.7 (Direct Bundle Representation)
*When a model represents each bundle directly by an end whose requirements equal that bundle, raw physical vector dominance strictly implies teleological bundle dominance:*

$$
\forall b_1, b_2, \quad \triangleright_{\mathrm{P}}(b_1, b_2) \implies \triangleright_{\mathrm{T}}(\rho, b_1, b_2)
$$

**Proof.** Let $`\triangleright_{\mathrm{P}}(b_1, b_2)`$, so $`\forall m, b_2(m) \le b_1(m)`$ and $`b_2(m^{\ast}) < b_1(m^{\ast})`$ for some $m^{\ast}$. By Lemma 1.10 (Part 1), any $S$ attainable under $`b_2`$ is attainable under $`b_1`$. Consider the singleton witness $`S = \{ \text{bundle}(b_1) \}`$. Since $`\sum_{e \in S} \rho(e, m) = b_1(m) \le b_1(m)`$, $S$ is attainable under $`b_1`$. But at $m^{\ast}$, $`b_1(m^{\ast}) \le b_2(m^{\ast})`$ fails because $`b_2(m^{\ast}) < b_1(m^{\ast})`$. Hence $S$ is not attainable under $`b_2`$, witnessing $`\triangleright_{\mathrm{T}}(\rho, b_1, b_2)`$. $\blacksquare$

## Purposeful Choice: Feasible, Enacted, and Undominated

We can now combine the ingredients. A purposeful action must be feasible and actually enacted. If it is not inaction, its end must improve strictly on the end of inaction; among all feasible actions, no rival may lead to a strictly preferred end. Because this last condition excludes only strict domination, it permits ties and incomparable options.

### Definition 3.8 (Purposeful Choice Relative to a Relation)
Let $R$ be a binary relation on ends. We call $\alpha^{\ast}$ purposeful relative to $R$ at $(i,t,h)$ when it satisfies the following four conditions:

$$
\begin{aligned}
\mathsf{P}_{R}(R, i, t, h, \alpha^{\ast}) \iff & \alpha^{\ast} \in \mathcal{A}_{\text{feas}}(i, t, h) \\
& \wedge \; \mathsf{Exec}(i, t, \alpha^{\ast}, h) \\
& \wedge \; \left( \alpha^{\ast} = \alpha_0 \vee R(\text{outcome}(i, \alpha^{\ast}, t, h), \text{outcome}(i, \alpha_0, t, h)) \right) \\
& \wedge \; \forall \beta \in \mathcal{A}_{\text{feas}}(i, t, h), \; \neg R(\text{outcome}(i, \beta, t, h), \text{outcome}(i, \alpha^{\ast}, t, h))
\end{aligned}
$$

The clauses have distinct roles:
1. Feasibility: The action belongs to the physically available choice menu $`\mathcal{A}_{\text{feas}}(i, t, h)`$ (Definition 1.4).
2. Physical Execution: The action is enacted on history $h$ at moment $t$. Chapter 2 defines this through the choice cell (Definition 2.11); enacted actions are recorded by Definition 2.7, and feasible alternatives have corresponding branches under Assumption 2.10.
3. Improvement over inaction: An active action must have an end ranked above the end of $\alpha_0$.
4. Undominatedness: No feasible alternative may have an end ranked strictly above the chosen end.

### Definition 3.9 (Purposeful Choice under the Agent's Preference)
We obtain the preference-based case by taking $R$ to be the agent's relation at the decision situation:

$$
\mathsf{P}(i, t, h, \alpha^{\ast}) \equiv \mathsf{P}_{R}(\succ_{i,t,h}, i, t, h, \alpha^{\ast})
$$

### Definition 3.10 (Active Purposeful Choice)
We call a purposeful choice active when it strictly improves on inaction:

$$
\mathsf{P}_{\mathrm{act}}(i, t, h, \alpha^{\ast}) \equiv \mathsf{P}(i, t, h, \alpha^{\ast}) \wedge \text{outcome}(i, \alpha^{\ast}, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha_0, t, h)
$$

### Theorem 3.11 (Consequences of Active Purposeful Choice)
Let $\alpha^{\ast} \in \mathcal{A}$ be a purposeful action for agent $i$ at decision node $\langle t, h \rangle$.
1. If $\alpha^{\ast} \neq \alpha_0$, then its assigned end differs from that of inaction: $\text{outcome}(i, \alpha^{\ast}, t, h) \neq \text{outcome}(i, \alpha_0, t, h)$.
2. If the assigned end of $\alpha^{\ast}$ is strictly preferred to the assigned end of inaction, then $\alpha^{\ast}$ is distinct from $\alpha_0$ and its assigned end differs from the end of inaction: $\alpha^{\ast} \neq \alpha_0 \wedge \text{outcome}(i, \alpha^{\ast}, t, h) \neq \text{outcome}(i, \alpha_0, t, h)$.
3. *Active purposeful action is logically equivalent to purposeful action distinct from the passive baseline:* $`\mathsf{P}_{\mathrm{act}}(i, t, h, \alpha^{\ast}) \iff \mathsf{P}(i, t, h, \alpha^{\ast}) \wedge \alpha^{\ast} \neq \alpha_0`$.
4. If the passive baseline $\alpha_0$ is strictly dominated by some feasible alternative $`\beta \in \mathcal{A}_{\text{feas}}(i, t, h)`$, then any purposeful action $\alpha^{\ast}$ strictly excludes inertia ($\alpha^{\ast} \neq \alpha_0$).

**Proof.**
1. By Definition 3.8, $\alpha^{\ast} = \alpha_0$ or $\text{outcome}(\alpha^{\ast}) \succ_{i,t,h} \text{outcome}(\alpha_0)$. Since $\alpha^{\ast} \neq \alpha_0$, the second comparison holds. If the assigned ends were equal, substitution would give $\text{outcome}(\alpha_0) \succ_{i,t,h} \text{outcome}(\alpha_0)$, contradicting Proposition 3.4. Thus the assigned ends differ.
2. Suppose $\text{outcome}(\alpha^{\ast}) \succ_{i,t,h} \text{outcome}(\alpha_0)$. If $\alpha^{\ast} = \alpha_0$, then $\text{outcome}(\alpha^{\ast}) = \text{outcome}(\alpha_0)$, yielding $\text{outcome}(\alpha_0) \succ_{i,t,h} \text{outcome}(\alpha_0)$, a contradiction. Similarly, $\text{outcome}(\alpha^{\ast}) \neq \text{outcome}(\alpha_0)$.
3. The forward direction follows immediately from Part 2. For the reverse direction, if $\mathsf{P}(\alpha^{\ast})$ and $\alpha^{\ast} \neq \alpha_0$, the disjunction $\alpha^{\ast} = \alpha_0 \vee \text{outcome}(\alpha^{\ast}) \succ \text{outcome}(\alpha_0)$ forces $\text{outcome}(\alpha^{\ast}) \succ \text{outcome}(\alpha_0)$, yielding $`\mathsf{P}_{\mathrm{act}}(\alpha^{\ast})`$.
4. Suppose $\alpha^{\ast} = \alpha_0$. By undominatedness, no feasible alternative strictly dominates $\alpha^{\ast}$: $`\forall \beta \in \mathcal{A}_{\text{feas}}, \neg(\text{outcome}(\beta) \succ_{i,t,h} \text{outcome}(\alpha^{\ast}))`$. But this directly contradicts the hypothesis that some $`\beta \in \mathcal{A}_{\text{feas}}`$ satisfies $`\text{outcome}(\beta) \succ_{i,t,h} \text{outcome}(\alpha_0)`$. Hence $\alpha^{\ast} \neq \alpha_0$. $\blacksquare$

### Theorem 3.12 (An Active Choice Separates Future Branches)
If an agent purposefully enacts an action other than $\alpha_0$ at $(t,h)$, then there is a history $h_0$ through $t$ on which the agent refrains. The two histories agree on the past of $t$, share no later moment, and have incomparable future moments:

$$
\begin{aligned}
\mathsf{P}(i,t,h,\alpha^{\ast})\wedge\alpha^{\ast}\ne\alpha_0
\implies\exists h_0\in\pi_i(t,\alpha_0),\quad
&\forall s < t,\ (s\in h\leftrightarrow s\in h_0)\\
&\wedge\ \forall w > t,\ \neg(w\in h\wedge w\in h_0)\\
&\wedge\ \exists u\in h\ \exists v\in h_0,\quad
t < u\wedge t < v\wedge u\ne v\wedge\neg(u < v)\wedge\neg(v < u).
\end{aligned}
$$

**Proof.** Inaction is feasible, so the history-partition condition supplies a history through $t$ on which it is enacted. The chosen action is enacted on $h$, and distinct choice cells are disjoint, so the histories differ. By the branching-time assumptions, distinct histories through the same moment share their past and have incompatible futures; the model's history-separation result supplies the stated incomparable later moments. $\blacksquare$

The theorem makes the counterfactual concrete: refraining is represented by a branch with the same past, not by changing the action on the already realized history.

### Theorem 3.13 (One Enacted Action per Decision Situation)
At a fixed decision situation, two purposeful actions must be the same action:

$$
\mathsf{P}(i, t, h, \alpha_1) \wedge \mathsf{P}(i, t, h, \alpha_2) \implies \alpha_1 = \alpha_2
$$

**Proof.** Suppose $\alpha_1 \neq \alpha_2$. By Definition 3.8, physical execution requires $h \in \pi_i(t, \alpha_1)$ and $h \in \pi_i(t, \alpha_2)$. Hence $h \in \pi_i(t, \alpha_1) \cap \pi_i(t, \alpha_2)$. But by the disjointness clause in Theorem 2.9, the choice cells for distinct actions do not intersect. This is a contradiction, so $\alpha_1 = \alpha_2$. $\blacksquare$

### Theorem 3.14 (Multi-Option Demonstrated Consistency)
Let the feasible menu be exactly $`\{\alpha_1,\alpha_2,\alpha_3\}`$. The passive baseline $`\alpha_0`$ supplies a comparison end but is not an additional fourth menu option. Suppose preference is transitive and asymmetric, with
$\text{outcome}(\alpha_1)\succ\text{outcome}(\alpha_2)$,
$\text{outcome}(\alpha_2)\succ\text{outcome}(\alpha_3)$, and
$\text{outcome}(\alpha_1)\succ\text{outcome}(\alpha_0)$.
If $\alpha_1$ is enacted along $h$, then $\alpha_1$ is purposeful, while $\alpha_2$ and $\alpha_3$ are not:

$$
\mathsf{P}(i, t, h, \alpha_1) \wedge \neg \mathsf{P}(i, t, h, \alpha_2) \wedge \neg \mathsf{P}(i, t, h, \alpha_3)
$$

**Proof.**
1. By transitivity, $\text{outcome}(\alpha_1)\succ\text{outcome}(\alpha_3)$. The action $\alpha_1$ is feasible and enacted, and it strictly improves on $\alpha_0$. Asymmetry rules out the reverse comparison from $\alpha_0$ to $\alpha_1$ and from $\alpha_2$ or $\alpha_3$ to $\alpha_1$; irreflexivity rules out a strict self-comparison. Thus no feasible action strictly dominates $\alpha_1$, so it is purposeful.
2. The feasible action $\alpha_1$ strictly dominates $\alpha_2$. Thus $\alpha_2$ fails the undominatedness condition and is not purposeful.
3. The feasible action $\alpha_2$ strictly dominates $\alpha_3$. Thus $\alpha_3$ fails the undominatedness condition and is not purposeful. $\blacksquare$

### Theorem 3.15 (Purposeful Choice Can Include Tied Actions)
In any action frame $F$, two distinct actions $\alpha_1 \neq \alpha_2$ can achieve the identical teleological end $\text{outcome}(i, \alpha_1, t, h) = \text{outcome}(i, \alpha_2, t, h)$ while $\alpha_1$ is purposefully enacted ( $\mathsf{P}(i, t, h, \alpha_1)$ ). Strict preference ranks ends; it does not require an injective correspondence between actions and ends.

**Proof.** Let $i$ be an agent at decision node $\langle t, h \rangle$ with two distinct actions $\alpha_1 \neq \alpha_2$ in the feasible menu $`\mathcal{A}_{\text{feas}}(i, t, h)`$ having identical ends $\text{outcome}(i, \alpha_1, t, h) = \text{outcome}(i, \alpha_2, t, h)$. Suppose $\alpha_1$ is enacted, relieves felt unease over inaction ( $\alpha_1 = \alpha_0 \vee \text{outcome}(\alpha_1) \succ_{i,t,h} \text{outcome}(\alpha_0)$ ), and no feasible alternative $\beta$ satisfies $\text{outcome}(\beta) \succ_{i,t,h} \text{outcome}(\alpha_1)$. Because $\text{outcome}(\alpha_2) = \text{outcome}(\alpha_1)$, irreflexivity (Proposition 3.4) guarantees $\neg(\text{outcome}(\alpha_2) \succ_{i,t,h} \text{outcome}(\alpha_1))$. Thus $\alpha_2$ cannot dominate $\alpha_1$, and $\mathsf{P}(i, t, h, \alpha_1)$ holds despite the tie. This condition is constructively witnessed on a finite branching model. $\blacksquare$

---

## Demonstrated Preference and Choice-Cell Invariance

We next separate the agent's preference relation from what a choice alone establishes. Purposefulness rules out any feasible end strictly preferred to the chosen one. It therefore gives a negative conclusion about rivals; a positive strict ranking requires an extra comparability assumption.

### Definition 3.16 (Demonstrated Preference Over Actions)
Agent $i$ demonstrates preference for action $\alpha^{\ast}$ over action $\beta$ at node $\langle t, h \rangle$, written $\alpha^{\ast} \triangleright_{i,t,h} \beta$, if and only if $\alpha^{\ast}$ is purposeful and $\beta$ is a distinct feasible alternative:

$$
\alpha^{\ast} \triangleright_{i,t,h} \beta \iff \mathsf{P}(i, t, h, \alpha^{\ast}) \wedge \beta \in \mathcal{A}_{\text{feas}}(i, t, h) \setminus \{ \alpha^{\ast} \}
$$

### Definition 3.17 (Demonstrated Preference Over Ends)
Agent $i$ demonstrates preference for end $e_1$ over end $e_2$ at node $\langle t, h \rangle$, written $e_1 \triangleright_{\mathcal{E}, i, t, h} e_2$, if and only if $e_1$ and $e_2$ are distinct and there exist feasible actions realizing $e_1$ and $e_2$ such that the action realizing $e_1$ is purposeful:

$$
e_1 \triangleright_{\mathcal{E}, i, t, h} e_2 \iff e_1 \neq e_2 \wedge \exists \alpha^{\ast}, \beta \in \mathcal{A}_{\text{feas}}(i, t, h), \quad \mathsf{P}(i, t, h, \alpha^{\ast}) \wedge \text{outcome}(\alpha^{\ast}) = e_1 \wedge \text{outcome}(\beta) = e_2
$$

### Theorem 3.18 (A Purposeful Choice Rules Out a Preferred Rival)
*Demonstrated preference on ends strictly reveals that the foregone end is not preferred to the chosen end:*

$$
e_1 \triangleright_{\mathcal{E}, i, t, h} e_2 \implies \neg(e_2 \succ_{i,t,h} e_1)
$$

**Proof.** By Definition 3.17, we can choose feasible actions that realize the two ends, with the action realizing $e_1$ purposeful:

$$
\alpha^{\ast}, \beta \in \mathcal{A}_{\text{feas}}(i, t, h), \quad
\mathsf{P}(\alpha^{\ast}), \quad
\text{outcome}(\alpha^{\ast}) = e_1, \quad
\text{outcome}(\beta) = e_2
$$

Purposeful choice excludes every feasible action whose outcome is strictly preferred to the outcome of $\alpha^{\ast}$:

$$
\forall \gamma \in \mathcal{A}_{\text{feas}}(i, t, h), \quad
\neg\bigl(\text{outcome}(\gamma) \succ_{i,t,h} \text{outcome}(\alpha^{\ast})\bigr)
$$

Since $\beta$ is feasible, we may take $\gamma = \beta$:

$$
\neg\bigl(\text{outcome}(\beta) \succ_{i,t,h} \text{outcome}(\alpha^{\ast})\bigr)
$$

Using the two outcome equalities, we obtain:

$$
\neg(e_2 \succ_{i,t,h} e_1)
$$

This is the required conclusion. $\blacksquare$

### Theorem 3.19 (Recovering a Strict Ranking under Comparability)
Let $e_1, e_2 \in \mathcal{E}$. Under local menu comparability ($e_1 \neq e_2 \implies e_1 \succ_{i,t,h} e_2 \vee e_2 \succ_{i,t,h} e_1$), demonstrated preference implies strict subjective preference:

$$
e_1 \triangleright_{\mathcal{E}, i, t, h} e_2 \implies e_1 \succ_{i,t,h} e_2
$$

**Proof.** By Theorem 3.18, $e_1 \triangleright_{\mathcal{E}} e_2 \implies \neg(e_2 \succ_{i,t,h} e_1)$. By local comparability, since $e_1 \neq e_2$, we have $e_1 \succ_{i,t,h} e_2 \vee e_2 \succ_{i,t,h} e_1$. Discharging the disjunction against $\neg(e_2 \succ_{i,t,h} e_1)$ leaves $e_1 \succ_{i,t,h} e_2$. $\blacksquare$

### Proposition 3.20 (Ties Prevent Strict Revealed Preference)
Without local menu comparability, demonstrated preference does not imply strict preference. In particular, when an agent in an action frame faces two distinct feasible actions $\alpha_1 \neq \alpha_2$ yielding the identical end $e^{\ast}$, neither action strictly dominates all other feasible rivals:

$$
\neg (\forall \beta \in \mathcal{A}_{\text{feas}}(i, t, h) \setminus \{\alpha_1\}, \ \text{outcome}(\alpha_1) \succ_{i,t,h} \text{outcome}(\beta))
$$

$$
\wedge \quad \neg (\forall \beta \in \mathcal{A}_{\text{feas}}(i, t, h) \setminus \{\alpha_2\}, \ \text{outcome}(\alpha_2) \succ_{i,t,h} \text{outcome}(\beta))
$$

Similarly, when an agent faces two distinct ends $e_1 \neq e_2$ that are mutually unranked ( $\neg(e_1 \succ_{i,t,h} e_2) \wedge \neg(e_2 \succ_{i,t,h} e_1)$ ), choosing an action realizing one end demonstrates preference in the undominated sense, yet strict preference fails in both directions.

**Proof.** Let $`\alpha_1, \alpha_2 \in \mathcal{A}_{\text{feas}}(i, t, h)`$ with $\alpha_1 \neq \alpha_2$ and $\text{outcome}(i, \alpha_1, t, h) = \text{outcome}(i, \alpha_2, t, h) = e^{\ast}$. Suppose toward a contradiction that $\alpha_1$ strictly dominates every distinct alternative in the feasible menu:

$$
\forall \beta \in \mathcal{A}_{\text{feas}}(i, t, h) \setminus \{\alpha_1\}, \quad \text{outcome}(i, \alpha_1, t, h) \succ_{i,t,h} \text{outcome}(i, \beta, t, h)
$$

Since $`\alpha_2 \in \mathcal{A}_{\text{feas}}(i, t, h) \setminus \{\alpha_1\}`$, substituting $\beta = \alpha_2$ yields $e^{\ast} \succ_{i,t,h} e^{\ast}$, directly contradicting strict irreflexivity (Proposition 3.4). Symmetrically, $\alpha_2$ cannot strictly dominate all distinct alternatives.

When the two actions yield distinct unranked ends $e_1 \neq e_2$, if $\alpha_1$ is enacted and undominated, it is purposeful and demonstrates preference for $e_1$ over $e_2$ in the sense of Definition 3.17. But because the ends are unranked, neither $e_1 \succ_{i,t,h} e_2$ nor $e_2 \succ_{i,t,h} e_1$ holds. Demonstrated preference proves only the absence of a preferred feasible rival, not positive strict preference. $\blacksquare$

### Theorem 3.21 (Purposefulness Is Constant within a Choice Cell)
Purposeful action is an invariant property of the agent's STIT choice cell: if two histories $h_1, h_2 \in H(t)$ belong to the same choice cell for agent $i$, then an action is purposeful at $\langle t, h_1 \rangle$ if and only if it is purposeful at $\langle t, h_2 \rangle$.

$$
t \in h_1 \wedge t \in h_2 \wedge \text{enacted}(i, t, h_1) = \text{enacted}(i, t, h_2) \implies (\mathsf{P}(i, t, h_1, \alpha^{\ast}) \iff \mathsf{P}(i, t, h_2, \alpha^{\ast}))
$$

**Proof.**
1. By the physical-invariance condition in Chapter 2, stocks and contemplated menus agree across histories through $t$. Since feasibility is determined from those stocks and menus by Definition 1.4, the feasible menus also agree:

$$
\mathcal{A}_{\mathrm{feas}}(i, t, h_1) = \mathcal{A}_{\mathrm{feas}}(i, t, h_2)
$$

2. By Definition 2.6, teleological ends are bundle-invariant: $\text{outcome}(i, \alpha, t, h_1) = \text{outcome}(i, \alpha, t, h_2)$.

3. By Definition 3.5, subjective preference is bundle-invariant: $`\succ_{i,t,h_1} \; = \; \succ_{i,t,h_2}`$.

4. By Definition 2.11, physical execution is defined by $\mathsf{Exec}(i, t, \alpha^{\ast}, h) \iff \text{enacted}(i, t, h) = \alpha^{\ast}$. Because $\text{enacted}(i, t, h_1) = \text{enacted}(i, t, h_2)$, physical execution along $h_1$ is logically equivalent to physical execution along $h_2$.

Since all four defining conjuncts of $\mathsf{P}$ in Definition 3.8 are identical between $\langle t, h_1 \rangle$ and $\langle t, h_2 \rangle$, the equivalence follows. Purposeful agency is invariant across the entire STIT choice cell. $\blacksquare$

---

## Finite Posets and Set-Valued Opportunity Cost

We need one more finite-order fact before defining opportunity cost. A finite set with an irreflexive, transitive relation contains an undominated element, but it may contain several. This is why we keep the foregone frontier set-valued unless additional assumptions reduce it to one end.

### Theorem 3.22 (A Finite Set Has an Undominated Element)
Let $S$ be a finite, non-empty set equipped with an irreflexive and transitive binary relation $R$. Then $S$ contains at least one undominated (maximal) element:

$$
S \neq \emptyset \wedge \text{Irreflexive}(R) \wedge \text{Transitive}(R) \implies \exists m \in S, \quad \forall x \in S, \quad \neg R(x, m)
$$

**Proof.** We proceed by strong induction on the cardinality $n = |S|$.
- Base Step: If $n = 1$, $`S = \{ a \}`$. By irreflexivity, $\neg R(a, a)$, so $a$ is vacuously undominated.
- Inductive Step: Assume the theorem holds for all sets of cardinality $k < n$. Let $|S| = n \ge 2$, and pick an arbitrary element $a \in S$.
  - *Case 1*: If $\forall x \in S, \neg R(x, a)$, then $a$ is undominated, and we are done.
  - *Case 2*: Otherwise, there exists $b \in S$ such that $R(b, a)$. Consider the dominating subset $`S' = \{ x \in S \mid R(x, a) \}`$.
    - Since $b \in S'$, $S'$ is non-empty.
    - By irreflexivity, $\neg R(a, a)$, so $a \notin S'$. Hence $`S' \subseteq S \setminus \{ a \}`$, which implies $|S'| \le |S| - 1 < n$.
    - The relation $R$ restricted to $S'$ remains irreflexive and transitive.
    - By the induction hypothesis, there exists $m \in S'$ such that $\forall y \in S', \neg R(y, m)$.
    - We claim $m$ is undominated in the entire set $S$. Suppose for contradiction that there exists $y \in S$ such that $R(y, m)$. Since $m \in S'$, we know $R(m, a)$. By transitivity of $R$, $R(y, m) \wedge R(m, a) \implies R(y, a)$. But this means $y \in S'$ by definition of $S'$. This contradicts the maximality of $m$ in $S'$.
    - Therefore, $\forall x \in S, \neg R(x, m)$, and $m \in S$ is undominated. $\blacksquare$

### Theorem 3.23 (A Finite Set Has a Least Element in the Reverse Order)
Let $S$ be a finite, non-empty set equipped with an irreflexive and transitive binary relation $R$. Then $S$ contains at least one minimal (least-urgent) element:

$$
S \neq \emptyset \wedge \text{Irreflexive}(R) \wedge \text{Transitive}(R) \implies \exists m \in S, \quad \forall x \in S, \quad \neg R(m, x)
$$

**Proof.** The argument is the exact dual of Theorem 3.22, inducting on cardinality using the lower filtering subset $`S' = \{ x \in S \mid R(a, x) \}`$. $\blacksquare$

### Definition 3.24 (Foregone Action Menus and Images)
After an agent chooses $\alpha^{\ast}$, we can list the foregone options in two steps. First we collect the feasible rival actions; then we map them to their ends. Since two actions may have the same end, we separately record ends different from the chosen one.

1. Foregone Actions: The set of feasible rival actions left unchosen:

$$
\mathcal{A}_{\mathrm{foregone}}(i, t, h, \alpha^{\ast}) \equiv \mathcal{A}_{\mathrm{feas}}(i, t, h) \setminus \{ \alpha^{\ast} \}
$$

2. Foregone Action Ends: The image of foregone actions under the teleological mapping $\text{outcome}$:

$$
C_{\mathrm{end}}(i, t, h, \alpha^{\ast}) \equiv \{ \text{outcome}(i, \beta, t, h) \mid \beta \in \mathcal{A}_{\mathrm{foregone}}(i, t, h, \alpha^{\ast}) \}
$$

3. Strict Foregone Ends: The set of foregone ends strictly distinct from the realized end:

$$
C^{+}_{\mathrm{end}}(i, t, h, \alpha^{\ast}) \equiv C_{\mathrm{end}}(i, t, h, \alpha^{\ast}) \setminus \{ \text{outcome}(i, \alpha^{\ast}, t, h) \}
$$

### Proposition 3.25 (Removing a Missing End Changes Nothing)
If no foregone action leads to the chosen end, then removing that end from the foregone set leaves the set unchanged:

$$
(\forall \beta \in \mathcal{A}_{\mathrm{foregone}}, \text{outcome}(\beta) \neq \text{outcome}(\alpha^{\ast})) \implies C_{\mathrm{end}} = C^{+}_{\mathrm{end}}
$$

**Proof.** By Definition 3.24, $`C^{+}_{\mathrm{end}} = C_{\mathrm{end}} \setminus \{ \text{outcome}(\alpha^{\ast}) \}`$. If no $`\beta \in \mathcal{A}_{\mathrm{foregone}}`$ maps to $\text{outcome}(\alpha^{\ast})$, then $`\text{outcome}(\alpha^{\ast}) \notin C_{\mathrm{end}}`$. Removing an element not present in a set leaves the set unchanged. $\blacksquare$

### Definition 3.26 (Opportunity-Cost Frontiers)
We define opportunity cost by retaining the undominated ends among the foregone options. We form one frontier from all foregone ends and another after removing any tie with the chosen end:

1. Action Opportunity Cost Set: The set of undominated ends among all foregone actions:

$$
\mathrm{OC}_{\mathrm{act}}(i, t, h, \alpha^{\ast}) \equiv \{ e \in C_{\mathrm{end}} \mid \forall e' \in C_{\mathrm{end}}, \neg(e' \succ_{i,t,h} e) \}
$$

2. Strict Opportunity-Cost Frontier: The undominated ends among the foregone ends different from the chosen end:

$$
\mathrm{OC}^{+}_{\mathrm{end}}(i, t, h, \alpha^{\ast}) \equiv \{ e \in C^{+}_{\mathrm{end}} \mid \forall e' \in C^{+}_{\mathrm{end}}, \neg(e' \succ_{i,t,h} e) \}
$$

### Theorem 3.27 (Basic Properties of the Opportunity-Cost Frontiers)

1. The chosen end is absent from the strict frontier:

$$
\text{outcome}(i, \alpha^{\ast}, t, h) \notin \mathrm{OC}^{+}_{\mathrm{end}}(i, t, h, \alpha^{\ast})
$$

2. If a foregone action has the same end as the chosen action, then the chosen end belongs to the frontier formed from all foregone ends:

$$
\beta \in \mathcal{A}_{\mathrm{foregone}} \wedge \text{outcome}(\beta) = \text{outcome}(\alpha^{\ast}) \implies \text{outcome}(i, \alpha^{\ast}, t, h) \in \mathrm{OC}_{\mathrm{act}}(i, t, h, \alpha^{\ast})
$$

3. If no foregone action ties the chosen action in its end, the two frontiers coincide:

$$
\mathrm{OC}_{\mathrm{act}}(i, t, h, \alpha^{\ast}) = \mathrm{OC}^{+}_{\mathrm{end}}(i, t, h, \alpha^{\ast})
$$

**Proof.**
1. We removed the chosen end before forming the strict frontier, and filtering that set cannot add it back.
2. The tied rival places the chosen end in the full foregone set. Purposefulness rules out any foregone end strictly above it, so it is undominated there.
3. Under the no-tie premise, Proposition 3.25 identifies the candidate sets. The same ranking on equal sets gives equal frontiers. $\blacksquare$

### Theorem 3.28 (Nonempty Foregone Sets Have Nonempty Frontiers)
Assume preference is transitive on each relevant finite set. A nonempty strict foregone-end set has a nonempty strict frontier, and a nonempty full foregone-end set has a nonempty full frontier:

$$
\begin{aligned}
C^{+}_{\mathrm{end}} \neq \emptyset & \implies \mathrm{OC}^{+}_{\mathrm{end}} \neq \emptyset \\
C_{\mathrm{end}} \neq \emptyset & \implies \mathrm{OC}_{\mathrm{act}} \neq \emptyset
\end{aligned}
$$

**Proof.** Asymmetry gives irreflexivity. Apply Theorem 3.22 to each nonempty finite candidate set with preference restricted to that set. An undominated member is exactly a member of the corresponding frontier. $\blacksquare$

### Theorem 3.29 (Connected Rankings Give Singleton Frontiers)
Assume both candidate sets are nonempty and preference is transitive and connected on each. Then each undominated frontier contains exactly one end:

$$
\text{Connected}(\succ_{i,t,h}) \wedge \text{Transitive}(\succ_{i,t,h}) \wedge C^{+}_{\mathrm{end}}\ne\emptyset \wedge C_{\mathrm{end}}\ne\emptyset \implies |\mathrm{OC}^{+}_{\mathrm{end}}| = 1 \wedge |\mathrm{OC}_{\mathrm{act}}| = 1
$$

**Proof.** Theorem 3.28 gives nonemptiness. If two distinct members of either frontier existed, connectedness would rank one above the other, contradicting the lower member's undominatedness. Thus each frontier has at most one member; nonemptiness makes its cardinality exactly one. $\blacksquare$

---

## Decision-Node Grounding and Strict Posets

For applications that require transitivity, we now examine strict preference structures grounded directly in an action frame. This refinement does not alter the fundamental asymmetry assumption; it demonstrates that apparent behavioral anomalies (contextual framing, loss aversion, hyperbolic discounting, and precommitment) are mathematically reconciled with strict partial orders when properly indexed by decision nodes $\langle t, h \rangle$.

### Definition 3.30 (Strict Preference and Strict Posets at a Decision Node)
In any action frame $W$, an agent $i$'s subjective preference relation at a decision node $\langle t, h \rangle$ induces a strict preference structure on the end domain $\mathcal{E}$:

$$
\text{StrictPreference}(\mathcal{E}) = \langle \mathcal{E}, \succ_{i,t,h} \rangle
$$

satisfying strict irreflexivity ( $\forall e, \neg(e \succ_{i,t,h} e)$ ) and asymmetry ( $\forall e_1, e_2, e_1 \succ_{i,t,h} e_2 \implies \neg(e_2 \succ_{i,t,h} e_1)$ ). When node-local transitivity holds ($\forall e_1, e_2, e_3, e_1 \succ_{i,t,h} e_2 \wedge e_2 \succ_{i,t,h} e_3 \implies e_1 \succ_{i,t,h} e_3$), the structure forms a strict partial order (strict poset) on $\mathcal{E}$.

### Proposition 3.31 (Purposeful Choice Instantiates a Strict Preference Structure)
Every purposeful action is governed by an action frame strict preference structure:

$$
\mathsf{P}(i, t, h, \alpha) \implies \exists P : \text{StrictPreference}(\mathcal{E}), \quad P.\text{lt} = \succ_{i,t,h}
$$

$$
\wedge \; (\alpha = \alpha_0 \vee \text{outcome}(i, \alpha, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha_0, t, h))
$$

$$
\wedge \; \forall \beta \in \mathcal{A}_{\text{feas}}(i, t, h), \quad \neg(\text{outcome}(i, \beta, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha, t, h))
$$

**Proof.** The relation $\succ_{i,t,h}$ satisfies irreflexivity and asymmetry by Proposition 3.4 and Assumption 3.3. Taking $P.\text{lt} \equiv \succ_{i,t,h}$, the remaining clauses are exactly the improvement and undominatedness requirements of purposeful action (Definition 3.8). $\blacksquare$

### Proposition 3.32 (Framing Reversals Require Context Distinction)
An apparent reversal of preference between two ends requires that the decision nodes (moment or history) be distinct:

$$
e_1 \succ_{i, t_1, h_1} e_2 \quad \wedge \quad e_2 \succ_{i, t_2, h_2} e_1 \implies t_1 \neq t_2 \vee h_1 \neq h_2
$$

**Proof.** Suppose toward a contradiction that $t_1 = t_2$ and $h_1 = h_2$. Then both comparisons hold in the same decision situation: $e_1 \succ_{i, t_1, h_1} e_2$ and $e_2 \succ_{i, t_1, h_1} e_1$. This directly contradicts preference asymmetry (Assumption 3.3). Hence at least one coordinate must differ. $\blacksquare$

Apparent framing anomalies in empirical experiments reflect distinct decision contexts rather than an internal contradiction of preference within a single choice node.

### Proposition 3.33 (Loss Aversion Grounded in Endowment Distinction)
Reference-dependent valuation is an instance of contextual valuation across histories with differing initial endowments. If an agent evaluates an outcome from a gain history $h_{\text{gain}}$ versus a loss history $h_{\text{loss}}$ at moment $t$ such that the physical stock of means $m$ strictly differs:

$$
\omega(i, t, h_{\text{gain}}, m) > \omega(i, t, h_{\text{loss}}, m)
$$

then the two histories are necessarily distinct:

$$
h_{\text{gain}} \neq h_{\text{loss}}
$$

**Proof.** If $h_{\text{gain}} = h_{\text{loss}}$, then $\omega(i, t, h_{\text{gain}}, m) = \omega(i, t, h_{\text{loss}}, m)$, which contradicts strict inequality of natural numbers by irreflexivity of $<$. $\blacksquare$

Because physical endowments differ, the two histories are distinct. By bundle invariance of endowments (Chapter 2), two histories passing through the same moment must record identical stocks; therefore, the gain and loss contexts represent genuinely distinct branches of history.

### Proposition 3.34 (Hyperbolic Discounting Reversals Require Distinct Evaluation Moments)
Intertemporal preference shifts between delayed and immediate consumption ends are compatible with strict partial orders because they occur across distinct moments:

$$
e_{\text{delayed}} \succ_{i, t_1, h} e_{\text{immediate}} \quad \wedge \quad e_{\text{immediate}} \succ_{i, t_2, h} e_{\text{delayed}} \implies t_1 \neq t_2
$$

**Proof.** Apply Proposition 3.32 with $h_1 = h_2 = h$. The disjunction $t_1 \neq t_2 \vee h \neq h$ reduces immediately to $t_1 \neq t_2$. $\blacksquare$

Predictable preference changes over time do not violate transitivity or asymmetry at any single moment; each ranking is a well-defined strict order at its own temporal stage.

### Theorem 3.35 (Precommitment Prunes Feasible Menus)
Let $i$ be an agent facing a downstream evaluation moment $t_2$. Suppose an earlier commitment action steers the agent onto history $h_{\text{commit}}$ where the feasible menu is restricted to saving:

$$
\mathcal{A}_{\text{feas}}(i, t_2, h_{\text{commit}}) = \{ \alpha_{\text{save}} \}
$$

whereas on the uncommitted history $h_{\text{uncommitted}}$, both actions remain feasible:

$$
\mathcal{A}_{\text{feas}}(i, t_2, h_{\text{uncommitted}}) = \{ \alpha_{\text{save}}, \alpha_{\text{consume}} \}
$$

If $\alpha_{\text{consume}} \neq \alpha_{\text{save}}$, then commitment physically excludes the temptation option:

$$
\alpha_{\text{consume}} \notin \mathcal{A}_{\text{feas}}(i, t_2, h_{\text{commit}}) \quad \wedge \quad \alpha_{\text{consume}} \in \mathcal{A}_{\text{feas}}(i, t_2, h_{\text{uncommitted}})
$$

**Proof.** Because $\alpha_{\text{consume}} \neq \alpha_{\text{save}}$, $\alpha_{\text{consume}}$ cannot belong to the singleton set $`\{ \alpha_{\text{save}} \}`$, establishing the first clause. For the second clause, $\alpha_{\text{consume}}$ belongs to the two-element set $`\{ \alpha_{\text{save}}, \alpha_{\text{consume}} \}`$. $\blacksquare$

### Proposition 3.36 (Constructive Witness of Precommitment Pruning)
There exists a constructive action frame witness in which precommitment prunes downstream temptation while preserving earlier intertemporal choice:

$$
\exists W (i : \mathcal{I}) (t_{\text{uncommitted}}, t_{\text{commit}} : \mathcal{T}) (h : \mathcal{H}) (\alpha_{\text{consume}} : \mathcal{A}),
$$

$$
\alpha_{\text{consume}} \notin \mathcal{A}_{\text{feas}}(i, t_{\text{commit}}, h) \quad \wedge \quad \alpha_{\text{consume}} \in \mathcal{A}_{\text{feas}}(i, t_{\text{uncommitted}}, h)
$$

**Proof.** A finite branching model provides an explicit witness: taking agent $0$, initial moment $0$, commitment moment $1$, history $0$, and action `consume`, the menu at moment $0$ contains `idle`, `consume`, and `defer`, whereas at moment $1$ the menu contracts to `{idle}`. Hence `consume` is available at $t_{\text{uncommitted}}$ and strictly excluded at $t_{\text{commit}}$. $\blacksquare$

### Proposition 3.37 (Bounded Contemplation and Purposeful Action)
Let $W$ be an action model. If an action $\alpha$ is purposeful for agent $i$ at $\langle t, h \rangle$, and $\gamma$ is an uncontemplated action ( $`\gamma \notin \mathcal{A}_{\text{cont}}(i, t, h)`$ ), then:
1. $\gamma$ is strictly infeasible ( $`\gamma \notin \mathcal{A}_{\text{feas}}(i, t, h)`$ ); and
2. $\alpha$ remains undominated within the feasible menu ( $`\forall \beta \in \mathcal{A}_{\text{feas}}(i, t, h), \neg(\text{outcome}(i, \beta, t, h) \succ_{i,t,h} \text{outcome}(i, \alpha, t, h))`$ ).

$$
\mathsf{P}(i, t, h, \alpha) \wedge \gamma \notin \mathcal{A}_{\text{cont}}(i, t, h) \implies \gamma \notin \mathcal{A}_{\text{feas}}(i, t, h) \wedge \forall \beta \in \mathcal{A}_{\text{feas}}(i, t, h), \neg(E(i, \beta, t, h) \succ_{i,t,h} E(i, \alpha, t, h))
$$

**Proof.** By the feasibility coupling condition (Definition 1.4), any feasible action must belong to the finite contemplated set $`\mathcal{A}_{\text{cont}}`$. Since $`\gamma \notin \mathcal{A}_{\text{cont}}`$, $`\gamma \notin \mathcal{A}_{\text{feas}}`$. The second clause is direct from the undominatedness condition of $\mathsf{P}(i, t, h, \alpha)$. $\blacksquare$

Bounded contemplation does not violate human action: an actor economizes scarce cognitive attention within their finite contemplated set $`\mathcal{A}_{\text{cont}}`$. Uncontemplated options cannot be selected because they are outside the agent's mental model and cannot be evaluated against ends.

### Definition 3.37b (Action Frame Majority Preference)
Let $\mathcal{W}$ be an Action Frame. At decision moment $t$ on history $h$, for three agents $i_1, i_2, i_3 \in \mathcal{I}$ and alternative ends $e_1, e_2 \in \mathcal{E}$, the collective pairwise majority preference is defined by:

$$
\text{ActionFrameMajorityPref}(t, h, i_1, i_2, i_3, e_1, e_2) \iff
\begin{aligned}
  &(e_1 \succ_{i_1, t, h} e_2 \wedge e_1 \succ_{i_2, t, h} e_2) \;\vee \\
  &(e_1 \succ_{i_1, t, h} e_2 \wedge e_1 \succ_{i_3, t, h} e_2) \;\vee \\
  &(e_1 \succ_{i_2, t, h} e_2 \wedge e_1 \succ_{i_3, t, h} e_2)
\end{aligned}
$$

### Proposition 3.38 (Condorcet Majority Cycles from Individual Strict Posets)
When each agent's individual preference relation $\succ_{i, t, h}$ over ends is a transitive strict partial order (inducing an individual strict poset), pairwise majority preference $\text{ActionFrameMajorityPref}$ can form a strict cycle over three ends $e_0, e_1, e_2 \in \mathcal{E}$:

$$
\text{ActionFrameMajorityPref}(t, h, i_1, i_2, i_3, e_0, e_1) \;\wedge\;
\text{ActionFrameMajorityPref}(t, h, i_1, i_2, i_3, e_1, e_2) \;\wedge\;
\text{ActionFrameMajorityPref}(t, h, i_1, i_2, i_3, e_2, e_0)
$$

**Proof.** Consider three ends $e_0, e_1, e_2$ and three agents whose individual preferences are transitive strict posets:
- Agent $i_1$: $e_0 \succ_{i_1} e_1 \succ_{i_1} e_2$
- Agent $i_2$: $e_1 \succ_{i_2} e_2 \succ_{i_2} e_0$
- Agent $i_3$: $e_2 \succ_{i_3} e_0 \succ_{i_3} e_1$

Evaluating pairwise majorities:
1. Between $e_0$ and $e_1$: Agents $i_1$ and $i_3$ rank $e_0 \succ e_1$, establishing a two-thirds majority for $e_0$ over $e_1$.
2. Between $e_1$ and $e_2$: Agents $i_1$ and $i_2$ rank $e_1 \succ e_2$, establishing a two-thirds majority for $e_1$ over $e_2$.
3. Between $e_2$ and $e_0$: Agents $i_2$ and $i_3$ rank $e_2 \succ e_0$, establishing a two-thirds majority for $e_2$ over $e_0$.

By `action_frame_majority_pref_of_strict_posets`, the majority relation over ends coincides with the majority preference over the induced strict posets. Each individual agent acts with an asymmetric, irreflexive, and transitive ranking, satisfying every axiom of purposeful human action. Yet their collective majority aggregation forms an intransitive cycle:

$$
e_0 \succ_{\text{maj}} e_1 \succ_{\text{maj}} e_2 \succ_{\text{maj}} e_0
$$

Because majority voting cycles over transitive individual posets, voting outcomes cannot be interpreted as the purposeful choice of a collective mind, nor can they define a coherent "social welfare function" or "social utility." In praxeology, purposeful choice and ordinal preference are strictly individual categories. $\blacksquare$

### Proposition 3.39 (Autonomous Self-Precommitment vs. External Menu Stripping)
In an Action Frame, there is a fundamental praxeological distinction between autonomous self-precommitment and external coercive menu stripping:
1. **Autonomous Self-Precommitment:** At moment $t_1$, an agent purposefully executes an action $\alpha_{\text{commit}}$ that steers their own future state into a branch $h_{\text{commit}}$ where a tempting action $\alpha_{\text{consume}}$ is pruned from $\mathcal{A}_{\text{feas}}(i, t_2, h_{\text{commit}})$. Both choices ($\alpha_{\text{commit}}$ at $t_1$ and $\alpha_{\text{save}}$ at $t_2$) are voluntary and purposeful, economizing scarce resources across the agent's own timeline.
2. **External Coercive Menu Stripping:** An external actor $j$ enacts an invasive action $\alpha_j$ that physically contracts $i$'s endowment $\omega(i, t', \text{jointBranch}(i, j, t, h, \alpha_0, \alpha_j), m) < \omega(i, t, h, m)$ without $i$'s consent (`EndogenouslyInvasiveJ`), forcibly stripping previously feasible actions from $i$'s choice menu (`self_precommitment_vs_external_menu_stripping`, Theorem 8.13b).

Paternalistic nudges or state regulations that coercively strip feasible actions cannot be justified as an externalized "precommitment device," because they replace the acting agent's own purposeful valuation with external physical compulsion (political means / coercive extortion). $\blacksquare$

## Conclusion

We have connected feasible outcomes to an agent's context-specific preferences, defined purposeful action through execution, improvement over inaction, and undominatedness, and identified the alternatives an action leaves behind. We have also shown that framing effects, loss aversion, hyperbolic discounting, and precommitment are fully compatible with strict partial orders when grounded in action frame decision nodes. We now turn to how scarce units of means are economized and how value is imputed to productive factors.

