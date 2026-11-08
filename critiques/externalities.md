# Praxeological Critique of Neoclassical Externality Theory

## 1. Original Argument and Theoretical Explanation

In neoclassical welfare economics, originated by Arthur Cecil Pigou (1920) and developed by Francis Bator (1958) and William Baumol (1972), an **externality** is defined as an unpriced cost or benefit imposed by an economic actor on an unconsenting third party outside the market mechanism. 

The core neoclassical propositions are:
1. **Divergence of Private and Social Cost (Negative Externalities):**
   When production imposes uncompensated physical damage on third parties, Marginal Private Cost $(PMC)$ falls below Marginal Social Cost $(SMC)$:

$$
SMC(Q) = PMC(Q) + MD(Q)
$$

   where $MD(Q) > 0$ represents unpriced marginal damage. Left to the unregulated market, competitive firms produce where $PMC(Q) = P$, resulting in overproduction, with $Q_{\text{market}} > Q^{\ast}$, and a deadweight loss of aggregate social welfare.
2. **Divergence of Private and Social Benefit (Positive Externalities):**
   When an activity generates external benefits for third parties without compensation, Marginal Private Benefit $(PMB)$ is lower than Marginal Social Benefit $(SMB)$:

$$
SMB(Q) = PMB(Q) + MEB(Q)
$$

   Competitive markets produce where $PMB(Q) = MC$, resulting in alleged underproduction, with $Q_{\text{market}} < Q^{\ast}$.
3. **The Pigouvian Tax and Subsidy Remedy:**
   To restore Pareto efficiency, the state must intervene:
   - Levying a corrective Pigouvian tax equal to marginal damage $(t = MD(Q^{\ast}))$ on negative externalities to internalize social costs.
   - Providing a Pigouvian subsidy equal to marginal external benefit $(s = MEB(Q^{\ast}))$ on positive externalities.
4. **Cardinal Welfare Aggregation:**
   The theory assumes aggregate social welfare can be expressed as the cardinal summation of individual utilities minus physical damages:
   $W = \sum_{i} U_i - \sum_{j} D_j$. By calculating the monetary equivalent of external damage, a planner aligns private marginal incentives with the social optimum.

---

## 2. Formal Definitions of the Target Doctrine

To evaluate whether the neoclassical externality doctrine is logically coherent within an operational framework of human action, we define its core constructs using the primitives established in Chapter 8, Chapter 9, and Chapter 12:

### Definition 1 (Interpersonal Cost Summation)
The target doctrine defines Marginal Social Cost by linearly summing the subjective factor expenditures of producer $i$ and the psychic or physical disutility of unconsenting third party $j$:

$$
SMC(Q) = C_i(Q) + D_j(Q)
$$

where $`D_j : \mathcal{Q} \to \mathbb{R}_{> 0}`$ represents an alleged cardinal disutility converted to monetary units.

### Definition 2 (Physical Invasion vs. Unacted Psychic Spillover)
Let $\omega(k, t, h, m)$ denote the physical inventory of agent $k$ across goods $m \in \mathcal{M}$. We distinguish two physically distinct interaction types:
1. **Physical Invasion (Property Tort):** An action $\alpha$ enacted by producer $i$ physically alters, occupies, or destroys the physical property or bodily integrity of agent $j$ without $j$'s prior consent:

$$
\Delta \omega_{\text{inv}}(j, m) = \omega(j, t', h, m) - \omega(j, t, h, m) \neq 0
$$

2. **Unacted Psychic / Pecuniary Spillover:** Producer $i$'s action alters no physical means owned by $j$ $(\Delta \omega(j, m) = 0)$, but induces unacted psychological displeasure, envy, or changes the competitive market prices facing $j$.

### Definition 3 (Pigouvian Tax Decree)
A regulatory authority $s \in \mathcal{I}$ decrees a mandatory tax $`t^{\ast} \in \mathbb{Q}_{> 0}`$ per unit of production on agent $i$, forcibly extracting money tokens without bilateral consent:

$$
\omega(i, t', h, m_{\text{money}}) = \omega(i, t, h, m_{\text{money}}) - t^{\ast} \cdot Q
$$

backed by physical coercion or penalties for non-compliance.

---

## 3. Invariance Failure of Interpersonal Utility Aggregation

**Proposition.** Subjective preferences are strictly ordinal posets over discrete ends. There exists no mathematically invariant scale that permits adding the subjective displeasure of one agent to the production costs of another. Consequently, Marginal Social Cost $(SMC)$ is an undefined mathematical expression, and the optimal Pigouvian tax $t = MD(Q^{\ast})$ is computationally impossible.

**Proof.**
1. By Chapter 9 ([Theorem 9.30](../natural_language/09_money_prices_and_calculation.md#theorem-930-the-socialist-incommensurability-antichain-theorem) on ordinal preference invariance), subjective valuations are strictly ordinal rankings over discrete ends: $e_1 \succ_i e_2$. Preferences express order, not cardinal magnitude or physical distance.
2. For two distinct agents $i, j \in \mathcal{I}$, there is no common physiological or psychic unit of measurement. Any monotone transformation $f : \mathcal{E} \to \mathbb{R}$ that preserves individual rankings leaves interpersonal sums non-invariant: $f_i(e_a) + f_j(e_b) \neq g_i(e_a) + g_j(e_b)$ under admissible order-preserving rescalings.
3. Therefore, the formula $SMC = C_i(Q) + D_j(Q)$ attempts to add non-commensurable ordinal states across distinct minds.
4. Because $D_j(Q)$ cannot be measured in invariant monetary units, the alleged optimal tax rate $t = MD(Q^{\ast})$ cannot be calculated by any objective economic procedure. $\blacksquare$

---

## 4. Demonstrated Preference and the Tort Dichotomy

**Proposition.** Economic preference is revealed strictly through purposeful action $(\mathsf{P})$. Purely psychological or pecuniary spillovers do not constitute property invasions; conversely, unconsented physical damage is a property tort requiring legal restitution, not an unpriced market failure.

**Proof.**
1. By Chapter 3 and Chapter 8, an agent's economic valuations are demonstrated if and only if the agent undertakes purposeful action $(\mathsf{P})$, choosing an undominated action from $`\mathcal{A}_{\text{feas}}`$ while sacrificing scarce means.
2. In the case of an unacted psychic spillover (Definition 2, part 2), no physical property of $j$ is invaded $(\Delta \omega = 0)$. Unacted feelings of disapproval or envy involve no surrender of means and are not demonstrated in action. Treating unacted psychic discontent as a cost to be socialized treats any non-pleasing autonomous human choice as an actionable externality, destroying the formal boundary of property rights.
3. In the case of physical damage (Definition 2, part 1), producer $i$'s emissions physically alter or destroy $j$'s inventory without consent $(\Delta \omega_{\text{inv}} \neq 0)$. By Chapter 8, this is an unconsented physical invasion (a tort).
4. Physical invasions are resolved under property law by enjoining trespass and enforcing physical restitution $(\Delta \omega_{\text{comp}})$ from the invader to the victim.
5. Characterizing physical pollution as an "externality" or "market failure" misclassifies a judicial failure to enforce property boundaries as an inherent defect of voluntary exchange. $\blacksquare$

> [!NOTE]
> This result establishes the praxeological foundation of the property rights approach formulated by Ronald Coase and Murray Rothbard. Where physical boundaries are well-defined and defended, negative externalities are resolved through tort liability; where physical boundaries are not invaded, no economic tort exists.

---

## 5. Pigouvian Taxation as Hegemonic Intervention

**Proposition.** Levying a Pigouvian tax does not maximize social welfare. In catallactic classification, taxation is an act of anchored extortion that strictly degrades the taxed producer below their unmolested baseline, transferring resources to the state treasury rather than compensating any victim.

**Proof.**
1. By Chapter 8 and Chapter 12, social interactions are partitioned into voluntary exchange, market competition, and hegemonic intervention (political means (coercive extortion)).
2. A Pigouvian tax forcibly extracts physical money balances from producer $i$ without $i$'s voluntary consent (Definition 3):

$$
\omega(i, t', h, m_{\text{money}}) = \omega(i, t, h, m_{\text{money}}) - t^{\ast} \cdot Q
$$

3. Producer $i$ is strictly harmed, having fewer physical means to pursue purposeful ends, while incurring no voluntary trade benefits.
4. The collected tax funds flow to the state treasury, providing zero compensation to affected third parties $j$.
5. Because at least one agent (the producer) is demonstrably harmed, asserting that the Pigouvian tax achieves a "net social welfare improvement" requires the interpersonal summation of utility refuted above. $\blacksquare$

---

## 6. Institutional Synthesis and Conclusion

Neoclassical externality theory collapses on both epistemological and catallactic grounds. "Social cost" is an incoherent mathematical concept resulting from the invalid aggregation of subjective ordinal preferences. Where physical property is damaged, the phenomenon is a property tort requiring judicial restitution; where physical property is uninvaded, psychic spillovers are the natural reality of human coexistence, which can never be objectively measured or corrected by state coercion.
