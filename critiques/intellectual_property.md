# Praxeological Critique of Intellectual Property (IP)

## 1. Original Argument and Theoretical Explanation

In neoclassical economics, originated by Kenneth J. Arrow (1962) and William D. Nordhaus (1969), ideas, technical designs, software, and artistic creations are classified as **non-rivalrous** and **non-excludable** information goods.

The core propositions of neoclassical intellectual property theory are:
1. **The Public Good Dilemma of Information:**
   Because the physical marginal cost of copying an existing blueprint, chemical formula, or artistic work approaches zero $(MC_{\text{replication}} \approx 0)$, competitive market pricing $(P = MC)$ would drive the price of copies down to zero.
2. **The Inability to Amortize Research Expenditures:**
   Under competitive pricing, an inventor cannot earn economic rents to recover upfront fixed research, development, and creative costs, with $F_{\text{RD}} > 0$. Consequently, an unhampered market suffers an alleged market failure: the underproduction of innovation due to free-riding competitors.
3. **Statutory Monopoly as the Second-Best Remedy:**
   To incentivize technological progress, the state must grant statutory **Intellectual Property** privileges (patents, copyrights, and industrial designs). The state grants the inventor a legal monopoly over the commercial use and manufacture of the idea for a statutory duration $T$ (e.g., twenty years), allowing the patent holder to restrict output, with $Q_m < Q_c$, and charge monopoly prices, with $P_m > MC$, to recoup research investments.
4. **The Nordhaus Trade-Off:**
   Neoclassical policy seeks an optimal statutory duration $T^{\ast}$ that balances the dynamic welfare gain of incentivized invention against the static deadweight loss of temporary monopoly pricing.

---

## 2. Formal Definitions of the Target Doctrine

To evaluate whether intellectual property privileges are consistent with property rights and teleological action, we formulate the target doctrine within the praxeological framework of production schedules, physical conservation, and institutional intervention (Chapter 2, Chapter 4, Chapter 8, and Chapter 12):

### Definition 1 (Ontological Scarcity vs. Causal Recipes)
We distinguish between physical means of production and mental causal recipes:
1. **Physical Means** $(\mathcal{M})$: Discrete, scarce physical goods (raw materials, machinery, paper, physical hardware, human bodies) recorded in stock inventories $\omega(k, t, h, m) \in \mathbb{N}$. Physical means are rivalrous: an agent's physical possession and use of a machine physically excludes another agent's simultaneous use.
2. **Causal Recipes** $(u, y)$: The input and yield schedules $u : \mathcal{A} \times \mathcal{M} \to \mathbb{N}$ and $y : \mathcal{A} \times \mathcal{M} \to \mathbb{N}$ defined in Chapter 2 and Chapter 4. A recipe is a mental conception of causal relations. Learning or adopting a recipe by agent $j$ does not diminish, consume, or physically alter the stock $\omega(i, t, h, m)$ of agent $i$.

### Definition 2 (Statutory Patent as Coercive Action Prohibition)
Let competitor $j \in \mathcal{I}$ possess physical means satisfying input requirements:

$$
\forall m \in \mathcal{M}, \quad \omega(j, t, h, m) \ge u(\alpha_{\text{prod}}, m)
$$

Under natural physical property boundaries, $`\alpha_{\text{prod}} \in \mathcal{A}_{\text{feas}}(j, t, h)`$. A statutory patent granted to innovator $i$ imposes a state decree that legally forbids competitor $j$ from arranging $j$'s own physical property in the patented configuration:

$$
\alpha_{\text{prod}} \notin \mathcal{A}_{\text{feas}}(j, t, h)
$$

enforced by the regulatory state authority through the threat of physical confiscation, fines, or imprisonment.

### Definition 3 (Multi-Patent Assembly Chains and Anticommons)
A modern complex production action $`\alpha_{\text{complex}}`$ requires obtaining $K$ separate statutory licenses $`L_k \in \{0, 1\}`$ held by independent patentees $`i_1, \dots, i_K`$:

$$
\alpha_{\text{complex}} \in \mathcal{A}_{\text{feas}} \iff \bigwedge_{k=1}^K (L_k = 1)
$$

---

## 3. Simultaneous Recipe Execution and Non-Invasive Competition

**Proposition.** Because causal recipes are non-scarce (Definition 1), competitor $j$'s simultaneous execution of a recipe using $j$'s own physical property leaves innovator $i$'s physical stock completely untouched. Consequently, emulation constitutes peaceful market competition that preserves physical endowments, whereas statutory patents coercively restrict competitors from deploying their legitimately acquired physical property.

**Proof.**
1. By Chapter 2 and Chapter 4, physical transitions satisfy conservation: $\omega(k, t', h, m) + u(\alpha, m) = \omega(k, t, h, m) + y(\alpha, m)$. When competitor $j$ enacts $\alpha_{\text{prod}}$, only $j$'s personal inventory is consumed and transformed.
2. The physical stock of innovator $i$ satisfies: $\Delta \omega(i, t', h, m) = \omega(i, t', h, m) - \omega(i, t, h, m) = 0$. Innovator $i$ retains full physical possession and operational control over all their tools, factory equipment, and prototypes.
3. By Chapter 8, an action that invades no physical property of another agent is classified as non-invasive market competition.
4. Enforcing a statutory patent (Definition 2) forcibly prohibits agent $j$ from deploying their legitimately acquired physical means. This constitutes a hegemonic intervention (political means (coercive extortion), Chapter 12) that grants patent holders partial ownership and veto power over the physical property of everyone else in society. $\blacksquare$

> [!NOTE]
> This result formalizes the core insight of Michele Boldrin and David K. Levine (2002, 2008), demonstrating that ideas are not scarce economic goods. Scarcity applies strictly to physical embodiments, proving that intellectual property creates artificial scarcity through coercion.

---

## 4. Sunk-Cost Irrelevance in Prospective Allocation

**Proposition.** By [Theorem 4.32 (Present-Endowment Choice Invariance)](../natural_language/04_marginal_allocation_and_imputation.md#theorem-432-present-endowment-choice-invariance), undominated choice at moment $t$ depends strictly on present physical stocks $\omega$ and prospective valuations of future ends; past factor expenditures $F_{\text{RD}}$ incurred at past moments $t_{\text{past}} \prec t$ are sunk and economically sterile. Demanding state-enforced monopoly rents to "amortize" past R&D expenditures is a catallactic fallacy.

**Proof.**
1. By [Theorem 4.32](../natural_language/04_marginal_allocation_and_imputation.md#theorem-432-present-endowment-choice-invariance), feasible action menus $`\mathcal{A}_{\text{feas}}(i, t, h)`$ and undominated choice $\mathsf{P}(i, t, h, \alpha^{\ast})$ are determined entirely by present stock endowments $\omega(i, t, h)$ and prospective preference rankings over anticipated ends.
2. Any past resource expenditure $F_{\text{RD}}$ occurred at historical moments $t_{\text{past}} \prec t$ along history $h$. In praxeological reality, past inputs are physically transformed and irreversible; they cannot exert causal pull over present consumer valuation.
3. In a free market, prospective prices are imputed backward from consumer appraisals (Chapter 4). No producer is guaranteed a return on past outlays: an entrepreneur who spends millions developing an unwanted product incurs a capital loss.
4. First-mover advantage, lead time, physical embodiment scarcity, and trade secrets provide natural market returns to innovation without requiring coercive insulation from consumer sovereignty. $\blacksquare$

---

## 5. Anticommons Holdout and Cumulative Innovation Paralysis

**Proposition.** Under cumulative innovation across multi-stage production chains (Definition 3), granting statutory exclusion privileges over early technological stages creates an anticommons patent thicket. Strategic holdout bargaining by individual patent holders legally blocks downstream production, paralyzing technological progress.

**Proof.**
1. By Definition 3, executing complex downstream production $\alpha_{\text{complex}}$ requires obtaining all $K$ statutory permissions: $\bigwedge_{k=1}^K (L_k = 1)$.
2. Each individual patentee $i_k$ holds absolute statutory veto power over $\alpha_{\text{complex}}$.
3. If any single patentee engages in strategic holdout bargaining by demanding a monopoly license fee that exceeds the expected net surplus of the project, or simply refuses to license, the condition fails: $`\exists k \in \{1, \dots, K\}, L_k = 0 \implies \alpha_{\text{complex}} \notin \mathcal{A}_{\text{feas}}`$.
4. The transaction costs and holdout vetoes of negotiating with dozens of separate monopoly claimants render downstream multi-stage innovation infeasible.
5. Rather than encouraging technological advancement, statutory patent systems legally paralyze cumulative research and freeze entrepreneurial discovery. $\blacksquare$

> [!NOTE]
> This result formalizes the tragedy of the anticommons, first articulated by Michael Heller and Rebecca Eisenberg (1998), derived here directly from our formalization of action feasibility menus and sequential production.

---

## 6. Property Synthesis and Conclusion

Intellectual property theory commits a fundamental category error by treating non-scarce causal recipes as if they were scarce physical property. By coercively restricting the peaceful use of real physical property, statutory patents create artificial monopolies, violate the law of sunk-cost irrelevance, and paralyze cumulative innovation through anticommons holdout thickets.
