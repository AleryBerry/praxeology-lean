# Praxeological Critique of the Labor Theory of Value (LTV)

## 1. Original Argument and Theoretical Explanation

The Labor Theory of Value (LTV), formulated in classical political economy by Adam Smith (1776) and David Ricardo (1817), and developed into the foundational basis of Karl Marx's critique of political economy in *Das Kapital* (1867), asserts the following core propositions:

1. **The Common Substance of Exchange:**
   Whenever two commodities exchange against one another in the ratio:

$$
x \, \text{Commodity } A = y \, \text{Commodity } B
$$

   they are asserted to be quantitatively equal. Marx argued that for two physically heterogeneous goods to be equated in exchange, they must contain a common substance of identical magnitude. Abstracting away from physical attributes and subjective utility, the LTV asserts that the only common property remaining is that both are products of **human labor**.
2. **Socially Necessary Labor Time (SNLT):**
   The economic value of any commodity is objectively determined by, and directly proportional to, the **Socially Necessary Labor Time** (SNLT) required for its production:

$$
V(x) = \text{SNLT}(x)
$$

   representing the labor time required under normal social conditions of production, with prevailing average skill and intensity.
3. **The Decomposition of Commodity Value:**
   The total value of a commodity $W$ decomposes additively into:

$$
W = c + v + s
$$

   where $c$ is **constant capital** (the value of physical machinery and raw materials transferred to the product without adding new value), $v$ is **variable capital** (the cost of purchasing labor-power, equal to the labor time needed to produce the worker's subsistence), and $s$ is **surplus value** (value created by living labor during the portion of the working day beyond the reproduction of labor-power).
4. **The Exploitation Hypothesis:**
   Because constant capital merely preserves existing embodied "dead labor," living labor $(v)$ is the sole source of surplus value $(s)$. The capitalist's profit is characterized as unpaid surplus labor appropriated through legal ownership of the means of production.

---

## 2. Formal Definitions of the Target Doctrine

To test whether the Labor Theory of Value holds within the operational reality of production and trade, we formulate the target doctrine's core concepts using the production schedules and exchange framework developed in Chapters 4, 7, and 8:

### Definition 1 (Historical Embodied Labor Value)
Let production be an intertemporal sequence of actions $\alpha_0 \prec \alpha_1 \prec \dots \prec \alpha_n$ yielding physical commodity $m \in \mathcal{M}$. The accumulated embodied labor content of $m$ at moment $t$ on history $h$ is defined by the historical sum of labor factor inputs:

$$
L(m, t, h) = \sum_{k=0}^{n} u(\alpha_k, m_{\text{labor}})
$$

Under the classical hypothesis, the objective value $V(m)$ is an increasing function of $L(m, t, h)$.

### Definition 2 (The Exchange Equality Postulate)
Under the LTV, an exchange of $q_A$ units of commodity $m_A$ for $q_B$ units of commodity $m_B$ between agents $i$ and $j$ represents an objective equivalence relation:

$$
q_A \cdot m_A \approx q_B \cdot m_B \iff q_A \cdot L(m_A) = q_B \cdot L(m_B)
$$

### Definition 3 (The Forward Cost Summation Hypothesis)
The economic value of output commodity $m_{\text{out}}$ is determined by summing forward the past input costs incurred across preceding production transitions:

$$
V(m_{\text{out}}) = \sum_{m \in \mathcal{M}} V(m) \cdot u(\alpha, m) + V(m_{\text{labor}}) \cdot u(\alpha, m_{\text{labor}})
$$

---

## 3. The Double-Inequality of Voluntary Exchange

**Proposition.** Exchange never expresses an equality; it expresses a strict double inequality of subjective ordinal preferences.

**Proof.**
1. In Chapter 8, voluntary bilateral exchange requires paired actions $\alpha_i = \text{Offer}(i, j, q_A, m_A, q_B, m_B)$ and $\alpha_j = \text{Accept}(j, i, q_A, m_A, q_B, m_B)$.
2. An agent enacts a trade action if and only if it is purposeful ( $\mathsf{P}$, Chapter 3). Purposeful action requires the expected end of trade to strictly dominate inaction $\alpha_0$:

$$
\text{End}(i, \text{receive } q_B \cdot m_B) \succ_{i,t,h} \text{End}(i, \text{retain } q_A \cdot m_A)
$$

and simultaneously for agent $j$:

$$
\text{End}(j, \text{receive } q_A \cdot m_A) \succ_{j,t,h} \text{End}(j, \text{retain } q_B \cdot m_B)
$$

3. If both parties valued the goods equally $(q_A \cdot m_A \sim q_B \cdot m_B)$, neither would incur the physical transfer costs and effort of trade. Trade would fail to relieve felt unease over $\alpha_0$, violating the necessary condition for purposeful action.
Because voluntary trade is motivated by opposite ordinal inequalities, Marx's search for an embodied "third common substance of equal magnitude" attempts to explain an equality that does not exist. $\blacksquare$

---

## 4. Intransitivity of Direct Exchangeability

**Proposition.** The LTV treats exchangeability as a transitive equivalence relation $(A = B \wedge B = C \implies A = C)$. In human action, direct exchangeability is an asymmetric event, not an equivalence relation.

**Proof.**
1. Consider three agents $i, j, k$ holding distinct endowments $m_A, m_B, m_C$.
2. Agent $i$ holds $m_A$ and desires $m_B$; agent $j$ holds $m_B$ and desires $m_C$; agent $k$ holds $m_C$ and desires $m_A$.
3. Bilateral exchange between $i$ and $j$ is feasible if $j$ accepts $m_A$. But if $j$ has no demand for $m_A$, direct bilateral trade between $i$ and $j$ is impossible, even if $L(m_A) = L(m_B)$.
4. If Marx's transitivity held universally, every commodity containing equal labor time would be directly exchangeable for every other, and money could never have emerged. Money arises precisely because exchangeability is not transitive, necessitating indirect exchange through generally marketable media (Chapter 9). $\blacksquare$

---

## 5. Historical Input Irrelevance (Theorem 4.32)

**Proposition.** Past labor hours expended in prior transitions are economically sterile; present market valuation and feasibility depend exclusively on present physical inventories and prospective ends.

**Proof.**
1. By Theorem 4.32 (Present-Endowment Choice Invariance, Chapter 4), whenever two situations share identical present inventories $\omega(i, t, h, m)$, identical contemplated menus, and identical preference orders over prospective ends, feasible menus and undominated choices are identical.
2. Suppose commodity $m_1$ required $1,000$ hours of labor $(L(m_1) = 1,000)$, while an identical physical commodity $m_2$ was found on the ground with zero labor $(L(m_2) = 0)$.
3. Because $m_1$ and $m_2$ have identical physical properties, their capacity to satisfy prospective ends is identical $(\text{End}(i, \alpha, m_1) = \text{End}(i, \alpha, m_2))$.
4. By Theorem 4.32, an economizing actor evaluates both units identically. The historical difference $L(m_1) \neq L(m_2)$ exerts zero causal influence on present valuation. $\blacksquare$

---

## 6. Doctrinal Critique and Theoretical Fallacies

### Backward Value Imputation vs. Forward Cost Summation
The LTV reverses the actual causal direction of economic valuation:
- The LTV claims that value flows **forward** from inputs to outputs: labor time produces factor value, which produces commodity value.
- In praxeology, value flows **backward** (Menger's Law of Imputation, Chapter 4): consumer ends are evaluated first by subjective preference rankings $(e_1 \succ e_2)$. Factors of production (including capital tools and labor) derive their economic appraisal solely from the anticipated value of the consumer goods they can produce.
- Factors of production do not make goods valuable; rather, the subjective value of goods makes factors of production valuable.

### Surplus Value as the Intertemporal Discount of Positive Time Preference
Marx characterizes the difference between output revenue and the wage bill $(s = W - c - v)$ as unpaid surplus labor extracted by force of ownership.

This deduction ignores the inescapable temporal dimension of human action:
- Production takes time: workers expend labor at moment $t_0$, but finished output matures only at a later moment $t_n$ across precedence chain $t_0 \prec t_n$ (Chapter 2).
- Under purposeful human action, agents exhibit positive time preference (Chapter 7): satisfying an end earlier is valued strictly above identical satisfaction at a later moment.
- The capitalist advances **present money** (immediate wages at $t_0$ ) to workers, long before the product is completed and sold at $t_n$.
- The spread between present wages and future product revenue is not stolen surplus value; it is the catallactic manifestation of **originary interest** $(\iota > 0)$. If workers were paid the full undiscounted future value of their output immediately at $t_0$, they would be receiving more than the present economic value of their contribution.

### The Logical Circularity of the Transformation Problem
To reconcile the LTV with uniform profit rates across industries with different capital intensities, Marx attempted in Volume III of *Das Kapital* to "transform" labor values into market prices of production.

This transformation traps the LTV in vicious circularity:
1. Marx transforms outputs from labor values into prices of production, but leaves input costs ( $c$ and $v$) denominated in labor values. Simultaneously transforming both inputs and outputs breaks the conservation of total value and total surplus value (Bortkiewicz, 1907).
2. Reducing heterogeneous, skilled labor to homogeneous "simple abstract labor" requires preexisting wage ratios determined in market exchange. Using market prices to determine labor coefficients, and then using labor coefficients to explain market prices, is a complete logical circularity.
