# Praxeological Critique of Modern Monetary Theory (MMT)

## 1. Original Argument and Theoretical Explanation

Modern Monetary Theory (MMT), developed from the Neo-Chartalist tradition of Georg Friedrich Knapp (1905) and Abba Lerner (1943), asserts the following foundational propositions concerning sovereign fiat currency systems:

1. **Chartalism ("Taxes Drive Money"):**
   Money is a creation of the state. The sovereign establishes universal demand for an otherwise unbacked paper token by imposing coercive tax obligations denominated exclusively in that token.
2. **Fiscal Dominance and Solvency Independence:**
   A monetarily sovereign government issuing non-convertible fiat currency under floating exchange rates cannot become involuntarily insolvent. Taxes do not finance government expenditure; rather, the state spends currency into existence before collecting it. National accounting identities dictate that sovereign deficits equal private net financial asset savings:

$$
(G - T) = (S - I) - \text{CAB}
$$

3. **The Slack Assumption and Physical Limits:**
   Government deficit spending is constrained not by financial revenues, but exclusively by real physical resources. As long as an economy exhibits "slack" or unutilized labor, sovereign monetary creation can mobilize these idle factors without generating inflation or structural distortions.
4. **Inflation Control via Fiscal Fine-Tuning:**
   When the economy approaches full capacity and general price inflation emerges, the state can neutralize excess aggregate demand by raising taxes or cutting spending, siphoning surplus purchasing power out of circulation.
5. **Permanent Zero-Interest-Rate Policy (ZIRP):**
   The natural rate of interest in a fiat currency regime is zero. Public bond yields represent a discretionary corporate subsidy, and central banks should permanently maintain short-term policy rates at zero.

---

## 2. Formal Definitions of the Target Doctrine

To evaluate MMT's macroeconomic propositions against the laws of physical production and human action, we formulate the target doctrine's core mechanisms using the primitives of Chapters 2, 9, 10, and 13:

### Definition 1 (The Sovereign Note-Issuance Transition)
The domain of physical means $\mathcal{M}$ distinguishes real capital goods $m_K$, raw materials $m_R$, complementary inputs $m_C$, and consumption goods $m_{\text{cons}}$ from fiat tokens $m_{\text{fiat}} \in \mathcal{M}$.
The sovereign expands currency via a note-issuance action $\alpha_{\text{issue}} \in \mathcal{A}$. Under the physical transition law of Chapter 2:

$$
\omega(\text{state}, t', h, m_{\text{fiat}}) = \omega(\text{state}, t, h, m_{\text{fiat}}) + P_{\text{issued}}
$$

while for all real physical means $m \neq m_{\text{fiat}}$:

$$
u(\alpha_{\text{issue}}, m) = 0 \quad \wedge \quad y(\alpha_{\text{issue}}, m) = 0
$$

The physical stocks of capital equipment, raw materials, and energy across all agents remain strictly unchanged across the issuance event.

### Definition 2 (The Slack Mobilization Hypothesis)
MMT asserts that deficit-financed token creation activates unemployed labor services $m_{\text{labor}}$ without consuming scarce complementary capital stocks or disrupting existing private production structures.

### Definition 3 (The Staged Network Inflow Schedule)
Let $d(i)$ be the assigned network distance of agent $i$ from the state currency injection node (Chapter 9, [Proposition 9.33](../natural_language/09_money_prices_and_calculation.md#proposition-933-a-downstream-bid-can-remain-below-the-wave-price)). At stage $k$, the currency increment $\delta > 0$ enters an agent's effective bid if and only if $d(i) \le k$.

### Definition 4 (The ZIRP Mandate)
The state mandates a nominal credit interest rate equal to zero: $\text{creditRate} = 0$.

---

## 3. Physical Factor Non-Synthesis

**Proposition.** Financial expansion cannot conjure physical means. If complementary physical goods required to complete an investment do not exist in inventory, no amount of newly issued fiat currency can make project completion physically feasible.

**Proof.**
1. By Chapter 2, physical inventory transitions follow exact integer conservation:

$$
\omega(i, t', h, m) + u(\alpha, m) = \omega(i, t, h, m) + y(\alpha, m)
$$

2. By Definition 1, note-issuance yields zero physical capital goods: $y(\alpha_{\text{issue}}, m_C) = 0$ for all $m_C \neq m_{\text{fiat}}$.
3. An action $\alpha_{\text{complete}}$ is physically feasible if and only if available inventory covers factor requirements: $\omega(i, t, h, m_C) \ge u(\alpha_{\text{complete}}, m_C)$ (Chapter 1).
4. If $\omega(i, t, h, m_C) < u(\alpha_{\text{complete}}, m_C)$, then $`\alpha_{\text{complete}} \notin \mathcal{A}_{\text{feas}}(i, t, h)`$.
5. Because $y(\alpha_{\text{issue}}, m_C) = 0$, executing $\alpha_{\text{issue}}$ leaves $\omega(m_C)$ completely unchanged.
Therefore, creating nominal fiat tokens cannot transform an infeasible physical project into a feasible one. $\blacksquare$

---

## 4. Cantillon Asymmetry and Factor Starvation

**Proposition.** Injected currency does not spread uniformly across the economy; it bids scarce complementary capital away from existing private production lines, triggering mid-chain project abandonment.

**Proof.**
1. By [Proposition 9.33](../natural_language/09_money_prices_and_calculation.md#proposition-933-a-downstream-bid-can-remain-below-the-wave-price) (Chapter 9), under a staged injection schedule, early recipients at distance $d(i) \le k$ possess expanded effective purchasing power, bidding prices up to $P_{\text{wave}}$.
2. Downstream private producers at distance $d(j) > k$ operate at base reservation bids $v_j < P_{\text{wave}}$.
3. Because labor cannot produce without complementary tools and intermediate inputs $(u(\alpha, m_C) > 0)$, state-funded employers bid scarce materials and equipment away from private enterprises.
4. Starved of complementary factors, downstream private production lines find $u(\alpha, m_C) > \omega(j, t, h, m_C)$, forcing them into physical infeasibility.
Deficit spending does not mobilize "idle slack" costlessly; it diverts scarce complementary physical capital, inducing factor exhaustion in ongoing production chains. $\blacksquare$

---

## 5. ZIRP Distorts Entrepreneurial Appraisal into Malinvestment

**Proposition.** Suppressing the credit interest rate to zero severs price signals from voluntary physical saving, mathematically inducing multi-stage malinvestment clusters.

**Proof.**
1. By Chapter 7 ([Theorem 7.16](../natural_language/07_time_preference_interest_and_capital.md#theorem-716-the-master-positive-time-preference-and-originary-interest-synthesis)), under explicit discounting and open-horizon premises, purposeful human action exhibits positive originary interest ($\delta \ge 1$): present control strictly dominates uncompensated deferred claims, and earlier attainment of a fixed end is strictly preferred to later attainment.
2. In Chapter 10 and Chapter 13, an entrepreneur's appraisal of a multi-stage investment project compares the projected intertemporal spread against the loan interest rate.
3. When the state forces $\text{creditRate} = 0$, long-horizon roundabout projects that fail to clear the natural time-preference hurdle $(\text{naturalRate} > 0)$ falsely appear profitable at the zero credit rate.
4. Entrepreneurs initiate capital projects requiring lengthy gestation periods $(t_0 \prec t_1 \prec \dots \prec t_n)$.
5. Because voluntary saving has not expanded, the complementary physical factors $m_C$ required to carry these projects to maturation do not exist in aggregate inventory.
6. When the initial credit injection is spent, factor starvation forces the abandonment of uncompleted projects, precipitating a systemic economic bust (Chapter 13, Master Theorem). $\blacksquare$

---

## 6. Macroeconomic Critique and Epistemic Impossibility

### The Epistemic Impossibility of Controlling Inflation via Taxation
MMT proposes that when inflation emerges, the state can neutralize excess aggregate demand by raising taxes.

This proposal fails on foundational epistemic grounds:
1. **Relative Price Distortions vs. Aggregate Scalars:** Inflation is not an undifferentiated increase in a scalar price index; it is an uncoordinated distortion of relative price ratios across heterogeneous capital goods and consumption stages (Chapter 9).
2. **Incommensurability of Central Calculation:** Heterogeneous capital goods form physical antichains ( $x_A \not\le x_B \wedge x_B \not\le x_A$, Chapter 9) that cannot be coordinated without genuine market exchange prices. A central taxing authority cannot know which specific production stages to contract, which factor prices are distorted, or which consumer goods are in genuine excess demand.
3. **Destructive Impact of Aggregate Tax Drains:** Levying broad taxes extracts liquid capital indiscriminately from productive and solvent firms, starving viable enterprises of operational cash and worsening physical factor shortages while leaving underlying relative price distortions uncorrected.
