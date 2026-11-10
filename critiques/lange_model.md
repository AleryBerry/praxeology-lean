# Praxeological Critique of the Lange Model of Market Socialism

## 1. Original Argument and Theoretical Explanation

The Lange model, formulated by Oskar Lange (1936, 1937) and Abba Lerner (1934), was conceived as a neoclassical refutation of Ludwig von Mises's demonstration that rational economic calculation is impossible under socialism. The model constructs a decentralized market socialism characterized by five core hypotheses:

1. **Socialized Ownership of Capital:**
   All capital equipment, natural resources, and intermediate factors of production are owned exclusively by the socialist state. Private ownership of capital and private equity/factor markets are legally abolished.
2. **Decentralized Consumer and Labor Markets:**
   Households freely choose occupations, receive monetary wages, and purchase consumer goods on decentralized retail markets at market-clearing prices.
3. **The Central Planning Board as Walrasian Auctioneer:**
   The Central Planning Board (CPB) acts as an administrative price-setter, publishing an economy-wide vector of accounting prices $\mathbf{P}$ for all capital goods, intermediate inputs, and industrial commodities.
4. **Mandatory Behavioral Rules for Socialist Managers:**
   State enterprise managers are commanded by law to follow two mechanical optimization rules:
   - *Rule 1 (Cost Minimization):* Managers must combine inputs to equate the marginal rate of technical substitution to the CPB accounting price ratios: $\frac{\partial F / \partial x_i}{\partial F / \partial x_j} = \frac{P_i}{P_j}$.
   - *Rule 2 (Marginal Cost Pricing):* Managers must expand production until marginal cost equals the CPB-administered price: $P_k = MC_k(Q_k)$.
5. **The Tâtonnement Trial-and-Error Algorithm:**
   The CPB adjusts prices iteratively by observing physical inventories of intermediate and capital goods: $\Delta P_k(t) = \kappa \cdot z_k(t) = \kappa \cdot (D_k(P, t) - S_k(P, t))$, with $\kappa > 0$.
   If there is excess demand (shortage, $z_k > 0$ ), the CPB raises the accounting price $P_k$; if there is excess supply (surplus, $z_k < 0$ ), the CPB lowers the accounting price $P_k$.

Lange and Lerner argued that this trial-and-error algorithm converges dynamically to general equilibrium prices $\mathbf{P}^{\ast}$, replicating the allocative efficiency of perfect competition without private capital ownership or capitalist profit.

---

## 2. Formal Definitions of the Target Doctrine

To test whether the Lange model can achieve rational resource allocation, we formulate the hypotheses of the target doctrine mathematically using the primitives established in the praxeological framework (Chapter 8, Chapter 9, and Chapter 11):

### Definition 1 (Socialized Factor Domain and Private Capital Prohibition)
The universe of physical means $\mathcal{M}$ is partitioned into consumption goods $`\mathcal{M}_{\text{cons}}`$ and capital/intermediate goods $`\mathcal{M}_{\text{cap}}`$:

$$
\mathcal{M} = \mathcal{M}_{\text{cons}} \sqcup \mathcal{M}_{\text{cap}}
$$

Socialism legally restricts the feasible action menus of all private households $`i \in \mathcal{I}_{\text{hh}}`$ such that bilateral exchange actions ( $\text{Offer}$ and $\text{Accept}$) over capital goods are strictly infeasible:

$$
\forall i \in \mathcal{I}_{\text{hh}}, \quad \forall m \in \mathcal{M}_{\text{cap}}, \quad \alpha_{\text{trade}}(i, \dots, m) \notin \mathcal{A}_{\text{feas}}(i, t, h)
$$

All physical stocks of capital goods are administered by state enterprise managers $`j \in \mathcal{I}_{\text{mgr}}`$ under public title.

### Definition 2 (Administrative Price Decrees)
At each planning moment $t$, the CPB decrees an administrative accounting price schedule:

$$
P_{\text{admin}} : \mathcal{M}_{\text{cap}} \times \mathcal{T} \to \mathbb{Q}_{> 0}
$$

These decreed accounting coefficients do not represent realized ratios of voluntary property transfers between independent owners:

$$
P_{\text{admin}}(m, t) \notin \mathcal{P}_{\text{realized}}(t)
$$

### Definition 3 (Managerial Payoff Decoupling and Soft Budget Constraint)
A state manager $`j \in \mathcal{I}_{\text{mgr}}`$ directs production action $`\alpha_{\text{prod}}`$ using capital inputs $`u(\alpha_{\text{prod}}, m)`$ to generate outputs $`y(\alpha_{\text{prod}}, m')`$. Accounting net revenue is defined by:

$$
\Pi_{\text{admin}}(j, t) = \sum_{m' \in \mathcal{M}} P_{\text{admin}}(m', t) \cdot y(\alpha_{\text{prod}}, m') - \sum_{m \in \mathcal{M}} P_{\text{admin}}(m, t) \cdot u(\alpha_{\text{prod}}, m)
$$

Managerial remuneration and personal physical endowment $\omega(j, t', h, m_{\text{wage}})$ are decoupled from operational performance:

$$
\Pi_{\text{admin}}(j, t) < 0 \implies \Delta \omega(j, t', h, m_{\text{wage}}) \ge 0
$$

with any accounting deficit fully covered by state fiscal transfers $\Delta \omega_{\text{subsidy}} = -\Pi_{\text{admin}}(j, t)$.

### Definition 4 (CPB Inventory Tâtonnement)
Let $D_k(P_{\text{admin}}, t)$ denote aggregate managerial input requisitions for factor $`k \in \mathcal{M}_{\text{cap}}`$, and let $S_k(t)$ denote realized available physical stock. The CPB updates accounting prices across planning periods according to:

$$
P_{\text{admin}}(k, t + \Delta t) = P_{\text{admin}}(k, t) + \kappa \cdot (D_k(P_{\text{admin}}, t) - S_k(t)), \quad \kappa > 0
$$

---

## 3. Calculation Impossibility on Capital Antichains

**Conditional concern.** When an administrative rule receives identical reports from states requiring different factor allocations, it cannot choose correctly in both. The existing Lean result does not establish that public ownership forces such identical reports. A comparison with a Lange-style price process requires its demand, reporting, adjustment, and settlement rules.

The physical antichain result says that two factor vectors need not be
coordinatewise comparable. The ordinal rank-sum result says a particular sum
of ordinal encodings is not invariant. Neither result evaluates the
administrative-price process or every price schedule it might generate.
To test this concern, the planning board needs an explicit rule for observing
demand, updating prices, assigning public inputs, compensating managers, and
allocating final goods. Reports and work choices must be strategic actions.
The current [calculation comparison register](../spec/11_strategic_calculation.md)
records these as open institutional questions.

> [!NOTE]
> The five steps above present an economic argument. The current formal theorem proves only the restricted-record implication. Its stronger institutional conclusion remains a research target.

---

## 4. Administrative Price Ceilings Induce Supply-Chain Paralysis

**Proposition.** Whenever the CPB fixes $P_{\text{admin}}(m)$ below the marginal reservation valuation of factor stewards, purposeful action mandates input withholding. This upstream withholding starves downstream production stages of physical endowments $(\omega = 0)$, causing downstream production infeasibility and systemic shortage cascades.

**Proof.**
1. An economic actor enacts an exchange or allocation action $\alpha$ if and only if $\alpha$ is purposeful $(\mathsf{P}(i, t, h, \alpha))$, which requires that the expected end dominates the baseline of refraining $(\alpha_0)$.
2. If the CPB decrees an accounting price $P_{\text{admin}}(m)$ below the actor's subjective reservation valuation for that physical factor, trading or surrendering the factor violates purposeful choice. The actor purposefully withholds the factor, enacting the inertial baseline $\alpha_0$.
3. By Chapter 11 ([Proposition 11.33](../natural_language/11_organization_firms_and_intervention.md#proposition-1133-a-ceiling-that-removes-the-sellers-gain-blocks-active-sale) and [Proposition 11.36](../natural_language/11_organization_firms_and_intervention.md#proposition-1136-withheld-supply-produces-downstream-infeasibility)), upstream price suppression induces factor withholding, resulting in an endowment collapse for downstream stages:

$$
\omega(j, t', h, m) = 0
$$

4. By Chapter 2 and Chapter 4, an action $\alpha_{\text{prod}}$ requiring input $m$ is feasible if and only if $\omega(j, t', h, m) \ge u(\alpha_{\text{prod}}, m)$. Because $\omega = 0 < u(\alpha_{\text{prod}}, m)$, downstream production becomes strictly infeasible:

$$
\alpha_{\text{prod}} \notin \mathcal{A}_{\text{feas}}(j, t', h)
$$

5. The CPB's discrete inventory adjustments $\Delta P_{\text{admin}}$ do not smoothly clear markets; they trigger physical supply-chain breakdowns and cascading factor shortages across the multi-stage production structure. $\blacksquare$

---

## 5. Equity Liability Asymmetry and Soft Budget Distortion

**Proposition.** Because state enterprise managers bear no personal equity liability for operational losses (Definition 3), managerial factor demand is decoupled from entrepreneurial prudence. Enterprise demand for capital goods becomes price-inelastic, corrupting the excess demand signal $z_k(t)$ and invalidating the CPB's tâtonnement mechanism.

**Proof.**
1. In a genuine market economy (Chapter 9 and Chapter 10), capital allocators are capitalist-entrepreneurs who risk their own physical property. Operational losses directly diminish their personal endowments:

$$
\Delta \omega(i, t', h, m_{\text{wealth}}) = \Pi(i, t) < 0
$$

This personal equity liability ruthlessly disciplines factor demand and eliminates inefficient capital stewards.
2. Under Definition 3, state managers face a soft budget constraint: operational losses $\Pi_{\text{admin}} < 0$ do not reduce managerial endowments $(\Delta \omega_{\text{wage}} \ge 0)$, and accounting deficits are compensated by state subsidies.
3. Under planning uncertainty and physical output quotas, a manager's undominated strategy is to hoard physical capital inputs $`m \in \mathcal{M}_{\text{cap}}`$ as precautionary buffers, regardless of the CPB's decreed price $`P_{\text{admin}}(m, t)`$.
4. Enterprise demand $D_k(P_{\text{admin}}, t)$ becomes structurally price-inelastic. The observable inventory discrepancy:

$$
z_k(t) = D_k(t) - S_k(t)
$$

reflects defensive bureaucratic factor hoarding rather than genuine consumer scarcity. The CPB's trial-and-error price adjustments cannot converge to equilibrium prices $\mathbf{P}^{\ast}$. $\blacksquare$

> [!NOTE]
> This theorem captures the exact institutional mechanism underlying János Kornai's soft budget constraint theorem, showing that bureaucratic insulation from property liability mechanically induces chronic, economy-wide factor shortages.

---

## 6. Institutional Synthesis and Conclusion

The Lange model fails because it treats prices as mere algebraic parameters in a system of static equations, ignoring the catallactic reality that prices are dynamic historical exchange ratios rooted in private property, personal risk liability, and subjective valuation. Without capital markets, the socialist state cannot calculate economic costs, and its administrative decrees inevitably collapse into calculational chaos and systemic shortages.
