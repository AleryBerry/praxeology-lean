# Chapter 10: Entrepreneurship, Credit, and Investment

We study entrepreneurial action under uncertainty. We distinguish belief, appraisal, realized gain, and discovery, then relate purposeful credit use to physical inventory transitions. Each result depends on the preference, menu, and outcome conditions stated with it.

## Entrepreneurial Exchange under Divergent Beliefs

Speculative exchange depends on beliefs about future outcomes. With heterogeneous plausibility orderings, exchange may be purposeful for both parties even though at least one cannot realize the anticipated gain. The conclusions are conditional on the stated belief and preference assumptions.

### Definition 10.1 (Realized Gain and Ex-Post Regret)
For an action chosen at $t$, let $R(i,\alpha,t,\tau,h)$ denote its matured outcome when evaluated at $\tau$ along history $h$, as in the projected-outcome construction of Chapter 5. The action yields **realized gain** over inaction at the later evaluation when

$$
\text{G}(i,t,\alpha,\tau,h)\iff
R(i,\alpha,t,\tau,h)\succ_{i,\tau,h}R(i,\alpha_0,t,\tau,h).
$$

It yields **ex-post regret**, in the weak sense used for this theorem, when that gain predicate fails:

$$
R_{\mathrm{post}}(i,t,\alpha,\tau,h)\iff
\neg\text{G}(i,t,\alpha,\tau,h).
$$

With an incomplete preference relation, failure to strictly prefer the trade outcome does not imply strict preference for inaction. The stronger, purely ordinal regret predicate is

$$
\text{OrdinalRegret}(i,t,\tau,h,\alpha)\iff
R(i,\alpha_0,t,\tau,h)\succ_{i,\tau,h}R(i,\alpha,t,\tau,h).
$$

The distinction matters: the first says that a gain has not been demonstrated; the second says the alternative is strictly preferred.

### Definition 10.2 (Speculative Exchange under Opposing Beliefs)
Let $E\subseteq\mathcal{H}$ describe a future event. Agent $i$ believes $E$ at $t$ when $E$ holds on every minimally plausible history for $i$ at $t$; belief in $\neg E$ is defined in the same way. A **speculative exchange under opposing beliefs** between distinct agents $i$ and $j$, with actions $\alpha_i$ and $\alpha_j$ at $t$ maturing at $\tau$, satisfies:

1. $t<\tau$;
2. agent $i$ believes $E$ and agent $j$ believes $\neg E$ at $t$; and
3. on every realized history, $E$ rules out realized gain for $j$, while $\neg E$ rules out realized gain for $i$.

The third condition is a payoff assumption of this model. It encodes the opposing speculative positions; it is not derived merely from the agents holding different beliefs.

### Theorem 10.3 (At Least One Trader Fails to Realize Gain)
In any speculative exchange satisfying Definition 10.2, for every realized history $h$,

$$
R_{\mathrm{post}}(i,t,\alpha_i,\tau,h)
\quad\vee\quad
R_{\mathrm{post}}(j,t,\alpha_j,\tau,h).
$$

**Proof.** Either $E(h)$ or $\neg E(h)$. In the first case the model's payoff condition rules out $j$'s realized gain; in the second it rules out $i$'s realized gain. This is exactly the stated disjunction by Definition 10.1. $\blacksquare$

The theorem establishes failure of mutual realized gain under the specified opposing-payoff structure. Belief disagreement alone does not assert that both trades were purposeful or expected to yield a gain. To derive ex-ante gains, add purposeful non-inertial actions; to identify one trader as the accurate forecaster and the other as a strict loser, we also need a further decisiveness premise.

### Proposition 10.4 (Shared Plausibility Excludes Opposing Beliefs)
If the agents share even one minimally plausible history, they cannot respectively believe $E$ and $\neg E$ when belief means truth throughout one's minimally plausible set.

**Proof.** At the shared history, the two belief conditions imply both $E$ and $\neg E$. Contradiction. $\blacksquare$

Thus speculative exchange in this model requires divergent plausibility judgments on the contested event. The proposition concerns these belief definitions; it does not say that every transaction requires disagreement about every feature of the future.

### Theorem 10.5 (Conditional Entrepreneurial Profit-and-Loss Dichotomy)
Suppose the actual event determines which participant gains: $E(h)$ implies realized gain for $i$, and $\neg E(h)$ implies realized gain for $j$. Together with Definition 10.2, the realized outcome has exactly the following form:

$$
\bigl(E(h)\wedge \text{Gain}_i\wedge\text{Loss}_j\bigr)
\quad\vee\quad
\bigl(\neg E(h)\wedge\text{Gain}_j\wedge\text{Loss}_i\bigr).
$$

**Proof.** Either $E(h)$ or $\neg E(h)$. In the first case the decisiveness premise gives gain to $i$, while Definition 10.2 rules out gain to $j$. In the second case the premise gives gain to $j$, while Definition 10.2 rules out gain to $i$. By Definition 10.1, failure of realized gain is exactly the stated weak loss predicate. $\square$

Here $`\text{Loss}_k`$ means failure of $k$'s realized-gain predicate. Theorem 10.5 supplies the single-period realized-outcome partition once the decisive event condition is fixed. Proposition 10.4 supplies a distinct belief-side result: shared plausibility rules out opposing beliefs about that event. If each non-inertial trade action was purposeful, Chapter 3's preference conditions add an ex-ante gain over inaction for each trader. A multi-period capital-reallocation model can compose these results with an explicit stock-transition schedule across repeated exchanges.

## Kirzner: Discovery beyond the Contemplated Menu

Prediction error and discovery are distinct. Error compares an anticipated outcome with a realized one; discovery adds an opportunity that was absent from the earlier contemplated menu. We first make this distinction within a fixed set of action names, then consider what changes when the description itself is enlarged.

### Definition 10.6 (Overlooked Physical Opportunity)
An **intertemporal discovery context** at action moment $t_{\text{act}}$ and maturation moment $t_{\text{mat}}$ contains a physically available action set $A_{\text{phys}}$, a chosen action $\alpha_{\text{chosen}}$, and an overlooked action $\alpha_{\text{novel}}$, such that

$$
\begin{aligned}
&\alpha_{\text{chosen}}\in A_{\text{cont}}(i,t_{\text{act}},h),\\
&\alpha_{\text{novel}}\in A_{\text{phys}},\qquad
  \alpha_{\text{novel}}\notin A_{\text{cont}}(i,t_{\text{act}},h),\\
&\text{maturedOutcome}(i,\alpha_{\text{novel}},t_{\text{act}},t_{\text{mat}},h)
  \succ_{i,t_{\text{mat}},h}
  \text{maturedOutcome}(i,\alpha_{\text{chosen}},t_{\text{act}},t_{\text{mat}},h).
\end{aligned}
$$

The first action is contemplated, while the second is in the separately supplied physical set but absent from the actor's considered set. Because the maturation model requires feasible actions to be contemplated, this external physical set must not be identified with its internal feasible menu. The last inequality records a later comparison. The context does not by itself assert that the chosen action was ex-ante purposeful; that can be added as a premise.

### Theorem 10.7 (Prediction Error and Discovery Regret Are Distinct)
Suppose the chosen action is ex-ante purposeful, the actual history is the sole minimally plausible history, preferences are stationary, and an overlooked physical opportunity satisfies Definition 10.6. Then no uniformly available feasible action is strictly preferred to the chosen action when evaluated through the projected ex-ante outcomes at maturation, while the overlooked action is preferred to the chosen action on the realized history.

**Proof.** If a uniformly available feasible action were strictly preferred to the chosen action at the sole plausible history, stationarity would make it strictly preferred in the ex-ante comparison as well. It would then be a robustly available rival that strictly dominates the chosen action, contradicting ex-ante undominatedness. The overlooked action's strict preference on the realized history is an explicit premise of Definition 10.6. Thus correct expectations about the realized history do not eliminate regret caused by an incomplete contemplated menu. $\square$

Availability, awareness, and know-how are separate conditions: membership in a contemplated menu neither proves robust feasibility nor supplies a uniformly successful action across epistemic alternatives. The paired result makes two sources of error visible. A contemplated alternative that becomes better may reflect surprise or a risk across plausible histories. An overlooked action may become salient through alertness even when the actual history was expected. These are different failures: one concerns forecasts, the other the set of alternatives considered.

### Definition 10.8 (Bounded Contemplation and Kirznerian Alertness Operator)
In an Action Frame $\mathcal{W}$, a **bounded contemplation context** $`B = \langle \mathcal{A}_{\text{phys}}, \mathcal{A}_{\text{cont}}, \text{End\_of}, \succ \rangle`$ models the agent's finite cognitive awareness:
1. $`\mathcal{A}_{\text{phys}} \subseteq \mathcal{A}`$ is the finite set of physically available actions whose input requirements do not exceed current physical endowment.
2. $`\mathcal{A}_{\text{cont}} \subseteq \mathcal{A}`$ is the finite set of actions actively contemplated by the actor.
3. The effective choice menu $`\mathcal{A}_{\text{eff}}`$ is their intersection:

$$
\mathcal{A}_{\text{eff}} = \mathcal{A}_{\text{phys}} \cap \mathcal{A}_{\text{cont}}
$$

The **Kirznerian Alertness Operator** records the pure discovery of an unconsidered opportunity $`\alpha^{\ast} \notin \mathcal{A}_{\text{cont}}`$, expanding the contemplated set without altering the physical endowment:

$$
\text{KirznerAlertnessOperator}(B, \alpha^{\ast}) = \mathcal{A}_{\text{cont}} \cup \{ \alpha^{\ast} \}
$$

The resulting expanded effective menu is $`\mathcal{A}_{\text{eff}}^{+} = \mathcal{A}_{\text{phys}} \cap (\mathcal{A}_{\text{cont}} \cup \{ \alpha^{\ast} \})`$. Pure entrepreneurial alertness expands the realm of purposeful human action without requiring prior physical expenditure or alterations of technological constraints.

### Theorem 10.9 (Kirznerian Alertness Discovery Expansion)
Suppose $\alpha^{\ast}$ is physically available ( $`\alpha^{\ast} \in \mathcal{A}_{\text{phys}}`$ ) but unconsidered ( $`\alpha^{\ast} \notin \mathcal{A}_{\text{cont}}`$ ). If its realized end is strictly preferred to the end of every previously contemplated action ( $`\forall \beta \in \mathcal{A}_{\text{cont}}, \text{End\_of}(\alpha^{\ast}) \succ \text{End\_of}(\beta)`$ ) and distinct from them, then under the Kirznerian alertness operator:
1. The effective choice menu strictly expands: $`\mathcal{A}_{\text{eff}} \subsetneq \mathcal{A}_{\text{eff}}^{+}`$.
2. The contemplated menu strictly expands: $`\mathcal{A}_{\text{cont}} \subsetneq \mathcal{A}_{\text{cont}} \cup \{ \alpha^{\ast} \}`$.
3. $\alpha^{\ast}$ belongs to the expanded effective menu: $`\alpha^{\ast} \in \mathcal{A}_{\text{eff}}^{+}`$.
4. Every old action in $`\mathcal{A}_{\text{cont}}`$ is strictly dominated by $\alpha^{\ast}$.
5. No action in the expanded menu is strictly preferred to $\alpha^{\ast}$:

$$
\forall \beta \in \mathcal{A}_{\text{cont}} \cup \{ \alpha^{\ast} \}, \quad \neg(\text{End\_of}(\beta) \succ \text{End\_of}(\alpha^{\ast}))
$$

6. $\alpha^{\ast}$ is the unique undominated action in the expanded menu:

$$
\forall \gamma \in \mathcal{A}_{\text{cont}} \cup \{ \alpha^{\ast} \}, \quad (\forall \beta, \neg(\text{End\_of}(\beta) \succ \text{End\_of}(\gamma))) \implies \gamma = \alpha^{\ast}
$$

**Proof.** Because $`\alpha^{\ast} \in \mathcal{A}_{\text{phys}}`$ and $`\alpha^{\ast} \notin \mathcal{A}_{\text{cont}}`$, $`\alpha^{\ast} \notin \mathcal{A}_{\text{eff}}`$. Thus $`\mathcal{A}_{\text{eff}}^{+} = \mathcal{A}_{\text{eff}} \cup \{ \alpha^{\ast} \}`$ is a strict superset of $`\mathcal{A}_{\text{eff}}`$, and $`\mathcal{A}_{\text{cont}} \cup \{ \alpha^{\ast} \}`$ is a strict superset of $`\mathcal{A}_{\text{cont}}`$. By hypothesis, $\alpha^{\ast}$ strictly dominates every $`\beta \in \mathcal{A}_{\text{cont}}`$. Asymmetry of preference rules out the reverse comparison $`\text{End\_of}(\beta) \succ \text{End\_of}(\alpha^{\ast})`$, and irreflexivity rules out self-preference. Hence $\alpha^{\ast}$ is undominated in $`\mathcal{A}_{\text{cont}} \cup \{ \alpha^{\ast} \}`$. If any $\gamma$ is undominated, it cannot be an element of $`\mathcal{A}_{\text{cont}}`$ (since $\alpha^{\ast}$ dominates it), forcing $\gamma = \alpha^{\ast}$. $\blacksquare$

## Purposeful Fiduciary Issuance and Loan Origination

The next results concern any action model satisfying the stated conditions. A note-issuance event is a purposeful, enacted, non-trade action at a moment with a specified immediate successor on the same history. It produces a positive principal quantity of a money good, uses none of that money or a distinct reserve good, and leaves the reserve good's yield at zero. Other agents enact the passive action at that moment. These conditions make note printing a production transition in the physical inventory account.

### Proposition 10.10 (Physical Effects of Note Issuance)

Under those issuance conditions, at the next moment:

1. the issuer's money stock has increased by exactly the principal;
2. the issuer's reserve stock is unchanged;
3. every other agent's money stock is unchanged;
4. money held by agents other than the issuer is unchanged; and
5. total money stock has increased by exactly the principal.

**Proof.** Apply the inventory balance to the issuer's money and reserve, using the specified inputs and yields. Apply it to each other agent, whose passive action uses and yields nothing. Summing the resulting equalities gives the final two statements. $\square$

The first statement concerns the issuer's inventory. The fourth concerns the sum of all other agents' stocks, so this printing step alone does not put the new notes into their hands.

### Proposition 10.10a (Spot-Purchase Feasibility and Impossibility of Additive Aggregation)

In any action model, accepting a spot purchase of $q_A$ units of commodity $m_A$ at price $P$ in exchange for medium $m$ is feasible for a buyer at $(t, h)$ if and only if the acceptance action is contemplated and the buyer's physical endowment of that specific medium satisfies $P \le \omega_{\mathrm{buyer}}(t, h, m)$.

Consequently:
1. **Cross-Medium Non-Additivity:** If an agent holds two distinct media $m_1 \neq m_2$ such that $\omega_{\mathrm{buyer}}(t, h, m_1) < P$ and $\omega_{\mathrm{buyer}}(t, h, m_2) < P$, then even if $P \le \omega_{\mathrm{buyer}}(t, h, m_1) + \omega_{\mathrm{buyer}}(t, h, m_2)$, accepting the spot purchase is infeasible in both media and cannot be enacted as a purposeful action.
2. **Cross-Agent Non-Additivity:** If two buyers each hold less than $P$ of medium $m$, then even if their combined stock satisfies $P \le \omega_{b_1}(t, h, m) + \omega_{b_2}(t, h, m)$, neither buyer can feasibly or purposefully enact the spot purchase.

**Proof.** For the equivalence, the feasibility coupling requires contemplation and that the used means do not exceed the endowment in any commodity. An acceptance action uses exactly $P$ units of medium $m$ and zero units of all other commodities. The condition for all other commodities is $0 \le \omega_{\mathrm{buyer}}(t, h, m')$, which holds universally. Thus feasibility reduces to contemplation and $P \le \omega_{\mathrm{buyer}}(t, h, m)$. For cross-medium and cross-agent non-additivity, since each medium balance is strictly less than $P$, the necessary condition $P \le \omega$ fails for each action individually. Because feasibility is a prerequisite for purposeful action, neither action can be purposeful. $\square$

### Proposition 10.10b (Total Media Conservation and Lender Menu-Stripping in Commodity Credit)

In a matched credit advance where the lender transfers principal $P$ of medium $m$ to the borrower in exchange for collateral custody, and non-participating agents remain passive:
1. Total spendable media of medium $m$ summed across all agents is strictly conserved:

$$
\sum_{a \in \mathcal{I}} \omega_a(t', h, m) = \sum_{a \in \mathcal{I}} \omega_a(t, h, m).
$$

2. The lender's money stock contracts by $P$, which strictly strips any tight money-using action (an action whose money requirement equaled the lender's pre-advance cash balance) from the lender's feasible menu.

**Proof.** By the bilateral transfer law, the borrower's stock of medium $m$ increases by $P$ while the lender's stock decreases by $P$. Their pairwise sum is conserved. Because bystanders enact the passive baseline, their stocks are unchanged. Summing over the population preserves total media. Because $P > 0$, the lender suffers a strict stock contraction in medium $m$. Any action requiring the full initial balance now exceeds the contracted balance and is stripped from the lender's feasible menu. $\square$

A loan origination links such an issuance to a matched credit advance. The lender is the issuer; the money and principal agree across the issuance and loan records; the advance occurs immediately after issuance on the same history; and other nonparticipants are passive during the advance. The loan terms also distinguish the lender and borrower and specify the promised repayment factor. The associated inventory run consists of note production followed by the matched offer and acceptance. The borrower is passive during note printing and receives the money only at the advance.

### Definition 10.11 (Principal Ledger)

A finite principal ledger is a finite list of loan-originations satisfying the preceding matching conditions. For each event, record the issued principal as an external note liability and the advanced principal as a loan asset. Repayment, default, and interest entries are outside this ledger definition.

### Proposition 10.12 (Principal Equality in the Origination Ledger)

For every finite principal ledger, the sum of recorded loan principal equals the sum of recorded external note principal. Appending one certified origination increases both totals by the same principal.

**Proof.** Each origination record equates the issuance principal with the loan principal. Summing these equalities over the finite list proves the first assertion. Appending an event adds its principal to both sums, proving the second. $\square$

The ledger identity is an accounting statement about certified origination events. It does not assert that every bank asset equals every bank liability, that reserves equal notes, or that all liabilities are redeemable. Those conclusions would require additional categories and lifecycle events.

### Proposition 10.12a (Reserve Invariance, Redemption Infeasibility, and the Fiduciary Shortfall)

Under a certified fiduciary origination where loan collateral is distinct from the reserve commodity:
1. The issuer's physical reserve stock at the conclusion of the origination remains strictly equal to its pre-issuance reserve stock:

$$
\omega_{\mathrm{issuer}}(t', h, m_{\mathrm{reserve}}) = \omega_{\mathrm{issuer}}(t, h, m_{\mathrm{reserve}}).
$$

2. Whenever redemption claims $q$ for the reserve commodity exceed the issuer's physical reserve stock ( $q > \omega_{\mathrm{issuer}}(t, h, m_{\mathrm{reserve}})$ ), accepting the redemption is resource-infeasible and cannot be enacted as a purposeful action.
3. If the issuer's opening reserve stock weakly covered or equaled circulating fiduciary notes, the origination strictly expands circulating fiduciary notes beyond the unchanged reserve stock:

$$
\omega_{\mathrm{issuer}}(t', h, m_{\mathrm{reserve}}) < \text{circulating media of } m_{\mathrm{money}} \text{ at } (t', h),
$$

creating an unbacked redemption shortfall where full par redemption of circulating fiduciary notes is physically impossible.

**Proof.** Note printing produces money without using or yielding reserves, leaving the issuer's reserve unchanged. During the matched credit advance, the traded commodities are money and collateral, which are both distinct from the reserve commodity; thus bilateral transfer leaves the issuer's reserve unchanged. This proves the first claim. By Proposition 10.10a, accepting redemption of $q$ notes for $q$ units of reserve requires $q \le \omega_{\mathrm{issuer}}(t, h, m_{\mathrm{reserve}})$; when this fails, acceptance is infeasible and non-purposeful, proving the second claim. For the third claim, fiduciary origination increases circulating fiduciary notes by the positive principal $P > 0$ while leaving reserves unchanged; adding $P$ to the opening circulating media strictly exceeds the reserve balance. $\square$

## Repayment, Collateral, and Default

Origination is only the opening event of a loan. We now add the contractual terms and distinguish repayment from an unpaid maturity. This lets us describe what the model records after the principal has been advanced, without treating the origination ledger as a complete balance sheet or a theory of every lending arrangement.

### Definition 10.13 (Collateralized Loan Terms)

A collateralized loan specifies a lender and a distinct borrower, a money good and a distinct collateral good, a positive principal $P$, a positive collateral quantity $Q$, a maturity, and a nonnegative net repayment factor $r$. Define the gross repayment factor and promised repayment by

$$
g=1+r,
\qquad
R=P g=P(1+r).
$$

The **nominal premium** above principal is

$$
I=P r,
$$

so that $P+I=R$. These are nominal quantities in the stated means. They do not by themselves adjust repayment for changes in purchasing power or establish that either party values the contract in a particular way.

### Proposition 10.14 (Repayment Covers Principal and Adds the Stated Premium)

For positive $P$ and nonnegative $r$, the promised repayment is at least the principal and satisfies $P+I=R$. The premium is zero exactly when repayment equals principal.

**Proof.** From $g=1+r$ and $r\ge0$, we have $g\ge1$, so $P\le Pg=R$. Also $P+I=P+Pr=P(1+r)=R$. Since $P>0$, $Pr=0$ exactly when $r=0$, which is also exactly when $R=P(1+r)=P$. $\square$

The loan's contractual status is separate from its physical inventory. The status records whether the obligation is outstanding, repaid, or defaulted; the inventory equations record where money and collateral are held.

The formal distinction is also reflected in the evidence types. An **enacted loan quote** consists of the contract terms and a matched, enacted advance. It does not contain a repayment event. A later repayment conclusion takes separate `CreditRepayment` evidence for that advance; an unpaid-maturity conclusion instead takes separate `UnpaidMaturity` evidence. Thus the promised amount in a contract is not itself evidence that the borrower paid it. Rate comparisons derived from origination and market-clearing evidence remain distinct from comparisons of actually observed repayments.

### Definition 10.15 (Loan Status Transitions)

We represent one loan by the following permitted transitions:

| Status before the event | Event | Status after the event |
|---|---|---|
| not yet advanced | matched advance | outstanding |
| outstanding | matched repayment before maturity | repaid |
| outstanding | maturity without repayment | defaulted |

The transition relation records these three cases. It does not permit a repayment event before the advance or a second repayment after the obligation has been discharged.

### Definition 10.16 (Matched Repayment)

A repayment is a purposeful exchange on the advance's history, after the advance and before maturity, in which the borrower transfers the promised amount $R$ of money to the lender and receives the specified quantity $Q$ of collateral. The exchange occurs over an immediate temporal transition.

By the paired inventory equations, a matched repayment increases the lender's money stock by $R$ and returns $Q$ units of collateral to the borrower's stock. These physical transfers do not alone prove that the borrower can repay or that repayment is purposeful; the matched action and its appraisal are explicit evidence.

### Definition 10.17 (Collateral Custody and Unpaid Maturity)

A collateral-custody trace runs from the moment after the advance to maturity along the same history. If the lender neither uses nor yields the collateral over this trace, the inventory balance keeps the lender's collateral stock unchanged. An **unpaid maturity** records both such custody and the absence of any matched repayment before maturity.

We take non-repayment as evidence in this definition. We do not infer it merely from the absence of a feasible repayment action, since that would require additional premises about the borrower's resources and available choices.

### Proposition 10.18 (Unpaid Maturity Classifies the Outstanding Loan as Defaulted)

If a loan remains unpaid at maturity under the stated custody trace, its status transition is from outstanding to defaulted, and the lender still holds the collateral quantity recorded after the advance.

**Proof.** The custody trace has zero total use and zero total yield of collateral, so the inventory-run balance makes the lender's collateral stock at maturity equal to its stock immediately after the advance. The unpaid-maturity condition supplies the event that classifies the outstanding obligation as defaulted. $\square$

The model records default status and retained collateral under these conditions. It does not add a further rule for selling collateral, recovering a shortfall, or distributing losses among other creditors.

The issuance, loan, and ledger statements are defined over any action model with the relevant physical transition and purposeful-action structure.

---

## The Praxeological Theory of Money Supply and Its Measurement

The introduction of fractional-reserve credit origination and secondary debt contracts raises a foundational catallactic question: how is the "supply of money" defined and measured within an economy characterized by multiple media, banking institutions, and credit instruments?

In mainstream macroeconomics, monetary authorities compile statistical aggregates ($M_1, M_2, M_3, M_4$, MZM) by classifying financial claims into arbitrary administrative "liquidity" tiers. In Austrian monetary economics, scholars have sought to isolate the "True Money Supply" (TMS) by restricting the aggregate to the general medium of exchange and its immediate par substitutes.

From the axiomatic floor of praxeology, any attempted scalar aggregation of money commits fatal physical and operational category errors. Action-frame feasibility operates on concrete, disaggregated holdings of specific media at specific decision nodes. Below, we formalize the theoretical structure of monetary measurement, demonstrate why scalar aggregates fail, and construct the praxeological alternative: a disaggregated coordinate vector of observable stocks and solvency boundaries.

### The Scalar Aggregation Fallacy

An aggregate scalar measure of money assumes that an economy's purchasing media can be represented as a single natural number:

$$
\mathcal{M}(t, h) \in \mathbb{N}.
$$

By Proposition 10.10a (Spot-Purchase Feasibility and Impossibility of Additive Aggregation), spot-market acceptance of an offer at price $P$ in medium $m$ is feasible for a buyer if and only if:

$$
P \le \omega_{\mathrm{buyer}}(t, h, m).
$$

Two insurmountable physical non-additivities immediately refute scalar representation:
1. **Cross-Medium Non-Additivity:** If an agent holds positive balances across distinct media $m_1 \neq m_2$, the sum $\omega(m_1) + \omega(m_2)$ cannot clear a transaction priced in either medium alone. Summing heterogeneous media into an aggregate scalar attributes spot-purchase feasibility to actors whose physical action menus are strictly contracted.
2. **Cross-Agent Non-Additivity:** If two distinct agents $a_1 \neq a_2$ hold cash balances of the same medium, their sum $\omega_{a_1}(m) + \omega_{a_2}(m)$ cannot clear a spot purchase priced at $P > \max\lbrace \omega_{a_1}(m), \omega_{a_2}(m) \rbrace$. Money exists solely in discrete, localized cash holdings of individual actors across a trading network (Proposition 9.24). A single aggregate scalar erases the topological distribution of balances that determines which exchanges can be executed.

### Critique of the Central Bank Liquidity Hierarchy ($M_1 \to M_4$)

Central banks assemble monetary aggregates along a supposed continuum of "liquidity":
- **$M_1$**: Physical currency in circulation outside banks and checkable demand deposits.
- **$M_2$**: $M_1$ plus small-denomination time deposits (certificates of deposit) and retail money market mutual fund balances (MMMFs).
- **$M_3$**: $M_2$ plus large-denomination time deposits, institutional money market funds, term repurchase agreements (repos), and Eurodollar deposits.
- **$M_4$ / Broad Money**: $M_3$ plus commercial paper, short-term Treasury bills, and bankers' acceptances.
- **MZM (Money of Zero Maturity)**: $M_2$ minus small time deposits plus all institutional money market funds, aiming to measure assets redeemable at par on demand.

The entire hierarchy embodies three structural category errors:

#### 1. Credit Double-Counting and Violation of Physical Conservation
By Proposition 10.10b (Commodity Credit Conservation), a pure credit advance transfers a quantity $P$ of medium $m$ from lender to borrower in exchange for a future repayment contract. Total media across the population is strictly conserved:

$$
\sum_{a \in \mathcal{I}} \omega_a(t', h, m) = \sum_{a \in \mathcal{I}} \omega_a(t, h, m).
$$

The lender's cash balance contracts by $P$, and any action requiring the lender's pre-advance cash balance is stripped from the lender's feasible menu. The lender holds a contractual claim maturing in the future; the lender does not hold spendable money.

By adding time deposits, repurchase agreements, and commercial paper to $M_1$, broader aggregates (including $M_2$, $M_3$, and $M_4$) count both the spendable cash transferred to the borrower and the deferred credit claim held by the lender. They record $2 \cdot P$ of "money" where only $P$ of physical medium exists, fabricating phantom purchasing power that violates the physical conservation law.

#### 2. Conflation of Investment Equity with Monetary Media
$M_2, M_3$, and MZM include shares in money market mutual funds. An investor in a mutual fund does not hold money or a deposit; the investor holds equity shares in an investment trust whose assets consist of short-term debt instruments.

By Proposition 10.10a, accepting a spot purchase requires the delivery of a concrete medium of exchange. Mutual fund shares cannot directly clear spot transactions. Even when check-writing privileges are attached, settling a check requires the fund to sell an underlying money market instrument to obtain central bank reserves or commercial bank deposits. Counting investment trust shares as money confuses an asset requiring prior secondary liquidation with the medium of exchange itself.

#### 3. Arbitrary Exclusion of Sovereign Cash Balances
While counting illiquid debt contracts and equity shares, central banks exclude the cash balance held by the sovereign Treasury at the central bank (the Treasury General Account). The sovereign's cash balance consists of central bank reserve media that bids for labor, commodities, and capital equipment in exactly the same way as private cash balances. Omitting sovereign cash creates an ungrounded institutional asymmetry that distorts the recorded stock of circulating media.

### Formal Evaluation of the Rothbard-Salerno True Money Supply (TMS)

To eliminate the credit double-counting of $M_2$ and $M_3$, Austrian economists formulated the True Money Supply (TMS), defined as:
- Currency in circulation outside banks;
- Demand deposits at commercial banks;
- Other checkable deposits (NOW accounts, ATS accounts);
- Savings deposits and money market deposit accounts (MMMDAs);
- Sovereign demand deposits at commercial banks and the central bank;
- *Excluded:* Small and large time deposits, repurchase agreements, commercial paper, and money market mutual fund shares.

#### 1. Theoretical Soundness: Credit Conservation and Sovereign Inclusion
TMS adheres to Proposition 10.10b by recognizing that pure credit transfers (time deposits) do not expand total media and must be excluded. It also correctly includes sovereign operating balances, preserving the physical conservation of base media.

#### 2. The Four Inherent Theoretical Contradictions of TMS as a Scalar Measure
Despite its advantages over central bank aggregates, TMS cannot be derived as a valid scalar measure within our formal action system:

1. **Cross-Medium Summation:** TMS adds distinct physical and institutional commodities into a single sum:

$$
\text{TMS} = \sum_{a} \omega_a(m_{\mathrm{cash}}) + \sum_{a} \omega_a(m_{\mathrm{dep}}) + \sum_{a} \omega_a(m_{\mathrm{sav}}) + \omega_{\mathrm{treas}}(m_{\mathrm{treas}}).
$$

By Proposition 10.10a, spot-purchase feasibility requires sufficient holdings of the *specific* tender medium required by the seller. Summing heterogeneous media across distinct legal classifications attributes aggregate purchasing capacity to actors that cannot be realized in any purposeful action.

2. **The Fiduciary Par-Redemption Fallacy:** TMS justifies adding commercial bank deposits to physical currency at 1:1 par value by treating demand deposits as "warehouse receipts" or "money substitutes" that are instantly redeemable on demand.

In a 100% reserve system, note liabilities are fully backed warehouse claims. But in a fractional-reserve banking system, by Proposition 10.12a, fiduciary loan origination creates new circulating liabilities without expanding the physical reserve stock:

$$
\omega_{\mathrm{issuer}}(t', h, m_{\mathrm{reserve}}) = \omega_{\mathrm{issuer}}(t, h, m_{\mathrm{reserve}}), \qquad \text{circulating notes at } (t', h) = \text{circulating notes at } (t, h) + P.
$$

Whenever circulating fiduciary media exceeds the physical reserve, simultaneous par redemption is resource-infeasible for the banking system (Proposition 10.12a). Fiduciary bank liabilities carry structural default risk and liquidity exposure; treating them as physical clones of base money assumes an economic property—universal par redeemability—that physical inventory transitions prove to be impossible.

3. **Gresham Par-Circulation Collapse:** TMS assumes that base currency and fractional-reserve bank deposits circulate side-by-side as a homogeneous pool.

However, by Gresham's Law (Theorems 11.17–11.18), when two distinct media are legally pegged at a fixed nominal parity, purposeful actors hoard the sounder base commodity and tender exclusively the overvalued, risk-exposed bank media:

$$
\mathcal{C}(m_{\mathrm{good}}) = \emptyset.
$$

Under distress, base money ceases to circulate as tender, destroying the empirical basis for adding them together.

4. **Cross-Agent Non-Additivity and Static Lists:** TMS compresses balances across all individuals into a national scalar, obscuring network topology (Definition 9.5) and Cantillon purchasing power dilution (Proposition 9.24). Furthermore, medium-of-exchange status is an endogenous property that emerges and dissolves through purposeful choice (Theorems 9.4, 9.10), rather than a permanent administrative category.

### The Praxeological Monetary Measure: Disaggregated Vector Accounting

Praxeological theory rejects the compression of monetary reality into an artificial scalar aggregate. At the most fundamental level, action-frame feasibility operates on concrete, localized holdings. The primary praxeological monetary state is therefore the full agent-by-medium **Endowment Matrix**:

$$
\boldsymbol{\Omega}(t, h) = \big[ \omega_a(t, h, m) \big]_{a \in \mathcal{I}, m \in \mathcal{M}}.
$$

Because individual commercial banks $`b \in \mathcal{I}_{\mathrm{banks}}`$ issue distinct checkable deposit liabilities, each bank's deposit is a distinct economic medium $`m_{\mathrm{fid}, b} \in \mathcal{M}`$.

To audit system-wide physical conservation and macro redemption boundaries without losing structural clarity, praxeology defines a coarse-grained **Sectoral Monetary Projection Vector** over the disjoint partition of economic actors: the non-bank public $`\mathcal{I}_{\mathrm{pub}}`$, the commercial banking sector $`\mathcal{I}_{\mathrm{banks}}`$, and the sovereign Treasury $`\{\mathrm{treas}\}`$ (where $`\mathcal{I} = \mathcal{I}_{\mathrm{pub}} \sqcup \mathcal{I}_{\mathrm{banks}} \sqcup \{\mathrm{treas}\}`$ ):

### Definition 10.19 (The Sectoral Monetary Projection Vector and Base Partition)
At any decision index $\langle t, h \rangle$, the sectoral monetary structure of an economy is represented by the coordinate vector:

$$
\mathbf{M}(t, h) = \big\langle M_{\mathrm{cash}}^{\mathrm{pub}}(t, h), \; M_{\mathrm{fid}}(t, h), \; R_{\mathrm{issuer}}(t, h), \; M_{\mathrm{treas}}(t, h), \; C_{\mathrm{pure}}(t, h) \big\rangle,
$$

where:
1. $`M_{\mathrm{cash}}^{\mathrm{pub}}(t, h) = \sum_{a \in \mathcal{I}_{\mathrm{pub}}} \omega_a(t, h, m_{\mathrm{reserve}})`$ is the physical base currency held outside banks and the Treasury.
2. $`M_{\mathrm{fid}}(t, h) = \sum_{b \in \mathcal{I}_{\mathrm{banks}}} \sum_{a \neq b} \omega_a(t, h, m_{\mathrm{fid}, b})`$ is the aggregate circulating checkable deposit liability issued across all commercial banks.
3. $`R_{\mathrm{issuer}}(t, h) = \sum_{b \in \mathcal{I}_{\mathrm{banks}}} \omega_b(t, h, m_{\mathrm{reserve}})`$ is the physical stock of base reserves held in commercial banking custody.
4. $M_{\mathrm{treas}}(t, h) = \omega_{\mathrm{treas}}(t, h, m_{\mathrm{reserve}})$ is the sovereign operating cash balance held at the central bank.
5. $C_{\mathrm{pure}}(t, h)$ is the aggregate outstanding principal volume of pure commodity credit contracts (term debt, small and large time deposits, commercial paper).

By the disjoint partition theorem of finite sets, total physical base money in the economy satisfies the exact three-sector conservation identity:

$$
M_{\mathrm{base}}^{\mathrm{total}}(t, h) = \sum_{a \in \mathcal{I}} \omega_a(t, h, m_{\mathrm{reserve}}) = M_{\mathrm{cash}}^{\mathrm{pub}}(t, h) + R_{\mathrm{issuer}}(t, h) + M_{\mathrm{treas}}(t, h).
$$

### Proposition 10.19a (Macro-Sum Underdetermination, Cross-Bank Non-Fungibility, and Tier Reserve Asymmetry)
1. **Macro-Sum Underdetermination:** A macro aggregate cash sum $\sum_{a \in \mathcal{I}} \omega_a(t, h, m)$ does not determine whether any individual agent can feasibly or purposefully enact a spot purchase of price $P$. If $P > \max_{a} \omega_a(t, h, m)$, the spot purchase is infeasible for every agent in the economy, even if the aggregate cash sum satisfies $\sum_{a} \omega_a(t, h, m) \ge P$.
2. **Cross-Bank Non-Fungibility:** Deposits issued by distinct commercial banks $b_1 \neq b_2$ are distinct media ($m_{\mathrm{fid}, b_1} \neq m_{\mathrm{fid}, b_2}$). If bank $b_1$ experiences a liquidity shortfall ($R_{b_1} < q$), accepting a redemption demand of $q$ is resource-infeasible for bank $b_1$, regardless of whether aggregate bank reserves satisfy $\sum_{b} R_b \ge q$.
3. **Bank-Tier Partition and Asymmetric Reserve Concentration:** Partitioning the commercial banking sector into disjoint institutional tiers (such as large money-center banks $`\mathrm{Tier}_1`$ and regional/community banks $`\mathrm{Tier}_2`$) partitions bank custodial reserves additively: $`R_{\mathrm{issuer}}(t, h) = R_{\mathrm{Tier}_1}(t, h) + R_{\mathrm{Tier}_2}(t, h)`$. If reserve coverage is asymmetrically concentrated in the first tier ( $`R_{\mathrm{Tier}_2} \cdot M_{\mathrm{fid}, \mathrm{Tier}_1} < R_{\mathrm{Tier}_1} \cdot M_{\mathrm{fid}, \mathrm{Tier}_2}`$ ), the second tier's local coverage ratio strictly lags the consolidated system ratio:
   $`\rho_{\mathrm{Tier}_2}(t, h) = \frac{R_{\mathrm{Tier}_2}(t, h)}{M_{\mathrm{fid}, \mathrm{Tier}_2}(t, h)} < \frac{R_{\mathrm{Tier}_1}(t, h) + R_{\mathrm{Tier}_2}(t, h)}{M_{\mathrm{fid}, \mathrm{Tier}_1}(t, h) + M_{\mathrm{fid}, \mathrm{Tier}_2}(t, h)} = \rho_{\mathrm{agg}}(t, h)`$.
   If an individual regional bank $`b_2 \in \mathrm{Tier}_2`$ faces a redemption run $q > R_{b_2}(t, h)$, spot redemption is resource-infeasible and non-purposeful for $b_2$, even when aggregate reserves across all tiers satisfy $`R_{\mathrm{issuer}}(t, h) \ge q`$.

**Proof.** The first claim follows from Proposition 10.10a (Cross-Agent Non-Additivity): spot-purchase feasibility requires individual endowment coverage $P \le \omega_a(m)$; when individual coverage fails, no purposeful spot purchase can be enacted. The second claim follows from Proposition 10.12a applied to bank $b_1$: accepting a redemption of $q$ units of reserve requires $q \le \omega_{b_1}(m_{\mathrm{reserve}})$; when this fails, acceptance is resource-infeasible and non-purposeful for $b_1$, independent of holdings at unrelated banks. The third claim follows by finite set partition: disjoint summation yields additivity of reserves. Cross-multiplying the tier inequality yields $`R_{\mathrm{Tier}_2}(M_{\mathrm{fid}, \mathrm{Tier}_1} + M_{\mathrm{fid}, \mathrm{Tier}_2}) < (R_{\mathrm{Tier}_1} + R_{\mathrm{Tier}_2}) M_{\mathrm{fid}, \mathrm{Tier}_2}`$, proving the coverage divergence; applying Proposition 10.12a to $b_2$ establishes local run infeasibility despite aggregate sufficiency. $\blacksquare$

### Definition 10.20 (The Unbacked Fiduciary Overhang and Reserve Coverage Ratio)
For any commercial banking sector with circulating fiduciary media $M_{\mathrm{fid}}(t, h)$ and custodial reserves $R_{\mathrm{issuer}}(t, h)$:

1. The **Aggregate Unbacked Fiduciary Overhang** is the natural-number redemption shortfall:

$$
\Delta_{\mathrm{overhang}}(t, h) = M_{\mathrm{fid}}(t, h) - R_{\mathrm{issuer}}(t, h).
$$

For an individual bank $`b \in \mathcal{I}_{\mathrm{banks}}`$, its bank-specific overhang is $`\Delta_b(t, h) = M_{\mathrm{fid}, b}(t, h) - R_b(t, h)`$.

2. For $M_{\mathrm{fid}}(t, h) > 0$, the **Reserve Coverage Ratio** is the exact fractional backing:

$$
\rho(t, h) = \frac{R_{\mathrm{issuer}}(t, h)}{M_{\mathrm{fid}}(t, h)}.
$$

### Proposition 10.21 (Systemic Insolvency Risk and Bank-Run Vulnerability)
1. When $\Delta_{\mathrm{overhang}}(t, h) = 0$ (meaning $\rho(t, h) \ge 1$ ), every circulating note liability is 100% backed by physical reserves in bank custody. Full simultaneous redemption is resource-feasible for the issuer.
2. When $\Delta_{\mathrm{overhang}}(t, h) > 0$ (meaning $\rho(t, h) < 1$ ), the banking system is operating with an unbacked redemption shortfall. By Proposition 10.12a, accepting a simultaneous redemption demand from all note holders is resource-infeasible and cannot be enacted as a purposeful action.
3. A decline in $\rho(t, h)$ strictly increases systemic run vulnerability: a smaller fraction of depositors can successfully convert their deposits into base money before the issuer's physical reserve is entirely exhausted.

**Proof.** The first claim follows from the definition of a fully covered warehouse receipt: if notes do not exceed reserves, the issuer holds sufficient physical commodity to execute full redemption. For the second claim, total claims $M_{\mathrm{fid}}$ exceed total reserves $R_{\mathrm{issuer}}$, so the bank lacks the physical commodity to honor simultaneous redemption; by the action-frame feasibility condition, an action requiring more means than an agent holds is infeasible, ruling out purposeful execution. For the third claim, the maximal fraction of claims redeemable before reserve exhaustion is exactly $R_{\mathrm{issuer}} / M_{\mathrm{fid}} = \rho(t, h)$. A decrease in $\rho$ contracts this feasible fraction. $\blacksquare$

### Proposition 10.21a (Two-Tier Fiat Architecture, Lender-of-Last-Resort Facilities, and Standing Repos)
In a modern two-tier fiat monetary system, the central bank issues base money $m_{\mathrm{reserve}}$ (digital master-account reserves and physical currency) through fiduciary note issuance at zero physical resource cost, while commercial banks issue checkable liabilities $m_{\mathrm{fid}}$ redeemable in base money. Under this institutional architecture:
1. The reserve coverage ratio $\rho(t, h) = R_{\mathrm{issuer}} / M_{\mathrm{fid}}$ defines the **autonomous commercial-bank liquidity boundary** prior to central bank intervention.
2. If depositors exercise redemption demands $q > R_{\mathrm{issuer}}(t, h)$, the commercial banking sector faces an operational dichotomy:
   - *Autonomous Default / Suspension:* Without external intervention, honoring redemption of $q$ is resource-infeasible for commercial banks (Proposition 10.12a), forcing suspension of payments or bankruptcy.
   - *Inflationary Central Bank Bailout:* If the central bank enacts a lender-of-last-resort fiduciary note issuance of base reserves with principal $\Delta M \ge q - R_{\mathrm{issuer}}$, the newly created reserves cover the shortfall, but total base money in the economy strictly expands ( $`M_{\mathrm{base}}^{\mathrm{total}}(t') = M_{\mathrm{base}}^{\mathrm{total}}(t) + \Delta M`$ ), diluting purchasing power across downstream network nodes (Proposition 9.24).
3. **Standing Credit Facilities and Collateral Encumbrance:** When the central bank operates standing emergency facilities (such as a discount window or standing repo facility), the injection is executed as a collateralized credit advance:
   - *Reserve Restoration:* If the borrowed principal $\Delta M$ satisfies $q \le R_b(t_0) + \Delta M$, the commercial bank's post-advance reserve endowment $R_b(t_2) = R_b(t_0) + \Delta M$ restores the physical feasibility of clearing redemption demand $q$.
   - *Collateral Encumbrance:* The commercial bank transfers eligible collateral (Treasury debt or high-grade paper) of quantity $Q$ to the central bank's custodial account, reducing its unencumbered assets: $\omega_b(t_2, \text{collateral}) + Q = \omega_b(t_0, \text{collateral})$.
   - *Systemic Base Expansion:* Total base money across all economic actors strictly increases by the newly minted principal: $`M_{\mathrm{base}}^{\mathrm{total}}(t_2) = M_{\mathrm{base}}^{\mathrm{total}}(t_0) + \Delta M`$.

**Proof.** The first claim is the direct definition of autonomous balance-sheet coverage without new credit origination. For the second claim, when $q > R_{\mathrm{issuer}}$, commercial banks lack the physical means to clear redemption autonomously, proving the first branch of the dichotomy by Proposition 10.21. For the second branch, central bank fiduciary issuance produces principal $\Delta M > 0$ in base reserves without consuming reserves (Proposition 10.10). By the physical inventory equations of note issuance, total base media in the economy strictly increases by $\Delta M$, expanding base money and initiating the staged purchasing-power dilution proved in Proposition 9.24. For the third claim, the physical inventory transfer theorem for bilateral advances proves that the borrower receives principal $\Delta M$ while surrendering collateral $Q$; because the lender issues new base fiat, the universal sum of base media across all agents expands by $\Delta M$ by the total media expansion theorem of fiduciary origination. $\blacksquare$

### Auditing Bank Ledgers: Operational Flow Separation

By tracking the monetary vector $\mathbf{M}(t, h)$, economic observers can rigorously audit banking operations into two mutually exclusive and physically distinct flows:

1. **Pure Commodity Credit Advances (Proposition 10.10b):**
   - *Inventory Law:* Total spendable media is conserved: $\sum \omega(t') = \sum \omega(t)$.
   - *Menu Effect:* The lender's cash balance contracts, stripping tight money-using actions from the lender's feasible menu.
   - *Catallactic Impact:* Non-inflationary capital reallocation; transfers pre-existing savings to entrepreneurial borrowers.
2. **Fiduciary Origination (Proposition 10.10, 10.12a):**
   - *Inventory Law:* Circulating media expands by $+P$ while physical reserves remain unchanged: $\omega_{\mathrm{issuer}}(t') = \omega_{\mathrm{issuer}}(t)$.
   - *Menu Effect:* New checkable purchasing media is created without contracting any saver's feasible menu.
   - *Catallactic Impact:* Inflationary credit creation; increases $\Delta_{\mathrm{overhang}}$ and dilutes purchasing power across the trading network (Proposition 9.24).

This separation allows monetary analysts to evaluate credit expansion directly from balance-sheet transactions without confusing capital accumulation with fiduciary inflation.

### Proposition 10.21a (Conditional Repayment-Rate Comparison under Fiduciary Origination)

Consider two loan contracts $T_{\mathrm{nat}}$ and $T_{\mathrm{cred}}$ sharing identical principal $T_{\mathrm{nat}}.\mathrm{principal} = T_{\mathrm{cred}}.\mathrm{principal}$ and currency $T_{\mathrm{nat}}.\mathrm{money} = T_{\mathrm{cred}}.\mathrm{money}$. If a fractional-reserve bank creates unbacked fiduciary notes via fiduciary origination ( $I, A_{\mathrm{cred}}, O$ ) to fund a marginal borrower whose project cash endowment at repayment moment $R.\mathrm{moment}$ strictly falls short of natural repayment ( $`\omega(T_{\mathrm{cred}}.\mathrm{borrower}, R.\mathrm{moment}, A_{\mathrm{cred}}.\mathrm{history}, T_{\mathrm{cred}}.\mathrm{money}) < T_{\mathrm{nat}}.\mathrm{repayment}`$ ), then:

1. Contractual credit repayment is strictly less than natural repayment: $`T_{\mathrm{cred}}.\mathrm{repayment} < T_{\mathrm{nat}}.\mathrm{repayment}`$.
2. The gross loan repayment rate is endogenously suppressed: $`T_{\mathrm{cred}}.\mathrm{grossRepaymentFactor} < T_{\mathrm{nat}}.\mathrm{grossRepaymentFactor}`$.
3. Total base and circulating media in the economic system strictly expands by the principal:
   $`\mathrm{totalMedia}(I.\mathrm{issuer}, I.\mathrm{money}, A_{\mathrm{cred}}.\mathrm{nextMoment}, I.\mathrm{history}) = \mathrm{totalMedia}(I.\mathrm{issuer}, I.\mathrm{money}, I.\mathrm{moment}, I.\mathrm{history}) + T_{\mathrm{cred}}.\mathrm{principal}`$.
4. Undertaking the loan under natural terms is physically infeasible and non-purposeful for the borrower:
   $`\mathrm{Offer}(T_{\mathrm{cred}}.\mathrm{borrower}, T_{\mathrm{nat}}.\mathrm{lender}, T_{\mathrm{nat}}.\mathrm{repayment}, \dots) \notin \mathcal{A}_{\mathrm{feas}} \ \wedge\ \neg \mathsf{P}(\mathrm{Offer}(\dots))`$.

**Proof.** Because the borrower executes repayment under $T_{\mathrm{cred}}$, the borrower's cash balance covers $T_{\mathrm{cred}}.\mathrm{repayment}$. Since that same cash balance is strictly less than $T_{\mathrm{nat}}.\mathrm{repayment}$, transitivity of order over $\mathbb{N}$ establishes $T_{\mathrm{cred}}.\mathrm{repayment} < T_{\mathrm{nat}}.\mathrm{repayment}$. With identical principals, dividing the repayment equation yields $T_{\mathrm{cred}}.\mathrm{grossRepaymentFactor} < T_{\mathrm{nat}}.\mathrm{grossRepaymentFactor}$. Fiduciary note issuance expands total media by $T_{\mathrm{cred}}.\mathrm{principal}$ by Proposition 10.10. Finally, because available cash is strictly less than natural repayment, offering natural repayment violates the resource feasibility coupling $`\mathcal{A}_{\mathrm{feas\_coupling}}`$, rendering the action infeasible and non-purposeful. $\blacksquare$

This is a conditional comparison of two repayment outcomes. The result uses evidence that the credit borrower actually repays and has less money at that repayment moment than the natural contract would require. It does not derive successful repayment, purposeful investment, or a general market-rate response from note issuance alone.

### Sectoral Liquidity Stress Testing: Cash-Backed Solvency

The disaggregated monetary measure connects directly to entrepreneurial solvency under price uncertainty, as developed in Chapter 9 (Definition 9.14a–9.14c):

### Definition 10.22 (Cash-Backed Factor Solvency Profile)
Let $\mathcal{B} = \langle P^{\inf}, P^{\sup} \rangle$ be a factor price box for $d$ inputs, and let $x_i \in \mathbb{N}^d$ be the input plan of enterprise $i$. Under monetary holding $\omega_i(m)$, the **cash-backed solvency profile** across an entrepreneurial cohort is:

$$
\mathcal{S}(\omega, m, \mathcal{B}, x, \text{Cohort}) = \left\lbrace i \in \text{Cohort} \;\middle|\; \sum_{k < d} P^{\sup}(k) \cdot x_i(k) \le \omega_i(m) \right\rbrace.
$$

### Theorem 10.23 (Solvency Contraction under Fiduciary Factor Price Inflation)
Suppose fiduciary credit origination injects new media into the trading network, bidding up factor prices and widening factor price uncertainty from $`\mathcal{B}_1`$ to $`\mathcal{B}_2`$:

$$
\forall k < d, \quad P^{\inf}_2(k) \le P^{\inf}_1(k) \quad \wedge \quad P^{\sup}_1(k) \le P^{\sup}_2(k).
$$

Then for any firm whose cash endowment $\omega_i(m)$ has not yet received the new credit injection:
1. Precautionary cash demand weakly increases: $`C^+(\mathcal{B}_1, x_i) \le C^+(\mathcal{B}_2, x_i)`$.
2. The cohort of solvent entrepreneurs able to complete production plans weakly contracts:

$$
\mathcal{S}(\omega, m, \mathcal{B}_2, x, \text{Cohort}) \subseteq \mathcal{S}(\omega, m, \mathcal{B}_1, x, \text{Cohort}).
$$

3. For any enterprise where $`P^{\sup}_1(k^{\ast}) < P^{\sup}_2(k^{\ast})`$ on a strictly necessary input $x_i(k^{\ast}) > 0$, if $`C^+(\mathcal{B}_1, x_i) \le \omega_i(m) < C^+(\mathcal{B}_2, x_i)`$, the enterprise transitions from solvent to strictly blocked: its completion action becomes resource-infeasible and cannot be enacted.

**Proof.** The first two statements follow directly from Proposition 9.14d. For the third statement, the strict increase in the upper bound yields $`C^+(\mathcal{B}_1, x_i) < C^+(\mathcal{B}_2, x_i)`$. Since $`\omega_i(m) < C^+(\mathcal{B}_2, x_i)`$, Proposition 9.14b proves that the completion action requires more cash than the enterprise possesses, rendering it resource-infeasible. $\blacksquare$

Theorem 10.23 is conditional on the stated widening of the price box and on the affected firm's cash endowment remaining fixed. Its arithmetic derives a weak contraction of the modeled cash-solvent set, and a strict affordability failure when the balance lies between the old and new costs. It does not derive the price-box change from credit origination, nor does it establish that projected eligibility is physical affordability, that investment was purposeful, or that a crisis cluster follows without the additional cohort and choice evidence stated in Chapter 13.

### The Econometric Boundary of Monetary Measurement

Finally, our formalization clarifies the exact boundary of what empirical observation can measure:

### Proposition 10.24 (The Observable-Unidentifiable Boundary in Monetary Accounting and Statistical Coarse-Graining)
1. **Observable Quantities:** Recorded physical stock coordinates $\omega_a(t, h, m)$, bank origination ledgers, transacted market prices, and loan contractual terms are fully observable and verifiable from historical balance-sheet records.
2. **Unidentifiable Quantities:** Counterfactual preference orderings, unchosen alternatives, subjective liquidity valuations, and whether acting individuals will suddenly exercise redemption options or abandon an overvalued medium cannot be identified from econometric time-series (Master Non-Identifiability Theorem, Chapter 14).
3. **Endogenous Media vs. Statistical Coarse-Graining:** Theoretically, medium-of-exchange status is determined endogenously by the Mengerian acceptance profile $\Gamma(t, h, m)$ (Definition 9.1) and direct spot-purchase feasibility (Proposition 10.10a) versus secondary portfolio liquidation. When empirical monetary measures map administrative categories (such as Federal Reserve H.6 savings deposits or money market mutual fund shares) into $M_{\mathrm{fid}}$ or $C_{\mathrm{pure}}$, this classification represents an *observational coarse-graining* that must be evaluated against the operational criteria of direct spot clearance versus secondary liquidation.
4. **Automated Sweep Accounts and the Liquidity Freeze Breakdown:** In modern retail banking, sweep algorithms automatically shift funds between non-reservable interest-bearing instruments (such as money market mutual fund shares or overnight repos) and checkable transaction accounts. Praxeologically:
   - *Two-Step Market Execution:* If secondary conversion markets clear at adjacent moments $t \to t'$, an automated credit advance delivers newly spendable checkable media $P$ to the buyer, raising physical cash holdings to $`\omega_i(t', h, m_{\mathrm{money}}) \ge P`$ and rendering a spot-purchase acceptance action feasible at $t'$ (conditional on contemplation).
   - *Liquidity Freeze Breakdown:* If secondary conversion freezes or counterparties withhold bids, the conversion transaction fails to match. The buyer enacts the passive baseline inaction $\alpha_0$ at $t \to t'$, leaving spendable cash unchanged: $`\omega_i(t', h, m_{\mathrm{money}}) = \omega_i(t, h, m_{\mathrm{money}}) < P`$. Consequently, spot-purchase acceptance remains strictly resource-infeasible and non-purposeful at $t'$.
   - *Catallactic Implication:* Sweep balances and secondary credit claims are not spot spendable media; their purchasing power is contingent on a two-step sequential bilateral exchange across discrete moments. Treating contingent sweep claims as equivalent to cash in a single scalar sum ignores liquidation counterparty risk.

**Proof.** Statements 1–3 summarize the epistemological boundary established in Chapters 9 and 14. For Statement 4, the first branch follows from the physical transfer theorem for matched bilateral advances (Proposition 10.10b): receiving principal $P$ increments the borrower's spendable media to at least the contract price, fulfilling the action-frame spot feasibility condition. The second branch follows from the baseline inaction transition equation: when an agent enacts $\alpha_0$, physical endowments are strictly conserved; since opening cash was strictly less than $P$, post-transition cash remains strictly less than $P$. By Proposition 10.10a, spot-purchase acceptance requires endowment coverage; when coverage fails, the action is resource-infeasible and cannot be enacted as a purposeful act. $\blacksquare$

This boundary establishes that while the physical coordinates of the monetary structure ($\mathbf{M}$, $\Delta_{\mathrm{overhang}}$, $\rho$) are rigorously measurable, economists cannot construct a single scalar aggregate that predicts human choice without violating the fundamental principles of praxeology.

---

## The Complete Credit Lifecycle Action Frame Witness

To check a finite arrangement of issuance, matched loan advances, collateral custody, project completion, repayment, and unpaid maturity, we construct the **Credit Lifecycle Action Frame**. Repayment and unpaid maturity are separate continuations after origination.

### Model Structure and Branching Architecture

The lifecycle model is defined over a branching temporal frame consisting of:
1. **Moments and Histories:** Twenty discrete moments ( $`\mathcal{T} = \{0, 1, \dots, 19\}`$ ) and fourteen histories ( $`\mathcal{H} = \{0, 1, \dots, 13\}`$ ).
2. **Economic Agents:** Three actors: the operator as lender, the entrepreneur and customer as borrowers in separate advances.
3. **Physical Means:** Eight enumerated means; money, collateral, and reserve goods are the coordinates used in the credit accounting.
4. **Actions:** A finite action menu including the passive baseline $\alpha_0$, money issuance, bilateral trade actions ($\text{Offer}$ and $\text{Accept}$ parameterized by quantity and commodity), and production tasks.

### Contractual and Physical Transitions

The tree represents origination and later repayment or nonpayment as separate events. Its main history includes issuance, two advances, project completion, two matched repayments, and maturity. Side histories represent selected refusals or unmatched bilateral transfers. The existing unpaid-maturity branch is used to construct `entrepreneurUnpaidEnactedLoanQuote`, and a theorem proves that its advance has no successful-repayment certificate. This tests the quote boundary on the represented default outcome; it adds no new economic scenario. The quote at origination requires neither later outcome:
- **Moment 0 (Fiduciary Issuance):** The lending agent enacts a note-issuance action. In accordance with Proposition 10.10, the issuer's money balance increases by the principal quantity, while collateral and the balances of other agents remain unchanged.
- **Moments 1 and 2 (Matched Collateralized Advances):** The lender and each borrower enact matching bilateral exchange actions ($\text{Offer}$ and $\text{Accept}$). By the bilateral transfer law, principal in money moves from the lender to the borrower, while the stipulated collateral moves from the borrower into the lender's custody.
- **Subsequent Branching (Completion and Transfer Outcomes):** The timeline branches into continuations that differ in whether the bilateral transfers match:
  - *Successful Repayment Branch:* The borrower carries out the represented production and a matched repayment of the promised amount, returning the stipulated collateral quantity.
  - *Unpaid Maturity:* On the represented history where repayment is absent, the unpaid-maturity evidence classifies the outstanding loan as defaulted. The lender retains the collateral stock recorded after the advance under the stated custody conditions. This is not a foreclosure or collateral-liquidation event: the model does not track particular collateral units, a foreclosure judgment, or their sale.

### Constructive Verification of the Frame Axioms

The Credit Lifecycle Action Frame satisfies every axiom of the praxeological action frame:
- **Temporal Validity:** Precedence is strictly irreflexive, transitive, and backward-linear; histories satisfy extensionality and separation.
- **Conservation and Bilateral Execution:** Physical transitions obey exact integer conservation. Unilateral offers or acceptances that lack a matching counterparty execute zero transfers ( $\omega(t') = \omega(t)$ ), while matched pairs execute exact simultaneous transfers.
- **Evaluative Coherence:** Agents' preferences over final consumption bundles satisfy asymmetry, transitivity, and teleological bundle dominance.

This witness establishes that the represented issuance, advances, repayment, and unpaid-maturity branches satisfy the stated frame and transfer laws. It does not make repayment part of origination, infer nonpayment solely from a missing repayment certificate, or add a refinancing or foreclosure rule. The specific default witness is separate from the five-project business-cycle program.

---

## Conclusion

We have separated disagreement about the future from the payoff conditions that determine realized gains, and we have distinguished a mistaken forecast from an opportunity absent from the actor's considered menu. We have also followed credit from purposeful issuance and loan origination through repayment or unpaid maturity, keeping contractual status separate from physical stocks. We now study how price information, delegation, and intervention shape the organizational setting in which such plans are carried out.
