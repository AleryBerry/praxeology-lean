# Chapter 13: Business Cycles and Crisis

Chapters 4 and 7 introduced tools for analyzing complementary requirements, capital, and intertemporal choice. Chapters 10 and 11 incorporated credit advances, price uncertainty, and organizational production. We now combine these elements into a formal model of investment and crisis.

The Austrian Business Cycle Theory traces five interrelated phases across an Action Frame:
1. **Fiduciary Credit Origination:** Unbacked note issuance expands loanable media, suppressing the contractual loan rate below the rate supported by voluntary savings.
2. **Purposeful Investment Decision:** Under the suppressed loan rate, the post-repayment physical endowment bundle teleologically dominates inaction, leading the entrepreneur to purposefully undertake roundabout investment.
3. **Physical Capital Formation:** Intermediate capital goods are produced along the transition run using the advanced credit.
4. **Complementary Factor Exhaustion:** Because credit expansion was unbacked by real saving, the complementary factors required to complete the lengthened production structure are physically absent, rendering completion infeasible.
5. **Contextual Regret and Capital Stranding:** The incomplete capital goods remain stranded, and the entrepreneur experiences contextual regret relative to the foregone safe liquidity baseline.

## Discrete Return Comparisons and Rate Signals

Let $s$ be a projected spread, $r$ a positive rate, $d$ a nonnegative allowance for uncertainty or rounding, and $v$ a benchmark. Since quantities are natural numbers, the model compares these terms by multiplication:

$$
\text{Above}(s,r,d,v)\;\Longleftrightarrow\;r(v+d) < s,
\qquad
\text{AtMost}(s,r,d,v)\;\Longleftrightarrow\;s\le r(v+d).
$$

The two conditions are exact complements. No quotient is rounded down, and the allowance creates a stated threshold interval.

### Definition 13.1 (An Intertemporal Signal Pair)

An intertemporal signal pair consists of natural numbers $s,r_n,r_c,d,v$ with $r_n>0$ and $r_c>0$ such that

$$
s\le r_n(v+d)
\qquad\text{and}\qquad
r_c(v+d) < s.
$$

The first inequality places the spread at or below the benchmark under the natural-rate comparison; the second places it above the benchmark under the credit-rate comparison.

In the endogenous credit framework established in Chapter 10 (Proposition 10.21a), the spread between $r_n$ and $r_c$ is derived directly from the banking system's balance sheet. When a bank issues unbacked fiduciary notes to clear a marginal loan whose gross revenue cannot cover the natural repayment demanded by genuine savers, fiduciary origination endogenously suppresses the gross repayment factor ($r_c < r_n$) while expanding circulating media by the loan principal.

## Purposeful Investment Grounded in Credit and Bundle Dominance

An arithmetic rate comparison translates into purposeful action through the entrepreneur's preference ordering over physical bundles. Under natural savings terms, the required debt repayment leaves a residual physical bundle that fails to improve upon inaction, rendering the investment non-purposeful ( $\neg \mathsf{P}$ ). Under fiduciary credit terms, the suppressed repayment factor leaves a strictly superior residual bundle. In the Action Frame, teleological bundle dominance natively induces strict ordinal preference (`teleological_bundle_dominance_induces_preference`), transforming the investment into a purposeful act ( $\mathsf{P}$ ).

### Theorem 13.2 (Endogenous Credit-Induced Investment Flip)

Suppose a fiduciary credit origination supplies principal $P$ at suppressed gross repayment factor $r_c < r_n$, funding an investment action $\alpha$:
1. At the natural rate $r_n$, the post-repayment outcome does not improve upon inaction, so $\alpha$ is rejected as non-purposeful ( $\neg \mathsf{P}$ );
2. At the credit rate $r_c$, the loan advance provides sufficient spendable media, and the post-repayment bundle strictly teleologically dominates inaction;
3. By `teleological_bundle_dominance_induces_preference`, $\alpha$ is strictly preferred to inaction and undominated among feasible alternatives;
4. The entrepreneur enacts $\alpha$.

Then $\alpha$ is non-purposeful at the natural rate and purposeful at the credit rate.

**Proof.** At the natural rate, purposeful active choice is excluded because $\alpha \neq \alpha_0$ and the outcome fails to improve upon inaction. At the credit rate, the matched advance fulfills the physical cash requirement for feasibility. Enactment is supplied, bundle dominance natively induces strict improvement over inaction via `teleological_bundle_dominance_induces_preference`, and undominatedness holds among feasible alternatives. These are the exact requirements of `PurposefulAct`. $\square$

## Capital Formation and a Missing Complementary Factor

Capital accumulation in the model is an observed physical transition. It may be a production step or an exchange. To establish that one unit of capital is present at the next moment, require zero initial stock, zero effective use of that capital in the transition, and effective yield one. The inventory balance then gives the stated next stock.

The completion obstruction is a separate condition. Let $m_c$ be a complementary means. Suppose its initial stock is zero, the capital-formation transition neither uses nor yields $m_c$, and the later completion action requires one unit of $m_c$. The inventory balance leaves the stock at zero, so the completion action is physically infeasible.

### Proposition 13.3 (Complementary-Factor Starvation Blocks Completion)

Under the preceding conditions, the next stock of capital is one, the next stock of $m_c$ is zero, and the completion action is infeasible at the next moment.

**Proof.** Apply the inventory balance separately to capital and to $m_c$. The capital equation is $\omega_{next}+0=0+1$, hence $\omega_{next}=1$. The complementary-factor equation is $\omega_{next}+0=0+0$, hence $\omega_{next}=0$. Since completion requires one unit and $0<1$, it violates the resource condition for feasibility. $\square$

The proposition does not say that every accumulated capital good is useless. It concerns a specified technology in which completion requires a factor that remains absent.

## Buffer Stocks, Substitution, and Liquidation

The preceding example asks whether one named complementary factor is present. We can also compare aggregate stocks with a stated completion requirement. This arithmetic model is deliberately small: it records a buffer stock, an alternative stock, and the quantity required for completion. We use its regime names only for these defined inequalities.

### Definition 13.4 (Absorption and Liquidation Thresholds)

Let $b$ be a buffer stock, $s$ a substitute stock, and $q$ the requirement for completion. Define the *absorption condition* by

$$
q\le b+s,
$$

and the *liquidation condition* by

$$
b+s < q.
$$

The first says that the combined stocks meet the requirement; the second says that they fall short. Since these are natural numbers, exactly one condition holds. The boundary is exact: equality belongs to the completion side, not the strict-shortfall side.

### Proposition 13.5 (The Basic Completion and Liquidation Conditions Are Complements)

For all natural numbers $b,s,q$, the liquidation condition holds exactly when the absorption condition fails.

**Proof.** The absorption condition is $q\le b+s$. Its negation over the natural numbers is $b+s < q$, which is the liquidation condition. $\square$

Substitute stocks may count differently when the model assigns them a penalty. Let $p>0$ be that penalty factor. Rather than divide by $p$ and lose information to integer rounding, we keep the comparison cross-multiplied.

### Definition 13.6 (Completion with Penalized Substitution)

In an action frame $W$, a *penalized substitution technology* $T$ at $(i, t, h)$ for action $\alpha$, primary buffer means $m_{\mathrm{buf}}$, and substitute means $m_{\mathrm{sub}}$ specifies a strictly positive penalty factor $p > 0$. The buffer stock $b = \omega(i, t, h, m_{\mathrm{buf}})$, substitute stock $s = \omega(i, t, h, m_{\mathrm{sub}})$, and requirement $q = u(\alpha, m_{\mathrm{buf}})$ govern the completion status.

Define *completion with penalized substitution* by:

$$
q \cdot p \le b \cdot p + s,
$$

and define *penalized liquidation* by:

$$
b \cdot p + s < q \cdot p.
$$

The two conditions are complements. They provide an explicit accounting rule within the action frame: the substitute stock contributes less to the requirement comparison as $p$ rises.

### Proposition 13.6a (Liquidation Implies Primary Buffer Deficit)

Under any penalized substitution technology with penalty $p > 0$, if the technology is in the liquidation regime, the primary buffer stock alone strictly falls short of the requirement:

$$
b \cdot p + s < q \cdot p \implies b < q.
$$

**Proof.** Suppose toward a contradiction that $b \ge q$. Then $b \cdot p \ge q \cdot p$. Since $s \ge 0$, we have $b \cdot p + s \ge q \cdot p$, which directly contradicts the strict inequality of the liquidation regime $b \cdot p + s < q \cdot p$. Hence $b < q$. $\square$

### Theorem 13.7 (A Penalty Can Change the Completion Classification)

For every natural-number penalty $p\ge2$, the stocks $b=2$, $s=4$, and $q=5$ meet the unpenalized absorption condition but satisfy penalized liquidation:

$$
5\le2+4
\qquad\text{and}\qquad
2p+4<5p.
$$

**Proof.** The first inequality is $5\le6$. Since $p\ge2$, we have $3p\ge6>4$, hence $2p+4<5p$. Thus total unweighted stock meets the requirement, while the penalized comparison falls strictly short. $\square$

For example, at $p=2$, the unweighted total is $2+4=6$, which meets the requirement $5$, while weighted coverage is $2\cdot2+4=8<10=5\cdot2$. The same stock record is therefore classified differently under the two stated completion rules. The result shows that substitution assumptions matter to a threshold calculation; it does not show that substitution always fails during a crisis.

This regime calculation and the missing-factor example answer different questions. The first aggregates two stocks under a specified substitution rule. The second follows an actual transition and proves that a required complement remains absent. We must not treat either arithmetic condition as evidence that a particular historical project was liquidated.

## Regret under a Shared Context

In this framework, regret compares an actual investment with a feasible safe action under one context correspondence. The correspondence must admit both action-history-maturity combinations in that context. In addition, outcomes must be grounded in physical endowments, and the safe bundle must teleologically dominate the actual bundle at the evaluation point. Under these conditions, teleological bundle dominance natively induces the relevant strict preference (`teleological_bundle_dominance_induces_preference`), and the common-context definition records regret.

### Theorem 13.8 (Conditional Cycle Conclusion)

Suppose the signal pair holds; a transition forms one unit of capital; completion is blocked; the investment is purposeful at the investment decision; and the actual investment and safe alternative are admitted by a common compatible context. If outcomes are determined by physical endowments and the safe bundle dominates the actual bundle at the evaluation point, then the model entails contextual regret for the investment relative to the safe action.

**Proof.** The common compatible context admits both the actual investment and the safe alternative. Physical grounding identifies their matured outcomes with the corresponding stock bundles. The safe bundle's stipulated strict teleological dominance, together with `teleological_bundle_dominance_induces_preference`, makes the safe outcome strictly preferred in that shared context. By the definition of contextual regret, these facts establish regret relative to the safe action. $\square$

This conclusion combines the arithmetic signal, physical transition, choice evidence, and later comparison. Removing any one of those premises removes the corresponding part of the conclusion. In particular, the blocked-completion premise may be supplied by missing physical inputs or by a specified cash shortfall; the theorem does not infer either obstruction from the rate signal alone.

## A Price-Box Cash Obstruction

Suppose completion requires a monetary input equal to the precautionary cash demand calculated from a factor-price box and a vector of factor quantities. If the agent's cash stock is strictly below that amount, completion is infeasible. This follows from the definition of feasibility and the stated cost equality.

### Proposition 13.9 (Cash Shortfall Blocks a Costed Completion)

Let $C$ be the monetary input required by a completion action, and suppose $C$ equals the precautionary cash demand associated with the stated price box and factor quantities. If available cash is less than that demand, the completion action is infeasible.

**Proof.** The stipulated equality identifies the action's required monetary input with the stated demand. The cash-shortfall inequality says that this requirement exceeds the agent's monetary endowment. The feasibility test therefore fails for this action. $\square$

The proposition concerns this one completion cost and cash stock. It does not establish that every wider price interval raises precautionary demand, or that a price-box shortfall caused the original investment. Such claims require their own price-box assumptions and purposeful-choice evidence.

When this cash shortfall supplies the blocked-completion premise in Theorem 13.8, and the common contextual and appraisal conditions there also hold, the same regret conclusion follows. A price calculation, by itself, does not establish that an investment was purposeful or regrettable.

### An Endogenous Two-Stage Price-Box Squeeze

The stronger price-box result traces how the shortfall can emerge after investment. Suppose the investment transition uses money but yields none. Before investment, cash covers both the stage-one expenditure and the completion demand computed from a pre-investment price box. Then suppose the post-investment box is weakly wider at every factor, while the upper price of a factor used in positive quantity rises strictly. If the completion action's money requirement equals the new precautionary demand and the original cash is less than stage-one spending plus that widened demand, the inventory balance shows that the remaining cash still covered the old demand but cannot cover the new one. Price-box widening strictly increases precautionary cash demand, exhausts the buffer, and makes completion infeasible.

The Cantillon result supplies a one-factor instance of this certificate. Let the factor quantity be one, set the pre- and post-box upper prices to $P_{\mathrm{pre}}$ and $P_{\mathrm{post}}$, and let downstream cash be $M$ with $P_{\mathrm{pre}}\le M < P_{\mathrm{post}}$. The earlier cash demand is affordable, while the completion action priced at $P_{\mathrm{post}}$ exceeds the downstream balance. This converts the purchasing-power dilution result into a price-box completion squeeze.

### Grounding Stranded-Capital Regret in Valued Ends

The physical comparison can also be derived from end requirements. Suppose the safe branch preserves every finite set of ends valued at the actual evaluation point that the actual branch can attain. Suppose further that the safe branch attains a valued target end whose money requirement exceeds actual cash. The actual bundle cannot attain that target, while the safe bundle can; together with preservation of all actual attainable valued sets, this proves strict teleological dominance of the safe bundle. When outcomes are grounded in inventories and teleological bundle dominance induces preference, the safe action is strictly preferred in a shared evaluation context, providing the regret comparison.

## Tracing Credit into Feasibility

We now make the funding step explicit. A matched loan advance transfers principal to the borrower and collateral to the lender. To use that advance as evidence for a later investment, we must trace the borrower's money stock between the transfer and the investment decision.

### Proposition 13.10 (An Unspent Advance Can Cover the Project's Money Input)

Suppose a lender transfers principal $P$ to a borrower at a moment on history $h$. Let the advance be followed by a later decision moment $t$ on that same history. If the borrower uses no units of the loan's money between receipt of the advance and $t$, then the borrower's money stock at $t$ is at least $P$. Consequently, if the investment requires at most $P$ units of that money and every other required input is available, a contemplated investment is feasible at $t$.

**Proof.** The matched transfer raises the borrower's stock by $P$, so immediately after the advance that stock is at least $P$. The inventory-run balance says that the later stock plus money used along the run equals the initial post-advance stock plus money yielded along the run. Money use is zero and money yield is nonnegative, so the later stock is at least the post-advance stock and hence at least $P$. The investment's money input is no greater than $P$; by hypothesis each other input is covered. The feasibility definition therefore applies. $\square$

The no-use condition matters. A loan's principal need not remain available merely because it was received earlier; the inventory trace supplies the needed link between receipt and present feasibility.

## The Full Endogenous Cycle

The complete praxeological business cycle synthesizes these layers without requiring external wrapper structures or arbitrary shock parameters. Instead of injecting external rate shock numbers, the model derives every causal step natively from the core categories of the Action Frame:

1. **Endogenous Loan Rate Suppression:** Unbacked fiduciary note issuance expands bank loanable funds, allowing the banking system to clear a marginal loan whose gross repayment factor $R_{\text{credit}}$ is strictly below the minimum rate $R_{\text{natural}}$ acceptable under genuine voluntary saving.
2. **Teleological Flip of Purposeful Investment:** When evaluating post-repayment physical bundles, the lower credit rate leaves the entrepreneur with a bundle that strictly teleologically dominates inaction. By `teleological_bundle_dominance_induces_preference`, this bundle dominance natively induces a strict preference that flips the entrepreneur from rejecting the project at the natural rate ( $\neg \text{PurposefulAct}$ ) to choosing it at the credit rate ( $\text{PurposefulAct}$ ).
3. **Physical Capital Formation:** The entrepreneur receives the loan advance, commits the funds to early-stage roundabout inputs, and forms intermediate capital goods along the production run.
4. **Native Stage-Two Blockage:** Because the credit expansion was unbacked by real saving, the complementary factors required to bring the capital good to final consumer completion remain physically absent in the economy ( $\omega(i, t_{\text{next}}, h, \text{comp}) = 0$ ). By the native feasibility coupling, this factor shortfall immediately proves completion infeasible ( $\text{completion} \notin \mathcal{A}_{\text{feas}}$ ) and hence non-purposeful.
5. **Contextual Regret:** Evaluated in a common context against the foregone safe liquidity alternative, the stranded capital delivers an inferior outcome, establishing strict contextual regret.

### Theorem 13.11 (An Endogenous Credit-Financed Starvation Cycle)

Consider an entrepreneur, an investment action, a completion action, a capital good, and a complementary factor in an Action Frame. Suppose:

1. the loan advance provides credit funding at gross repayment factor $R_{\text{credit}}$;
2. under post-repayment bundle dominance at rate $R_{\text{credit}}$, roundabout investment is purposeful ( $\text{PurposefulAct}$ ), whereas at the natural rate it is rejected ( $\neg \text{PurposefulAct}$ );
3. the investment is enacted, forming intermediate capital stock while leaving complementary factor stock at zero ( $\omega(i, t_{\text{next}}, h, \text{comp}) = 0$ );
4. the completion action requires a strictly positive quantity of the complementary factor; and
5. a safe liquidity alternative is feasible and admitted in a compatible evaluation context, with physically grounded outcomes where the safe bundle teleologically dominates the stranded actual bundle.

Then:
1. the entrepreneur purposefully undertakes the roundabout investment at the credit rate, but would have refrained at the natural rate;
2. at the next stage, completion is strictly infeasible ( $\text{completion} \notin \mathcal{A}_{\text{feas}}$ ) and cannot be purposefully enacted;
3. the capital stock remains stranded; and
4. evaluated in the shared context, the entrepreneur experiences strict contextual regret relative to the safe alternative.

**Proof.** The credit funding and teleological bundle dominance (`teleological_bundle_dominance_induces_preference`) establish purposeful investment at the subsidized rate and its absence at the natural rate. The inventory transition certifies that intermediate capital is formed while complementary stock is zero. Since completion requires positive complementary means, the native feasibility coupling $\mathcal{A}_{\text{feas\_coupling}}$ forces $\text{completion} \notin \mathcal{A}_{\text{feas}}$. Physical outcome grounding and teleological bundle dominance then yield strict preference for the safe outcome, establishing contextual regret. $\square$

### Theorem 13.12 (An Endogenous Credit-Financed Cash Squeeze Cycle)

When completion requires spot factor purchases rather than pre-existing inventory, the same cycle holds via monetary outpricing:
1. credit expansion bids up factor prices, creating a cash shortfall ( $`\omega(i, t_{\text{next}}, h, \text{money}) < P_{\text{bid}}`$ );
2. spot factor acceptance is infeasible by insufficient cash balance;
3. completion is blocked, stranding capital and inducing contextual regret.

**Proof.** By the spot-trade feasibility equivalence, an agent lacking money cannot accept factor offers. Infeasibility of factor acquisition forces completion infeasibility, yielding stranded-capital regret as in Theorem 13.11. $\square$

## Organized Production and Finite Illustrations

The cycle can also occur inside an organization. In a three-person construction, a principal directs an operator to produce an intermediate good. The operator accepts the assignment and later transfers one unit of the intermediate good to the principal under an authorized internal exchange. The principal then sells an output to an independently governed customer. The model places the production task, internal transfer, and external sale on one history and orders the sale after the work. If the transfer supplies the principal's capital good while the required complementary input remains absent, the same completion obstruction applies. A shared evaluation context and a valued safe bundle supply the regret comparison.

This organized firm specialization ties internal delegation and external market sale directly to the general cycle theorem: even within an organized firm, credit-induced roundabout expansion without complementary physical factors terminates in factor starvation, stranded capital, and contextual regret.

---

## Model-Theoretic Witnesses for the Business Cycle

The formal architecture provides concrete, verified action frame witnesses that demonstrate the consistency and non-vacuity of the business-cycle theorems. Each witness addresses a distinct analytical question:

### 1. The Grounded ABCT Action Frame Witness

The core praxeological account of the Austrian Business Cycle Theory is certified by an explicit, finite model witness: the Grounded ABCT Action Frame. This closed model instantiates the full signature $\Sigma_{\text{prx}}$ across four moments, four branching histories, and three distinct agents:
- *Bank:* Executes fiduciary credit creation and offers loan advances at an artificially reduced interest rate.
- *Entrepreneur:* Conducts intertemporal appraisals, accepts the credit advance, and commits resources to long-term capital formation.
- *Worker / Counterparty:* Engages in factor transfers and production tasks.

The grounded frame unifies all five causal phases in a single constructive structure:
1. *Credit Expansion:* The bank enacts note issuance, expanding loanable funds without prior voluntary saving.
2. *Distorted Appraisal:* The entrepreneur evaluates the lower credit rate against the natural rate, finding roundabout capital investment purposeful where inaction was previously preferred.
3. *Physical Malinvestment:* The loan is advanced, and the entrepreneur commits goods to intermediate capital goods.
4. *Complementary Factor Starvation:* Because the credit expansion was not accompanied by real physical saving, the complementary goods needed to complete the project are physically exhausted, rendering completion infeasible.
5. *Contextual Regret:* Evaluated in a shared deliberative context against the foregone safe liquidity alternative, the entrepreneur experiences strict ordinal regret over the aborted project.

### 2. The Complete Credit Lifecycle Witness

To witness the entire temporal progression of credit contracts—from origination through distress, refinancing, and liquidation—the formalization provides the Credit Lifecycle Action Frame. As established in Chapter 10, this twenty-node branching tree with twelve maximal histories proves that fiduciary issuance, collateral custody, productive restructuring, and default foreclosure can coexist in a single, closed action frame obeying all physical conservation and bilateral transfer laws.

### 3. Clustered Malinvestment: Shared Shortages and Price Squeezes

A central question in business-cycle theory is why entrepreneurial errors are systemically clustered rather than randomly distributed. The formalization provides two distinct cluster theorems over action frame cohorts:
- *Shared Input Shortage:* When a cohort of multiple distinct entrepreneurs is exposed to a common credit expansion, they simultaneously expand roundabout production. If these projects require a shared, non-expandable complementary factor, aggregate factor demand outstrips accessible physical supply. When accessible supply falls $k$ units below aggregate demand ($k \ge 2$), at least $k$ distinct projects are mathematically guaranteed to be starved of inputs and fail. This derives a synchronized cluster of at least two distinct regretful entrepreneurs.
- *Factor Price Squeezes:* When multiple projects compete for a common bottleneck factor, factor prices rise. As the factor-price bound crosses entrepreneurs' cash buffers, project completion becomes financially infeasible, precipitating an economy-wide cluster of project abandonments.

### 4. Epistemic Indistinguishability and Observation Equivalence

Why do entrepreneurs not simply discount fiduciary credit expansions in advance? An epistemic indistinguishability theorem shows that:
- In a market setting where bank credit and genuine voluntary saving quote identical gross repayment factors, the derived observation at the decision node is identical across both regimes.
- An entrepreneur acting under a fixed observational decision policy rationally chooses the identical investment action under either regime.
- Only an explicit, external source disclosure can distinguish the two regimes; market rate signals alone cannot do so.

This establishes that malinvestment is not an artifact of psychological irrationality or erratic animal spirits, but the mathematically necessary response of rational agents to distorted market signals.

---

## Scope of the Crisis Results

The chapter unifies the complete causal chain of the Austrian Business Cycle Theory: bank fiduciary expansion endogenously suppresses loan rates; post-repayment bundle dominance induces purposeful investment; physical inventory transitions form early-stage capital; complementary factor absence enforces stage-two completion infeasibility; and contextual regret emerges against the safe liquidity alternative.

The finite action frame witnesses establish that these stages hold together consistently within a unified, closed axiomatic model.

## Conclusion

We have traced the Austrian Business Cycle from fiduciary credit origination through appraisal, roundabout capital formation, physical factor exhaustion, and crisis liquidation. Both individual cycle theorems and multi-entrepreneur cluster mechanisms are verified by constructive model-theoretic witnesses. The next chapter examines what observational records can identify about preferences, counterfactuals, and macroeconomic crises.
