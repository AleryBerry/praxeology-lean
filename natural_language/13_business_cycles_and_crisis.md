# Chapter 13: Business Cycles and Crisis

Chapters 4 and 7 introduced tools for analyzing complementary requirements, capital, and intertemporal choice. Chapters 10 and 11 incorporated credit advances, price uncertainty, and organizational production. We now combine these elements into a formal model of investment and crisis.

This chapter collects conditional results about credit signals, purposeful choice, inventory transitions, completion constraints, and regret. These components can be composed when their premises are supplied, but the formalization does not derive the entire Austrian Business Cycle from fiduciary issuance alone. In particular, a lower quoted rate does not establish purposeful investment; a cash-buffer eligibility test is not a physical inventory check; and a missing complementary input must be shown in the relevant branch before completion is ruled out. The five-project physical program clears its later markets from each branch's actual state, but it does not derive household saving, purposeful investment, or the early production that converts inputs into capital.

The conditional chain studied here has five possible components:
1. **Origination and rate evidence:** An enacted advance and a loan quote can be established independently of whether the loan is later repaid. Rate comparisons require the stated market or repayment evidence.
2. **Purposeful investment:** This requires explicit feasibility, enactment, and preference evidence at the declared evaluation horizon.
3. **Physical transition:** Inventory balances determine what capital goods and complementary factors are present after the represented operations.
4. **Completion obstruction:** Completion fails only when the required physical input or monetary input is absent under the model's feasibility rule.
5. **Contextual regret:** Regret additionally requires a safe alternative, a shared compatible context, physically grounded outcomes, and the relevant preference comparison.

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

The inequalities in this definition are a supplied signal pair. They do not by themselves derive either rate from fiduciary issuance, identify the source of loanable funds, or establish what borrowers and savers chose. Chapter 10 contains separate conditional results: issuance changes the issuer's recorded money stock, while a repayment-rate comparison uses evidence about an actually enacted repayment and the borrower's balance at that repayment moment.

## Purposeful Investment Grounded in Credit and Bundle Dominance

An arithmetic rate comparison alone does not establish purposeful action. The conditional result below uses projected bundles calculated from the contract's promised repayment terms; this projection is not evidence that repayment later occurs. Feasibility, enactment, and preferences remain separate inputs to the Action Frame. The finite program adapter also makes the evaluation horizon explicit; a longer horizon can change the inventory bundle being compared, but does not by itself show that an agent prefers or chooses the investment.

### Theorem 13.2 (Conditional Credit-Rate Investment Comparison)

Suppose a fiduciary credit origination supplies principal $P$ at suppressed gross repayment factor $r_c < r_n$, funding an investment action $\alpha$:
1. At the natural rate $r_n$, the projected bundle after the promised repayment does not improve upon inaction, so $\alpha$ is not a purposeful active choice ( $\neg \mathsf{P}$ );
2. At the credit rate $r_c$, the loan advance provides the stated money input, other required inputs are available, and the projected bundle after promised repayment strictly teleologically dominates inaction;
3. By `teleological_bundle_dominance_induces_preference`, $\alpha$ is strictly preferred to inaction and undominated among feasible alternatives;
4. The entrepreneur enacts $\alpha$.

Then, under the stated appraisal, feasibility, and enactment conditions, $\alpha$ is non-purposeful at the natural rate and purposeful at the credit rate. This conclusion concerns projected appraisal and does not assert that either contract is later repaid.

**Proof.** At the natural rate, the stated appraisal condition fails the improvement-over-inaction requirement for an active purposeful act. At the credit rate, the matched advance supplies the stated money input, while the other physical inputs must also meet the feasibility condition. Enactment, preference for the projected bundle over inaction, and undominatedness among feasible alternatives are separate premises or derived from the stated bundle-dominance result. Together these are the requirements of `PurposefulAct`; the rate comparison alone proves none of them. $\square$

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

## Composing the Conditional Cycle Components

The formalization does not derive one end-to-end cycle from bank issuance. It supplies conditional components that can be composed when their interfaces are met: loan-market evidence for a quote or advance; explicit preferences and action evidence for purposeful investment; inventory-run evidence for capital and other stocks; a physical or cash constraint for blocked completion; and common-context preference evidence for regret. The five-project program recalculates the loan and factor markets at their scheduled cursor positions from each branch's actual money, recorded advances, and offered factor stocks. It executes only the listed operations and does not model the earlier use that would convert funds into capital or establish a purposeful investment decision.

Accordingly, the result below is a conditional composition. The rate, purposeful-choice, physical-shortage, and regret premises must each be supplied or separately proved. Neither fiduciary issuance nor a longer evaluation horizon supplies the missing premises.

### Theorem 13.11 (A Conditional Credit-Financed Starvation Cycle)

Consider an entrepreneur, an investment action, a completion action, a capital good, and a complementary factor in an Action Frame. Suppose:

1. the loan advance provides credit funding at gross repayment factor $R_{\text{credit}}$;
2. under the stated projected bundle comparisons using the promised terms, roundabout investment is purposeful ( $\text{PurposefulAct}$ ) at rate $R_{\text{credit}}$, whereas it is not purposeful at the natural rate ( $\neg \text{PurposefulAct}$ );
3. the investment is enacted, forming intermediate capital stock while leaving complementary factor stock at zero ( $\omega(i, t_{\text{next}}, h, \text{comp}) = 0$ );
4. the completion action requires a strictly positive quantity of the complementary factor; and
5. a safe liquidity alternative is feasible and admitted in a compatible evaluation context, with physically grounded outcomes where the safe bundle teleologically dominates the stranded actual bundle.

Then:
1. the entrepreneur purposefully undertakes the roundabout investment at the credit rate, but would have refrained at the natural rate;
2. at the next stage, completion is strictly infeasible ( $`\text{completion} \notin \mathcal{A}_{\text{feas}}`$ ) and cannot be purposefully enacted;
3. the capital stock remains stranded; and
4. evaluated in the shared context, the entrepreneur experiences strict contextual regret relative to the safe alternative.

**Proof.** Premise 2 supplies the purposeful-choice comparison at the stated appraisal and horizon. The inventory transition in premise 3 records intermediate capital while complementary stock is zero. Since the completion action requires a positive quantity of that absent factor, feasibility fails. Premise 5 supplies the common-context, physical-grounding, and preference evidence for regret relative to the safe alternative. The result composes these conditions; it does not derive them from the loan rate or advance alone. $\square$

### Proposition 13.12 (A Cash Shortfall Blocks a Required Spot-Factor Purchase)

Suppose completion requires a factor that the entrepreneur does not hold, the factor is offered only through a spot purchase at price $P$, and the entrepreneur's available balance of the specified money good is less than $P$. Then the spot acceptance is infeasible; if that factor is a necessary completion input, completion is physically infeasible as well.

**Proof.** Spot acceptance requires at least $P$ units of the specified money good. The stipulated balance is smaller, so the feasibility condition fails. If the factor is required for completion and is not otherwise available, the completion action also fails its input condition. This establishes neither that credit caused the price or cash shortfall nor that the investment was purposeful or regrettable. Those conclusions require the separate premises in Theorem 13.8. $\square$

## Organized Production and Finite Illustrations

The cycle can also occur inside an organization. In a three-person construction, a principal directs an operator to produce an intermediate good. The operator accepts the assignment and later transfers one unit of the intermediate good to the principal under an authorized internal exchange. The principal then sells an output to an independently governed customer. The model places the production task, internal transfer, and external sale on one history and orders the sale after the work. If the transfer supplies the principal's capital good while the required complementary input remains absent, the same completion obstruction applies. A shared evaluation context and a valued safe bundle supply the regret comparison.

This organized-production example composes a represented task, transfer, and sale with a separately specified missing-input condition. Its completion obstruction follows from the absent factor; any purposeful investment or regret conclusion still requires the preference and contextual premises stated for those claims.

---

## Model-Theoretic Witnesses for the Business Cycle

The formalization uses distinct finite witnesses for distinct claims. These examples check that the stated configurations can be represented; they do not combine all of the chapter's assumptions into one derived economic mechanism.

### 1. The Grounded ABCT Action Frame Witness

The **Grounded ABCT Action Frame** is a small explicit witness for a matched investment, a missing complementary input, blocked completion, and the supplied purposeful-choice and contextual-regret comparisons. Its finite construction establishes consistency of that instance. It does not establish that fiduciary issuance generally causes the missing input, or that voluntary saving, a rate response, and early production follow from the same causal rule.

### 2. The Complete Credit Lifecycle Witness

The **Credit Lifecycle Action Frame** represents issuance, matched advance, later repayment and unpaid-maturity branches. As described in Chapter 10, its unpaid branch classifies the outstanding loan as defaulted and retains the collateral stock under the stated custody conditions. It does not model foreclosure or collateral liquidation, and it is separate from the five-project program.

### 3. Conditional Cluster Results: Shared Shortages and Price Squeezes

A shared-input cluster theorem takes a finite cohort, common completion node, unit input requirements, and an explicit bound relating accessible stock to demand. Under its shortage bound, it derives a minimum number of blocked projects and composes each with separately supplied purposeful-choice and regret evidence. A one-unit shortfall for two unit-demand projects blocks only one, so at least a two-unit shortfall is needed for two failures. The price-squeeze result likewise takes a stated price response and cash-buffer crossing; it does not derive either from credit issuance alone. In both cases the cohort size and minimum failure count are explicit conditions, not conclusions from a credit shock by itself.

The **five-project physical program** is a separate stateful witness. Each scheduled loan or factor market clears from the actual branch state when its cursor position is reached. The program records matched advances, limits household offers to stated remaining stock, derives completion and sales from acquired inputs and actual output, and records repayment attempts from assigned terms. Refused transfers do not alter inventories and are not retried. This witness checks physical schedules and balances; it does not turn forecast eligibility into physical affordability or prove the scheduled investment purposeful.

### 4. Epistemic Indistinguishability and Observation Equivalence

An epistemic indistinguishability result has a narrower scope:
- In a market setting where bank credit and genuine voluntary saving quote identical gross repayment factors, the derived observation at the decision node is identical across both regimes.
- Under a fixed policy whose input is the stated market observation, the same action is selected under either regime.
- Only an explicit, external source disclosure can distinguish the two regimes; market rate signals alone cannot do so.

This is an observation-equivalence result under the specified information and policy. It does not show that the common action is purposeful, that the policy is rational, or that malinvestment is a necessary response to every credit expansion.

---

## Scope of the Crisis Results

The chapter places several conditional modules side by side: supplied or market-derived loan signals, preference evidence for purposeful action, interpreter-derived inventory outcomes, explicit completion constraints, and contextual regret. The finite witnesses establish particular instances and branch calculations. A full derivation from note issuance through saving, investment, capital formation, crisis, and foreclosure remains outside the represented model.

## Conclusion

We have separated loan origination from repayment and distinguished rate signals, planned eligibility, physical affordability, purposeful choice, and regret. The branch-dependent program verifies the stated physical schedule, while cluster conclusions require their explicit resource, cash, and preference premises. The next chapter examines what observational records can identify about preferences, counterfactuals, and macroeconomic crises.
