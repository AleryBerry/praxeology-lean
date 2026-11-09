# Chapter 13: Business Cycles and Crisis

Chapters 4 and 7 introduced tools for analyzing complementary requirements, capital, and intertemporal choice. Chapters 10 and 11 incorporated credit advances, price uncertainty, and organizational production. We now combine these elements into a formal model of investment and crisis.

This chapter formalizes the integrated causal sequence of Austrian Business Cycle Theory through an explicit composition of credit signals, purposeful choice, physical inventory transitions, completion bottlenecks, and evaluative regret. The formalization preserves the categorical independence of each causal link: an artificial suppression of loan quotes does not mechanically force entrepreneurial investment without an evaluating actor; planned cash eligibility does not create physical factor supplies; and completion obstructions depend strictly on the presence or absence of complementary goods along specific historical branches. The five-project physical program formalizes early-input purchases, capital formation, household deposit origination and redemption, current-cash factor market clearing, and contractual unpaid-maturity settlement. Integrated behavioral theorems verify purposeful bank note issuance, purposeful household saving under explicit terminal preferences, subjective purposefulness for marginal borrower entry under a four-factor forecast, and contextual regret on the default path relative to cautious refusal.

The conditional chain studied here has five possible components:
1. **Origination and rate evidence:** An enacted advance and a loan quote can be established independently of whether the loan is later repaid. Rate comparisons require the stated market or repayment evidence.
2. **Purposeful investment:** This requires explicit feasibility, enactment, and preference evidence at the declared evaluation horizon.
3. **Physical transition:** Inventory balances determine what capital goods and complementary factors are present after the represented operations.
4. **Completion obstruction:** Completion fails only when the required physical input or monetary input is absent under the model's feasibility rule.
5. **Contextual regret:** Regret additionally requires a safe alternative, a shared compatible context, physically grounded outcomes, and the relevant preference comparison.

### Branch-Sensitive Execution in the Five-Project Example

The executable example in `BusinessCycle.ProfileProgram` is a finite physical ledger. Its generated phase list determines the number and order of execution steps. At each step, the inventory interpreter produces the next physical state, while the cursor records a transaction only when the relevant action is enacted: exchanges require matching offers and acceptances, production records require the corresponding operation, and later sales, repayments, and maturity settlement use the inventory and contract terms then present. The event trace is the source of the cursor's transaction summaries.

Loan capacity is cleared from the bank's cash after the note-issuance and household-transfer steps. The program records an advance only when the lender's offer and borrower's acceptance match. When the factor market is reached, it uses those recorded advances and factors currently available for sale. Factor market clearing evaluates each project's actual post-early-input cash balance (`currentCash`), directly accounting for early-input expenditures. In the fiduciary regime, each funded borrower holds $2$ units of current cash ($1 + 6 - 5 = 2$), clearing the 2-unit factor market at price $2$. Completion is proposed only for projects with a matched factor purchase. Customer offers use output actually held and customer money remaining. Repayment attempts use recorded advances and their promised terms. A failed action still uses its scheduled phase, so the generator does not silently retry it; a clearing result already recorded is not retroactively repriced.

The household's finite plan menu separates deposit quantity, factor consumption, and factor offers; factors not offered remain in household inventory. A matched deposit exchange creates the recorded claim and bank liability, and redemption requires a later matched transfer. Consumption services are recorded separately from physical stocks. The named physical path selects one plan by schedule. A separate ActionFrame theorem proves the selected household plan purposeful under the stated preference over deposit balance, services, money, and retained holdings, grounding household participation in explicit teleological choice.

The physical program establishes accounting for the selected path and makes refusal branches available for comparison. In `BehavioralProgram.lean` and `BehavioralChoices.lean`, the frame additionally proves purposeful bank note issuance, purposeful household saving, subjective purposefulness for the two marginal borrowers under a four-factor forecast, and purposeful cautious refusal at the natural quote. The program also proves contextual regret for each marginal borrower on the actual default path: under the explicit collateral-first preference, declining the loan preserves collateral that the actual acceptance branch loses at contractual settlement.

The physical boundary with four funded projects and only two completion inputs is fully resolved by three explicit theorems:
1. **Repayment without Completion via Larger Buffers**: If all borrowers receive 4-unit cash buffers (`fiveProject_larger_buffers_repayment_without_completion_causes_loss`), uncompleted borrowers $[2, 3]$ repay their debt out of pocket to protect collateral, suffering an outright net cash loss ($0 < 4$) while physical completions remain strictly $[0, 1]$.
2. **Displacement via Single Borrower Buffer**: Giving borrower 2 a cash buffer of 3 (`fiveProject_single_borrower_buffer_displacement`) raises the factor clearing price to 3 and shifts completions from $[0, 1]$ to $[0, 2]$, displacing borrower 1 while still leaving 2 funded borrowers uncompleted.
3. **Factor Conservation Bound**: Across all four regimes (`fiveProject_factor_conservation_bound`), the number of completed projects is strictly bounded by $\le 2$ (the physical supply of complementary factors). More cash alone supplies no missing physical input.

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

This definition isolates the pure mathematical divergence between natural and credit rate thresholds. In [Chapter 10](10_entrepreneurship_credit_and_investment.md#chapter-10-entrepreneurship-credit-and-capital-markets), the corresponding market origination theorems derive how note expansion generates this rate spread, while repayment comparisons trace the borrower's cash balance across execution histories.

## Purposeful Investment Grounded in Credit and Bundle Dominance

To establish purposeful investment, rate comparisons are evaluated through projected bundles calculated from the contract's promised terms. Feasibility, enactment, and preferences are explicitly represented within the Action Frame. The finite program adapter defines the evaluation horizon, grounding comparisons in physical inventory bundles across specified decision horizons.

### Proposition 13.2 (Conditional Credit-Rate Investment Comparison)

Suppose a fiduciary credit origination supplies principal $P$ at suppressed gross repayment factor $r_c < r_n$, funding an investment action $\alpha$:
1. At the natural rate $r_n$, the projected bundle after the promised repayment does not improve upon inaction, so $\alpha$ is not a purposeful active choice ( $\neg \mathsf{P}$ );
2. At the credit rate $r_c$, the loan advance provides the stated money input, other required inputs are available, and the projected bundle after promised repayment strictly teleologically dominates inaction;
3. By `teleological_bundle_dominance_induces_preference`, $\alpha$ is strictly preferred to inaction and undominated among feasible alternatives;
4. The entrepreneur enacts $\alpha$.

Then, under the stated appraisal, feasibility, and enactment conditions, $\alpha$ is non-purposeful at the natural rate and purposeful at the credit rate.

**Proof.** At the natural rate, the stated appraisal condition fails the improvement-over-inaction requirement for an active purposeful act. At the credit rate, the matched advance supplies the stated money input, while the other physical inputs must also meet the feasibility condition. Enactment, preference for the projected bundle over inaction, and undominatedness among feasible alternatives are separate premises or derived from the stated bundle-dominance result. Together these establish the complete requirements of `PurposefulAct`, demonstrating how favorable rate terms and bundle dominance jointly actuate purposeful entrepreneurial entry. $\square$

## Capital Formation and a Missing Complementary Factor

Capital accumulation in the model is an observed physical transition. It may be a production step or an exchange. To establish that one unit of capital is present at the next moment, require zero initial stock, zero effective use of that capital in the transition, and effective yield one. The inventory balance then gives the stated next stock.

The completion obstruction is a separate condition. Let $m_c$ be a complementary means. Suppose its initial stock is zero, the capital-formation transition neither uses nor yields $m_c$, and the later completion action requires one unit of $m_c$. The inventory balance leaves the stock at zero, so the completion action is physically infeasible.

### Proposition 13.3 (Complementary-Factor Starvation Blocks Completion)

Under the preceding conditions, the next stock of capital is one, the next stock of $m_c$ is zero, and the completion action is infeasible at the next moment.

**Proof.** Apply the inventory balance separately to capital and to $m_c$. The capital equation is $\omega_{next}+0=0+1$, hence $\omega_{next}=1$. The complementary-factor equation is $\omega_{next}+0=0+0$, hence $\omega_{next}=0$. Since completion requires one unit and $0<1$, it violates the resource condition for feasibility. $\square$

This proposition rigorously demonstrates the Austrian capital-theoretic principle: in complementary multi-stage production, intermediate capital goods cannot be brought to completion when a required complementary input is physically absent.

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

Substitute stocks may count differently when the model assigns them a penalty. Let $p>0$ be that penalty factor. To preserve exact discrete precision and prevent information loss from integer division, the technological requirement is formulated in cross-multiplied form.

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

### Proposition 13.7 (Liquidation Implies Primary Buffer Deficit)

Under any penalized substitution technology with penalty $p > 0$, if the technology is in the liquidation regime, the primary buffer stock alone strictly falls short of the requirement:

$$
b \cdot p + s < q \cdot p \implies b < q.
$$

**Proof.** Suppose toward a contradiction that $b \ge q$. Then $b \cdot p \ge q \cdot p$. Since $s \ge 0$, we have $b \cdot p + s \ge q \cdot p$, which directly contradicts the strict inequality of the liquidation regime $b \cdot p + s < q \cdot p$. Hence $b < q$. $\square$

### Proposition 13.8 (A Penalty Can Change the Completion Classification)

For every natural-number penalty $p\ge2$, the stocks $b=2$, $s=4$, and $q=5$ meet the unpenalized absorption condition but satisfy penalized liquidation:

$$
5\le2+4
\qquad\text{and}\qquad
2p+4<5p.
$$

**Proof.** The first inequality is $5\le6$. Since $p\ge2$, we have $3p\ge6>4$, hence $2p+4<5p$. Thus total unweighted stock meets the requirement, while the penalized comparison falls strictly short. $\square$

For example, at $p=2$, the unweighted total is $2+4=6$, which meets the requirement $5$, while weighted coverage is $2\cdot2+4=8<10=5\cdot2$. The same stock record is therefore classified differently under the two stated completion rules. This theorem demonstrates how substitution parameters strictly alter project feasibility thresholds under input constraints.

These two constructions model distinct aspects of production bottlenecks: the first analyzes substitution thresholds, while the second traces historical transitions under missing complementary factors.

## Regret under a Shared Context

In this framework, regret compares an actual investment with a feasible safe action under one context correspondence. The correspondence must admit both action-history-maturity combinations in that context. In addition, outcomes must be grounded in physical endowments, and the safe bundle must teleologically dominate the actual bundle at the evaluation point. Under these conditions, teleological bundle dominance natively induces the relevant strict preference (`teleological_bundle_dominance_induces_preference`), and the common-context definition records regret.

### Theorem 13.9 (The Austrian Business Cycle Master Theorem)

Suppose the signal pair holds; a transition forms one unit of capital; completion is blocked; the investment is purposeful at the investment decision; and the actual investment and safe alternative are admitted by a common compatible context. If outcomes are determined by physical endowments and the safe bundle dominates the actual bundle at the evaluation point, then the model entails contextual regret for the investment relative to the safe action.

**Proof.** The common compatible context admits both the actual investment and the safe alternative. Physical grounding identifies their matured outcomes with the corresponding stock bundles. The safe bundle's stipulated strict teleological dominance, together with `teleological_bundle_dominance_induces_preference`, makes the safe outcome strictly preferred in that shared context. By the definition of contextual regret, these facts establish regret relative to the safe action. $\square$

This conclusion unites the rate signal, physical capital formation, purposeful choice, and ex-post evaluation into a rigorous theorem of malinvestment regret.

## A Price-Box Cash Obstruction

Suppose completion requires a monetary input equal to the precautionary cash demand calculated from a factor-price box and a vector of factor quantities. If the agent's cash stock is strictly below that amount, completion is infeasible. This follows from the definition of feasibility and the stated cost equality.

### Proposition 13.10 (Cash Shortfall Blocks a Costed Completion)

Let $C$ be the monetary input required by a completion action, and suppose $C$ equals the precautionary cash demand associated with the stated price box and factor quantities. If available cash is less than that demand, the completion action is infeasible.

**Proof.** The stipulated equality identifies the action's required monetary input with the stated demand. The cash-shortfall inequality says that this requirement exceeds the agent's monetary endowment. The feasibility test therefore fails for this action. $\square$

This proposition establishes an exact affordability threshold: when factor market prices rise to match precautionary demand, an entrepreneur with cash below that threshold is physically blocked from completing the factor purchase.

When this cash shortfall supplies the blocked-completion premise in [Theorem 13.9](#theorem-139-the-austrian-business-cycle-master-theorem), the contextual regret conclusion follows directly.

### An Endogenous Two-Stage Price-Box Squeeze

The stronger price-box result traces how the shortfall can emerge after investment. Suppose the investment transition uses money but yields none. Before investment, cash covers both the stage-one expenditure and the completion demand computed from a pre-investment price box. Then suppose the post-investment box is weakly wider at every factor, while the upper price of a factor used in positive quantity rises strictly. If the completion action's money requirement equals the new precautionary demand and the original cash is less than stage-one spending plus that widened demand, the inventory balance shows that the remaining cash still covered the old demand but cannot cover the new one. Price-box widening strictly increases precautionary cash demand, exhausts the buffer, and makes completion infeasible.

The Cantillon result supplies a one-factor instance of this certificate. Let the factor quantity be one, set the pre- and post-box upper prices to $P_{\mathrm{pre}}$ and $P_{\mathrm{post}}$, and let downstream cash be $M$ with $P_{\mathrm{pre}}\le M < P_{\mathrm{post}}$. The earlier cash demand is affordable, while the completion action priced at $P_{\mathrm{post}}$ exceeds the downstream balance. This converts the purchasing-power dilution result into a price-box completion squeeze.

### Grounding Stranded-Capital Regret in Valued Ends

The physical comparison can also be derived from end requirements. Suppose the safe branch preserves every finite set of ends valued at the actual evaluation point that the actual branch can attain. Suppose further that the safe branch attains a valued target end whose money requirement exceeds actual cash. The actual bundle cannot attain that target, while the safe bundle can; together with preservation of all actual attainable valued sets, this proves strict teleological dominance of the safe bundle. When outcomes are grounded in inventories and teleological bundle dominance induces preference, the safe action is strictly preferred in a shared evaluation context, providing the regret comparison.

## Tracing Credit into Feasibility

We now make the funding step explicit. A matched loan advance transfers principal to the borrower and collateral to the lender. To use that advance as evidence for a later investment, we must trace the borrower's money stock between the transfer and the investment decision.

### Proposition 13.11 (An Unspent Advance Can Cover the Project's Money Input)

Suppose a lender transfers principal $P$ to a borrower at a moment on history $h$. Let the advance be followed by a later decision moment $t$ on that same history. If the borrower uses no units of the loan's money between receipt of the advance and $t$, then the borrower's money stock at $t$ is at least $P$. Consequently, if the investment requires at most $P$ units of that money and every other required input is available, a contemplated investment is feasible at $t$.

**Proof.** The matched transfer raises the borrower's stock by $P$, so immediately after the advance that stock is at least $P$. The inventory-run balance says that the later stock plus money used along the run equals the initial post-advance stock plus money yielded along the run. Money use is zero and money yield is nonnegative, so the later stock is at least the post-advance stock and hence at least $P$. The investment's money input is no greater than $P$; by hypothesis each other input is covered. The feasibility definition therefore applies. $\square$

The inventory trace establishes the rigorous physical conservation link between loan receipt and downstream feasibility.

## Composing the Conditional Cycle Components

The business-cycle causal chain is formulated as an explicit, modular composition of praxeological conditions: loan-market clearing establishes the quoted interest rate; subjective expectations and preference rankings govern purposeful entry; physical inventory transitions govern capital formation and factor stocks; complementary resource scarcity determines completion feasibility; and ex-post evaluation in a shared context determines regret. The five-project program formalizes each transition along branch-dependent execution paths, computing loan allocation, early-input transformation, factor bidding, project completion, customer sales, and contractual settlement from actual state variables.

Accordingly, the result below composes these links into a unified intertemporal cycle theorem. Each premise—the rate signal, the purposeful choice, the physical factor constraint, and the regret comparison—is stated explicitly to demonstrate how microeconomic choices and material limits jointly determine the systemic outcome.

### Theorem 13.12 (The Fiduciary Factor Starvation Cycle Theorem)

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

**Proof.** Premise 2 supplies the purposeful-choice comparison at the stated appraisal and horizon. The inventory transition in premise 3 records intermediate capital while complementary stock is zero. Since the completion action requires a positive quantity of that absent factor, feasibility fails. Premise 5 supplies the common-context, physical-grounding, and preference evidence for regret relative to the safe alternative. The theorem explicitly integrates these structural conditions, demonstrating how monetary loan terms, physical inventory scarcity, and teleological preference structures jointly produce the crisis dynamic. $\square$

### Proposition 13.13 (A Cash Shortfall Blocks a Required Spot-Factor Purchase)

Suppose completion requires a factor that the entrepreneur does not hold, the factor is offered only through a spot purchase at price $P$, and the entrepreneur's available balance of the specified money good is less than $P$. Then the spot acceptance is infeasible; if that factor is a necessary completion input, completion is physically infeasible as well.

**Proof.** Spot acceptance requires at least $P$ units of the specified money good. The stipulated balance is smaller, so the feasibility condition fails. If the factor is required for completion and is not otherwise available, the completion action also fails its input condition. This proposition isolates the exact physical-liquidity mechanism: an unbacked cash deficiency strictly prevents spot-factor acquisition and forces project cessation, which [Theorem 13.9](#theorem-139-the-austrian-business-cycle-master-theorem) integrates with purposeful choice and contextual regret. $\square$

## Organized Production and Finite Illustrations

The cycle can also occur inside an organization. In a three-person construction, a principal directs an operator to produce an intermediate good. The operator accepts the assignment and later transfers one unit of the intermediate good to the principal under an authorized internal exchange. The principal then sells an output to an independently governed customer. The model places the production task, internal transfer, and external sale on one history and orders the sale after the work. If the transfer supplies the principal's capital good while the required complementary input remains absent, the same completion obstruction applies. A shared evaluation context and a valued safe bundle supply the regret comparison.

This organized-production model demonstrates the structural generality of the completion obstruction within multi-agent hierarchies, combining internal workflow directives, physical capital accumulation, and complementary factor constraints.

---

## Model-Theoretic Witnesses for the Business Cycle

The formalization constructs dedicated finite witnesses for distinct theoretical milestones, rigorously validating the physical and logical realizability of each configuration within concrete Action Frames.

### 1. The Grounded ABCT Action Frame Witness

The **Grounded ABCT Action Frame** provides an explicit, constructive witness for a matched credit investment, a complementary input shortage, blocked completion, purposeful choice, and contextual regret, formally demonstrating the joint mathematical consistency of the praxeological business-cycle sequence.

### 2. The Complete Credit Lifecycle Witness

The **Credit Lifecycle Action Frame** represents issuance, matched advance, later repayment and unpaid-maturity branches. As established in [Chapter 10](10_entrepreneurship_credit_and_investment.md#chapter-10-entrepreneurship-credit-and-capital-markets), its unpaid branch formally classifies the outstanding obligation as defaulted and tracks collateral retention under strict custodial balance constraints. The five-project program further integrates this into an explicit contractual unpaid-maturity branch within a comprehensive dynamic clearing environment.

### 3. Conditional Cluster Results: Shared Shortages and Price Squeezes

The shared-input cluster theorems analyze finite cohorts of simultaneous investment projects under aggregate factor shortages. Under explicit bounds relating available factor stocks to aggregate demand, the theorem derives the minimum number of unfinishable projects, proving how complementary factor scarcity mathematically forces project abandonment across multi-entrepreneur cohorts. In parallel, the price-squeeze theorem formally derives project infeasibility whenever bidding for scarce factors depletes an entrepreneur's cash reserves below the spot threshold.

The **five-project physical and behavioral program** (`ProfileProgram.lean`, `BehavioralProgram.lean`, `BehavioralChoices.lean`, `IntegratedResults.lean`, and `MasterResults.lean`) compiles this entire sequence into a checked finite `ActionFrame`:
- **Current-Cash Clearing**: Loan and factor markets clear from actual branch states. At the factor stage, bidding uses current post-early-input cash, clearing at price $2$.
- **Integrated Purposeful Choices and Physical Consequences**: Proves bank note issuance expanding advances (`fiveProjectBankNoteIssuance_expands_advances`), purposeful household saving (`fiveProjectHouseholdSaving_purposeful`), purposeful borrower entry for Projects 2 and 3 under the 4-factor optimistic forecast (`fiveProjectProjectTwoEntry_purposeful`, `fiveProjectProjectThreeEntry_purposeful`), and cautious refusal avoiding defaults at the natural quote 6 (`fiveProjectCautiousProjectTwoRefusal_avoids_default`, `fiveProjectCautiousProjectThreeRefusal_avoids_default`).
- **Unilateral Replay and Default**: Proves that replacing cautious refusal with credit acceptance replays factor bidding, clears the factor market at price 2, leaves Projects 2 and 3 uncompleted, and triggers contractual default settlement.
- **Derived Contextual Regret**: Derives contextual regret (`ContextualRegret`) for Projects 2 and 3 on their actual default histories relative to the safe cautious refusal branch.
- **The Master Cycle Theorem**: Formalized in `MasterResults.lean` as `austrian_business_cycle_master_theorem` and instantiated concretely by `fiveProject_fiduciary_causal_cycle_master`.

### 4. Epistemic Indistinguishability and Observation Equivalence

An epistemic indistinguishability result has a narrower scope:
- In a market setting where bank credit and genuine voluntary saving quote identical gross repayment factors, the derived observation at the decision node is identical across both regimes.
- Under a fixed policy whose input is the stated market observation, the same action is selected under either regime.
- Only an explicit, external source disclosure can distinguish the two regimes; market rate signals alone cannot do so.

This theorem formally establishes an epistemic boundary: identical quoted interest rates across fiduciary and non-fiduciary regimes produce observationally equivalent signals, proving that entrepreneurs facing uniform market quotes cannot distinguish credit expansion from genuine voluntary saving without explicit institutional disclosure.

---

## Scope of the Crisis Results

The formalization brings together the physical and behavioral components of the Austrian Business Cycle within an explicit `ActionFrame`: supplied or market-derived loan signals, subjective scenario forecasts, interpreter-derived inventory outcomes, current-cash factor auctions, contractual default settlements, purposeful choices, and contextual regret. The Master Theorem verifies that when these explicit premises hold together, fiduciary expansion induces entrepreneurial entry, bids up complementary factor prices, starves later projects of completion inputs, and triggers contractual defaults and regret, providing a rigorous, axiomatically verified foundation for the Austrian theory of capital misallocation.

## Conclusion

The branch-dependent program establishes the complete physical schedule and behavioral cascade, while the cluster theorems rigorously delineate the exact resource, cash, and preference conditions governing structural crises. [Chapter 14](14_historical_observation_and_identification.md#chapter-14-historical-observation-and-identification) examines what observational records can formally identify about preferences, counterfactuals, and macroeconomic crises.
