# Strategic economic calculation: current results and open claims

The [formal module](../Praxeology/EconomicCalculation.lean) separates an
information obstruction from the institutional argument needed to apply it.
Its proofs are over arbitrary state and report types, not two hard-coded
economies.

## What is proved

For a state $s$, record $O(s)$, and acceptable-decision relation $G(s,d)$,
`InformationProblem.solvable_iff_common_decision` proves:

$$
\bigl(\exists f\,\forall s\;G(s,f(O(s)))\bigr)
\quad\Longleftrightarrow\quad
\forall r\in\operatorname{range}(O),\;
\exists d\;\forall s\;(O(s)=r\Rightarrow G(s,d)).
$$

An equal record is insufficient for impossibility unless the states sharing
it have incompatible acceptable decisions. Full-state observation provides a
control: if every state has an acceptable decision, a rule seeing that state
can choose one. These statements are about information, not ownership.

`ReportingProtocol` supplies arbitrary private types, observable local
histories, reports, instructions, physical execution, and ordinal preferences.
Strategies may report anything of the declared report type. Dominant
truthfulness is an independently stated property; when established, it gives
an ex-post equilibrium. `FullyImplementsPareto` requires both an equilibrium
and Pareto efficiency of **every** equilibrium outcome. The physical feasible
set is independent of the institution's legal permissions.

The module's executable steps verify narrower physical and accounting facts:
publicly authorized production is limited by real capacity and stock;
certificate redemption consumes personal claims and existing goods; a
voluntary spot transfer requires both parties' assent and sufficient goods
and cash; and a capped administrative price can stop moving while excess
demand persists. Expanded capacities, stocks, and authorizations preserve
the feasibility of old production runs when their inputs are unchanged.

## What still requires proof

| Claim | Current status | Missing bridge |
|---|---|---|
| Public ownership prevents calculation | Open | A legal and reporting protocol that *derives* incompatible states from actual records |
| Labor certificates induce truthful work and efficient production | Open | Verified effort, public deductions, labor-cost accounting, rationing, compensation, and all strategic deviations |
| Lange adjustment clears and coordinates production | Open | An explicit multi-round protocol, demand and supply formation, strategy incentives, and convergence conditions |
| A private market always implements Pareto efficiency | Open | Incentives, settlement, equilibrium existence, and all-equilibrium analysis under the same ordinal preferences |
| Innovation worsens either institution | Open | Discovery, disclosure, adoption, and the resulting observation and strategy changes |

These are open questions rather than implicit theorem hypotheses. The earlier
[`action_frame_socialist_calculation_impossibility`](../Praxeology/Catallactics.lean)
assumes the two economies, equal records, and opposite appraisals. It does not
instantiate a labor-certificate economy, a Lange price process, or a private
factor market. The present module makes the next tests expressible and checks
some necessary physical rules, but it does not yet settle the institutional
comparison.

For the labor-certificate reference, see Marx's [*Critique of the Gotha
Programme*, Part I](https://www.marxists.org/archive/marx/works/1875/gotha/ch01.htm).
For the administrative-price reference, see Lange's [*On the Economic Theory
of Socialism*](https://competitionandappropriation.econ.ucla.edu/wp-content/uploads/sites/95/2018/06/LangeEcTheorySocI.pdf).
