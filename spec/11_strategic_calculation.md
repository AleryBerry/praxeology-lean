# Strategic economic calculation: current results and open claims

The core formal framework in
[`Praxeology/EconomicCalculation.lean`](../Praxeology/EconomicCalculation.lean)
separates an information obstruction from the institutional models needed to
apply it, and the companion modules
[`Praxeology/EconomicCalculation/Institutions.lean`](../Praxeology/EconomicCalculation/Institutions.lean)
and
[`Praxeology/EconomicCalculation/Incentives.lean`](../Praxeology/EconomicCalculation/Incentives.lean)
instantiate restricted labor-voucher, input-output/administered-price, and
worker-effort models alongside positive controls and ground `ActionFrame`
witnesses.

## What is proved

### 1. Generic information and strategic reporting
For a state $s$, record $O(s)$, and acceptable-decision relation $G(s,d)$,
[`InformationProblem.solvable_iff_common_decision`](../Praxeology/EconomicCalculation.lean#L42)
proves:

$$
\bigl(\exists f\,\forall s\;G(s,f(O(s)))\bigr)
\quad\Longleftrightarrow\quad
\forall r\in\text{range}(O),\;
\exists d\;\forall s\;(O(s)=r\Rightarrow G(s,d)).
$$

An equal record is insufficient for impossibility unless the states sharing
it have incompatible acceptable decisions
([`unsolvable_of_conflicting_states`](../Praxeology/EconomicCalculation.lean#L67)).
Full-state observation provides a control
([`full_information_control`](../Praxeology/EconomicCalculation.lean#L81)):
if every state has an acceptable decision, a rule seeing that state can choose
one. These statements are about information, not ownership.

[`ReportingProtocol`](../Praxeology/EconomicCalculation.lean#L93) supplies
arbitrary private types, observable local histories, reports, instructions,
physical execution, and ordinal preferences. Strategies may report anything of
the declared report type. Dominant truthfulness is an independently stated
property; when established,
[`truthful_equilibrium_of_dominance`](../Praxeology/EconomicCalculation.lean#L153)
gives an ex-post equilibrium.
[`FullyImplementsPareto`](../Praxeology/EconomicCalculation.lean#L183) requires
both an equilibrium and Pareto efficiency of **every** equilibrium outcome;
[`implementation_requires_equilibrium`](../Praxeology/EconomicCalculation.lean#L188)
extracts that equilibrium premise. When payoffs are invariant across reports
([`ReportPayoffInsensitive`](../Praxeology/EconomicCalculation.lean#L194)),
[`babbling_equilibrium_of_payoff_insensitive`](../Praxeology/EconomicCalculation.lean#L206)
shows every constant reporting profile is an ex-post equilibrium and
[`not_strictly_prefers_truth_of_payoff_insensitive`](../Praxeology/EconomicCalculation.lean#L225)
shows no type strictly prefers truthful reporting.

The executable steps verify physical and accounting transitions: publicly
authorized production is limited by real capacity and stock;
[`WorkLedger.redeem`](../Praxeology/EconomicCalculation.lean#L472) atomically
synchronizes certificate redemption across both the consumer claim ledger and
the public production stock
([`WorkLedger.redeem_stock_sync`](../Praxeology/EconomicCalculation.lean#L495),
[`WorkLedger.redeem_conserves_good`](../Praxeology/EconomicCalculation.lean#L504));
a voluntary spot transfer requires both parties' assent and sufficient goods
and cash; and a capped administrative price can stop moving while excess
demand persists.

### 2. Shared physical economy, ground witness, and restricted interfaces
[`Institutions.lean`](../Praxeology/EconomicCalculation/Institutions.lean)
constructs a finite physical calculation economy (`K1 = 2`, `K2 = 2`, one
consumable setup unit, shared labor capacity `2`) after an executed common
prefix. Method `A` uses `(2 K1, 1 K2, 1 setup, 1 hr)` to produce target `Q`,
and method `B` uses `(1 K1, 2 K2, 1 setup, 1 hr)` to produce the same `Q`
([`method_stock_conservation`](../Praxeology/EconomicCalculation/Institutions.lean#L296),
[`cannot_run_second_method`](../Praxeology/EconomicCalculation/Institutions.lean#L382)).
Downstream actions `D1` (consuming `1 K1` for `C1`) and `D2` (consuming `1 K2`
for `C2`) yield distinct residual affordability
([`downstream_affordability_after_A`](../Praxeology/EconomicCalculation/Institutions.lean#L403),
[`downstream_affordability_after_B`](../Praxeology/EconomicCalculation/Institutions.lean#L419),
[`terminal_outcomes_table`](../Praxeology/EconomicCalculation/Institutions.lean#L441)),
so under ordinal end-attainment preferences ([`acceptable`](../Praxeology/EconomicCalculation/Institutions.lean#L497)),
world `wantsC1` accepts only `B`
([`acceptable_wantsC1_iff`](../Praxeology/EconomicCalculation/Institutions.lean#L508))
and world `wantsC2` accepts only `A`
([`acceptable_wantsC2_iff`](../Praxeology/EconomicCalculation/Institutions.lean#L525)).

Over this same branching physical program, the module proves purposeful
downstream executions in each world
([`wantsC1_downstream_purposeful`](../Praxeology/EconomicCalculation/Institutions.lean#L1025),
[`wantsC2_downstream_purposeful`](../Praxeology/EconomicCalculation/Institutions.lean#L1142))
and constructs the ground `ActionFrame` witness
[`ground_action_frame_calculation_witness`](../Praxeology/EconomicCalculation/Institutions.lean#L1367)
without placing opposite current appraisals on histories sharing one decision
node. It then proves impossibility for the two specified pre-commitment
accounting interfaces in which downstream appraisal reports are absent until
after the irreversible method choice:

- **Labor-voucher interface**: with acyclic embodied-hour coefficients `K1 ↦ 1`,
  `K2 ↦ 1`, `setup ↦ 0` (`laborCost .A = laborCost .B = 4`,
  [`laborCost_equal`](../Praxeology/EconomicCalculation/Institutions.lean#L1424)),
  equal pre-commitment records
  ([`voucher_records_equal`](../Praxeology/EconomicCalculation/Institutions.lean#L1458))
  imply [`voucher_accounting_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1461).
- **Input-output and administered-price interface**: with separate input and
  output matrices, satisfied material constraints
  ([`io_material_constraints_satisfied`](../Praxeology/EconomicCalculation/Institutions.lean#L1470)),
  and a settled pre-signal consumer spot receipt
  ([`preSignalCommonSpot_settled`](../Praxeology/EconomicCalculation/Institutions.lean#L1484)),
  equal records
  ([`io_records_equal`](../Praxeology/EconomicCalculation/Institutions.lean#L1521))
  imply [`io_accounting_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1524).
- **Multi-round transcript and zero-queue quote dynamics**: for any finite
  horizon $n$ with equal initial records and identical permitted replies
  ([`transcript_eq_of_initial_eq`](../Praxeology/EconomicCalculation/Institutions.lean#L1539)),
  [`transcript_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1553)
  proves the $n$-round transcript remains blind. Under the pre-commitment
  order-book rule where future capital-use requests are not yet admissible, zero
  measured factor queues leave arbitrary initial factor quotes unchanged
  ([`precommitment_queue_clears`](../Praxeology/EconomicCalculation/Institutions.lean#L1573),
  [`precommitment_zero_queue_leaves_quotes_unchanged`](../Praxeology/EconomicCalculation/Institutions.lean#L1578),
  [`precommitment_zero_queue_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1585)).
  Separately, [`methods_form_physical_antichain`](../Praxeology/EconomicCalculation/Institutions.lean#L1596)
  and [`methods_in_indeterminacy_cone`](../Praxeology/EconomicCalculation/Institutions.lean#L1599)
  show that the positive price vectors `(1, 3)` and `(3, 1)` reverse the cost
  ranking of `(2, 1)` and `(1, 2)`.

### 3. Controls and exact antichain equivalence
Six positive controls delimit the obstruction:
1. Physical dominance: [`control_physical_dominance`](../Praxeology/EconomicCalculation/Institutions.lean#L1680).
2. Reverse dominance and ties: [`control_reverse_dominance_and_tie`](../Praxeology/EconomicCalculation/Institutions.lean#L1691).
3. Single-factor linearity: [`control_single_factor`](../Praxeology/EconomicCalculation/Institutions.lean#L1703).
4. Shared-appraisal antichain: [`control_successful_antichain`](../Praxeology/EconomicCalculation/Institutions.lean#L1723).
5. Distinguishing pre-commitment report: [`control_distinguishing_report`](../Praxeology/EconomicCalculation/Institutions.lean#L1735).
6. Full-state observation: [`control_full_information`](../Praxeology/EconomicCalculation/Institutions.lean#L1744).

Within the parameterized two-factor bottleneck family
([`acceptableParam`](../Praxeology/EconomicCalculation/Institutions.lean#L1634)),
[`antichain_iff_param_conflict`](../Praxeology/EconomicCalculation/Institutions.lean#L1751)
and
[`param_unsolvable_iff_antichain_of_blind_obs`](../Praxeology/EconomicCalculation/Institutions.lean#L1781)
prove that `PhysicalAntichain xA xB` is both necessary and sufficient for
conflicting acceptable methods and for unsolvability under any world-blind
observation.

### 4. Worker effort incentives under clock-hour vouchers
Separate from information blindness,
[`Incentives.lean`](../Praxeology/EconomicCalculation/Incentives.lean) proves in
a concrete worker `ActionFrame` that when an easy and a hard task both pay one
clock-hour voucher and redeem one food unit while only the hard task supplies an
essential intermediate good, every purposeful worker selects the easy task
([`worker_easy_purposeful`](../Praxeology/EconomicCalculation/Incentives.lean#L508),
[`worker_every_purposeful_selects_easy`](../Praxeology/EconomicCalculation/Incentives.lean#L537))
and starves downstream production
([`purposeful_easy_starves_downstream`](../Praxeology/EconomicCalculation/Incentives.lean#L577)).
In a matched control where both tasks consume equal effort, hard work is
purposeful and leaves downstream production feasible
([`equal_effort_hard_purposeful_and_downstream_feasible`](../Praxeology/EconomicCalculation/Incentives.lean#L723)).

## Scope boundaries and what still requires proof

The calculation theorems above prove impossibility strictly for the **stated
restricted pre-commitment interfaces** where downstream valuation reports
cannot distinguish `wantsC1` from `wantsC2` before the irreversible technique
choice. As emphasized in Ludwig von Mises, *Human Action* (Chapter XXVI, §1,
"The Problem"), a planning analysis that assumes settled valuations of ultimate
ends, full factor inventories, and complete technological recipes to be already
given to the director falls outside this restricted-information boundary
(matching [`control_distinguishing_report`](../Praxeology/EconomicCalculation/Institutions.lean#L1735)
and [`control_full_information`](../Praxeology/EconomicCalculation/Institutions.lean#L1744)).
These theorems therefore do **not** claim universal impossibility of every
mathematical planning method regardless of information available.

| Claim | Current status | Formal coverage / Missing bridge |
|---|---|---|
| Restricted pre-commitment voucher and IO accounting cannot always economize | **Proved** (restricted interface) | Derived on the constructed physical economy in [`voucher_accounting_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1461), [`io_accounting_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1524), and [`transcript_cannot_always_economize`](../Praxeology/EconomicCalculation/Institutions.lean#L1553) |
| Clock-hour vouchers starve effort-intensive bottleneck production | **Proved** (worker model) | Derived from ordinal preferences in [`purposeful_easy_starves_downstream`](../Praxeology/EconomicCalculation/Incentives.lean#L577), with control [`equal_effort_hard_purposeful_and_downstream_feasible`](../Praxeology/EconomicCalculation/Incentives.lean#L723) |
| Full planning impossibility when ultimate valuations are given pre-commitment | Not claimed / Refuted under full info | Shown solvable under distinguishing reports or full information in [`control_distinguishing_report`](../Praxeology/EconomicCalculation/Institutions.lean#L1735) and [`control_full_information`](../Praxeology/EconomicCalculation/Institutions.lean#L1744) |
| Full dynamic Lange tâtonnement across unrestricted multi-agent strategic reports | **Open** | Requires explicit demand/supply formation, budget/bonus rules, strategy incentives, and equilibrium convergence conditions |
| A private factor market always implements Pareto efficiency | **Open** | Requires explicit strategic incentives, settlement, equilibrium existence, and all-equilibrium analysis under the same ordinal preferences |
| Dynamic entrepreneurial discovery and innovation | **Open** | Requires formalizing endogenous discovery, disclosure, adoption, and resulting changes in feasible production menus |

For the labor-certificate reference, see Marx's [*Critique of the Gotha
Programme*, Part I](https://www.marxists.org/archive/marx/works/1875/gotha/ch01.htm).
For the administrative-price reference, see Lange's [*On the Economic Theory
of Socialism*](https://competitionandappropriation.econ.ucla.edu/wp-content/uploads/sites/95/2018/06/LangeEcTheorySocI.pdf).
For Mises's statement of given technological data and ultimate end valuations in the calculation problem, see Mises, *Human Action* (Chapter XXVI, §1, "The Problem").
