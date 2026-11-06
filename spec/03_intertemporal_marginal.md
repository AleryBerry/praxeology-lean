# Specification 03: Allocation, Marginal Sacrifice, and Intertemporal Choice

This specification records the current scope of Praxeology/Marginal.lean and
the new allocation-choice development in Praxeology/Marginal/AllocationChoice.lean.
Formal results are conditional on the stated technology, stock, preference, and
menu assumptions.

## 1. Homogeneous-use allocation

[`HomogeneousUseTechnology`](../Praxeology/Marginal/AllocationChoice.lean#L29)
specifies a finite ordered list of distinct ends.
Each end requires the same positive quantity q of one focal means. The
technology record is independent of the actor's stock and preference.

[`LocalOrdinalAllocationLaws`](../Praxeology/Marginal/AllocationChoice.lean#L70)
states three separate ordinal assumptions about
allocation outcomes:

1. Adding an unused end strictly improves an allocation.
2. Replacing a used lower-ranked end with an unused higher-ranked end strictly
   improves the allocation, with other selected ends held fixed.
3. Preference is transitive over these allocation outcomes.

The combinatorial theorem
[`ranked_prefix_optimality`](../Praxeology/Marginal/AllocationChoice.lean#L368)
derives that the first k
uses are either exactly the allocation or strictly preferred to it, whenever
the allocation has at most k items. Its proof constructs a finite sequence of
improving additions and exchanges, measured by the number of selected items
from the top-k prefix. It does not assume that the prefix globally dominates
every feasible bundle.

[`StockedAllocationContext`](../Praxeology/Marginal/AllocationChoice.lean#L84)
connects this technology to ActionFrame. It records
actual endowment omega = k*q + r with r < q; exact action costs; a map from
feasible actions to allocations; and a realization action for every allocation
that fits the stock. Feasibility of realized allocations follows from the
ActionFrame resource-feasibility law, contemplation, exact costs, and the
strict remainder bound. The theorem
[`StockedAllocationContext.purposeful_choice_is_ranked_prefix`](../Praxeology/Marginal/AllocationChoice.lean#L1144)
then derives the
prefix for a purposeful action from the local ordinal laws.

The repository now includes a finite ordinal witness in the existing
`FiniteBranchingModel`: [`finiteModelRankedTechnology`](../Praxeology/Marginal/AllocationChoice.lean#L437),
[`finite_model_ranked_stock_is_two_units`](../Praxeology/Marginal/AllocationChoice.lean#L488),
and [`finite_model_top_two_beats_nonprefix`](../Praxeology/Marginal/AllocationChoice.lean#L548).
Three distinct ends require one unit of the focal means, the frame gives the
agent two units, and the model's ordinal preference ranks allocation `{0,1}`
above `{0,2}`. The local ordinal laws are derived from the frame's explicit
bundle-rank preference. This is a finite preference-and-technology witness;
it is not an enacted purposeful-choice witness. The existing frame's actions
do not encode every subset allocation, so it cannot yet instantiate
`StockedAllocationContext`'s complete realization map.

The separate [`AllocationActionFrame`](../Praxeology/Marginal/AllocationActionFrame.lean)
does provide a complete menu and enacted purposeful choices inside an
ActionFrame. [`allocationFrame_comparative_stock_witness`](../Praxeology/Marginal/AllocationActionFrame.lean#L829)
uses the same three-use technology and ordinal ranking at stocks one and two;
the agents purposefully select `{0}` and `{0,1}`, and the next use is strictly
lower ranked. The companion theorem
[`allocationFrame_prefix_has_purposeful_execution`](../Praxeology/Marginal/AllocationActionFrame.lean#L876)
constructs a realized history for either agent's ranked prefix.

The finite allocation model also proves the q=2 capacity and purposeful-choice
tables for stocks zero through four, and unit-use satiation after the three
listed ends. These are finite menu results, not claims that actual wants are
exhausted or that every technology has homogeneous requirements.

## 2. Legacy allocation results

[`LegacyUnitRequirementSchedule`](../Praxeology/Marginal.lean#L164) combines end requirements, a stock equality,
and the agent's ranking in one record.
[`LegacyBundleAllocationMenu`](../Praxeology/Marginal.lean#L301) assumes
that a designated prefix outcome is preferred to every other feasible
allocation through its h_opt_dominates field. This helper is private; results
using that field do not derive optimal allocation from purposeful choice and
the helper is not part of the public API.

[`LegacyTeleologicalQuantumRegime`](../Praxeology/Marginal.lean#L783) and
the private `LegacyTeleologicalBundleSystem` have the same limitation: the
latter assumes its designated prefix globally dominates each feasible
alternative. The schedule lemmas remain, but the optimality-assuming helper
is not public and is not the current allocation-choice result. Legacy
imputation lemmas also inherit that premise and should be read conditionally.

## 3. Marginal sacrifice and complementarity

[`finite_preference_relation_has_least_element`](../Praxeology/Marginal.lean#L1026)
is an order-theoretic result:
transitivity on a finite nonempty set gives an element with no strictly
preferred successor in that set. By itself it does not prove that reducing a
physical stock causes the actor to abandon that end. That economic conclusion
also needs a feasible allocation, an actual stock change, and a preference
bridge between the lost stock and the foregone end.

[`Marginal/ComplementarityWitness.lean`](../Praxeology/Marginal/ComplementarityWitness.lean)
specifies the pair technology directly: each pair requires one left shoe and
one right shoe. [`unmatched_left_shoe_stock_does_not_attain_pair`](../Praxeology/Marginal/ComplementarityWitness.lean#L111)
shows that two left shoes and no right shoe do not attain one pair. The named
walking end has the same one-left-and-one-right requirement:
[`extra_left_stock_does_not_enable_walking`](../Praxeology/Marginal/ComplementarityWitness.lean#L92)
proves that two left shoes and no right shoe do not enable walking, and
[`complementary_stock_enables_walking`](../Praxeology/Marginal/ComplementarityWitness.lean#L98)
shows that one of each shoe suffices under the stated technology. The theorem
[`unmatched_left_inventory_does_not_change_walking`](../Praxeology/Marginal/ComplementarityWitness.lean#L105)
proves that adding a second left shoe while right stock remains zero does not
change walking attainability. The theorem
[`unmatched_left_inventory_same_attainable_pair_counts`](../Praxeology/Marginal/ComplementarityWitness.lean#L125)
proves that increasing left stock from one to two leaves every pair count's
attainment unchanged when right stock is zero. The subjective-gain result
[`unmatched_left_inventory_no_subjective_teleological_gain`](../Praxeology/Marginal/ComplementarityWitness.lean#L163)
additionally assumes that the only valued end is one pair. The separate
bounded-menu satiation witness is limited to wants of at most one pair.

The arithmetic result
[`quantum_capacity_bound_for_subquantum_remainder`](../Praxeology/Marginal.lean#L984)
says
that a remainder smaller than q cannot finance an additional complete use
when every listed end requires q units. This is an allocation-capacity bound,
not a theorem that the remainder has no economic use in every technology.

## 4. Time preference and interest

[`causal_enacted_consumption_demonstrates_nonneg_time_pref`](../Praxeology/Marginal.lean#L1123)
derives that, when a
later same-end action remains feasible in the modeled open horizon, purposeful
enactment rules out preferring that later outcome to the enacted outcome. It
does not derive strict preference from purposefulness alone.

[`strict_time_preference_from_distinct_end_dominance`](../Praxeology/Marginal.lean#L1178)
has stronger premises. It
assumes the enacted action dominates every feasible action with a distinct
outcome (DistinctEndDominantAct), an available later deferral, and injective
timed ends. Under those assumptions it derives strict preference for the
nearer dated end. It is not a universal theorem about every act or every
agent.

[`positive_originary_interest`](../Praxeology/Marginal.lean#L1240) and
[`purposeful_positive_originary_interest`](../Praxeology/Marginal.lean#L1272)
derive a larger future repayment quantity in the specified exchange setup.
Their conclusions depend on strict time preference, an accepted exchange,
synchrony monotonicity, transitivity, or purposeful choice with a feasible
present alternative. They do not establish a universal market rate or a
positive nominal rate in every monetary institution.

## 5. Seasonal saving and production

[`winter_security_preference_consequences_of_explicit_premises`](../Praxeology/Marginal.lean#L1478)
assumes the relevant dated preferences and their ordering. It packages those
premises into a consistency result; it does not derive seasonal saving from
the ActionFrame axioms or establish that all saving expresses positive time
preference. The separate `earlier_control_preferred_from_storage_and_security`
result derives a preference between control bundles when storage preserves
later valued plans and an additional valued service is available only under
earlier control. `current_security_choice_is_purposeful` derives purposeful
action only from the explicit execution, valuation, preference, and
undominated-choice evidence in its input record.

Roundabout-production and capital-epoch results likewise depend on the
specific feasibility, preference, and production hypotheses named by each
theorem. Consult the Lean declaration before treating any such result as a
general necessity claim.
