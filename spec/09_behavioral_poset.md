# Specification 09: Preference structure and behavioral examples

This page documents the endogenous preference and choice declarations in
[`Praxeology/Action.lean`](../Praxeology/Action.lean) and
[`Praxeology/StateMonopoly.lean`](../Praxeology/StateMonopoly.lean).
The modules give structural results and formal examples; they do not
empirically explain or refute behavioral-economic findings.

## 1. Asymmetry and transitivity

[`preference_irrefl`](../Praxeology/Action.lean#L1853) records irreflexivity
and [`preference_asymm`](../Praxeology/Action.lean#L1858) records asymmetry
directly on `W.Preference i t h`. An ActionFrame's contextual preference relation
is irreflexive and asymmetric at each decision node.
These results do not imply completeness, numerical utility, or global transitivity.

## 2. Changes across decision contexts

[`framing_reversal_requires_context_distinction`](../Praxeology/Action.lean#L1875)
shows that opposite strict comparisons cannot both hold at the same agent,
moment, and history. If both comparisons are supplied, either the moments or
the histories must differ. This is a consistency observation about
context-indexed relations, not a model of how framing causes a preference
reversal.

[`hyperbolic_reversal_requires_distinct_moments`](../Praxeology/Action.lean#L1891)
is the corresponding implication for two temporal comparisons: opposite
comparisons require a distinct moment or history. It does not construct a
hyperbolic discounting schedule or prove that an agent acts purposefully at
both nodes.

The declaration [`loss_aversion_endowment_distinction`](../Praxeology/Action.lean#L1939)
proves that two histories with different endowments of a specified means
are distinct.

## 3. Menu dependence and social aggregation

[`bounded_contemplation_purposeful_act`](../Praxeology/Action.lean#L1950)
uses the ActionFrame coupling between feasible and contemplated actions: an
uncontemplated action is not feasible, while purposefulness rules out a
strictly preferred action within the modeled feasible menu.

[`precommitment_prunes_temptation`](../Praxeology/Action.lean#L1902)
derives membership and nonmembership from two stipulated downstream menus. Its
finite witness instantiates a menu difference.

[`action_frame_majority_cycle`](../Praxeology/StateMonopoly.lean#L824)
shows that across three agents with individually transitive preferences,
the aggregated majority relation `ActionFrameMajorityPref` can cycle.
This is a social-choice result; the conclusion concerns the defined majority relation
and does not attribute an action to a collective agent.
