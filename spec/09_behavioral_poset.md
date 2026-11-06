# Specification 09: Preference structure and behavioral examples

This page documents the declarations in
[`Praxeology/BehavioralPoset.lean`](../Praxeology/BehavioralPoset.lean).
The module gives structural results and small formal examples; it does not
empirically explain or refute behavioral-economic findings.

## 1. Asymmetry and transitivity

[`StrictPreference`](../Praxeology/BehavioralPoset.lean#L28) records irreflexivity
and asymmetry. [`StrictPoset`](../Praxeology/BehavioralPoset.lean#L34) adds
transitivity as a separate field. An ActionFrame's preference relation
instantiates `StrictPreference` by its asymmetry law.
[`action_frame_strict_poset`](../Praxeology/BehavioralPoset.lean#L106) additionally
requires a transitivity proof; the base ActionFrame laws alone do not provide
one. These results do not imply completeness or a numerical utility
representation.

## 2. Changes across decision contexts

[`framing_reversal_requires_context_distinction`](../Praxeology/BehavioralPoset.lean#L125)
shows that opposite strict comparisons cannot both hold at the same agent,
moment, and history. If both comparisons are supplied, either the moments or
the histories must differ. This is a consistency observation about
context-indexed relations, not a model of how framing causes a preference
reversal.

[`hyperbolic_reversal_requires_distinct_moments`](../Praxeology/BehavioralPoset.lean#L141)
is the corresponding implication for two temporal comparisons: opposite
comparisons require a distinct moment or history. It does not construct a
hyperbolic discounting schedule or prove that an agent acts purposefully at
both nodes.

The declaration [`loss_aversion_endowment_distinction`](../Praxeology/BehavioralPoset.lean#L189)
only proves that two histories with different endowments of a specified means
are distinct. Despite its name and docstring, it does not define loss aversion
or derive a choice pattern from reference-dependent preferences; the broader
loss-aversion claim has been removed from this specification.

## 3. Menu dependence and social aggregation

[`bounded_contemplation_purposeful_act`](../Praxeology/BehavioralPoset.lean#L206)
uses the ActionFrame coupling between feasible and contemplated actions: an
uncontemplated action is not feasible, while purposefulness rules out a
strictly preferred action within the modeled feasible menu. This says nothing
about what the agent would choose if the menu or contemplation set changed.

[`precommitment_prunes_temptation`](../Praxeology/BehavioralPoset.lean#L152)
derives membership and nonmembership from two stipulated downstream menus. Its
finite witness instantiates a menu difference. Neither result proves that
precommitment is purposeful or welfare-improving.

[`condorcet_majority_cycle_of_strict_posets`](../Praxeology/BehavioralPoset.lean#L271)
constructs three transitive strict preference orders over three alternatives
whose pairwise-majority relation cycles. This is a finite social-choice
example; the conclusion concerns the defined majority relation and does not
attribute a preference or action to a collective agent.
