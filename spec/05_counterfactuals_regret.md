# Specification 05: Counterfactual comparison and regret

This page documents the counterfactual and regret declarations that currently
exist in [`Praxeology/Action.lean`](../Praxeology/Action.lean) and
[`Praxeology/Entrepreneurship.lean`](../Praxeology/Entrepreneurship.lean).
Earlier text on Lawson's second-best result, speculative profit and loss, and
an interventionist cascade named declarations and files that are not in this
repository; those claims are removed pending a separate formal development.

## 1. Alternative histories and shared context

[`AlternativeHistoryImprovement`](../Praxeology/Action.lean#L1241) records a feasible
alternative action with a better outcome on another history. It does not say
that the alternative outcome is generated under circumstances comparable to
the realized outcome. The weaker cross-history comparison should not by itself
be described as causal regret.

[`ContextMatchedRegret`](../Praxeology/Action.lean#L1270) adds a
`ContextCorrespondence`: one context must be compatible with the decision
history, and it must admit both the actual outcome and the foregone alternative
outcome. The preference comparison is then made between those outcomes.
[`GuaranteedContextRegret`](../Praxeology/Action.lean#L1316) strengthens this by
requiring a nonempty set of admitted alternative outcomes and requiring every
such outcome to be preferred to the actual one. The theorem
[`guaranteedContextRegret_implies_contextMatchedRegret`](../Praxeology/Action.lean#L1330)
derives the weaker existential comparison from the guaranteed one.

The context correspondence and its admissibility relation are substantive
modeling premises. Common choice cells or unchanged endowments do not, by
themselves, prove that a causal context has been held fixed.

## 2. Entrepreneurial regret from blocked completion

[`ContextualCycleEvaluation.regret`](../Praxeology/Entrepreneurship.lean#L451)
derives matched regret from an explicit safe alternative, a shared-context
certificate, admissibility certificates for the actual and safe outcomes,
physical grounding of outcomes in endowments, and a teleological dominance
comparison favoring the safe terminal bundle. The synthesis theorem for
blocked completion also requires a purposeful investment and a transition
that physically creates capital; blockage alone does not imply regret.

[`abct_grounded_action_frame_master`](../Praxeology/BusinessCycle/Grounded.lean#L217)
is a finite witness for one entrepreneur in a two-agent ActionFrame. It shows a
particular investment, an unavailable complementary input, and contextual
regret under its specified preference and correspondence. It is not a
multi-entrepreneur market economy, and it does not derive a general credit
expansion mechanism.

## 3. Limits of the current scope

No current declaration proves a general ex-ante/ex-post entrepreneurial
profit-and-loss partition, universal market selection of accurate forecasters,
Lawson-style second-best non-monotonicity, or a regulatory cascade. Those
topics require their own definitions, assumptions, and instantiated witnesses
before the repository should claim them.
