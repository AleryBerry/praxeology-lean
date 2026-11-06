# Specification 08: Non-identifiability in a specified model class

This page describes [`Praxeology/EconometricLimits.lean`](../Praxeology/EconometricLimits.lean).
The results are mathematical statements about the module's `EconometricInterpretation`,
observation map, and model classes. They do not establish a blanket impossibility
for empirical economics.

## 1. The observation and estimator theorem

An [`EconometricInterpretation`](../Praxeology/EconometricLimits.lean#L26) supplies
an outcome function and an asymmetric preference relation over an existing
ActionFrame. A [`HistoricalObservation`](../Praxeology/EconometricLimits.lean#L55)
contains only the enacted action and the interpreted end at one agent, moment,
and history. [`ObsEquiv`](../Praxeology/EconometricLimits.lean#L66) is equality of
those records at that observation point.

[`non_identifiability_of_divergent_models`](../Praxeology/EconometricLimits.lean#L84)
proves: if two interpretations belong to the stated model class, give equal
observations at the selected point, and have different values of the parameter
function, then no estimator taking only that observation can identify the
parameter over that class at that point. The result depends on the chosen model
class, observation map, parameter, and pair of interpretations.

## 2. Constructed countermodels and their limits

[`causal_econometric_non_identifiability`](../Praxeology/EconometricLimits.lean#L102)
changes the outcome assigned to an idle action on a different history while
preserving the observation on the realized history. Its argument does not use
the supplied purposeful-action hypothesis, and the constructed second
interpretation is not required to preserve a full set of ActionFrame outcome
laws or to make the observed action purposeful under that interpretation. The
theorem therefore witnesses freedom in this interpretation class; it does not
show that purposeful action itself entails a substantive causal
non-identifiability result.

[`lucas_critique_policy_invariance_failure`](../Praxeology/EconometricLimits.lean#L137)
rewrites the interpreted outcome of one feasible, unchosen action to an end
that dominates the enacted action. This makes the enacted action fail the
module's `PurposefulUnder` predicate in the modified interpretation. It is a
countermodel to invariance under unrestricted outcome-function changes, not a
general empirical theorem about estimated policy coefficients.

[`iv_exclusion_restriction_unverifiable`](../Praxeology/EconometricLimits.lean#L168)
constructs two functions whose outputs agree at the selected action and whose
alternative-action outputs differ across instrument values. There is no
separate statistical data structure, sampling process, or causal-instrument
model in this result. [`duhem_quine_underdetermination`](../Praxeology/EconometricLimits.lean#L208)
likewise constructs two outcome maps agreeing on one selected action and
disagreeing on one alternative action at one node.

## 3. ABCT-labelled regime witness

[`abct_macro_aggregate_regime_non_identifiability`](../Praxeology/EconometricLimits.lean#L260)
is the generic two-model estimator theorem applied to the inductive labels
`Absorption` and `Liquidation`. The finite
[`abct_regime_non_identifiability_witness`](../Praxeology/EconometricLimits.lean#L276)
assigns those labels to two interpretations over `FiniteBranchingModel` that
have the same selected observation. The label function is constructed for the
witness; the result does not model capital goods, household saving, credit
creation, factor markets, or an actual business-cycle process.

Accordingly, the current witness supports only this limited claim: in the
specified interpretation class, one selected observation does not determine
an externally assigned two-valued regime label. It is not a calibrated or
causally grounded Austrian business-cycle model.
