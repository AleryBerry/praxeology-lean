# Specification 01: ActionFrame ontology and branching histories

The central interface is [`ActionFrame`](../Praxeology/Frame/Core.lean#L276). It
packages sorts for agents, moments, histories, actions, means, and ends, along
with laws that each instance must satisfy. It is a model interface with
substantive assumptions, not a zero-axiom derivation of those laws.

## 1. Temporal and history structure

`ActionFrame` supplies an irreflexive, transitive temporal precedence relation.
Its backward-linearity law says that any two moments preceding a common later
moment are comparable. Histories are maximal linear chains; the interface
requires that every moment belongs to some history and that histories with the
same incident moments are equal. Separate divergence laws require distinct
histories through a moment to have incompatible futures.

The main typeclass includes additional behavioral and physical requirements,
so results quantified over an `ActionFrame` inherit all of them. The concrete
finite [`FiniteBranchingModel`](../Praxeology/Frame/Witnesses.lean#L277) proves that
the interface is inhabited. That witness establishes consistency of the
packaged interface; it does not instantiate every later economic structure.

## 2. Menus, endowments, and action realization

At each agent, moment, and history, an instance supplies a finite contemplated
menu, natural-number endowments, and action-specific means used and yielded.
The feasible menu is coupled to contemplation and coordinatewise resource
requirements. A passive baseline is always contemplated, uses no means, and
yields no means. Enacted actions at incident moments must be feasible.

The interface also supplies `sigma`, a selector that realizes each feasible
action on some history through the decision moment, and a co-agency law for
other actors. This is an explicit alternative-realization assumption in the
framework. It should not be described as a result of the action axiom.

## 3. Trade and physical accounting

Offer and accept actions have explicit means-use and means-yield functions.
For nontrade actions, `law_in_re_transition` gives the inventory balance at a
next moment. For a matched offer and accept, `bilateral_transfer_law` states
the corresponding two-agent transfer balances. Unmatched offers and accepts
are governed by separate no-op laws. Thus these are accounting requirements
imposed on each ActionFrame instance; applications still need to show that
their particular actions and event sequences satisfy them.

## 4. Derived choice and modal notions

[`ChoicePartition`](../Praxeology/Frame/Core.lean#L1460) groups histories on which an
agent enacts the same action at a moment. The covering and disjointness
properties are proved from the frame's feasibility and realization laws.
`Exec` is defined using that partition. `DynamicBox` universally quantifies
over the histories in one action cell, and `dstit` combines truth throughout
the current choice cell with a counterexample history through the moment.
These definitions inherit the frame's choice-cell and history assumptions;
they do not add probability or empirical uncertainty models.

## 5. Concrete frame witness

[`action_frame_consistent`](../Praxeology/Frame/Witnesses.lean#L529) proves
nonemptiness by constructing the finite `FiniteBranchingModel`. Use that model
as a witness only for declarations actually instantiated over it. In
particular, a generic theorem over `ActionFrame` or a witness for the bare
frame does not establish the existence of a credit market, productive firm,
or multi-agent business-cycle mechanism.
