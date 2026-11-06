/-
Copyright (c) 2026 Alexander Etxeberria. All rights reserved.
Released under the MIT License as described in the file LICENSE.
Authors: Alexander Etxeberria
-/
module

public import Praxeology.FiniteEconomy.Tree
public import Praxeology.FiniteEconomy.Physical
public import Praxeology.FiniteEconomy.Policy
public import Praxeology.FiniteEconomy.Compiler
public import Praxeology.FiniteEconomy.ActionFrameCompiler
public import Praxeology.FiniteEconomy.Program
public import Praxeology.FiniteEconomy.ProfileSchedule
public import Praxeology.FiniteEconomy.ProgramActionFrame
public import Praxeology.FiniteEconomy.ProgramActionFrameWitness
public import Praxeology.FiniteEconomy.ScaleBenchmarks
public import Praxeology.FiniteEconomy.FiveStageSupplyChain
public import Praxeology.FiniteEconomy.Execution
public import Praxeology.FiniteEconomy.Market
public import Praxeology.FiniteEconomy.Communication
public import Praxeology.FiniteEconomy.Credit

/-!
# Finite economy interfaces

The structural tree engine and physical transition semantics are kept below
ActionFrame-specific execution adapters in the import graph. Economic banking,
price formation, and communication theories remain polymorphic in
`[W : ActionFrame]`; finite-economy data only instantiates those theories.
-/

@[expose] public section

end
