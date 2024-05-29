/-
Copyright (c) 2024 Dimitar Jetchev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: definitions took from the branch `xfr-regulator` of Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice.Covolume
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!

# The regulator of a number field

## Important definitions
* `NumberField.Units.regulator`: the regulator of the number field `K`.

## Implementation notes

## TODO

## Tags
Regulator of a number field.

-/

open scoped NumberField

noncomputable section

namespace NumberField.Units

variable (K : Type*) [Field K] [NumberField K]

open MeasureTheory Classical BigOperators NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem

/-- The regulator of a number fied `K`. -/
def regulator : ℝ := Zlattice.covolume (unitLattice K)

theorem regulator_ne_zero : regulator K ≠ 0 := Zlattice.covolume_ne_zero (unitLattice K) volume

theorem regulator_pos : 0 < regulator K := Zlattice.covolume_pos (unitLattice K) volume

/-- The subgroup of the unit group generated by a given set of units. -/
def subgroupGeneratedByUnits (units : Set (𝓞 K)ˣ) : Subgroup (𝓞 K)ˣ := Subgroup.closure (units)

def logEmbeddingSublattice (units : Set (𝓞 K)ˣ): AddSubgroup ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
  AddSubgroup.closure (units.image (logEmbedding K))

/-- The regulator of the subgroup generated by a given set of units. -/
noncomputable def regulatorSubgroupGenByUnits (units : Set (𝓞 K)ˣ) : ℝ := Zlattice.covolume (logEmbeddingSublattice units)

end NumberField.Units
