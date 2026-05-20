import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Shapes.PiProd

/-!
W152 audit: singleton packaging for the `none` subproduct in the Option-product route.

The support route selected `singleton-product`. This file packages the reduction of the
`{x : Option J // x = none}` subproduct to the `none` factor using `Limits.productUniqueIso`.
It is a focused frontier contribution for the larger decomposition

`∏ᶜ (K : Option J → CochainComplex C ℤ) ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j))`.

This file does not claim finite-product stability or product success.
-/

set_option autoImplicit false

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OptionProductReindexPackagingW152

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The singleton subindex selecting only the `none` entry of an `Option J` family. -/
abbrev optionNoneIndex (J : Type w) : Type w :=
  {x : Option J // x = none}

/-- The complementary subindex used by `Pi.binaryFanOfProp`; this is reindexed separately. -/
abbrev optionSomeComplementIndex (J : Type w) : Type w :=
  {x : Option J // ¬ x = none}

instance optionNoneIndexUnique (J : Type w) : Unique (optionNoneIndex J) where
  default := ⟨none, rfl⟩
  uniq := by
    intro a
    cases a with
    | mk x hx =>
      cases x with
      | none => rfl
      | some j => cases hx

/-- The `none` subproduct of cochain complexes is canonically the `none` complex. -/
noncomputable def noneSubproductIso {J : Type w}
    (K : Option J → CochainComplex C ℤ) :
    ∏ᶜ (fun i : optionNoneIndex J => K i.val) ≅ K none :=
  Limits.productUniqueIso (fun i : optionNoneIndex J => K i.val)

/-- The same singleton reduction at a fixed cochain degree. -/
noncomputable def noneSubproductDegreeIso {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ) :
    ∏ᶜ (fun i : optionNoneIndex J => (K i.val).X n) ≅ (K none).X n :=
  Limits.productUniqueIso (fun i : optionNoneIndex J => (K i.val).X n)

/-- The binary fan split whose left object is discharged separately by `noneSubproductIso`. -/
noncomputable abbrev optionProductBinaryFanBeforeSingleton {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : optionSomeComplementIndex J => K i.val)] :
    BinaryFan
      (∏ᶜ (fun i : optionNoneIndex J => K i.val))
      (∏ᶜ (fun i : optionSomeComplementIndex J => K i.val)) :=
  Pi.binaryFanOfProp K (fun x : Option J => x = none)

/--
Current route state after proving the singleton side.

The remaining step is the complement reindexing plus complex-level assembly; the `none` side no
longer needs to be treated as a blocker.
-/
structure SingletonProductRouteState : Type where
  singletonIndex : String
  singletonReduction : String
  degreewiseReduction : String
  remainingComplementReindex : Option String
  remainingComplexIsoAssembly : Option String

/-- W152's current singleton-product frontier. -/
def currentSingletonProductRouteState : SingletonProductRouteState where
  singletonIndex := "{x : Option J // x = none}"
  singletonReduction := "noneSubproductIso packages Limits.productUniqueIso for cochain complexes"
  degreewiseReduction := "noneSubproductDegreeIso packages Limits.productUniqueIso at each degree"
  remainingComplementReindex :=
    some "Reindex {x : Option J // ¬ x = none} along Option.some to J"
  remainingComplexIsoAssembly :=
    some "Combine Pi.binaryFanOfProp, singleton reduction, complement reindexing, and HomologicalComplex.isLimitOfEval"

theorem currentSingletonProductRouteState_singleton_done :
    currentSingletonProductRouteState.remainingComplementReindex =
      some "Reindex {x : Option J // ¬ x = none} along Option.some to J" :=
  rfl

/-- Compact checklist for the next step after the singleton reduction. -/
def singletonProductNextObligations : List String :=
  ["reuse optionSomeComplementEquiv to package {x : Option J // ¬ x = none} ≃ J",
    "use Limits.Pi.reindex, Limits.Pi.map', or Limits.Pi.mapIso for the complement product",
    "compose the complement reindexing with Pi.binaryFanOfProp",
    "promote the fixed-degree product split with HomologicalComplex.isLimitOfEval",
    "feed the resulting OptionProductIsoBiprod input back to the finite exact-acyclic product closure"]

theorem singletonProductNextObligations_count :
    singletonProductNextObligations.length = 5 :=
  rfl

section Checks

#check optionNoneIndex
#check optionSomeComplementIndex
#check optionNoneIndexUnique
#check noneSubproductIso
#check noneSubproductDegreeIso
#check optionProductBinaryFanBeforeSingleton
#check SingletonProductRouteState
#check currentSingletonProductRouteState
#check currentSingletonProductRouteState_singleton_done
#check singletonProductNextObligations
#check singletonProductNextObligations_count
#check Limits.productUniqueIso
#check Limits.Pi.binaryFanOfProp
#check Limits.Pi.binaryFanOfPropIsLimit
#check Limits.Pi.reindex
#check Limits.Pi.map'
#check Limits.Pi.mapIso
#check HomologicalComplex.isLimitOfEval

end Checks

end OptionProductReindexPackagingW152

end LeanLCAExactChallenge
