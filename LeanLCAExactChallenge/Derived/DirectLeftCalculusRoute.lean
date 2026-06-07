import LeanLCAExactChallenge.Derived.TypeclassStableLeftCalculusRoute
import LeanLCAExactChallenge.Derived.LeftRightComparisonProductRoute

/-!
W830 direct-left-calculus route for the bounded-derived stable surface.

This module turns the W829 left-calculus premise into concrete, already-named route data:
left-right comparison homology, kernel/cokernel exact-at topology, triangulated closure, and the
localized right adjoint. It is still nonterminal because those data are not constructed here, and
the remaining finite-limit/finite-colimit/triangulated `Dbounded` fields are still required.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- Concrete data currently sufficient to prove direct bounded left calculus for MetrizableLCA. -/
structure MetrizableDirectBoundedLeftCalculusDataW830 : Type 2 where
  comparisonIso :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S)
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  kernelCokernelTopologyData :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
  localizedRightAdjoint :
    BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}

/--
W830 proves the direct bounded left-calculus premise consumed by W829 from concrete route data.
-/
theorem directBoundedLeftCalculusOfKernelCokernelComparisonW830
    (data : MetrizableDirectBoundedLeftCalculusDataW830) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions := by
  letI : (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    data.exactClosed2
  exact Dbounded.leftCalculus_of_kernelCokernelConditionedTopology_w668
    (cochainHasHomology_of_leftRightComparisonIsoW768 data.comparisonIso)
    data.kernelCokernelTopologyData
    data.localizedRightAdjoint

/--
The same W830 data supplies the four left-calculus semantic fields used by the stable route.
-/
noncomputable def metrizableLeftCalculusFieldsOfDirectBoundedRouteW830
    (data : MetrizableDirectBoundedLeftCalculusDataW830) :
    Dbounded.MetrizableLeftCalculusSemanticFields := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfKernelCokernelComparisonW830 data
  exact Dbounded.metrizableLeftCalculusSemanticFields

/--
W830 stable route with the W829 raw left-calculus premise replaced by concrete route data.
-/
noncomputable def boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusRouteW830
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfKernelCokernelComparisonW830 data
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      Pretriangulated (Dbounded MetrizableLCA.{0}))
    (triangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfKernelCokernelComparisonW830 data
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
      IsTriangulated (Dbounded MetrizableLCA.{0})) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfKernelCokernelComparisonW830 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/--
W830 semantic-field stable route with the direct-left-calculus data bundled and the remaining
stable fields supplied as the canonical semantic-field record.
-/
noncomputable def boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusFields
    (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data) remaining

/-- The W830 semantic-field route preserves the ordinary `Dbounded MetrizableLCA` carrier. -/
theorem
boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_quasicategoryCarrier
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).quasicategoryCarrier = rfl :=
  rfl

/-- The W830 semantic-field route preserves the direct-left-calculus preadditive field. -/
theorem boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_preadditive
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).preadditive =
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data).preadditive :=
  rfl

/-- The W830 semantic-field route preserves the remaining finite-limit field. -/
theorem
    boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_finiteLimitInstance
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).finiteLimitInstance = remaining.finiteLimits :=
  rfl

/-- The W830 semantic-field route preserves the remaining finite-colimit field. -/
theorem
boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_finiteColimitInstance
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).finiteColimitInstance = remaining.finiteColimits :=
  rfl

/-- The W830 semantic-field route preserves the direct-left-calculus zero-object field. -/
theorem
boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_zeroObjectInstance
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).zeroObjectInstance =
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data).zeroObject :=
  rfl

/-- The W830 semantic-field route preserves the direct-left-calculus all-shift additivity field. -/
theorem boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_shiftAdditiveAll
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).shiftAdditiveAll =
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data).shiftAdditiveAll :=
  rfl

/-- The W830 semantic-field route preserves the direct-left-calculus suspension-additivity field. -/
theorem
boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_suspensionAdditive
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).suspensionAdditive =
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data).suspensionAdditive :=
  rfl

/-- The W830 semantic-field route preserves the remaining pretriangulated field. -/
theorem
boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_pretriangulatedStructure
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).pretriangulatedStructure = remaining.pretriangulated :=
  rfl

/-- The W830 semantic-field route preserves the remaining triangulated field. -/
theorem
boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830_triangulatedStructure
    (data : MetrizableDirectBoundedLeftCalculusDataW830)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830
      data remaining).triangulatedStructure = remaining.triangulated :=
  rfl

/-- Concrete W830 inputs replacing the raw W829 direct-left-calculus premise. -/
def metrizableDirectBoundedLeftCalculusInputNamesW830 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "bounded homotopy localized right adjoint plus unit membership"]

/-- Four concrete inputs currently suffice for the W830 direct-left-calculus theorem. -/
theorem metrizableDirectBoundedLeftCalculusInputNamesW830_count :
    Dbounded.metrizableDirectBoundedLeftCalculusInputNamesW830.length = 4 :=
  rfl

/-- W830 stable route requirements when the direct-left-calculus data are bundled. -/
def metrizableDirectLeftCalculusStableRouteRequiredFieldNamesW830 : List String :=
  ["MetrizableDirectBoundedLeftCalculusDataW830",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W830 keeps the W829 route to five bundled requirements, with the first now concrete. -/
theorem metrizableDirectLeftCalculusStableRouteRequiredFieldNamesW830_count :
    Dbounded.metrizableDirectLeftCalculusStableRouteRequiredFieldNamesW830.length = 5 :=
  rfl

/-- Expanded W830 requirements, showing the exact current mathematical obligations. -/
def metrizableDirectLeftCalculusStableRouteExpandedRequiredFieldNamesW830 : List String :=
  Dbounded.metrizableDirectBoundedLeftCalculusInputNamesW830 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W830 expanded stable route has eight concrete requirements. -/
theorem metrizableDirectLeftCalculusStableRouteExpandedRequiredFieldNamesW830_count :
    Dbounded.metrizableDirectLeftCalculusStableRouteExpandedRequiredFieldNamesW830.length =
      8 :=
  rfl

/-- Current checked W830 state for the direct-left-calculus route. -/
structure MetrizableDirectLeftCalculusRouteStateW830 : Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W830 state. -/
def currentMetrizableDirectLeftCalculusRouteStateW830 :
    Dbounded.MetrizableDirectLeftCalculusRouteStateW830 where
  seed := "w830-direct-left-calculus-route"
  declarations :=
    ["MetrizableDirectBoundedLeftCalculusDataW830",
      "directBoundedLeftCalculusOfKernelCokernelComparisonW830",
      "metrizableLeftCalculusFieldsOfDirectBoundedRouteW830",
      "boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusRouteW830",
      "boundedDerivedInfinityCategoryOfMetrizableDirectLeftCalculusFieldsRouteW830",
      "metrizableDirectBoundedLeftCalculusInputNamesW830",
      "metrizableDirectBoundedLeftCalculusInputNamesW830_count",
      "metrizableDirectLeftCalculusStableRouteRequiredFieldNamesW830",
      "metrizableDirectLeftCalculusStableRouteRequiredFieldNamesW830_count",
      "metrizableDirectLeftCalculusStableRouteExpandedRequiredFieldNamesW830",
      "metrizableDirectLeftCalculusStableRouteExpandedRequiredFieldNamesW830_count"]
  leftCalculusResult :=
    "proved: W768 comparison homology plus W668 kernel-cokernel topology and\
      localized-right-adjoint data supply direct bounded left calculus"
  replacedInputs :=
    ["raw (boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions premise"]
  remainingInputs :=
    Dbounded.metrizableDirectLeftCalculusStableRouteExpandedRequiredFieldNamesW830
  productSuccessClaimed := false

theorem currentMetrizableDirectLeftCalculusRouteStateW830_productSuccess :
    Dbounded.currentMetrizableDirectLeftCalculusRouteStateW830.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
