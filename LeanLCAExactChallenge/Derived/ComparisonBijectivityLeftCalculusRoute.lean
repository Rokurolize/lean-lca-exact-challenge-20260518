import LeanLCAExactChallenge.Derived.DirectLeftCalculusRoute
import LeanLCAExactChallenge.Derived.ComparisonBijectivityRoute

/-!
W831 comparison-bijectivity route into direct bounded left calculus.

This module removes the explicit W830 universal comparison-isomorphism input
by deriving it from the W821 `CategoryWithHomology MetrizableLCA` construction
and the W765 category-with-homology comparison route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W821 and W765 supply the universal comparison isomorphism used by W830. -/
theorem universalLeftRightComparisonIso_of_comparisonBijectivityW831 :
    ∀ S : ShortComplex MetrizableLCA.{0},
      IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S) := by
  letI : CategoryWithHomology MetrizableLCA.{0} :=
    MetrizableLCA.categoryWithHomology_of_leftRightComparisonBijectiveW821
  exact Dbounded.universalLeftRightComparisonIso_of_categoryWithHomologyInstanceW765

/-- Direct-left-calculus data after W831 derives the comparison input. -/
structure MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831 : Type 2 where
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  kernelCokernelTopologyData :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs
  localizedRightAdjoint :
    BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}

/-- W831 supplies W830's data package from the remaining three route inputs. -/
noncomputable def directBoundedLeftCalculusDataOfComparisonBijectivityW831
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831) :
    MetrizableDirectBoundedLeftCalculusDataW830 where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  exactClosed2 := data.exactClosed2
  kernelCokernelTopologyData := data.kernelCokernelTopologyData
  localizedRightAdjoint := data.localizedRightAdjoint

/--
W831 proves direct bounded left calculus with the comparison input discharged
by the W821/W765 route.
-/
theorem directBoundedLeftCalculusOfComparisonBijectivityW831
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  Dbounded.directBoundedLeftCalculusOfKernelCokernelComparisonW830
    (Dbounded.directBoundedLeftCalculusDataOfComparisonBijectivityW831 data)

/--
W831 stable route with the W830 comparison input derived from prior comparison
bijectivity work.
-/
noncomputable def boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusW831
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfComparisonBijectivityW831 data
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
        directBoundedLeftCalculusOfComparisonBijectivityW831 data
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
    directBoundedLeftCalculusOfComparisonBijectivityW831 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/--
W831 supplies the left-calculus semantic fields after comparison bijectivity discharges the
W830 comparison-isomorphism input.
-/
noncomputable def metrizableLeftCalculusFieldsOfComparisonBijectivityW831
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831) :
    Dbounded.MetrizableLeftCalculusSemanticFields :=
  Dbounded.metrizableLeftCalculusFieldsOfDirectBoundedRouteW830
    (Dbounded.directBoundedLeftCalculusDataOfComparisonBijectivityW831 data)

/--
W831 semantic-field stable route with comparison bijectivity bundled and the remaining stable
fields supplied as the canonical semantic-field record.
-/
noncomputable def boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusFields
    (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data) remaining

/-- The W831 semantic-field route preserves the ordinary `Dbounded MetrizableLCA` carrier. -/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_quasicategoryCarrier
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).quasicategoryCarrier = rfl :=
  rfl

/-- The W831 semantic-field route preserves the comparison-bijectivity preadditive field. -/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_preadditive
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).preadditive =
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data).preadditive :=
  rfl

/-- The W831 semantic-field route preserves the remaining finite-limit field. -/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_finiteLimitInstance
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).finiteLimitInstance = remaining.finiteLimits :=
  rfl

/-- The W831 semantic-field route preserves the remaining finite-colimit field. -/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_finiteColimitInstance
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).finiteColimitInstance = remaining.finiteColimits :=
  rfl

/-- The W831 semantic-field route preserves the comparison-bijectivity zero-object field. -/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_zeroObjectInstance
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).zeroObjectInstance =
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data).zeroObject :=
  rfl

/--
The W831 semantic-field route preserves the comparison-bijectivity all-shift additivity field.
-/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_shiftAdditiveAll
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).shiftAdditiveAll =
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data).shiftAdditiveAll :=
  rfl

/--
The W831 semantic-field route preserves the comparison-bijectivity suspension-additivity field.
-/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_suspensionAdditive
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).suspensionAdditive =
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data).suspensionAdditive :=
  rfl

/-- The W831 semantic-field route preserves the remaining pretriangulated field. -/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_pretriangulatedStructure
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).pretriangulatedStructure = remaining.pretriangulated :=
  rfl

/-- The W831 semantic-field route preserves the remaining triangulated field. -/
theorem
boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831_triangulatedStructure
    (data : MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831)
    (remaining : Dbounded.MetrizableRemainingStableSemanticFields
      (Dbounded.metrizableLeftCalculusFieldsOfComparisonBijectivityW831 data)) :
    (Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831
      data remaining).triangulatedStructure = remaining.triangulated :=
  rfl

/-- Remaining direct-left-calculus inputs after W831 derives comparison isomorphisms. -/
def metrizableComparisonBijectivityLeftCalculusInputNamesW831 : List String :=
  ["exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "bounded homotopy localized right adjoint plus unit membership"]

/-- Three direct-left-calculus inputs remain after W831. -/
theorem metrizableComparisonBijectivityLeftCalculusInputNamesW831_count :
    Dbounded.metrizableComparisonBijectivityLeftCalculusInputNamesW831.length = 3 :=
  rfl

/-- W831 stable route requirements when comparison bijectivity supplies comparison isomorphisms. -/
def metrizableComparisonBijectivityLeftCalculusStableRouteRequiredFieldNamesW831 :
    List String :=
  ["MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W831 keeps the stable route to five bundled requirements. -/
theorem metrizableComparisonBijectivityLeftCalculusStableRouteRequiredFieldNamesW831_count :
    Dbounded.metrizableComparisonBijectivityLeftCalculusStableRouteRequiredFieldNamesW831.length =
      5 :=
  rfl

/-- Expanded W831 requirements, with comparison isomorphisms supplied by W821/W765. -/
def metrizableComparisonBijectivityLeftCalculusStableRouteExpandedRequiredFieldNamesW831 :
    List String :=
  Dbounded.metrizableComparisonBijectivityLeftCalculusInputNamesW831 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W831 expanded stable route has seven concrete requirements. -/
theorem metrizableComparisonBijectivityLeftCalculusStableRouteExpandedRequiredFieldNamesW831_count :
    metrizableComparisonBijectivityLeftCalculusStableRouteExpandedRequiredFieldNamesW831.length =
      7 :=
  rfl

/-- Current checked W831 state for the comparison-bijectivity left-calculus route. -/
structure MetrizableComparisonBijectivityLeftCalculusRouteStateW831 : Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W831 state. -/
def currentMetrizableComparisonBijectivityLeftCalculusRouteStateW831 :
    Dbounded.MetrizableComparisonBijectivityLeftCalculusRouteStateW831 where
  seed := "w831-comparison-bijectivity-left-calculus-route"
  declarations :=
    ["universalLeftRightComparisonIso_of_comparisonBijectivityW831",
      "MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831",
      "directBoundedLeftCalculusDataOfComparisonBijectivityW831",
      "directBoundedLeftCalculusOfComparisonBijectivityW831",
      "boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusW831",
      "metrizableLeftCalculusFieldsOfComparisonBijectivityW831",
      "boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusFieldsW831",
      "metrizableComparisonBijectivityLeftCalculusInputNamesW831",
      "metrizableComparisonBijectivityLeftCalculusInputNamesW831_count",
      "metrizableComparisonBijectivityLeftCalculusStableRouteRequiredFieldNamesW831",
      "metrizableComparisonBijectivityLeftCalculusStableRouteRequiredFieldNamesW831_count",
      "metrizableComparisonBijectivityLeftCalculusStableRouteExpandedRequiredFieldNamesW831",
      "metrizableComparisonBijectivityLeftCalculusStableRouteExpandedRequiredFieldNamesW831_count"]
  leftCalculusResult :=
    "proved: W821 comparison bijectivity and W765 category-with-homology\
      comparison data supply the W830 universal comparison-isomorphism input"
  derivedInputs :=
    ["universal IsIso for every MetrizableLCA left-right homology comparison"]
  remainingInputs :=
    metrizableComparisonBijectivityLeftCalculusStableRouteExpandedRequiredFieldNamesW831
  productSuccessClaimed := false

theorem currentMetrizableComparisonBijectivityLeftCalculusRouteStateW831_productSuccess :
    currentMetrizableComparisonBijectivityLeftCalculusRouteStateW831.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
