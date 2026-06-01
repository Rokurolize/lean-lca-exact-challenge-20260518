import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW831ComparisonBijectivityLeftCalculusConvergenceGuardW1531

/-!
W1532 makes the W829 left-calculus stable-route step explicit for the W1531
W987 surface. W1531 names the W830 direct-bounded-left-calculus data; W1532
records the induced W829 left-calculus premise, the semantic fields supplied by
that premise, and the stable bounded-derived package route that still requires
the remaining finite-limit, finite-colimit, pretriangulated, and triangulated
fields.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519
open scoped ZeroObject

namespace Dbounded

noncomputable section

/-- W1532 reuses the W1531 W831/W830 comparison-bijectivity left-calculus surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531

/-- W1532 closed-map W829 left-calculus premise from the W1531 W830 branch. -/
theorem closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfKernelCokernelComparisonW830
    (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1532 closed-embedding W829 left-calculus premise from the W1531 W830 branch. -/
theorem closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfKernelCokernelComparisonW830
    (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1532 closed-map semantic fields supplied by the W829 left-calculus premise. -/
noncomputable def closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableLeftCalculusSemanticFields :=
  metrizableLeftCalculusFieldsOfDirectBoundedRouteW830
    (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1532 closed-embedding semantic fields supplied by the W829 left-calculus premise. -/
noncomputable def closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableLeftCalculusSemanticFields :=
  metrizableLeftCalculusFieldsOfDirectBoundedRouteW830
    (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1532 closed-map semantic fields are the W830 direct-route semantic fields. -/
theorem w1532ClosedMapSemanticFieldsRunThroughW830W829
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider =
      metrizableLeftCalculusFieldsOfDirectBoundedRouteW830
        (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) :=
  rfl

/-- W1532 closed-embedding semantic fields are the W830 direct-route semantic fields. -/
theorem w1532ClosedEmbeddingSemanticFieldsRunThroughW830W829
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider =
      metrizableLeftCalculusFieldsOfDirectBoundedRouteW830
        (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1532 closed-map stable route through W829. -/
noncomputable def closedMapBoundedDerivedInfinityCategoryOfW829ConvergenceW1532
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
          input globalClosedMapComponents mappedCokernelClosedMapProvider
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
        closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
          input globalClosedMapComponents mappedCokernelClosedMapProvider
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
    closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedMapComponents mappedCokernelClosedMapProvider
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W1532 closed-embedding stable route through W829. -/
noncomputable def closedEmbeddingBoundedDerivedInfinityCategoryOfW829ConvergenceW1532
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider
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
        closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider
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
    closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W1532 names the remaining W829 stable-route fields after W830 supplies left calculus. -/
def w829LeftCalculusStableRouteRemainingFieldNamesW1532 : List String :=
  ["HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

theorem w829LeftCalculusStableRouteRemainingFieldNamesW1532_count :
    w829LeftCalculusStableRouteRemainingFieldNamesW1532.length = 4 :=
  rfl

/-- W1532 keeps the W1531 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531_count

/-- Current W1532 nonterminal W829 left-calculus stable-route state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceStateW1532 :
    Type where
  seed : String
  declarations : List String
  leftCalculusPremiseResult : String
  semanticFieldsResult : String
  stableRouteResult : String
  remainingInputs : List String
  w829SuppliedFields : List String
  w829RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1532 records the W830-to-W829 stable-route bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceStateW1532 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceStateW1532 where
  seed :=
    "w1532-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w829-left-calculus-stable-route-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputW1532",
      "closedMapLeftCalculusPremiseW829OfW830ConvergenceW1532",
      "closedEmbeddingLeftCalculusPremiseW829OfW830ConvergenceW1532",
      "closedMapLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532",
      "closedEmbeddingLeftCalculusSemanticFieldsW829OfW830ConvergenceW1532",
      "w1532ClosedMapSemanticFieldsRunThroughW830W829",
      "w1532ClosedEmbeddingSemanticFieldsRunThroughW830W829",
      "closedMapBoundedDerivedInfinityCategoryOfW829ConvergenceW1532",
      "closedEmbeddingBoundedDerivedInfinityCategoryOfW829ConvergenceW1532",
      "w829LeftCalculusStableRouteRemainingFieldNamesW1532_count",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532_count"]
  leftCalculusPremiseResult :=
    "proved: W1531 W830 data supply the W829 direct bounded left-calculus \
      premise on both closed-map and closed-embedding branches"
  semanticFieldsResult :=
    "proved: the W829 left-calculus premise supplies preadditivity, zero \
      object, all-shift additivity, and suspension additivity fields"
  stableRouteResult :=
    "proved: W1531/W1532 data route through W829 to the stable bounded-derived \
      package once finite limits, finite colimits, pretriangulated, and \
      triangulated structures are supplied"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceInputNamesW1532
  w829SuppliedFields :=
    metrizableLeftCalculusStableRouteSuppliedFieldNames
  w829RemainingInputs :=
    w829LeftCalculusStableRouteRemainingFieldNamesW1532
  productSuccessClaimed := false

theorem currentW1532W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W829LeftCalculusStableRouteConvergenceStateW1532.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
