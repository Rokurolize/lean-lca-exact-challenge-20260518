import LeanLCAExactChallenge.Derived.ExactInputsLeftCalculusRoute

/-!
W836 routes W735 exact-input branch-localized W721 data into the W835
exact-inputs iso-closure left-calculus route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W836 closed-map inputs; W721 data is read from the W735 branch. -/
structure MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651

/-- W836 closed-embedding inputs; W721 data is read from the W735 branch. -/
structure
    MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651

/-- W836 closed-map data converted to the W835 data shape. -/
def exactInputsLeftCalculusDataOfClosedMapBranchLocalizedW836
    (data : MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836) :
    MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835 where
  exactInputs := data.exactInputs
  isoClosureRealization := data.isoClosureRealization
  localizedRightAdjointData := data.exactInputs.localizedRightAdjointData

/-- W836 closed-embedding data converted to the W835 data shape. -/
def exactInputsLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836
    (data :
      MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836) :
    MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835 where
  exactInputs := data.exactInputs
  isoClosureRealization := data.isoClosureRealization
  localizedRightAdjointData := data.exactInputs.localizedRightAdjointData

/-- W836 closed-map data converted to W834 data through W835. -/
noncomputable def isoClosureLeftCalculusDataOfClosedMapBranchLocalizedW836
    (data : MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 :=
  isoClosureLeftCalculusDataOfClosedMapExactInputsW835
    (exactInputsLeftCalculusDataOfClosedMapBranchLocalizedW836 data)

/-- W836 closed-embedding data converted to W834 data through W835. -/
noncomputable def isoClosureLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836
    (data :
      MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 :=
  isoClosureLeftCalculusDataOfClosedEmbeddingExactInputsW835
    (exactInputsLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836 data)

/-- W836 derives the W785 target ExactAt payload from closed-map branch data. -/
noncomputable def targetExactAtPayloadOfClosedMapBranchLocalizedW836
    (data : MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedMapExactInputsIsoClosureW835
    (exactInputsLeftCalculusDataOfClosedMapBranchLocalizedW836 data)

/-!
W836 derives the W785 target ExactAt payload from closed-embedding branch
data.
-/
noncomputable def targetExactAtPayloadOfClosedEmbeddingBranchLocalizedW836
    (data :
      MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedEmbeddingExactInputsIsoClosureW835
    (exactInputsLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836 data)

/-- W836 proves direct bounded left calculus from closed-map W735/W651 data. -/
theorem directBoundedLeftCalculusOfClosedMapBranchLocalizedW836
    (data : MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapExactInputsIsoClosureW835
    (exactInputsLeftCalculusDataOfClosedMapBranchLocalizedW836 data)

/-- W836 proves direct bounded left calculus from closed-embedding W735/W651 data. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingBranchLocalizedW836
    (data :
      MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingExactInputsIsoClosureW835
    (exactInputsLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836 data)

/-- W836 stable route using closed-map branch-localized exact-input data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapBranchLocalizedW836
    (data : MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedMapBranchLocalizedW836 data
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
        directBoundedLeftCalculusOfClosedMapBranchLocalizedW836 data
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
  exact boundedDerivedInfinityCategoryOfClosedMapExactInputsIsoClosureW835
    (exactInputsLeftCalculusDataOfClosedMapBranchLocalizedW836 data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W836 stable route using closed-embedding branch-localized exact-input data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingBranchLocalizedW836
    (data :
      MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedEmbeddingBranchLocalizedW836 data
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
        directBoundedLeftCalculusOfClosedEmbeddingBranchLocalizedW836 data
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
  exact boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsIsoClosureW835
    (exactInputsLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836 data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W836 direct-left-calculus inputs after reusing W735's W721 field. -/
def branchLocalizedExactInputsLeftCalculusInputNamesW836 : List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W651 exact-acyclic iso-closure strict realization data"]

/-- W836 uses two concrete inputs for direct left calculus. -/
theorem branchLocalizedExactInputsLeftCalculusInputNamesW836_count :
    Dbounded.branchLocalizedExactInputsLeftCalculusInputNamesW836.length =
      2 :=
  rfl

/-- W836 stable route requirements when branch-localized data are bundled. -/
def branchLocalizedExactInputsLeftCalculusStableRouteRequiredFieldNamesW836 :
    List String :=
  ["closed-map or closed-embedding W836 branch-localized exact-input data",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W836 keeps the stable route to five bundled requirements. -/
theorem branchLocalizedExactInputsLeftCalculusStableRouteRequiredFieldNamesW836_count :
    Dbounded.branchLocalizedExactInputsLeftCalculusStableRouteRequiredFieldNamesW836.length =
      5 :=
  rfl

/-- Expanded W836 requirements, showing the current concrete route obligations. -/
def branchLocalizedExactInputsLeftCalculusExpandedRequiredFieldNamesW836 :
    List String :=
  Dbounded.branchLocalizedExactInputsLeftCalculusInputNamesW836 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W836 expanded stable route has six concrete requirements. -/
theorem branchLocalizedExactInputsLeftCalculusExpandedRequiredFieldNamesW836_count :
    Dbounded.branchLocalizedExactInputsLeftCalculusExpandedRequiredFieldNamesW836.length =
      6 :=
  rfl

/-- Current checked W836 state for branch-localized exact-input left calculus. -/
structure MetrizableBranchLocalizedExactInputsLeftCalculusRouteStateW836 :
    Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W836 state. -/
def currentMetrizableBranchLocalizedExactInputsLeftCalculusRouteStateW836 :
    Dbounded.MetrizableBranchLocalizedExactInputsLeftCalculusRouteStateW836 where
  seed := "w836-branch-localized-exact-inputs-left-calculus-route"
  declarations :=
    ["MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836",
      "MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836",
      "exactInputsLeftCalculusDataOfClosedMapBranchLocalizedW836",
      "exactInputsLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836",
      "isoClosureLeftCalculusDataOfClosedMapBranchLocalizedW836",
      "isoClosureLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836",
      "targetExactAtPayloadOfClosedMapBranchLocalizedW836",
      "targetExactAtPayloadOfClosedEmbeddingBranchLocalizedW836",
      "directBoundedLeftCalculusOfClosedMapBranchLocalizedW836",
      "directBoundedLeftCalculusOfClosedEmbeddingBranchLocalizedW836",
      "boundedDerivedInfinityCategoryOfClosedMapBranchLocalizedW836",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingBranchLocalizedW836",
      "branchLocalizedExactInputsLeftCalculusInputNamesW836",
      "branchLocalizedExactInputsLeftCalculusInputNamesW836_count",
      "branchLocalizedExactInputsLeftCalculusStableRouteRequiredFieldNamesW836",
      "branchLocalizedExactInputsLeftCalculusStableRouteRequiredFieldNamesW836_count",
      "branchLocalizedExactInputsLeftCalculusExpandedRequiredFieldNamesW836",
      "branchLocalizedExactInputsLeftCalculusExpandedRequiredFieldNamesW836_count"]
  leftCalculusResult :=
    "proved: W735/W651 data supply W835 exact-inputs left-calculus data"
  replacedInputs :=
    ["separate W721 bounded homotopy localized right adjoint data"]
  remainingInputs :=
    Dbounded.branchLocalizedExactInputsLeftCalculusExpandedRequiredFieldNamesW836
  productSuccessClaimed := false

theorem currentMetrizableBranchLocalizedExactInputsLeftCalculusRouteStateW836_productSuccess :
    (let state :=
        Dbounded.currentMetrizableBranchLocalizedExactInputsLeftCalculusRouteStateW836;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
