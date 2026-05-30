import LeanLCAExactChallenge.Derived.ComparisonBijectivityStrictRealizationLeftCalculusRoute
import LeanLCAExactChallenge.Derived.LeftRightComparisonProductRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroExactInputsClosedRangeProductRoute

/-!
W839 routes W790 target homology-zero realization data into the W838
comparison-bijectivity strict-realization left-calculus path.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W839 derives global cochain homology from W831 comparison-bijectivity. -/
theorem cochainHasHomology_of_comparisonBijectivityW839 :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i :=
  cochainHasHomology_of_leftRightComparisonIsoW768
    universalLeftRightComparisonIso_of_comparisonBijectivityW831

/-- W839 closed-map data after W831 supplies homology for the W790 payload. -/
structure MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
      cochainHasHomology_of_comparisonBijectivityW839

/-- W839 closed-embedding data after W831 supplies homology for the W790 payload. -/
structure
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  targetHomologyZeroPayload :
    MetrizableExactAcyclicHomotopyObjectTargetHomologyZeroPayloadW790
      cochainHasHomology_of_comparisonBijectivityW839

/-- W839 derives W784 target-isomorphism realization from closed-map data. -/
noncomputable def targetIsoRealizationOfClosedMapTargetHomologyZeroW839
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 :=
  targetIsoRealizationOfTargetHomologyZeroExactInputsClosedRangeW790
    cochainHasHomology_of_comparisonBijectivityW839
    (closedRangeEndpointTopologyOfClosedMapExactInputsW790 data.exactInputs)
    data.targetHomologyZeroPayload

/-- W839 derives W784 target-isomorphism realization from closed-embedding data. -/
noncomputable def targetIsoRealizationOfClosedEmbeddingTargetHomologyZeroW839
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 :=
  targetIsoRealizationOfTargetHomologyZeroExactInputsClosedRangeW790
    cochainHasHomology_of_comparisonBijectivityW839
    (closedRangeEndpointTopologyOfClosedEmbeddingExactInputsW790
      data.exactInputs)
    data.targetHomologyZeroPayload

/-- W839 derives W783 strict triangleh realization from closed-map data. -/
noncomputable def trianglehRealizationOfClosedMapTargetHomologyZeroW839
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783 :=
  trianglehRealizationOfTargetIsoRealizationW784
    (targetIsoRealizationOfClosedMapTargetHomologyZeroW839 data)

/-- W839 derives W783 strict triangleh realization from closed-embedding data. -/
noncomputable def trianglehRealizationOfClosedEmbeddingTargetHomologyZeroW839
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783 :=
  trianglehRealizationOfTargetIsoRealizationW784
    (targetIsoRealizationOfClosedEmbeddingTargetHomologyZeroW839 data)

/-- W839 closed-map data converted to W838 data. -/
noncomputable def
    comparisonBijectivityStrictRealizationDataOfClosedMapTargetHomologyZeroW839
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838
    where
  trianglehRealization :=
    trianglehRealizationOfClosedMapTargetHomologyZeroW839 data
  exactInputs := data.exactInputs

/-- W839 closed-embedding data converted to W838 data. -/
noncomputable def
    comparisonBijectivityStrictRealizationDataOfClosedEmbeddingTargetHomologyZeroW839
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838
    where
  trianglehRealization :=
    trianglehRealizationOfClosedEmbeddingTargetHomologyZeroW839 data
  exactInputs := data.exactInputs

/-- W839 closed-map data converted to the W836 exact-input route. -/
noncomputable def exactInputsLeftCalculusDataOfClosedMapTargetHomologyZeroW839
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836 :=
  exactInputsLeftCalculusDataOfClosedMapComparisonBijectivityStrictRealizationW838
    (comparisonBijectivityStrictRealizationDataOfClosedMapTargetHomologyZeroW839
      data)

/-- W839 closed-embedding data converted to the W836 exact-input route. -/
noncomputable def
    exactInputsLeftCalculusDataOfClosedEmbeddingTargetHomologyZeroW839
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836 :=
  exactInputsLeftCalculusDataOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (comparisonBijectivityStrictRealizationDataOfClosedEmbeddingTargetHomologyZeroW839
      data)

/-- W839 derives the W785 target ExactAt payload from closed-map data. -/
noncomputable def targetExactAtPayloadOfClosedMapTargetHomologyZeroW839
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedMapComparisonBijectivityStrictRealizationW838
    (comparisonBijectivityStrictRealizationDataOfClosedMapTargetHomologyZeroW839
      data)

/-- W839 derives the W785 target ExactAt payload from closed-embedding data. -/
noncomputable def targetExactAtPayloadOfClosedEmbeddingTargetHomologyZeroW839
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (comparisonBijectivityStrictRealizationDataOfClosedEmbeddingTargetHomologyZeroW839
      data)

/-- W839 proves direct bounded left calculus from closed-map data. -/
theorem directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapComparisonBijectivityStrictRealizationW838
    (comparisonBijectivityStrictRealizationDataOfClosedMapTargetHomologyZeroW839
      data)

/-- W839 proves direct bounded left calculus from closed-embedding data. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (comparisonBijectivityStrictRealizationDataOfClosedEmbeddingTargetHomologyZeroW839
      data)

/-- W839 stable route using closed-map target homology-zero data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroW839
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data
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
        directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data
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
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W839 stable route using closed-embedding target homology-zero data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroW839
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data
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
        directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data
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
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W839 direct-left-calculus inputs after W831 supplies homology. -/
def targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839 :
    List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W790 target homology-zero realization data indexed by W821/W831-derived homology"]

/-- W839 leaves two direct-left-calculus inputs. -/
theorem targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839_count :
    Dbounded.targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839.length =
      2 :=
  rfl

/-- W839 stable route requirements after W831 supplies homology. -/
def targetHomologyZeroStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW839 :
    List String :=
  ["closed-map or closed-embedding W839 target homology-zero data",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W839 keeps the stable route to five bundled requirements. -/
theorem
    targetHomologyZeroStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW839_count :
    (let names :=
      targetHomologyZeroStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW839;
      names.length) =
        5 :=
  rfl

/-- Expanded W839 requirements, showing the current route obligations. -/
def targetHomologyZeroStrictRealizationLeftCalculusExpandedRequiredFieldNamesW839 :
    List String :=
  Dbounded.targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W839 expanded stable route has six concrete requirements. -/
theorem
    targetHomologyZeroStrictRealizationLeftCalculusExpandedRequiredFieldNamesW839_count :
    (let names :=
      targetHomologyZeroStrictRealizationLeftCalculusExpandedRequiredFieldNamesW839;
      names.length) =
        6 :=
  rfl

/-- Current checked W839 state for target homology-zero strict realization. -/
structure MetrizableTargetHomologyZeroStrictRealizationLeftCalculusRouteStateW839 :
    Type where
  seed : String
  declarations : List String
  homologyResult : String
  realizationResult : String
  leftCalculusResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W839 state. -/
def currentMetrizableTargetHomologyZeroStrictRealizationLeftCalculusRouteStateW839 :
    Dbounded.MetrizableTargetHomologyZeroStrictRealizationLeftCalculusRouteStateW839
    where
  seed := "w839-target-homology-zero-strict-realization-left-calculus-route"
  declarations :=
    ["cochainHasHomology_of_comparisonBijectivityW839",
      "MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839",
      "MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839",
      "targetIsoRealizationOfClosedMapTargetHomologyZeroW839",
      "targetIsoRealizationOfClosedEmbeddingTargetHomologyZeroW839",
      "trianglehRealizationOfClosedMapTargetHomologyZeroW839",
      "trianglehRealizationOfClosedEmbeddingTargetHomologyZeroW839",
      "comparisonBijectivityStrictRealizationDataOfClosedMapTargetHomologyZeroW839",
      "comparisonBijectivityStrictRealizationDataOfClosedEmbeddingTargetHomologyZeroW839",
      "exactInputsLeftCalculusDataOfClosedMapTargetHomologyZeroW839",
      "exactInputsLeftCalculusDataOfClosedEmbeddingTargetHomologyZeroW839",
      "targetExactAtPayloadOfClosedMapTargetHomologyZeroW839",
      "targetExactAtPayloadOfClosedEmbeddingTargetHomologyZeroW839",
      "directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839",
      "boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroW839",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroW839",
      "targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839",
      "targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839_count",
      "targetHomologyZeroStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW839",
      "targetHomologyZeroStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW839_count",
      "targetHomologyZeroStrictRealizationLeftCalculusExpandedRequiredFieldNamesW839",
      "targetHomologyZeroStrictRealizationLeftCalculusExpandedRequiredFieldNamesW839_count"]
  homologyResult :=
    "proved: W831 comparison-bijectivity supplies global cochain homology for W790"
  realizationResult :=
    "proved: W790 target homology-zero payloads feed W784 and then W783 strict realization"
  leftCalculusResult :=
    "proved: W839 data feed W838 direct left calculus without a separate W783 field"
  derivedInputs :=
    ["universal IsIso for every MetrizableLCA left-right homology comparison",
      "global homology exists for every MetrizableLCA cochain complex and degree",
      "W783 strict triangleh realization from W790 target homology-zero realization data"]
  remainingInputs :=
    Dbounded.targetHomologyZeroStrictRealizationLeftCalculusExpandedRequiredFieldNamesW839
  productSuccessClaimed := false

theorem currentW839TargetHomologyZeroStrictRealizationLeftCalculusRoute_productSuccess :
    (let state :=
        currentMetrizableTargetHomologyZeroStrictRealizationLeftCalculusRouteStateW839;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
