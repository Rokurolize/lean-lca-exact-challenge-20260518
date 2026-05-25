import LeanLCAExactChallenge.Derived.IsoClosureDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.ComparisonBijectivityStrictRealizationLeftCalculusRoute

/-!
W846 replaces the W845 W651 iso-closure realization premise by the W812
homology-detection route from W783 strict triangleh realization data.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W846 closed-map data using W783 strict triangleh realization data. -/
structure MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783

/-- W846 closed-embedding data using W783 strict triangleh realization data. -/
structure
    MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783

/-- W846 closed-map data converted to the W838 strict-realization surface. -/
noncomputable def closedMapW838DataOfStrictDirectSourceW846
    (data :
      MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838
    where
  exactInputs := data.exactInputs
  trianglehRealization := data.trianglehRealization

/-- W846 closed-embedding data converted to the W838 strict-realization surface. -/
noncomputable def closedEmbeddingW838DataOfStrictDirectSourceW846
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838
    where
  exactInputs := data.exactInputs
  trianglehRealization := data.trianglehRealization

/-- W846 derives W845's closed-map W651 iso-closure data from W783. -/
noncomputable def closedMapIsoClosureDataOfStrictDirectSourceW846
    (data :
      MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845
    where
  exactInputs := data.exactInputs
  isoClosureRealization :=
    isoClosureRealizationOfStrictRealizationHomologyDetectionW812
      (homologyDetectionOfClosedMapExactInputsW812
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        data.exactInputs)
      data.trianglehRealization

/-- W846 derives W845's closed-embedding W651 iso-closure data from W783. -/
noncomputable def closedEmbeddingIsoClosureDataOfStrictDirectSourceW846
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845
    where
  exactInputs := data.exactInputs
  isoClosureRealization :=
    isoClosureRealizationOfStrictRealizationHomologyDetectionW812
      (homologyDetectionOfClosedEmbeddingExactInputsW812
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        data.exactInputs)
      data.trianglehRealization

/-- W846 closed-map data converted to the W844 target-isomorphism surface. -/
noncomputable def closedMapTargetIsoDataOfStrictDirectSourceW846
    (data :
      MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844 :=
  closedMapTargetIsoDataOfIsoClosureW845
    (closedMapIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-embedding data converted to the W844 target-isomorphism surface. -/
noncomputable def closedEmbeddingTargetIsoDataOfStrictDirectSourceW846
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844 :=
  closedEmbeddingTargetIsoDataOfIsoClosureW845
    (closedEmbeddingIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-map data converted to the W839 target homology-zero surface. -/
noncomputable def closedMapTargetHomologyZeroDataOfStrictDirectSourceW846
    (data :
      MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedMapTargetHomologyZeroDataOfIsoClosureW845
    (closedMapIsoClosureDataOfStrictDirectSourceW846 data)

/--
W846 closed-embedding data converted to the W839 target homology-zero surface.
-/
noncomputable def closedEmbeddingTargetHomologyZeroDataOfStrictDirectSourceW846
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedEmbeddingTargetHomologyZeroDataOfIsoClosureW845
    (closedEmbeddingIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-map route preserves W845's direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedMapStrictDirectSourceW846
    (data :
      MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceW845
    (closedMapIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-embedding route preserves W845's direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingStrictDirectSourceW846
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceW845
    (closedEmbeddingIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-map route derives all stable fields from W783 data. -/
noncomputable def remainingStableFieldsOfClosedMapStrictDirectSourceW846
    (data :
      MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840
        (closedMapTargetHomologyZeroDataOfStrictDirectSourceW846 data)) :=
  remainingStableFieldsOfClosedMapIsoClosureDirectSourceW845
    (closedMapIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-embedding route derives all stable fields from W783 data. -/
noncomputable def remainingStableFieldsOfClosedEmbeddingStrictDirectSourceW846
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840
        (closedEmbeddingTargetHomologyZeroDataOfStrictDirectSourceW846 data)) :=
  remainingStableFieldsOfClosedEmbeddingIsoClosureDirectSourceW845
    (closedEmbeddingIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-map stable package from W783 strict-realization data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapStrictDirectSourceW846
    (data :
      MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceW845
    (closedMapIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 closed-embedding stable package from W783 strict-realization data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingStrictDirectSourceW846
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceW845
    (closedEmbeddingIsoClosureDataOfStrictDirectSourceW846 data)

/-- W846 has one bundled route input: the strict-realization direct-source data. -/
def strictRealizationDirectSourceStableRouteInputNamesW846 : List String :=
  ["W846 strict-realization direct-source stable route data"]

/-- W846 keeps the route to one bundled input. -/
theorem strictRealizationDirectSourceStableRouteInputNamesW846_count :
    Dbounded.strictRealizationDirectSourceStableRouteInputNamesW846.length =
      1 :=
  rfl

/-- Expanded W846 requirements are the exact-input branch and W783 data. -/
def strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846 :
    List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W783 exact-acyclic homotopy-object strict triangleh realization data"]

/-- The W846 expanded stable route has two concrete requirements. -/
theorem strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846_count :
    Dbounded.strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846.length =
      2 :=
  rfl

/-- Current checked W846 state for W783-derived stable fields. -/
structure MetrizableStrictRealizationDirectSourceStableRouteStateW846 :
    Type where
  seed : String
  declarations : List String
  conversionResult : String
  leftCalculusResult : String
  stablePackageResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W846 state. -/
def currentMetrizableStrictRealizationDirectSourceStableRouteStateW846 :
    Dbounded.MetrizableStrictRealizationDirectSourceStableRouteStateW846
    where
  seed := "w846-strict-realization-direct-source-stable-route"
  declarations :=
    ["MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846",
      "MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846",
      "closedMapW838DataOfStrictDirectSourceW846",
      "closedEmbeddingW838DataOfStrictDirectSourceW846",
      "closedMapIsoClosureDataOfStrictDirectSourceW846",
      "closedEmbeddingIsoClosureDataOfStrictDirectSourceW846",
      "closedMapTargetIsoDataOfStrictDirectSourceW846",
      "closedEmbeddingTargetIsoDataOfStrictDirectSourceW846",
      "closedMapTargetHomologyZeroDataOfStrictDirectSourceW846",
      "closedEmbeddingTargetHomologyZeroDataOfStrictDirectSourceW846",
      "directBoundedLeftCalculusOfClosedMapStrictDirectSourceW846",
      "directBoundedLeftCalculusOfClosedEmbeddingStrictDirectSourceW846",
      "remainingStableFieldsOfClosedMapStrictDirectSourceW846",
      "remainingStableFieldsOfClosedEmbeddingStrictDirectSourceW846",
      "boundedDerivedInfinityCategoryOfClosedMapStrictDirectSourceW846",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingStrictDirectSourceW846",
      "strictRealizationDirectSourceStableRouteInputNamesW846",
      "strictRealizationDirectSourceStableRouteInputNamesW846_count",
      "strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846",
      "strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846_count"]
  conversionResult :=
    "proved: W812 plus W831 turn W783 strict realization into W845 W651 data"
  leftCalculusResult :=
    "proved: W846 data feed W845 direct bounded left calculus through W783-derived W651 data"
  stablePackageResult :=
    "proved: W846 assembles the W845 stable package from W783 strict-realization data"
  derivedInputs :=
    ["W651 exact-acyclic iso-closure strict realization data from W783 by\
        W812/W831",
      "W784 target-isomorphism realization data from W651 through W845",
      "W785/W663 target ExactAt realization data through W844",
      "W790 target homology-zero realization data through W843/W844/W845",
      "W653 direct finite-shape source data through W842",
      "W657 direct-localization triangulated source data through W842",
      "finite-limit, finite-colimit, pretriangulated, and triangulated fields\
        through W842"]
  remainingInputs :=
    Dbounded.strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846
  productSuccessClaimed := false

theorem currentW846StrictRealizationDirectSourceStableRoute_productSuccess :
    (let state :=
        currentMetrizableStrictRealizationDirectSourceStableRouteStateW846;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
