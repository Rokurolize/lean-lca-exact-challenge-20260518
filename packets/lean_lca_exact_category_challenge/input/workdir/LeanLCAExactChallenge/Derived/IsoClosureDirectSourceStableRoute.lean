import LeanLCAExactChallenge.Derived.TargetIsoDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.IsoClosureStrictRealizationTerminalProductRoute

/-!
W845 replaces the W844 target-isomorphism realization premise by the W810/W809
iso-closure strict-realization route from W651.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W845 closed-map data using W651 iso-closure realization data. -/
structure MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651

/-- W845 closed-embedding data using W651 iso-closure realization data. -/
structure MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  isoClosureRealization :
    MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651

/-- W845 derives W844's target-isomorphism realization data from W651. -/
noncomputable def targetIsoRealizationOfIsoClosureDirectSourceW845
    (isoClosureRealization :
      MetrizableExactAcyclicIsoClosureTrianglehIso13RealizationInputW651) :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784 :=
  targetIsoRealizationOfTrianglehRealizationW809
    (strictRealizationOfIsoClosureRealizationW810 isoClosureRealization)

/-- W845 closed-map data converted to the W844 target-isomorphism surface. -/
noncomputable def closedMapTargetIsoDataOfIsoClosureW845
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844
    where
  exactInputs := data.exactInputs
  targetIsoRealization :=
    targetIsoRealizationOfIsoClosureDirectSourceW845
      data.isoClosureRealization

/-- W845 closed-embedding data converted to the W844 target-isomorphism surface. -/
noncomputable def closedEmbeddingTargetIsoDataOfIsoClosureW845
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844
    where
  exactInputs := data.exactInputs
  targetIsoRealization :=
    targetIsoRealizationOfIsoClosureDirectSourceW845
      data.isoClosureRealization

/-- W845 closed-map data converted to the W839 target homology-zero surface. -/
noncomputable def closedMapTargetHomologyZeroDataOfIsoClosureW845
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedMapTargetHomologyZeroDataOfTargetIsoW844
    (closedMapTargetIsoDataOfIsoClosureW845 data)

/--
W845 closed-embedding data converted to the W839 target homology-zero surface.
-/
noncomputable def closedEmbeddingTargetHomologyZeroDataOfIsoClosureW845
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedEmbeddingTargetHomologyZeroDataOfTargetIsoW844
    (closedEmbeddingTargetIsoDataOfIsoClosureW845 data)

/-- W845 closed-map route preserves W844's direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceW845
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceW844
    (closedMapTargetIsoDataOfIsoClosureW845 data)

/-- W845 closed-embedding route preserves W844's direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceW845
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceW844
    (closedEmbeddingTargetIsoDataOfIsoClosureW845 data)

/-- W845 closed-map route derives all stable fields from W651 data. -/
noncomputable def remainingStableFieldsOfClosedMapIsoClosureDirectSourceW845
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840
        (closedMapTargetHomologyZeroDataOfIsoClosureW845 data)) :=
  remainingStableFieldsOfClosedMapTargetIsoDirectSourceW844
    (closedMapTargetIsoDataOfIsoClosureW845 data)

/-- W845 closed-embedding route derives all stable fields from W651 data. -/
noncomputable def remainingStableFieldsOfClosedEmbeddingIsoClosureDirectSourceW845
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840
        (closedEmbeddingTargetHomologyZeroDataOfIsoClosureW845 data)) :=
  remainingStableFieldsOfClosedEmbeddingTargetIsoDirectSourceW844
    (closedEmbeddingTargetIsoDataOfIsoClosureW845 data)

/-- W845 closed-map stable package from W651 iso-closure data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceW845
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceW844
    (closedMapTargetIsoDataOfIsoClosureW845 data)

/-- W845 closed-embedding stable package from W651 iso-closure data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceW845
    (data :
      MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceW844
    (closedEmbeddingTargetIsoDataOfIsoClosureW845 data)

/-- W845 has one bundled route input: the iso-closure direct-source data. -/
def isoClosureDirectSourceStableRouteInputNamesW845 : List String :=
  ["W845 iso-closure direct-source stable route data"]

/-- W845 keeps the route to one bundled input. -/
theorem isoClosureDirectSourceStableRouteInputNamesW845_count :
    Dbounded.isoClosureDirectSourceStableRouteInputNamesW845.length =
      1 :=
  rfl

/-- Expanded W845 requirements are the exact-input branch and W651 data. -/
def isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845 :
    List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W651 exact-acyclic iso-closure strict realization data"]

/-- The W845 expanded stable route has two concrete requirements. -/
theorem isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845_count :
    Dbounded.isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845.length =
      2 :=
  rfl

/-- Current checked W845 state for W651-derived stable fields. -/
structure MetrizableIsoClosureDirectSourceStableRouteStateW845 : Type where
  seed : String
  declarations : List String
  conversionResult : String
  leftCalculusResult : String
  stablePackageResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W845 state. -/
def currentMetrizableIsoClosureDirectSourceStableRouteStateW845 :
    Dbounded.MetrizableIsoClosureDirectSourceStableRouteStateW845
    where
  seed := "w845-iso-closure-direct-source-stable-route"
  declarations :=
    ["MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845",
      "MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845",
      "targetIsoRealizationOfIsoClosureDirectSourceW845",
      "closedMapTargetIsoDataOfIsoClosureW845",
      "closedEmbeddingTargetIsoDataOfIsoClosureW845",
      "closedMapTargetHomologyZeroDataOfIsoClosureW845",
      "closedEmbeddingTargetHomologyZeroDataOfIsoClosureW845",
      "directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceW845",
      "directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceW845",
      "remainingStableFieldsOfClosedMapIsoClosureDirectSourceW845",
      "remainingStableFieldsOfClosedEmbeddingIsoClosureDirectSourceW845",
      "boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceW845",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceW845",
      "isoClosureDirectSourceStableRouteInputNamesW845",
      "isoClosureDirectSourceStableRouteInputNamesW845_count",
      "isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845",
      "isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845_count"]
  conversionResult :=
    "proved: W810/W809 turn W651 iso-closure realization into W844 target-isomorphism data"
  leftCalculusResult :=
    "proved: W845 data feed W844 direct bounded left calculus through W651-derived W784 data"
  stablePackageResult :=
    "proved: W845 assembles the W844 stable package from W651 iso-closure data"
  derivedInputs :=
    ["W783 strict triangleh realization data from W651 by W810",
      "W784 target-isomorphism realization data from W783 by W809",
      "W785/W663 target ExactAt realization data through W844",
      "W790 target homology-zero realization data through W843/W844",
      "W653 direct finite-shape source data through W842",
      "W657 direct-localization triangulated source data through W842",
      "finite-limit, finite-colimit, pretriangulated, and triangulated fields\
        through W842"]
  remainingInputs :=
    Dbounded.isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845
  productSuccessClaimed := false

theorem currentW845IsoClosureDirectSourceStableRoute_productSuccess :
    (let state :=
        currentMetrizableIsoClosureDirectSourceStableRouteStateW845;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
