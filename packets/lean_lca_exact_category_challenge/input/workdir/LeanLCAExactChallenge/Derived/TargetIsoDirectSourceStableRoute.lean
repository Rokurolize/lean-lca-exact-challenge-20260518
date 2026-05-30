import LeanLCAExactChallenge.Derived.TargetExactAtDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.TargetIsoToTargetExactAtTerminalProductRoute

/-!
W844 replaces the W843 target ExactAt realization premise by the W808
target-isomorphism-to-target-ExactAt conversion, then reuses the W843
direct-source stable route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W844 closed-map data using target-isomorphism realization data. -/
structure MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784

/-- W844 closed-embedding data using target-isomorphism realization data. -/
structure MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  targetIsoRealization :
    MetrizableExactAcyclicHomotopyObjectTargetIsoRealizationW784

/-- W844 closed-map data converted to the W808 target-isomorphism surface. -/
noncomputable def closedMapW808DataOfTargetIsoW844
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedMapTargetIsoTerminalBranchDataW808
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  targetIsoRealization := data.targetIsoRealization
  exactInputs := data.exactInputs

/-- W844 closed-embedding data converted to the W808 target-isomorphism surface. -/
noncomputable def closedEmbeddingW808DataOfTargetIsoW844
    (data :
      MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedEmbeddingTargetIsoTerminalBranchDataW808
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  targetIsoRealization := data.targetIsoRealization
  exactInputs := data.exactInputs

/-- W844 closed-map data converted to the W803 target ExactAt terminal surface. -/
noncomputable def closedMapW803DataOfTargetIsoW844
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803 :=
  closedMapTargetExactAtDataOfTargetIsoW808
    (closedMapW808DataOfTargetIsoW844 data)

/--
W844 closed-embedding data converted to the W803 target ExactAt terminal
surface.
-/
noncomputable def closedEmbeddingW803DataOfTargetIsoW844
    (data :
      MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803 :=
  closedEmbeddingTargetExactAtDataOfTargetIsoW808
    (closedEmbeddingW808DataOfTargetIsoW844 data)

/-- W844 closed-map data converted to the W843 direct-source surface. -/
noncomputable def closedMapTargetExactAtDirectSourceDataOfTargetIsoW844
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843
    where
  exactInputs := data.exactInputs
  targetExactAtPayload :=
    (closedMapW803DataOfTargetIsoW844 data).targetExactAtPayload

/-- W844 closed-embedding data converted to the W843 direct-source surface. -/
noncomputable def closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844
    (data :
      MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843
    where
  exactInputs := data.exactInputs
  targetExactAtPayload :=
    (closedEmbeddingW803DataOfTargetIsoW844 data).targetExactAtPayload

/-- W844 closed-map data converted to the W839 target homology-zero surface. -/
noncomputable def closedMapTargetHomologyZeroDataOfTargetIsoW844
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedMapTargetHomologyZeroDataOfTargetExactAtW843
    (closedMapTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/--
W844 closed-embedding data converted to the W839 target homology-zero surface.
-/
noncomputable def closedEmbeddingTargetHomologyZeroDataOfTargetIsoW844
    (data :
      MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843
    (closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/-- W844 closed-map route preserves the W843 direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceW844
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceW843
    (closedMapTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/-- W844 closed-embedding route preserves the W843 direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceW844
    (data :
      MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceW843
    (closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/-- W844 closed-map route derives all stable fields from target-isomorphism data. -/
noncomputable def remainingStableFieldsOfClosedMapTargetIsoDirectSourceW844
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840
        (closedMapTargetHomologyZeroDataOfTargetIsoW844 data)) :=
  remainingStableFieldsOfClosedMapTargetExactAtDirectSourceW843
    (closedMapTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/--
W844 closed-embedding route derives all stable fields from target-isomorphism
data.
-/
noncomputable def remainingStableFieldsOfClosedEmbeddingTargetIsoDirectSourceW844
    (data :
      MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840
        (closedEmbeddingTargetHomologyZeroDataOfTargetIsoW844 data)) :=
  remainingStableFieldsOfClosedEmbeddingTargetExactAtDirectSourceW843
    (closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/-- W844 closed-map stable package from target-isomorphism data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceW844
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceW843
    (closedMapTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/-- W844 closed-embedding stable package from target-isomorphism data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceW844
    (data :
      MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceW843
    (closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/-- W844 has one bundled route input: the target-isomorphism direct-source data. -/
def targetIsoDirectSourceStableRouteInputNamesW844 : List String :=
  ["W844 target-isomorphism direct-source stable route data"]

/-- W844 keeps the route to one bundled input. -/
theorem targetIsoDirectSourceStableRouteInputNamesW844_count :
    Dbounded.targetIsoDirectSourceStableRouteInputNamesW844.length =
      1 :=
  rfl

/-- Expanded W844 requirements are the exact-input branch and target-isomorphism data. -/
def targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844 :
    List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W784 exact-acyclic homotopy-object target-isomorphism realization data"]

/-- The W844 expanded stable route has two concrete requirements. -/
theorem targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844_count :
    Dbounded.targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844.length =
      2 :=
  rfl

/-- Current checked W844 state for target-isomorphism-derived stable fields. -/
structure MetrizableTargetIsoDirectSourceStableRouteStateW844 :
    Type where
  seed : String
  declarations : List String
  conversionResult : String
  leftCalculusResult : String
  stablePackageResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W844 state. -/
def currentMetrizableTargetIsoDirectSourceStableRouteStateW844 :
    Dbounded.MetrizableTargetIsoDirectSourceStableRouteStateW844
    where
  seed := "w844-target-iso-direct-source-stable-route"
  declarations :=
    ["MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844",
      "MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844",
      "closedMapW808DataOfTargetIsoW844",
      "closedEmbeddingW808DataOfTargetIsoW844",
      "closedMapW803DataOfTargetIsoW844",
      "closedEmbeddingW803DataOfTargetIsoW844",
      "closedMapTargetExactAtDirectSourceDataOfTargetIsoW844",
      "closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844",
      "closedMapTargetHomologyZeroDataOfTargetIsoW844",
      "closedEmbeddingTargetHomologyZeroDataOfTargetIsoW844",
      "directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceW844",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceW844",
      "remainingStableFieldsOfClosedMapTargetIsoDirectSourceW844",
      "remainingStableFieldsOfClosedEmbeddingTargetIsoDirectSourceW844",
      "boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceW844",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceW844",
      "targetIsoDirectSourceStableRouteInputNamesW844",
      "targetIsoDirectSourceStableRouteInputNamesW844_count",
      "targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844",
      "targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844_count"]
  conversionResult :=
    "proved: W808 turns W784 target-isomorphism data into the W843 target ExactAt surface"
  leftCalculusResult :=
    "proved: W844 data feed W843 direct bounded left calculus through W808"
  stablePackageResult :=
    "proved: W844 assembles the W843 stable package from target-isomorphism data"
  derivedInputs :=
    ["W785/W663 target ExactAt realization data from W784 target-isomorphism\
        realization data",
      "W790 target homology-zero realization data through W843",
      "W653 direct finite-shape source data through W842",
      "W657 direct-localization triangulated source data through W842",
      "finite-limit, finite-colimit, pretriangulated, and triangulated fields\
        through W842"]
  remainingInputs :=
    Dbounded.targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844
  productSuccessClaimed := false

theorem currentW844TargetIsoDirectSourceStableRoute_productSuccess :
    (let state :=
        currentMetrizableTargetIsoDirectSourceStableRouteStateW844;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
