import LeanLCAExactChallenge.Derived.TargetExactAtW664TerminalProductRoute
import LeanLCAExactChallenge.Derived.TargetHomologyZeroDirectSourceStableRoute

/-!
W843 replaces the W842 target homology-zero realization premise by the W803
target ExactAt-to-homology-zero conversion, then reuses the W842 direct-source
stable route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W843 closed-map data using target ExactAt realization data. -/
structure MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785

/-- W843 closed-embedding data using target ExactAt realization data. -/
structure MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  targetExactAtPayload :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785

/-- W843 closed-map data converted to the W803 target ExactAt terminal surface. -/
noncomputable def closedMapW803DataOfTargetExactAtW843
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    MetrizableClosedMapTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/--
W843 closed-embedding data converted to the W803 target ExactAt terminal
surface.
-/
noncomputable def closedEmbeddingW803DataOfTargetExactAtW843
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    MetrizableClosedEmbeddingTargetExactAtW664TerminalBranchDataW803
    where
  comparisonIso := universalLeftRightComparisonIso_of_comparisonBijectivityW831
  targetExactAtPayload := data.targetExactAtPayload
  exactInputs := data.exactInputs

/-- W843 closed-map data converted to the W839 target homology-zero surface. -/
noncomputable def closedMapTargetHomologyZeroDataOfTargetExactAtW843
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839
    where
  exactInputs := data.exactInputs
  targetHomologyZeroPayload :=
    targetHomologyZeroPayloadOfTargetExactAtW803
      cochainHasHomology_of_comparisonBijectivityW839
      data.targetExactAtPayload

/--
W843 closed-embedding data converted to the W839 target homology-zero surface.
-/
noncomputable def closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839
    where
  exactInputs := data.exactInputs
  targetHomologyZeroPayload :=
    targetHomologyZeroPayloadOfTargetExactAtW803
      cochainHasHomology_of_comparisonBijectivityW839
      data.targetExactAtPayload

/-- W843 closed-map data converted to the W664 terminal route through W803. -/
noncomputable def closedMapW664TerminalDataOfTargetExactAtW843
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    MetrizableClosedMapTargetHomologyZeroW664TerminalBranchDataW799 :=
  closedMapW664TerminalDataOfTargetExactAtW803
    (closedMapW803DataOfTargetExactAtW843 data)

/-- W843 closed-embedding data converted to the W664 terminal route through W803. -/
noncomputable def closedEmbeddingW664TerminalDataOfTargetExactAtW843
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    MetrizableClosedEmbeddingTargetHomologyZeroW664TerminalBranchDataW799 :=
  closedEmbeddingW664TerminalDataOfTargetExactAtW803
    (closedEmbeddingW803DataOfTargetExactAtW843 data)

/-- W843 closed-map route preserves the W842 direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceW843
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetHomologyZeroDirectSourceW842
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data)

/-- W843 closed-embedding route preserves the W842 direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceW843
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroDirectSourceW842
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data)

/-- W843 closed-map route derives all stable fields from target ExactAt data. -/
noncomputable def remainingStableFieldsOfClosedMapTargetExactAtDirectSourceW843
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840
        (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data)) :=
  remainingStableFieldsOfClosedMapTargetHomologyZeroDirectSourceW842
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data)

/-- W843 closed-embedding route derives all stable fields from target ExactAt data. -/
noncomputable def remainingStableFieldsOfClosedEmbeddingTargetExactAtDirectSourceW843
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840
        (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data)) :=
  remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroDirectSourceW842
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data)

/-- W843 closed-map stable package from target ExactAt data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceW843
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroDirectSourceW842
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data)

/-- W843 closed-embedding stable package from target ExactAt data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceW843
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroDirectSourceW842
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data)

/-- W843 has one bundled route input: the target ExactAt direct-source data. -/
def targetExactAtDirectSourceStableRouteInputNamesW843 : List String :=
  ["W843 target ExactAt direct-source stable route data"]

/-- W843 keeps the route to one bundled input. -/
theorem targetExactAtDirectSourceStableRouteInputNamesW843_count :
    Dbounded.targetExactAtDirectSourceStableRouteInputNamesW843.length =
      1 :=
  rfl

/-- Expanded W843 requirements are the exact-input branch and target ExactAt data. -/
def targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843 :
    List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W785/W663 target ExactAt realization data for exactAcyclicHomotopyObject MetrizableLCA"]

/-- The W843 expanded stable route has two concrete requirements. -/
theorem targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843_count :
    Dbounded.targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843.length =
      2 :=
  rfl

/-- Current checked W843 state for target ExactAt-derived stable fields. -/
structure MetrizableTargetExactAtDirectSourceStableRouteStateW843 :
    Type where
  seed : String
  declarations : List String
  conversionResult : String
  leftCalculusResult : String
  stablePackageResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W843 state. -/
def currentMetrizableTargetExactAtDirectSourceStableRouteStateW843 :
    Dbounded.MetrizableTargetExactAtDirectSourceStableRouteStateW843
    where
  seed := "w843-target-exact-at-direct-source-stable-route"
  declarations :=
    ["MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843",
      "MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843",
      "closedMapW803DataOfTargetExactAtW843",
      "closedEmbeddingW803DataOfTargetExactAtW843",
      "closedMapTargetHomologyZeroDataOfTargetExactAtW843",
      "closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843",
      "closedMapW664TerminalDataOfTargetExactAtW843",
      "closedEmbeddingW664TerminalDataOfTargetExactAtW843",
      "directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceW843",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceW843",
      "remainingStableFieldsOfClosedMapTargetExactAtDirectSourceW843",
      "remainingStableFieldsOfClosedEmbeddingTargetExactAtDirectSourceW843",
      "boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceW843",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceW843",
      "targetExactAtDirectSourceStableRouteInputNamesW843",
      "targetExactAtDirectSourceStableRouteInputNamesW843_count",
      "targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843",
      "targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843_count"]
  conversionResult :=
    "proved: W803 turns W785/W663 target ExactAt data into the W839 target homology-zero surface"
  leftCalculusResult :=
    "proved: W843 data feed W842 direct bounded left calculus through W839"
  stablePackageResult :=
    "proved: W843 assembles the W842 stable package from target ExactAt data"
  derivedInputs :=
    ["W790 target homology-zero realization data from W785/W663 target ExactAt data",
      "W653 direct finite-shape source data through W842",
      "W657 direct-localization triangulated source data through W842",
      "finite-limit, finite-colimit, pretriangulated, and triangulated fields\
        through W842"]
  remainingInputs :=
    Dbounded.targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843
  productSuccessClaimed := false

theorem currentW843TargetExactAtDirectSourceStableRoute_productSuccess :
    (let state :=
        currentMetrizableTargetExactAtDirectSourceStableRouteStateW843;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
