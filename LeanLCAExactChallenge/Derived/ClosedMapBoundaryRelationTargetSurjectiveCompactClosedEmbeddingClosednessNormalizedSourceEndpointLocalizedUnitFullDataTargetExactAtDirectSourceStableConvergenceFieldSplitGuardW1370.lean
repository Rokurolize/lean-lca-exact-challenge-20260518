import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataEndpointLocalizedConcreteLeavesConvergenceFieldSplitGuardW1369
import LeanLCAExactChallenge.Derived.TargetExactAtDirectSourceStableExactAtRoute

/-!
W1370 records the definitional convergence from W843/W839 target-ExactAt
direct-source data into the W862 concrete-leaves route and the W863/W864 stable
ExactAt route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W863 closed-map direct calculus is exactly the W862 concrete-leaves route. -/
theorem w863ClosedMapDirectCalculusRunsThroughW862W1370
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
        data =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
        data :=
  rfl

/-- W863 closed-embedding direct calculus is exactly the W862 concrete-leaves route. -/
theorem w863ClosedEmbeddingDirectCalculusRunsThroughW862W1370
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        data =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
        data :=
  rfl

/-- W863 closed-map stable package is exactly the W842 direct-source package. -/
theorem w863ClosedMapStablePackageRunsThroughW842W1370
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863
        data =
      boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroDirectSourceW842
        data :=
  rfl

/-- W863 closed-embedding stable package is exactly the W842 direct-source package. -/
theorem w863ClosedEmbeddingStablePackageRunsThroughW842W1370
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        data =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroDirectSourceW842
        data :=
  rfl

/-- W864 closed-map direct calculus is exactly W843-to-W839 followed by W863. -/
theorem w864ClosedMapDirectCalculusRunsThroughW843W839W863W1370
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        data =
      directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data) :=
  rfl

/-- W864 closed-embedding direct calculus is exactly W843-to-W839 followed by W863. -/
theorem w864ClosedEmbeddingDirectCalculusRunsThroughW843W839W863W1370
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        data =
      directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data) :=
  rfl

/-- W864 closed-map stable package is exactly W843-to-W839 followed by W863. -/
theorem w864ClosedMapStablePackageRunsThroughW843W839W863W1370
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        data =
      boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863
        (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data) :=
  rfl

/-- W864 closed-embedding stable package is exactly W843-to-W839 followed by W863. -/
theorem w864ClosedEmbeddingStablePackageRunsThroughW843W839W863W1370
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        data =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
        (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data) :=
  rfl

/-- W862 closed-map data uses W839 exact inputs to produce W861 concrete leaves. -/
theorem w862ClosedMapConcreteLeavesFieldUsesW839InputsW1370
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (concreteLeavesTargetExactAtDataOfClosedMapTargetHomologyZeroW862
        data).concreteLeaves =
      closedMapConcreteLeavesOfComparisonBijectivityW855 data.exactInputs :=
  rfl

/-- W862 closed-embedding data uses W839 exact inputs to produce W861 concrete leaves. -/
theorem w862ClosedEmbeddingConcreteLeavesFieldUsesW839InputsW1370
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (concreteLeavesTargetExactAtDataOfClosedEmbeddingTargetHomologyZeroW862
        data).concreteLeaves =
      closedEmbeddingConcreteLeavesOfComparisonBijectivityW855
        data.exactInputs :=
  rfl

/-- W1370 keeps the W863 bundled input count visible. -/
theorem w1370TargetHomologyZeroStableExactAtInputCountMatchesW863 :
    targetHomologyZeroStableExactAtInputNamesW863.length = 1 :=
  targetHomologyZeroStableExactAtInputNamesW863_count

/-- W1370 keeps the W864 bundled input count visible. -/
theorem w1370TargetExactAtDirectSourceStableExactAtInputCountMatchesW864 :
    targetExactAtDirectSourceStableExactAtInputNamesW864.length = 1 :=
  targetExactAtDirectSourceStableExactAtInputNamesW864_count

/-- Current W1370 nonterminal state. -/
structure TargetExactAtDirectSourceStableConvergenceStateW1370 : Type where
  seed : String
  declarations : List String
  targetHomologyZeroResult : String
  targetExactAtDirectSourceResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1370 records W843/W839 convergence into the W862/W863/W864 route. -/
def currentTargetExactAtDirectSourceStableConvergenceStateW1370 :
    TargetExactAtDirectSourceStableConvergenceStateW1370 where
  seed := "w1370-target-exact-at-direct-source-stable-convergence"
  declarations :=
    ["w863ClosedMapDirectCalculusRunsThroughW862W1370",
      "w863ClosedEmbeddingDirectCalculusRunsThroughW862W1370",
      "w863ClosedMapStablePackageRunsThroughW842W1370",
      "w863ClosedEmbeddingStablePackageRunsThroughW842W1370",
      "w864ClosedMapDirectCalculusRunsThroughW843W839W863W1370",
      "w864ClosedEmbeddingDirectCalculusRunsThroughW843W839W863W1370",
      "w864ClosedMapStablePackageRunsThroughW843W839W863W1370",
      "w864ClosedEmbeddingStablePackageRunsThroughW843W839W863W1370",
      "w862ClosedMapConcreteLeavesFieldUsesW839InputsW1370",
      "w862ClosedEmbeddingConcreteLeavesFieldUsesW839InputsW1370",
      "w1370TargetHomologyZeroStableExactAtInputCountMatchesW863",
      "w1370TargetExactAtDirectSourceStableExactAtInputCountMatchesW864"]
  targetHomologyZeroResult :=
    "proved: W839 target homology-zero data route through W862 concrete leaves \
      for direct calculus and through W842 for the stable package"
  targetExactAtDirectSourceResult :=
    "proved: W843 target ExactAt direct-source data route through W839 and W863 \
      for both direct calculus and stable package construction"
  remainingInputs :=
    targetExactAtDirectSourceStableExactAtExpandedInputNamesW864
  productSuccessClaimed := false

theorem currentW1370TargetExactAtDirectSourceStableConvergence_productSuccess :
    currentTargetExactAtDirectSourceStableConvergenceStateW1370.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
