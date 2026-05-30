import LeanLCAExactChallenge.Derived.TargetExactAtConcreteLeavesFromTargetHomologyZero
import LeanLCAExactChallenge.Derived.TargetHomologyZeroDirectSourceStableRoute

/-!
W863 reconciles the W862 concrete-leaves target-ExactAt direct route with the
W842 direct-source stable package, removing the separate stable-field arguments
from this W839 surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W863 closed-map direct bounded left calculus through the W862 target-ExactAt route. -/
theorem directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862 data

/--
W863 closed-embedding direct bounded left calculus through the W862
target-ExactAt route.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
    data

/--
W863 closed-map stable package from W839 data, using W842 for the stable fields
and W862 for the concrete-leaves target-ExactAt direct route evidence.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroDirectSourceW842
    data

/--
W863 closed-embedding stable package from W839 data, using W842 for the stable
fields and W862 for the concrete-leaves target-ExactAt direct route evidence.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroDirectSourceW842
    data

/-- W863 has one bundled route input: W839 target homology-zero data. -/
def targetHomologyZeroStableExactAtInputNamesW863 : List String :=
  ["W839 closed-map or closed-embedding target homology-zero data"]

theorem targetHomologyZeroStableExactAtInputNamesW863_count :
    targetHomologyZeroStableExactAtInputNamesW863.length = 1 :=
  rfl

/-- Expanded W863 requirements are the two concrete fields inside W839 data. -/
def targetHomologyZeroStableExactAtExpandedInputNamesW863 : List String :=
  Dbounded.targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839

theorem targetHomologyZeroStableExactAtExpandedInputNamesW863_count :
    targetHomologyZeroStableExactAtExpandedInputNamesW863.length = 2 :=
  Dbounded.targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839_count

/-- Current checked W863 state. -/
structure MetrizableTargetHomologyZeroStableExactAtRouteStateW863 :
    Type where
  seed : String
  declarations : List String
  targetExactAtDirectResult : String
  stablePackageResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetHomologyZeroStableExactAtRouteStateW863 :
    MetrizableTargetHomologyZeroStableExactAtRouteStateW863
    where
  seed := "w863-target-homology-zero-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863",
      "boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863",
      "targetHomologyZeroStableExactAtInputNamesW863",
      "targetHomologyZeroStableExactAtInputNamesW863_count",
      "targetHomologyZeroStableExactAtExpandedInputNamesW863",
      "targetHomologyZeroStableExactAtExpandedInputNamesW863_count"]
  targetExactAtDirectResult :=
    "proved: W839 data feed the W862 concrete-leaves target-ExactAt direct route"
  stablePackageResult :=
    "proved: W842 supplies the stable package from the same W839 data without \
      separate stable-field arguments"
  removedInputs :=
    ["separate HasFiniteLimits (Dbounded MetrizableLCA)",
      "separate HasFiniteColimits (Dbounded MetrizableLCA)",
      "separate Pretriangulated (Dbounded MetrizableLCA)",
      "separate IsTriangulated (Dbounded MetrizableLCA)"]
  remainingInputs :=
    targetHomologyZeroStableExactAtExpandedInputNamesW863
  productSuccessClaimed := false

theorem currentW863TargetHomologyZeroStableExactAtRoute_productSuccess :
    (let state := currentMetrizableTargetHomologyZeroStableExactAtRouteStateW863;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
