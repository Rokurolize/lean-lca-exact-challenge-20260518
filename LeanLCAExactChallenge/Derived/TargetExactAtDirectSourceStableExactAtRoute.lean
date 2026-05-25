import LeanLCAExactChallenge.Derived.TargetExactAtDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.TargetExactAtConcreteLeavesStableFromTargetHomologyZero

/-!
W864 composes the W843 target ExactAt direct-source data with the W863
stable-ExactAt route, so the concrete-leaves target ExactAt direct proof and
the direct-source stable package share one W843 input surface.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W864 closed-map direct bounded left calculus through W863 after W843 converts
target ExactAt data to the W839 target homology-zero surface.
-/
theorem directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetHomologyZeroStableExactAtW863
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data)

/--
W864 closed-embedding direct bounded left calculus through W863 after W843
converts target ExactAt data to the W839 target homology-zero surface.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data)

/--
W864 closed-map stable package through the same W843-to-W839 conversion used by
the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
    (data : MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroStableExactAtW863
    (closedMapTargetHomologyZeroDataOfTargetExactAtW843 data)

/--
W864 closed-embedding stable package through the same W843-to-W839 conversion
used by the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
    (data :
      MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroStableExactAtW863
    (closedEmbeddingTargetHomologyZeroDataOfTargetExactAtW843 data)

/-- W864 has one bundled input: W843 target ExactAt direct-source data. -/
def targetExactAtDirectSourceStableExactAtInputNamesW864 : List String :=
  Dbounded.targetExactAtDirectSourceStableRouteInputNamesW843

theorem targetExactAtDirectSourceStableExactAtInputNamesW864_count :
    targetExactAtDirectSourceStableExactAtInputNamesW864.length = 1 :=
  Dbounded.targetExactAtDirectSourceStableRouteInputNamesW843_count

/-- Expanded W864 requirements are exactly the two concrete W843 fields. -/
def targetExactAtDirectSourceStableExactAtExpandedInputNamesW864 :
    List String :=
  Dbounded.targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843

theorem targetExactAtDirectSourceStableExactAtExpandedInputNamesW864_count :
    targetExactAtDirectSourceStableExactAtExpandedInputNamesW864.length =
      2 :=
  Dbounded.targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843_count

/-- Current checked W864 state. -/
structure MetrizableTargetExactAtDirectSourceStableExactAtRouteStateW864 :
    Type where
  seed : String
  declarations : List String
  targetHomologyZeroConversionResult : String
  concreteLeavesResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetExactAtDirectSourceStableExactAtRouteStateW864 :
    MetrizableTargetExactAtDirectSourceStableExactAtRouteStateW864
    where
  seed := "w864-target-exact-at-direct-source-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864",
      "boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864",
      "targetExactAtDirectSourceStableExactAtInputNamesW864",
      "targetExactAtDirectSourceStableExactAtInputNamesW864_count",
      "targetExactAtDirectSourceStableExactAtExpandedInputNamesW864",
      "targetExactAtDirectSourceStableExactAtExpandedInputNamesW864_count"]
  targetHomologyZeroConversionResult :=
    "proved: W843 target ExactAt data feed the W839 target homology-zero \
      surface through W803"
  concreteLeavesResult :=
    "proved: W843 data feed the W863 concrete-leaves target ExactAt direct \
      route through W862"
  stablePackageResult :=
    "proved: W843 data feed the W863 direct-source stable package through W842"
  replacedInputs :=
    ["separate W839/W790 target homology-zero branch surface at the W863 \
        boundary"]
  remainingInputs := targetExactAtDirectSourceStableExactAtExpandedInputNamesW864
  productSuccessClaimed := false

theorem currentW864TargetExactAtDirectSourceStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableTargetExactAtDirectSourceStableExactAtRouteStateW864;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
