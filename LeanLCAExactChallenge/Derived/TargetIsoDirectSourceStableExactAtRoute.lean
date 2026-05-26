import LeanLCAExactChallenge.Derived.TargetIsoDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.TargetExactAtDirectSourceStableExactAtRoute

/-!
W865 composes the W844 target-isomorphism direct-source data with the W864
stable-ExactAt route, so the W844 target-isomorphism surface gets the same
concrete-leaves target ExactAt direct proof and direct-source stable package.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W865 closed-map direct bounded left calculus through W864 after W844 converts
target-isomorphism data to the W843 target ExactAt direct-source surface.
-/
theorem directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
    (closedMapTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/--
W865 closed-embedding direct bounded left calculus through W864 after W844
converts target-isomorphism data to the W843 target ExactAt surface.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
    (data : MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
    (closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/--
W865 closed-map stable package through the same W844-to-W843 conversion used by
the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
    (closedMapTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/--
W865 closed-embedding stable package through the same W844-to-W843 conversion
used by the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
    (data : MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
    (closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844 data)

/-- W865 has one bundled input: W844 target-isomorphism direct-source data. -/
def targetIsoDirectSourceStableExactAtInputNamesW865 : List String :=
  Dbounded.targetIsoDirectSourceStableRouteInputNamesW844

theorem targetIsoDirectSourceStableExactAtInputNamesW865_count :
    targetIsoDirectSourceStableExactAtInputNamesW865.length = 1 :=
  Dbounded.targetIsoDirectSourceStableRouteInputNamesW844_count

/-- Expanded W865 requirements are exactly the two concrete W844 fields. -/
def targetIsoDirectSourceStableExactAtExpandedInputNamesW865 :
    List String :=
  Dbounded.targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844

theorem targetIsoDirectSourceStableExactAtExpandedInputNamesW865_count :
    targetIsoDirectSourceStableExactAtExpandedInputNamesW865.length =
      2 :=
  Dbounded.targetIsoDirectSourceStableRouteExpandedRequiredFieldNamesW844_count

/-- Current checked W865 state. -/
structure MetrizableTargetIsoDirectSourceStableExactAtRouteStateW865 :
    Type where
  seed : String
  declarations : List String
  targetExactAtConversionResult : String
  concreteLeavesResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetIsoDirectSourceStableExactAtRouteStateW865 :
    MetrizableTargetIsoDirectSourceStableExactAtRouteStateW865
    where
  seed := "w865-target-iso-direct-source-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865",
      "boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865",
      "targetIsoDirectSourceStableExactAtInputNamesW865",
      "targetIsoDirectSourceStableExactAtInputNamesW865_count",
      "targetIsoDirectSourceStableExactAtExpandedInputNamesW865",
      "targetIsoDirectSourceStableExactAtExpandedInputNamesW865_count"]
  targetExactAtConversionResult :=
    "proved: W844 target-isomorphism data feed the W843 target ExactAt \
      surface through W808"
  concreteLeavesResult :=
    "proved: W844 data feed the W864 concrete-leaves target ExactAt direct \
      route through W843"
  stablePackageResult :=
    "proved: W844 data feed the W864 direct-source stable package through W843"
  replacedInputs :=
    ["separate W843/W785 target ExactAt payload surface at the W864 boundary"]
  remainingInputs := targetIsoDirectSourceStableExactAtExpandedInputNamesW865
  productSuccessClaimed := false

theorem currentW865TargetIsoDirectSourceStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableTargetIsoDirectSourceStableExactAtRouteStateW865;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
