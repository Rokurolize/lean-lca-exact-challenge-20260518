import LeanLCAExactChallenge.Derived.IsoClosureDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.TargetIsoDirectSourceStableExactAtRoute

/-!
W866 composes the W845 iso-closure direct-source data with the W865
stable-ExactAt route, so the W651 iso-closure surface inherits the
concrete-leaves target ExactAt direct proof and direct-source stable package.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W866 closed-map direct bounded left calculus through W865 after W845 converts
iso-closure data to the W844 target-isomorphism direct-source surface.
-/
theorem directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865
    (closedMapTargetIsoDataOfIsoClosureW845 data)

/--
W866 closed-embedding direct bounded left calculus through W865 after W845
converts iso-closure data to the W844 target-isomorphism direct-source surface.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
    (data : MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
    (closedEmbeddingTargetIsoDataOfIsoClosureW845 data)

/--
W866 closed-map stable package through the same W845-to-W844 conversion used by
the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865
    (closedMapTargetIsoDataOfIsoClosureW845 data)

/--
W866 closed-embedding stable package through the same W845-to-W844 conversion
used by the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
    (data : MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
    (closedEmbeddingTargetIsoDataOfIsoClosureW845 data)

/-- W866 has one bundled input: W845 iso-closure direct-source data. -/
def isoClosureDirectSourceStableExactAtInputNamesW866 : List String :=
  Dbounded.isoClosureDirectSourceStableRouteInputNamesW845

theorem isoClosureDirectSourceStableExactAtInputNamesW866_count :
    isoClosureDirectSourceStableExactAtInputNamesW866.length = 1 :=
  Dbounded.isoClosureDirectSourceStableRouteInputNamesW845_count

/-- Expanded W866 requirements are exactly the two concrete W845 fields. -/
def isoClosureDirectSourceStableExactAtExpandedInputNamesW866 :
    List String :=
  Dbounded.isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845

theorem isoClosureDirectSourceStableExactAtExpandedInputNamesW866_count :
    isoClosureDirectSourceStableExactAtExpandedInputNamesW866.length =
      2 :=
  Dbounded.isoClosureDirectSourceStableRouteExpandedRequiredFieldNamesW845_count

/-- Current checked W866 state. -/
structure MetrizableIsoClosureDirectSourceStableExactAtRouteStateW866 :
    Type where
  seed : String
  declarations : List String
  targetIsoConversionResult : String
  concreteLeavesResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableIsoClosureDirectSourceStableExactAtRouteStateW866 :
    MetrizableIsoClosureDirectSourceStableExactAtRouteStateW866
    where
  seed := "w866-iso-closure-direct-source-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866",
      "directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866",
      "boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866",
      "isoClosureDirectSourceStableExactAtInputNamesW866",
      "isoClosureDirectSourceStableExactAtInputNamesW866_count",
      "isoClosureDirectSourceStableExactAtExpandedInputNamesW866",
      "isoClosureDirectSourceStableExactAtExpandedInputNamesW866_count"]
  targetIsoConversionResult :=
    "proved: W845 iso-closure data feed the W844 target-isomorphism surface"
  concreteLeavesResult :=
    "proved: W845 data feed the W865 concrete-leaves target ExactAt direct \
      route through W844"
  stablePackageResult :=
    "proved: W845 data feed the W865 direct-source stable package through W844"
  replacedInputs :=
    ["separate W844/W784 target-isomorphism realization surface at the W865 \
        boundary"]
  remainingInputs := isoClosureDirectSourceStableExactAtExpandedInputNamesW866
  productSuccessClaimed := false

theorem currentW866IsoClosureDirectSourceStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableIsoClosureDirectSourceStableExactAtRouteStateW866;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
