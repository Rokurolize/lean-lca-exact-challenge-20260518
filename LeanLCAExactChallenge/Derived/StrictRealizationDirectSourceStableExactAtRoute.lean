import LeanLCAExactChallenge.Derived.StrictRealizationDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.IsoClosureDirectSourceStableExactAtRoute

/-!
W867 composes the W846 strict-realization direct-source data with the W866
stable-ExactAt route, so the W783 strict triangleh realization surface inherits
the concrete-leaves target ExactAt direct proof and stable package.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W867 closed-map direct bounded left calculus through W866 after W846 derives
the W845 iso-closure data from strict-realization data.
-/
theorem
    directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
    (data : MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapIsoClosureDirectSourceStableExactAtW866
    (closedMapIsoClosureDataOfStrictDirectSourceW846 data)

/--
W867 closed-embedding direct bounded left calculus through W866 after W846
derives the W845 iso-closure data from strict-realization data.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
    (closedEmbeddingIsoClosureDataOfStrictDirectSourceW846 data)

/--
W867 closed-map stable package through the same W846-to-W845 conversion used by
the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
    (data : MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapIsoClosureDirectSourceStableExactAtW866
    (closedMapIsoClosureDataOfStrictDirectSourceW846 data)

/--
W867 closed-embedding stable package through the same W846-to-W845 conversion
used by the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingIsoClosureDirectSourceStableExactAtW866
    (closedEmbeddingIsoClosureDataOfStrictDirectSourceW846 data)

/-- W867 has one bundled input: W846 strict-realization direct-source data. -/
def strictRealizationDirectSourceStableExactAtInputNamesW867 :
    List String :=
  Dbounded.strictRealizationDirectSourceStableRouteInputNamesW846

theorem strictRealizationDirectSourceStableExactAtInputNamesW867_count :
    strictRealizationDirectSourceStableExactAtInputNamesW867.length =
      1 :=
  Dbounded.strictRealizationDirectSourceStableRouteInputNamesW846_count

/-- Expanded W867 requirements are exactly the two concrete W846 fields. -/
def strictRealizationDirectSourceStableExactAtExpandedInputNamesW867 :
    List String :=
  Dbounded.strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846

theorem strictRealizationDirectSourceStableExactAtExpandedInputNamesW867_count :
    strictRealizationDirectSourceStableExactAtExpandedInputNamesW867.length =
      2 :=
  Dbounded.strictRealizationDirectSourceStableRouteExpandedRequiredFieldNamesW846_count

/-- Current checked W867 state. -/
structure MetrizableStrictRealizationDirectSourceStableExactAtRouteStateW867 :
    Type where
  seed : String
  declarations : List String
  isoClosureConversionResult : String
  concreteLeavesResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableStrictRealizationDirectSourceStableExactAtRouteStateW867 :
    MetrizableStrictRealizationDirectSourceStableExactAtRouteStateW867
    where
  seed := "w867-strict-realization-direct-source-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867",
      "directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867",
      "boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealization" ++
        "DirectSourceStableExactAtW867",
      "strictRealizationDirectSourceStableExactAtInputNamesW867",
      "strictRealizationDirectSourceStableExactAtInputNamesW867_count",
      "strictRealizationDirectSourceStableExactAtExpandedInputNamesW867",
      "strictRealizationDirectSourceStableExactAtExpandedInputNamesW867_count"]
  isoClosureConversionResult :=
    "proved: W846 strict-realization data feed W845 iso-closure data"
  concreteLeavesResult :=
    "proved: W846 data feed the W866 concrete-leaves target ExactAt direct \
      route through W845"
  stablePackageResult :=
    "proved: W846 data feed the W866 direct-source stable package through W845"
  replacedInputs :=
    ["separate W845/W651 iso-closure realization surface at the W866 boundary"]
  remainingInputs :=
    strictRealizationDirectSourceStableExactAtExpandedInputNamesW867
  productSuccessClaimed := false

theorem currentW867StrictRealizationDirectSourceStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableStrictRealizationDirectSourceStableExactAtRouteStateW867;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
