import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainStrictificationRoute
import LeanLCAExactChallenge.Derived.StrictRealizationDirectSourceStableExactAtRoute

/-!
W868 composes the W847 exact-acyclic selected-cochain direct-source data with
the W867 stable-ExactAt route, so the selected-cochain strictification boundary
inherits the concrete-leaves target ExactAt direct proof and stable package.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W868 closed-map direct bounded left calculus through W867 after W847 converts
selected-cochain strictification data to the W846 strict-realization surface.
-/
theorem
    directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapStrictRealizationDirectSourceStableExactAtW867
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/--
W868 closed-embedding direct bounded left calculus through W867 after W847
converts selected-cochain strictification data to the W846 strict-realization
surface.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/--
W868 closed-map stable package through the W847-to-W846 conversion used by the
concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapStrictRealizationDirectSourceStableExactAtW867
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/--
W868 closed-embedding stable package through the W847-to-W846 conversion used by
the concrete-leaves target ExactAt direct route.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationDirectSourceStableExactAtW867
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/-- W868 has one bundled input: W847 selected-cochain direct-source data. -/
def selectedCochainDirectSourceStableExactAtInputNamesW868 :
    List String :=
  Dbounded.selectedCochainDirectSourceStableRouteInputNamesW847

theorem selectedCochainDirectSourceStableExactAtInputNamesW868_count :
    selectedCochainDirectSourceStableExactAtInputNamesW868.length =
      1 :=
  Dbounded.selectedCochainDirectSourceStableRouteInputNamesW847_count

/-- Expanded W868 requirements are exactly the two concrete W847 fields. -/
def selectedCochainDirectSourceStableExactAtExpandedInputNamesW868 :
    List String :=
  Dbounded.selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847

theorem selectedCochainDirectSourceStableExactAtExpandedInputNamesW868_count :
    selectedCochainDirectSourceStableExactAtExpandedInputNamesW868.length =
      2 :=
  Dbounded.selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847_count

/-- Current checked W868 state. -/
structure MetrizableSelectedCochainDirectSourceStableExactAtRouteStateW868 :
    Type where
  seed : String
  declarations : List String
  strictRealizationConversionResult : String
  concreteLeavesResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSelectedCochainDirectSourceStableExactAtRouteStateW868 :
    MetrizableSelectedCochainDirectSourceStableExactAtRouteStateW868
    where
  seed := "w868-selected-cochain-direct-source-stable-exact-at-route"
  declarations :=
    ["directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868",
      "directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868",
      "boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochain" ++
        "DirectSourceStableExactAtW868",
      "selectedCochainDirectSourceStableExactAtInputNamesW868",
      "selectedCochainDirectSourceStableExactAtInputNamesW868_count",
      "selectedCochainDirectSourceStableExactAtExpandedInputNamesW868",
      "selectedCochainDirectSourceStableExactAtExpandedInputNamesW868_count"]
  strictRealizationConversionResult :=
    "proved: W847 selected-cochain data feed W846 strict-realization data"
  concreteLeavesResult :=
    "proved: W847 data feed the W867 concrete-leaves target ExactAt direct \
      route through W846"
  stablePackageResult :=
    "proved: W847 data feed the W867 direct-source stable package through W846"
  replacedInputs :=
    ["separate W846/W783 strict-realization surface at the W867 boundary"]
  remainingInputs :=
    selectedCochainDirectSourceStableExactAtExpandedInputNamesW868
  productSuccessClaimed := false

theorem currentW868SelectedCochainDirectSourceStableExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableSelectedCochainDirectSourceStableExactAtRouteStateW868;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
