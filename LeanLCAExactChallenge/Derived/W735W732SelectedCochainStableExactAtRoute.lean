import LeanLCAExactChallenge.Derived.RouteDataProviderFromComparisonBijectivity
import LeanLCAExactChallenge.Derived.W732SelectedCochainStableExactAtRoute

/-!
W876 feeds the W875 W732 selected-cochain stable-ExactAt route from the W735
closed-map or closed-embedding branch records using W855 comparison-bijectivity
route-data constructors.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W876 closed-map W732 route data from one W735 branch record. -/
def routeDataProviderOfClosedMapW735ForW876
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  closedMapRouteDataProviderOfComparisonBijectivityW855 inputs

/-- W876 closed-embedding W732 route data from one W735 branch record. -/
def routeDataProviderOfClosedEmbeddingW735ForW876
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732 :=
  closedEmbeddingRouteDataProviderOfComparisonBijectivityW855 inputs

/--
W876 closed-map direct bounded left calculus through W855 route-data
construction and the W875 stable ExactAt route.
-/
theorem directBoundedLeftCalculusOfClosedMapW735W732SelectedCochainStableExactAtW876
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
    (routeDataProviderOfClosedMapW735ForW876 inputs)

/--
W876 closed-embedding direct bounded left calculus through W855 route-data
construction and the W875 stable ExactAt route.
-/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingW735W732SelectedCochainStableExactAtW876
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
    (routeDataProviderOfClosedEmbeddingW735ForW876 inputs)

/--
W876 closed-map bounded derived infinity-category package through W855 route
data and W875 stable ExactAt evidence.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapW735W732SelectedCochainStableExactAtW876
    (inputs : MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
    (routeDataProviderOfClosedMapW735ForW876 inputs)

/--
W876 closed-embedding bounded derived infinity-category package through W855
route data and W875 stable ExactAt evidence.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingW735W732SelectedCochainStableExactAtW876
    (inputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
    (routeDataProviderOfClosedEmbeddingW735ForW876 inputs)

/-- W876 exposes the nine concrete W735 branch fields consumed by W855. -/
def w735W732SelectedCochainStableExactAtInputNamesW876 : List String :=
  comparisonBijectivityRouteDataBranchInputNamesW855

theorem w735W732SelectedCochainStableExactAtInputNamesW876_count :
    w735W732SelectedCochainStableExactAtInputNamesW876.length = 9 :=
  comparisonBijectivityRouteDataBranchInputNamesW855_count

/-- Current checked W876 state. -/
structure MetrizableW735W732SelectedCochainStableExactAtRouteStateW876 :
    Type where
  seed : String
  declarations : List String
  routeDataConstructionResult : String
  exactAtResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableW735W732SelectedCochainStableExactAtRouteStateW876 :
    MetrizableW735W732SelectedCochainStableExactAtRouteStateW876
    where
  seed := "w876-w735-w732-selected-cochain-stable-exact-at-route"
  declarations :=
    ["routeDataProviderOfClosedMapW735ForW876",
      "routeDataProviderOfClosedEmbeddingW735ForW876",
      "directBoundedLeftCalculusOfClosedMapW735W732" ++
        "SelectedCochainStableExactAtW876",
      "directBoundedLeftCalculusOfClosedEmbeddingW735W732" ++
        "SelectedCochainStableExactAtW876",
      "boundedDerivedInfinityCategoryOfClosedMapW735W732" ++
        "SelectedCochainStableExactAtW876",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingW735W732" ++
        "SelectedCochainStableExactAtW876",
      "w735W732SelectedCochainStableExactAtInputNamesW876",
      "w735W732SelectedCochainStableExactAtInputNamesW876_count"]
  routeDataConstructionResult :=
    "proved: W855 constructs the W732 provider for each W735 branch record"
  exactAtResult :=
    "proved: W735 branch records feed the W875 stable ExactAt route"
  replacedInputs :=
    w732SelectedCochainStableExactAtInputNamesW875
  remainingInputs :=
    w735W732SelectedCochainStableExactAtInputNamesW876
  productSuccessClaimed := false

theorem currentW876W735W732SelectedCochainStableExactAtRoute_productSuccess :
    currentMetrizableW735W732SelectedCochainStableExactAtRouteStateW876.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
