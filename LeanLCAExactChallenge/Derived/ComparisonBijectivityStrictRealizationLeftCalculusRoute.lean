import LeanLCAExactChallenge.Derived.StrictRealizationLeftCalculusRoute
import LeanLCAExactChallenge.Derived.ComparisonBijectivityLeftCalculusRoute

/-!
W838 routes the W831 comparison-bijectivity result into the W837 strict
realization left-calculus path.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- W838 closed-map data after W831 supplies comparison isomorphisms. -/
structure MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838 :
    Type 2 where
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735

/-- W838 closed-embedding data after W831 supplies comparison isomorphisms. -/
structure
    MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838 :
    Type 2 where
  trianglehRealization :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735

/-- W838 closed-map data converted to W809 strict-realization data. -/
noncomputable def strictRealizationDataOfClosedMapComparisonBijectivityW838
    (data :
      MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableClosedMapStrictRealizationTerminalBranchDataW809
    where
  comparisonIso :=
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
  trianglehRealization := data.trianglehRealization
  exactInputs := data.exactInputs

/-- W838 closed-embedding data converted to W809 strict-realization data. -/
noncomputable def
    strictRealizationDataOfClosedEmbeddingComparisonBijectivityW838
    (data :
      MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809
    where
  comparisonIso :=
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
  trianglehRealization := data.trianglehRealization
  exactInputs := data.exactInputs

/-- W838 closed-map data converted to W836 data through W837. -/
noncomputable def
    exactInputsLeftCalculusDataOfClosedMapComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836 :=
  exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837
    (strictRealizationDataOfClosedMapComparisonBijectivityW838 data)

/-- W838 closed-embedding data converted to W836 data through W837. -/
noncomputable def
    exactInputsLeftCalculusDataOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836 :=
  exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837
    (strictRealizationDataOfClosedEmbeddingComparisonBijectivityW838 data)

/-- W838 closed-map data converted to the W835 exact-input route. -/
noncomputable def
    exactInputsIsoClosureDataOfClosedMapComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835 :=
  exactInputsIsoClosureDataOfClosedMapStrictRealizationW837
    (strictRealizationDataOfClosedMapComparisonBijectivityW838 data)

/-- W838 closed-embedding data converted to the W835 exact-input route. -/
noncomputable def
    exactInputsIsoClosureDataOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835 :=
  exactInputsIsoClosureDataOfClosedEmbeddingStrictRealizationW837
    (strictRealizationDataOfClosedEmbeddingComparisonBijectivityW838 data)

/-- W838 closed-map data converted to the W834 iso-closure route. -/
noncomputable def
    isoClosureLeftCalculusDataOfClosedMapComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 :=
  isoClosureLeftCalculusDataOfClosedMapStrictRealizationW837
    (strictRealizationDataOfClosedMapComparisonBijectivityW838 data)

/-- W838 closed-embedding data converted to the W834 iso-closure route. -/
noncomputable def
    isoClosureLeftCalculusDataOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 :=
  isoClosureLeftCalculusDataOfClosedEmbeddingStrictRealizationW837
    (strictRealizationDataOfClosedEmbeddingComparisonBijectivityW838 data)

/-- W838 derives the W785 target ExactAt payload from closed-map data. -/
noncomputable def
    targetExactAtPayloadOfClosedMapComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedMapStrictRealizationW837
    (strictRealizationDataOfClosedMapComparisonBijectivityW838 data)

/-- W838 derives the W785 target ExactAt payload from closed-embedding data. -/
noncomputable def
    targetExactAtPayloadOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedEmbeddingStrictRealizationW837
    (strictRealizationDataOfClosedEmbeddingComparisonBijectivityW838 data)

/-- W838 proves direct bounded left calculus from closed-map data. -/
theorem
    directBoundedLeftCalculusOfClosedMapComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapStrictRealizationW837
    (strictRealizationDataOfClosedMapComparisonBijectivityW838 data)

/-- W838 proves direct bounded left calculus from closed-embedding data. -/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationW837
    (strictRealizationDataOfClosedEmbeddingComparisonBijectivityW838 data)

/-- W838 stable route using closed-map data and W831 comparison isomorphisms. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedMapComparisonBijectivityStrictRealizationW838 data
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      Pretriangulated (Dbounded MetrizableLCA.{0}))
    (triangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedMapComparisonBijectivityStrictRealizationW838 data
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
      IsTriangulated (Dbounded MetrizableLCA.{0})) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedMapComparisonBijectivityStrictRealizationW838
      data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-!
W838 stable route using closed-embedding data and W831 comparison
isomorphisms.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
    (data :
      MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityStrictRealizationW838 data
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      Pretriangulated (Dbounded MetrizableLCA.{0}))
    (triangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityStrictRealizationW838 data
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
      IsTriangulated (Dbounded MetrizableLCA.{0})) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityStrictRealizationW838
      data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/--
W838 direct-left-calculus inputs after W831 supplies the W837 comparison
function.
-/
def comparisonBijectivityStrictRealizationLeftCalculusInputNamesW838 :
    List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W783 exact-acyclic homotopy-object strict triangleh realization data"]

/-- W838 leaves two direct-left-calculus inputs. -/
theorem comparisonBijectivityStrictRealizationLeftCalculusInputNamesW838_count :
    Dbounded.comparisonBijectivityStrictRealizationLeftCalculusInputNamesW838.length =
      2 :=
  rfl

/-- W838 stable route requirements when W831 supplies comparison isomorphisms. -/
def comparisonBijectivityStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW838 :
    List String :=
  ["closed-map or closed-embedding W838 strict-realization data",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W838 keeps the stable route to five bundled requirements. -/
theorem
    comparisonBijectivityStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW838_count :
    (let names :=
      comparisonBijectivityStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW838;
      names.length) =
        5 :=
  rfl

/-- Expanded W838 requirements, showing the current route obligations. -/
def comparisonBijectivityStrictRealizationLeftCalculusExpandedRequiredFieldNamesW838 :
    List String :=
  Dbounded.comparisonBijectivityStrictRealizationLeftCalculusInputNamesW838 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W838 expanded stable route has six concrete requirements. -/
theorem
    comparisonBijectivityStrictRealizationLeftCalculusExpandedRequiredFieldNamesW838_count :
    (let names :=
      comparisonBijectivityStrictRealizationLeftCalculusExpandedRequiredFieldNamesW838;
      names.length) =
        6 :=
  rfl

/-- Current checked W838 state for comparison-bijectivity strict realization. -/
structure
    MetrizableComparisonBijectivityStrictRealizationLeftCalculusRouteStateW838 :
    Type where
  seed : String
  declarations : List String
  comparisonResult : String
  leftCalculusResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W838 state. -/
def currentMetrizableComparisonBijectivityStrictRealizationLeftCalculusRouteStateW838 :
    Dbounded.MetrizableComparisonBijectivityStrictRealizationLeftCalculusRouteStateW838 where
  seed := "w838-comparison-bijectivity-strict-realization-left-calculus-route"
  declarations :=
    ["MetrizableClosedMapComparisonBijectivityStrictRealizationLeftCalculusDataW838",
      "MetrizableClosedEmbeddingComparisonBijectivityStrictRealizationLeftCalculusDataW838",
      "strictRealizationDataOfClosedMapComparisonBijectivityW838",
      "strictRealizationDataOfClosedEmbeddingComparisonBijectivityW838",
      "exactInputsLeftCalculusDataOfClosedMapComparisonBijectivityStrictRealizationW838",
      "exactInputsLeftCalculusDataOfClosedEmbeddingComparisonBijectivityStrictRealizationW838",
      "directBoundedLeftCalculusOfClosedMapComparisonBijectivityStrictRealizationW838",
      "directBoundedLeftCalculusOfClosedEmbeddingComparisonBijectivityStrictRealizationW838",
      "boundedDerivedInfinityCategoryOfClosedMapComparisonBijectivityStrictRealizationW838",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonBijectivityStrictRealizationW838",
      "comparisonBijectivityStrictRealizationLeftCalculusInputNamesW838",
      "comparisonBijectivityStrictRealizationLeftCalculusInputNamesW838_count",
      "comparisonBijectivityStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW838",
      "comparisonBijectivityStrictRealizationLeftCalculusStableRouteRequiredFieldNamesW838_count",
      "comparisonBijectivityStrictRealizationLeftCalculusExpandedRequiredFieldNamesW838",
      "comparisonBijectivityStrictRealizationLeftCalculusExpandedRequiredFieldNamesW838_count"]
  comparisonResult :=
    "proved: W821 and W831 supply the universal left-right comparison\
      isomorphism used by W837"
  leftCalculusResult :=
    "proved: W735 exact inputs plus W783 strict realization data feed W837\
      direct left calculus without a separate comparison function"
  derivedInputs :=
    ["universal IsIso for every MetrizableLCA left-right homology comparison"]
  remainingInputs :=
    Dbounded.comparisonBijectivityStrictRealizationLeftCalculusExpandedRequiredFieldNamesW838
  productSuccessClaimed := false

theorem currentW838ComparisonBijectivityStrictRealizationLeftCalculusRoute_productSuccess :
    (let state :=
        currentMetrizableComparisonBijectivityStrictRealizationLeftCalculusRouteStateW838;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
