import LeanLCAExactChallenge.Derived.BranchLocalizedExactInputsLeftCalculusRoute
import LeanLCAExactChallenge.Derived.IsoClosureHomologyDetectionTerminalProductRoute

/-!
W837 routes W809 strict triangleh realization data into the W836
branch-localized exact-inputs left-calculus route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/--
W837 closed-map data converted to W836 data by deriving W651 through W812
homology detection.
-/
noncomputable def exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedMapBranchLocalizedExactInputsLeftCalculusDataW836 where
  exactInputs := data.exactInputs
  isoClosureRealization :=
    isoClosureRealizationOfStrictRealizationHomologyDetectionW812
      (homologyDetectionOfClosedMapExactInputsW812 data.comparisonIso
        data.exactInputs)
      data.trianglehRealization

/--
W837 closed-embedding data converted to W836 data by deriving W651 through
W812 homology detection.
-/
noncomputable def exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedEmbeddingBranchLocalizedExactInputsLeftCalculusDataW836
    where
  exactInputs := data.exactInputs
  isoClosureRealization :=
    isoClosureRealizationOfStrictRealizationHomologyDetectionW812
      (homologyDetectionOfClosedEmbeddingExactInputsW812 data.comparisonIso
        data.exactInputs)
      data.trianglehRealization

/-- W837 closed-map data converted to W835 data through W836. -/
noncomputable def exactInputsIsoClosureDataOfClosedMapStrictRealizationW837
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedMapExactInputsIsoClosureLeftCalculusDataW835 :=
  exactInputsLeftCalculusDataOfClosedMapBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837 data)

/-- W837 closed-embedding data converted to W835 data through W836. -/
noncomputable def exactInputsIsoClosureDataOfClosedEmbeddingStrictRealizationW837
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableClosedEmbeddingExactInputsIsoClosureLeftCalculusDataW835 :=
  exactInputsLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837 data)

/-- W837 closed-map data converted to W834 data through W836. -/
noncomputable def isoClosureLeftCalculusDataOfClosedMapStrictRealizationW837
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 :=
  isoClosureLeftCalculusDataOfClosedMapBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837 data)

/-- W837 closed-embedding data converted to W834 data through W836. -/
noncomputable def isoClosureLeftCalculusDataOfClosedEmbeddingStrictRealizationW837
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableIsoClosureRealizationLeftCalculusDataW834 :=
  isoClosureLeftCalculusDataOfClosedEmbeddingBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837 data)

/-- W837 derives the W785 target ExactAt payload from closed-map strict data. -/
noncomputable def targetExactAtPayloadOfClosedMapStrictRealizationW837
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedMapBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837 data)

/-- W837 derives the W785 target ExactAt payload from closed-embedding strict data. -/
noncomputable def targetExactAtPayloadOfClosedEmbeddingStrictRealizationW837
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    MetrizableExactAcyclicHomotopyObjectTargetExactAtPayloadW785 :=
  targetExactAtPayloadOfClosedEmbeddingBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837 data)

/-- W837 proves direct bounded left calculus from closed-map W809 data. -/
theorem directBoundedLeftCalculusOfClosedMapStrictRealizationW837
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837 data)

/-- W837 proves direct bounded left calculus from closed-embedding W809 data. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationW837
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837 data)

/-- W837 stable route using closed-map strict-realization data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapStrictRealizationW837
    (data : MetrizableClosedMapStrictRealizationTerminalBranchDataW809)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedMapStrictRealizationW837 data
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
        directBoundedLeftCalculusOfClosedMapStrictRealizationW837 data
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
  exact boundedDerivedInfinityCategoryOfClosedMapBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837 data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W837 stable route using closed-embedding strict-realization data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationW837
    (data : MetrizableClosedEmbeddingStrictRealizationTerminalBranchDataW809)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationW837 data
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
        directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationW837 data
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
  exact boundedDerivedInfinityCategoryOfClosedEmbeddingBranchLocalizedW836
    (exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837 data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W837 direct-left-calculus inputs after deriving W836's W651 field through W812. -/
def strictRealizationLeftCalculusInputNamesW837 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W783 exact-acyclic homotopy-object strict triangleh realization data"]

/-- W837 uses three concrete inputs for direct left calculus. -/
theorem strictRealizationLeftCalculusInputNamesW837_count :
    Dbounded.strictRealizationLeftCalculusInputNamesW837.length =
      3 :=
  rfl

/-- W837 stable route requirements when W809 strict data are bundled. -/
def strictRealizationLeftCalculusStableRouteRequiredFieldNamesW837 :
    List String :=
  ["closed-map or closed-embedding W809 strict-realization branch data",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- W837 keeps the stable route to five bundled requirements. -/
theorem strictRealizationLeftCalculusStableRouteRequiredFieldNamesW837_count :
    Dbounded.strictRealizationLeftCalculusStableRouteRequiredFieldNamesW837.length =
      5 :=
  rfl

/-- Expanded W837 requirements, showing the current concrete route obligations. -/
def strictRealizationLeftCalculusExpandedRequiredFieldNamesW837 :
    List String :=
  Dbounded.strictRealizationLeftCalculusInputNamesW837 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

/-- The W837 expanded stable route has seven concrete requirements. -/
theorem strictRealizationLeftCalculusExpandedRequiredFieldNamesW837_count :
    Dbounded.strictRealizationLeftCalculusExpandedRequiredFieldNamesW837.length =
      7 :=
  rfl

/-- Current checked W837 state for strict-realization left calculus. -/
structure MetrizableStrictRealizationLeftCalculusRouteStateW837 :
    Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W837 state. -/
def currentMetrizableStrictRealizationLeftCalculusRouteStateW837 :
    Dbounded.MetrizableStrictRealizationLeftCalculusRouteStateW837 where
  seed := "w837-strict-realization-left-calculus-route"
  declarations :=
    ["exactInputsLeftCalculusDataOfClosedMapStrictRealizationW837",
      "exactInputsLeftCalculusDataOfClosedEmbeddingStrictRealizationW837",
      "exactInputsIsoClosureDataOfClosedMapStrictRealizationW837",
      "exactInputsIsoClosureDataOfClosedEmbeddingStrictRealizationW837",
      "isoClosureLeftCalculusDataOfClosedMapStrictRealizationW837",
      "isoClosureLeftCalculusDataOfClosedEmbeddingStrictRealizationW837",
      "targetExactAtPayloadOfClosedMapStrictRealizationW837",
      "targetExactAtPayloadOfClosedEmbeddingStrictRealizationW837",
      "directBoundedLeftCalculusOfClosedMapStrictRealizationW837",
      "directBoundedLeftCalculusOfClosedEmbeddingStrictRealizationW837",
      "boundedDerivedInfinityCategoryOfClosedMapStrictRealizationW837",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingStrictRealizationW837",
      "strictRealizationLeftCalculusInputNamesW837",
      "strictRealizationLeftCalculusInputNamesW837_count",
      "strictRealizationLeftCalculusStableRouteRequiredFieldNamesW837",
      "strictRealizationLeftCalculusStableRouteRequiredFieldNamesW837_count",
      "strictRealizationLeftCalculusExpandedRequiredFieldNamesW837",
      "strictRealizationLeftCalculusExpandedRequiredFieldNamesW837_count"]
  leftCalculusResult :=
    "proved: W809 data supplies W836 branch-localized exact-inputs left calculus"
  replacedInputs :=
    ["W651 exact-acyclic iso-closure strict realization data"]
  remainingInputs :=
    Dbounded.strictRealizationLeftCalculusExpandedRequiredFieldNamesW837
  productSuccessClaimed := false

theorem currentMetrizableStrictRealizationLeftCalculusRouteStateW837_productSuccess :
    (let state :=
        Dbounded.currentMetrizableStrictRealizationLeftCalculusRouteStateW837;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
