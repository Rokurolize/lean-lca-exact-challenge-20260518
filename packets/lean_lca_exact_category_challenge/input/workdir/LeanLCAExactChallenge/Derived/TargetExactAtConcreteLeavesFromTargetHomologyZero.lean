import LeanLCAExactChallenge.Derived.TargetExactAtConcreteLeavesFromClosednessBranch
import LeanLCAExactChallenge.Derived.TargetHomologyZeroStrictRealizationLeftCalculusRoute
import LeanLCAExactChallenge.Derived.RouteDataProviderFromComparisonBijectivity

/-!
W862 feeds the W861 concrete-leaves target-ExactAt route from W839 target
homology-zero branch data.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/--
W862 closed-map data: W839 supplies the W735 branch record and W785 payload;
W855 turns the W735 record into W733 concrete leaves.
-/
noncomputable def concreteLeavesTargetExactAtDataOfClosedMapTargetHomologyZeroW862
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861
    where
  concreteLeaves := closedMapConcreteLeavesOfComparisonBijectivityW855
    data.exactInputs
  targetExactAtPayload := targetExactAtPayloadOfClosedMapTargetHomologyZeroW839
    data

/--
W862 closed-embedding data: W839 supplies the W735 branch record and W785
payload; W855 turns the W735 record into W733 concrete leaves.
-/
noncomputable def
    concreteLeavesTargetExactAtDataOfClosedEmbeddingTargetHomologyZeroW862
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    MetrizableConcreteLeavesTargetExactAtLeftCalculusDataW861
    where
  concreteLeaves := closedEmbeddingConcreteLeavesOfComparisonBijectivityW855
    data.exactInputs
  targetExactAtPayload :=
    targetExactAtPayloadOfClosedEmbeddingTargetHomologyZeroW839 data

/-- W862 closed-map direct bounded left calculus through W861. -/
theorem directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfConcreteLeavesTargetExactAtW861
    (concreteLeavesTargetExactAtDataOfClosedMapTargetHomologyZeroW862 data)

/-- W862 closed-embedding direct bounded left calculus through W861. -/
theorem
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfConcreteLeavesTargetExactAtW861
    (concreteLeavesTargetExactAtDataOfClosedEmbeddingTargetHomologyZeroW862
      data)

/-- W862 closed-map stable package after W839 supplies the W861 direct data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroConcreteLeavesW862
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
          data
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
        directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
          data
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
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862
      data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/--
W862 closed-embedding stable package after W839 supplies the W861 direct data.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
          data
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
        directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
          data
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
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862
      data
  exact Dbounded.boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    finiteLimits finiteColimits pretriangulated triangulated

/-- W862 direct-left-calculus inputs after W839 supplies W733 and W785. -/
def targetHomologyZeroConcreteLeavesTargetExactAtInputNamesW862 :
    List String :=
  ["W839 closed-map or closed-embedding target homology-zero data carrying W735 \
      exact inputs and W790 payload data"]

theorem targetHomologyZeroConcreteLeavesTargetExactAtInputNamesW862_count :
    targetHomologyZeroConcreteLeavesTargetExactAtInputNamesW862.length = 1 :=
  rfl

/-- W862 expanded stable-route requirements. -/
def targetHomologyZeroConcreteLeavesTargetExactAtStableRouteInputNamesW862 :
    List String :=
  targetHomologyZeroConcreteLeavesTargetExactAtInputNamesW862 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

theorem targetHomologyZeroConcreteLeavesTargetExactAtStableRouteInputNamesW862_count :
    targetHomologyZeroConcreteLeavesTargetExactAtStableRouteInputNamesW862.length =
      5 :=
  rfl

/-- Current checked W862 state. -/
structure MetrizableTargetHomologyZeroConcreteLeavesTargetExactAtRouteStateW862 :
    Type where
  seed : String
  declarations : List String
  closedMapResult : String
  closedEmbeddingResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetHomologyZeroConcreteLeavesTargetExactAtRouteStateW862 :
    MetrizableTargetHomologyZeroConcreteLeavesTargetExactAtRouteStateW862
    where
  seed := "w862-target-homology-zero-to-concrete-leaves-target-exact-at"
  declarations :=
    ["concreteLeavesTargetExactAtDataOfClosedMapTargetHomologyZeroW862",
      "concreteLeavesTargetExactAtDataOfClosedEmbeddingTargetHomologyZeroW862",
      "directBoundedLeftCalculusOfClosedMapTargetHomologyZeroConcreteLeavesW862",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862",
      "boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroConcreteLeavesW862",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroConcreteLeavesW862",
      "targetHomologyZeroConcreteLeavesTargetExactAtInputNamesW862",
      "targetHomologyZeroConcreteLeavesTargetExactAtInputNamesW862_count",
      "targetHomologyZeroConcreteLeavesTargetExactAtStableRouteInputNamesW862",
      "targetHomologyZeroConcreteLeavesTargetExactAtStableRouteInputNamesW862_count"]
  closedMapResult :=
    "proved: W839 closed-map data supplies W861 concrete leaves and target ExactAt payload"
  closedEmbeddingResult :=
    "proved: W839 closed-embedding data supplies W861 concrete leaves and target ExactAt payload"
  replacedInputs :=
    ["separate W733 concrete leaves input",
      "separate W785 target ExactAt payload input"]
  remainingInputs :=
    targetHomologyZeroConcreteLeavesTargetExactAtStableRouteInputNamesW862
  productSuccessClaimed := false

theorem currentW862TargetHomologyZeroConcreteLeavesTargetExactAtRoute_productSuccess :
    (let state :=
        currentMetrizableTargetHomologyZeroConcreteLeavesTargetExactAtRouteStateW862;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
