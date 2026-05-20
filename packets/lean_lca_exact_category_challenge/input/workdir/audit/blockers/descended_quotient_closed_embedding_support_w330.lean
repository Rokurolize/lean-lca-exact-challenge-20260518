import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Topology.Maps.Basic

/-!
W330: descended quotient closed-embedding support.

This file attacks the W327 descended coequalizer-quotient frontier.  It proves
the algebraic injectivity step for the descended quotient map from the exact
preimage of the target cokernel relation subgroup.  The remaining topological
range/closed-map input is recorded as a typed boundary.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace MetrizableLCA

universe u

/--
The descended map between cokernel quotient presentations is injective when the
target relation subgroup has exact preimage along the component map.
-/
theorem coequalizerMap_descended_injective_of_relation_preimage_exact
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _))
    (hcompat :
      quotientMap B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
        iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _))
    (hpre :
      ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
        b ∈ cokernelSubgroup (f - g)) :
    Function.Injective (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) := by
  intro x y hxy
  rcases quotientMap_surjective B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) x with ⟨b, rfl⟩
  rcases quotientMap_surjective B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) y with ⟨c, rfl⟩
  have hb :
      descended
          (quotientMap B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) b) =
        quotientMap B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _) (iB b) := by
    exact congrArg (fun q : B ⟶ quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) => q b) hcompat
  have hc :
      descended
          (quotientMap B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) c) =
        quotientMap B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _) (iB c) := by
    exact congrArg (fun q : B ⟶ quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) => q c) hcompat
  have htarget :
      ((iB b : B') : B' ⧸ cokernelSubgroup (f' - g')) =
        ((iB c : B') : B' ⧸ cokernelSubgroup (f' - g')) := by
    simpa [quotientMap_apply] using hb.symm.trans (hxy.trans hc)
  have htarget_sub :
      ((iB (b - c) : B') : B' ⧸ cokernelSubgroup (f' - g')) = 0 := by
    have hsub :
        ((iB b : B') : B' ⧸ cokernelSubgroup (f' - g')) -
            ((iB c : B') : B' ⧸ cokernelSubgroup (f' - g')) = 0 :=
      sub_eq_zero.mpr htarget
    simpa [map_sub] using hsub
  have htarget_mem : iB (b - c) ∈ cokernelSubgroup (f' - g') := by
    exact (QuotientAddGroup.eq_zero_iff (iB (b - c))).mp htarget_sub
  have hsource_mem : b - c ∈ cokernelSubgroup (f - g) :=
    (hpre (b - c)).mp htarget_mem
  exact QuotientAddGroup.eq_iff_sub_mem.mpr hsource_mem

/--
Typed topological boundary left after the injectivity calculation: a continuous
descended quotient map becomes a closed embedding once the closed-map/range
input is supplied.
-/
theorem coequalizerMap_isClosedEmbedding_of_descended_closedMap
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _))
    (hinj : Function.Injective (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)))
    (hclosedMap : IsClosedMap (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _))) :
    IsClosedEmbedding (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap descended.hom.continuous hinj hclosedMap

/--
Machine-readable W330 state.  The useful checked contribution is the injectivity
datum from relation-preimage exactness; closed range remains a separate input.
-/
structure DescendedQuotientClosedEmbeddingFrontierState : Type where
  seed : String
  checkedFacts : List String
  quotientEqualityTools : List String
  closedMapTools : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentDescendedQuotientClosedEmbeddingFrontierState :
    DescendedQuotientClosedEmbeddingFrontierState where
  seed := "3be386c6e85079b9a03c2c09"
  checkedFacts :=
    ["MetrizableLCA.coequalizerMap_descended_injective_of_relation_preimage_exact",
      "MetrizableLCA.coequalizerMap_isClosedEmbedding_of_descended_closedMap"]
  quotientEqualityTools :=
    ["MetrizableLCA.quotientMap_surjective",
      "MetrizableLCA.quotientMap_apply",
      "QuotientAddGroup.eq_zero_iff",
      "QuotientAddGroup.eq_iff_sub_mem"]
  closedMapTools :=
    ["Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap",
      "IsClosedMap.isClosed_range",
      "IsClosedEmbedding.isClosedMap"]
  remainingInputs :=
    ["prove MetrizableLCA.coequalizerMap_relation_preimage_exact_of_component_closedEmbedding from component closed embeddings and the two commuting squares",
      "prove MetrizableLCA.coequalizerMap_descended_range_closed_of_component_closedEmbedding or equivalently an IsClosedMap input for the descended quotient map",
      "assemble MetrizableLCA.coequalizerMap_isClosedEmbedding_of_component_closedEmbedding using the checked injectivity datum and the closed-map input"]
  productSuccessClaimed := false

theorem currentDescendedQuotientClosedEmbeddingFrontierState_productSuccess :
    currentDescendedQuotientClosedEmbeddingFrontierState.productSuccessClaimed = false := rfl

def descendedQuotientClosedEmbeddingSupportDeclarationNames : List String :=
  ["MetrizableLCA.coequalizerMap_descended_injective_of_relation_preimage_exact",
    "MetrizableLCA.coequalizerMap_isClosedEmbedding_of_descended_closedMap",
    "DescendedQuotientClosedEmbeddingFrontierState",
    "currentDescendedQuotientClosedEmbeddingFrontierState",
    "currentDescendedQuotientClosedEmbeddingFrontierState_productSuccess"]

theorem descendedQuotientClosedEmbeddingSupportDeclarationNames_count :
    descendedQuotientClosedEmbeddingSupportDeclarationNames.length = 5 := rfl

section Checks

#check MetrizableLCA.coequalizerMap_descended_injective_of_relation_preimage_exact
#check MetrizableLCA.coequalizerMap_isClosedEmbedding_of_descended_closedMap
#check DescendedQuotientClosedEmbeddingFrontierState
#check currentDescendedQuotientClosedEmbeddingFrontierState
#check currentDescendedQuotientClosedEmbeddingFrontierState_productSuccess
#check descendedQuotientClosedEmbeddingSupportDeclarationNames
#check descendedQuotientClosedEmbeddingSupportDeclarationNames_count
#check MetrizableLCA.quotientMap_surjective
#check MetrizableLCA.quotientMap_apply
#check QuotientAddGroup.eq_zero_iff
#check QuotientAddGroup.eq_iff_sub_mem
#check Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
#check IsClosedMap.isClosed_range
#check IsClosedEmbedding.isClosedMap

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
