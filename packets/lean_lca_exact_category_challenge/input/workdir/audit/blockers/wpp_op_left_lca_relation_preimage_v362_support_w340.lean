import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W340: v362 left LCA relation-preimage and descended closed-map support.

This file attacks the two concrete inputs left by W335/W337:

* exact preimage of the target cokernel relation subgroup along the component map;
* `IsClosedMap` for the descended quotient/coequalizer map.

The checked contribution is deliberately narrow.  The square equations always
give the forward relation-preimage direction after taking closures.  The reverse
direction is not a consequence of component closed embedding alone; it requires
an algebraic pullback/exactness input saying that no extra target relation class
from `A'` meets the image of `B` except those coming from `A`.
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
The commuting squares give the easy half of relation-preimage exactness:
if `b` is in the source cokernel relation subgroup, then `iB b` is in the
target cokernel relation subgroup.
-/
theorem coequalizerMap_relation_preimage_forward_of_squares
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    ∀ b : B, b ∈ cokernelSubgroup (f - g) →
      iB b ∈ cokernelSubgroup (f' - g') := by
  intro b hb
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g'))
  have hrange_le :
      AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A) ≤
        targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ cokernelSubgroup (f' - g')
    have hleft : iB (f a) = f' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_left
    have hright : iB (g a) = g' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_right
    have hval : iB ((f - g) a) = (f' - g') (iA a) := by
      calc
        iB ((f - g) a) = iB (f a - g a) := by rfl
        _ = iB (f a) - iB (g a) := by
          exact map_sub iB.hom.toAddMonoidHom (f a) (g a)
        _ = f' (iA a) - g' (iA a) := by rw [hleft, hright]
        _ = (f' - g') (iA a) := by rfl
    rw [hval]
    exact map_mem_cokernelSubgroup (f' - g') (iA a)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed ((fun b : B => iB b) ⁻¹' (cokernelSubgroup (f' - g') : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  have hclosure_le : cokernelSubgroup (f - g) ≤ targetPreimage :=
    AddSubgroup.topologicalClosure_minimal
      (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A))
      hrange_le htargetPreimage_closed
  exact hclosure_le hb

/--
The exact relation-preimage statement is therefore reduced to the reverse
preimage inclusion.  This is the smallest algebraic/topological missing input
found in the v362 route.
-/
theorem coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse :
      ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
        b ∈ cokernelSubgroup (f - g)) :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
      b ∈ cokernelSubgroup (f - g) := by
  intro b
  exact ⟨hreverse b,
    coequalizerMap_relation_preimage_forward_of_squares iA iB hsquare_left hsquare_right b⟩

/--
The v362 quotient-presentation boundary, separated into algebraic preimage,
topological closed-map, and quotient-compatibility fields.
-/
structure CoequalizerRelationPreimageClosedMapInputs
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iA : A ⟶ A') (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  square_left : f ≫ iB = iA ≫ f'
  square_right : g ≫ iB = iA ≫ g'
  component_closedEmbedding : IsClosedEmbedding (iB : B → B')
  quotient_compat :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)
  relation_preimage_reverse :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
      b ∈ cokernelSubgroup (f - g)
  descended_closedMap : IsClosedMap (descended :
    quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    quotientObj B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))

theorem CoequalizerRelationPreimageClosedMapInputs.relation_preimage_exact
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h :
      CoequalizerRelationPreimageClosedMapInputs A B A' B' f g f' g' iA iB descended) :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
      b ∈ cokernelSubgroup (f - g) :=
  coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage
    iA iB h.square_left h.square_right h.relation_preimage_reverse

theorem CoequalizerRelationPreimageClosedMapInputs.descended_injective
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h :
      CoequalizerRelationPreimageClosedMapInputs A B A' B' f g f' g' iA iB descended) :
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
        (AddSubgroup.isClosed_topologicalClosure _) => q b) h.quotient_compat
  have hc :
      descended
          (quotientMap B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) c) =
        quotientMap B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _) (iB c) := by
    exact congrArg (fun q : B ⟶ quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) => q c) h.quotient_compat
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
    (h.relation_preimage_exact (b - c)).mp htarget_mem
  exact QuotientAddGroup.eq_iff_sub_mem.mpr hsource_mem

theorem CoequalizerRelationPreimageClosedMapInputs.descended_closedEmbedding
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h :
      CoequalizerRelationPreimageClosedMapInputs A B A' B' f g f' g' iA iB descended) :
    IsClosedEmbedding (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    descended.hom.continuous h.descended_injective h.descended_closedMap

theorem CoequalizerRelationPreimageClosedMapInputs.descended_fields
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h :
      CoequalizerRelationPreimageClosedMapInputs A B A' B' f g f' g' iA iB descended) :
    Function.Injective (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) ∧
      IsInducing (descended :
        quotientObj B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) →
        quotientObj B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _)) ∧
        IsClosed (Set.range (descended :
          quotientObj B (cokernelSubgroup (f - g))
            (AddSubgroup.isClosed_topologicalClosure _) →
          quotientObj B' (cokernelSubgroup (f' - g'))
            (AddSubgroup.isClosed_topologicalClosure _))) := by
  have hclosedEmbedding := h.descended_closedEmbedding
  exact ⟨h.descended_injective, hclosedEmbedding.toIsEmbedding.toIsInducing,
    hclosedEmbedding.isClosed_range⟩

/-- Machine-readable v362 state. -/
structure LeftLcaRelationPreimageV362SupportState : Type where
  seed : String
  selectedRoute : String
  checkedFacts : List String
  separatedInputs : List String
  smallestMissingLocalTheorem : String
  productSuccessClaimed : Bool

def currentLeftLcaRelationPreimageV362SupportState :
    LeftLcaRelationPreimageV362SupportState where
  seed := "e05deca9cdb78f01"
  selectedRoute := "forward-relation-preimage-plus-boundary-for-reverse-preimage-and-closed-map"
  checkedFacts :=
    ["MetrizableLCA.coequalizerMap_relation_preimage_forward_of_squares",
      "MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage",
      "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.relation_preimage_exact",
      "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_injective",
      "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_closedEmbedding",
      "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_fields"]
  separatedInputs :=
    ["algebraic: relation_preimage_reverse, equivalent to pulling the target closed relation subgroup back to the source relation subgroup",
      "topological: descended_closedMap for the quotient map",
      "compatibility: quotient_compat for the descended quotient presentation",
      "component topology: component_closedEmbedding is recorded but does not prove the reverse relation-preimage inclusion by itself"]
  smallestMissingLocalTheorem :=
    "If x : B and iB x lies in closure(range (f' - g')), prove x lies in closure(range (f - g)); closed embedding plus square equations only gives the opposite implication without an additional algebraic pullback condition on target relations."
  productSuccessClaimed := false

theorem currentLeftLcaRelationPreimageV362SupportState_productSuccess :
    currentLeftLcaRelationPreimageV362SupportState.productSuccessClaimed = false := rfl

def leftLcaRelationPreimageV362SupportDeclarationNames : List String :=
  ["MetrizableLCA.coequalizerMap_relation_preimage_forward_of_squares",
    "MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage",
    "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs",
    "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.relation_preimage_exact",
    "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_injective",
    "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_closedEmbedding",
    "MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_fields",
    "MetrizableLCA.LeftLcaRelationPreimageV362SupportState",
    "MetrizableLCA.currentLeftLcaRelationPreimageV362SupportState",
    "MetrizableLCA.currentLeftLcaRelationPreimageV362SupportState_productSuccess"]

theorem leftLcaRelationPreimageV362SupportDeclarationNames_count :
    leftLcaRelationPreimageV362SupportDeclarationNames.length = 10 := rfl

section Checks

#check MetrizableLCA.coequalizerMap_relation_preimage_forward_of_squares
#check MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage
#check MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs
#check MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.relation_preimage_exact
#check MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_injective
#check MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_closedEmbedding
#check MetrizableLCA.CoequalizerRelationPreimageClosedMapInputs.descended_fields
#check MetrizableLCA.currentLeftLcaRelationPreimageV362SupportState
#check MetrizableLCA.currentLeftLcaRelationPreimageV362SupportState_productSuccess
#check MetrizableLCA.leftLcaRelationPreimageV362SupportDeclarationNames
#check MetrizableLCA.leftLcaRelationPreimageV362SupportDeclarationNames_count
#check MetrizableLCA.quotientMap_surjective
#check MetrizableLCA.quotientMap_apply
#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.map_mem_cokernelSubgroup
#check AddSubgroup.topologicalClosure_minimal
#check Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
#check IsClosedMap.isClosed_range

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
