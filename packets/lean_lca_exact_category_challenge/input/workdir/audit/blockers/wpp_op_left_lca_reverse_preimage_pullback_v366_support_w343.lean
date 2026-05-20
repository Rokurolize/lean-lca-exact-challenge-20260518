import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W343: v366 reverse relation-preimage pullback support.

W340 proved the square-equation forward inclusion and isolated the reverse
relation-preimage inclusion as the smallest remaining input.  This standalone
file sharpens that input to an exact pullback condition for the target cokernel
relation subgroup along the component map `iB`.

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
The target cokernel relation subgroup pulls back exactly to the source cokernel
relation subgroup along the component map.
-/
abbrev relationPreimagePullbackCondition
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/--
The one-sided reverse relation-preimage condition left open by W340.
-/
abbrev relationPreimageReverseCondition
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
    b ∈ cokernelSubgroup (f - g)

/--
The pullback equality immediately supplies W340's reverse inclusion.
-/
theorem coequalizerMap_relation_preimage_reverse_of_pullback_condition
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackCondition f g f' g' iB) :
    relationPreimageReverseCondition f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) := hb
  simpa [relationPreimagePullbackCondition] using (hpullback ▸ hbcomap)

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
W340's exact relation-preimage bridge, included here because audit files are
checked as standalone Lean files rather than importable Lake modules.
-/
theorem coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationPreimageReverseCondition f g f' g' iB) :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
      b ∈ cokernelSubgroup (f - g) := by
  intro b
  exact ⟨hreverse b,
    coequalizerMap_relation_preimage_forward_of_squares iA iB hsquare_left hsquare_right b⟩

/--
Squares plus the target-relation pullback equality prove exact relation-preimage.
-/
theorem coequalizerMap_relation_preimage_exact_of_squares_and_pullback_condition
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hpullback : relationPreimagePullbackCondition f g f' g' iB) :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
      b ∈ cokernelSubgroup (f - g) :=
  coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage
    iA iB hsquare_left hsquare_right
    (coequalizerMap_relation_preimage_reverse_of_pullback_condition iB hpullback)

/--
The v366 input package: component closed embedding and square equations are
recorded, but the algebraic content needed for W340 is the target-relation
pullback condition.
-/
structure CoequalizerRelationPullbackInputs
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
  relation_pullback : relationPreimagePullbackCondition f g f' g' iB
  reverse_preimage : relationPreimageReverseCondition f g f' g' iB
  quotient_compat :
    quotientMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ descended =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)
  descended_closedMap : IsClosedMap (descended :
    quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    quotientObj B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))

theorem CoequalizerRelationPullbackInputs.reverse_of_pullback
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : CoequalizerRelationPullbackInputs A B A' B' f g f' g' iA iB descended) :
    relationPreimageReverseCondition f g f' g' iB :=
  coequalizerMap_relation_preimage_reverse_of_pullback_condition iB h.relation_pullback

theorem CoequalizerRelationPullbackInputs.relation_preimage_exact
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : CoequalizerRelationPullbackInputs A B A' B' f g f' g' iA iB descended) :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
      b ∈ cokernelSubgroup (f - g) :=
  coequalizerMap_relation_preimage_exact_of_squares_and_pullback_condition
    iA iB h.square_left h.square_right h.relation_pullback

/-- Machine-readable v366 state. -/
structure LeftLcaReversePreimagePullbackV366SupportState : Type where
  seed : String
  checkedFacts : List String
  minimalExtraHypothesis : String
  negativeBoundary : List String
  productSuccessClaimed : Bool

def currentLeftLcaReversePreimagePullbackV366SupportState :
    LeftLcaReversePreimagePullbackV366SupportState where
  seed := "6214e11fb7f8a8d6"
  checkedFacts :=
    ["MetrizableLCA.relationPreimagePullbackCondition",
      "MetrizableLCA.relationPreimageReverseCondition",
      "MetrizableLCA.coequalizerMap_relation_preimage_reverse_of_pullback_condition",
      "MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_pullback_condition",
      "MetrizableLCA.CoequalizerRelationPullbackInputs.reverse_of_pullback",
      "MetrizableLCA.CoequalizerRelationPullbackInputs.relation_preimage_exact"]
  minimalExtraHypothesis :=
    "AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) = cokernelSubgroup (f - g)"
  negativeBoundary :=
    ["component_closedEmbedding plus square equations is recorded but not used to prove the reverse inclusion",
      "the pullback equality is the minimal extra algebraic relation-preimage hypothesis exposed here"]
  productSuccessClaimed := false

theorem currentLeftLcaReversePreimagePullbackV366SupportState_productSuccess :
    currentLeftLcaReversePreimagePullbackV366SupportState.productSuccessClaimed = false := rfl

def leftLcaReversePreimagePullbackV366SupportDeclarationNames : List String :=
  ["MetrizableLCA.relationPreimagePullbackCondition",
    "MetrizableLCA.relationPreimageReverseCondition",
    "MetrizableLCA.coequalizerMap_relation_preimage_reverse_of_pullback_condition",
    "MetrizableLCA.coequalizerMap_relation_preimage_forward_of_squares",
    "MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage",
    "MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_pullback_condition",
    "MetrizableLCA.CoequalizerRelationPullbackInputs",
    "MetrizableLCA.CoequalizerRelationPullbackInputs.reverse_of_pullback",
    "MetrizableLCA.CoequalizerRelationPullbackInputs.relation_preimage_exact",
    "MetrizableLCA.currentLeftLcaReversePreimagePullbackV366SupportState",
    "MetrizableLCA.currentLeftLcaReversePreimagePullbackV366SupportState_productSuccess"]

theorem leftLcaReversePreimagePullbackV366SupportDeclarationNames_count :
    leftLcaReversePreimagePullbackV366SupportDeclarationNames.length = 11 := rfl

section Checks

#check MetrizableLCA.relationPreimagePullbackCondition
#check MetrizableLCA.relationPreimageReverseCondition
#check MetrizableLCA.coequalizerMap_relation_preimage_reverse_of_pullback_condition
#check MetrizableLCA.coequalizerMap_relation_preimage_forward_of_squares
#check MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_reverse_preimage
#check MetrizableLCA.coequalizerMap_relation_preimage_exact_of_squares_and_pullback_condition
#check MetrizableLCA.CoequalizerRelationPullbackInputs
#check MetrizableLCA.CoequalizerRelationPullbackInputs.reverse_of_pullback
#check MetrizableLCA.CoequalizerRelationPullbackInputs.relation_preimage_exact
#check MetrizableLCA.currentLeftLcaReversePreimagePullbackV366SupportState
#check MetrizableLCA.currentLeftLcaReversePreimagePullbackV366SupportState_productSuccess
#check MetrizableLCA.leftLcaReversePreimagePullbackV366SupportDeclarationNames
#check MetrizableLCA.leftLcaReversePreimagePullbackV366SupportDeclarationNames_count
#check MetrizableLCA.quotientObj
#check MetrizableLCA.quotientMap
#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.map_mem_cokernelSubgroup

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
