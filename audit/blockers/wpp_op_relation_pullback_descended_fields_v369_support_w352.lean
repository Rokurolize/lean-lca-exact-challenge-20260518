import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W352: relation-pullback descended-fields support.

This standalone audit file connects the W343/W349 relation-pullback equality to
the three descended quotient-map fields consumed by W342/W348.  The checked
route is intentionally explicit:

* square equations give the forward relation-preimage inclusion;
* the pullback equality gives the reverse inclusion;
* under the square equations, reverse inclusion is equivalent to the subgroup
  pullback equality and to the closed-range preimage spelling;
* adding quotient compatibility and a closed-map hypothesis for the descended
  quotient morphism yields injectivity, inducing topology, and closed range.

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

/-- W352-local spelling of the target relation pullback equality. -/
abbrev relationPreimagePullbackConditionW352
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W352-local spelling of W340's reverse elementwise relation-preimage condition. -/
abbrev relationPreimageReverseConditionW352
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
    b ∈ cokernelSubgroup (f - g)

/-- Closed-range/preimage spelling of the same target relation pullback equality. -/
abbrev relationClosedRangePreimageEqualityW352
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

/--
The square equations give the forward relation-preimage inclusion by taking the
closure of the algebraic range inclusion.
-/
theorem relationPreimageForwardOfSquaresW352
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

/-- The pullback equality immediately gives W340's reverse relation-preimage input. -/
theorem relationPreimageReverseOfPullbackConditionW352
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW352 f g f' g' iB) :
    relationPreimageReverseConditionW352 f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) := hb
  simpa [relationPreimagePullbackConditionW352] using (hpullback ▸ hbcomap)

/-- Reverse relation-preimage plus the square equations imply the full pullback equality. -/
theorem relationPreimagePullbackConditionOfReverseW352
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationPreimageReverseConditionW352 f g f' g' iB) :
    relationPreimagePullbackConditionW352 f g f' g' iB := by
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · intro b hb
    exact relationPreimageForwardOfSquaresW352 iA iB hsquare_left hsquare_right b hb

/-- Under square equations, the pullback equality is equivalent to the reverse condition. -/
theorem relationPreimagePullbackConditionIffReverseW352
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    relationPreimagePullbackConditionW352 f g f' g' iB ↔
      relationPreimageReverseConditionW352 f g f' g' iB := by
  constructor
  · exact relationPreimageReverseOfPullbackConditionW352 iB
  · exact relationPreimagePullbackConditionOfReverseW352 iA iB hsquare_left hsquare_right

/-- The pullback condition is definitionally the closed-range preimage equality. -/
theorem relationPreimagePullbackConditionIffClosedRangeEqualityW352
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B') :
    relationPreimagePullbackConditionW352 f g f' g' iB ↔
      relationClosedRangePreimageEqualityW352 f g f' g' iB := by
  rfl

/-- The three descended quotient fields consumed by W342/W348. -/
structure DescendedQuotientFieldsW352
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  injective : Function.Injective (descended :
    quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    quotientObj B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
  inducing : IsInducing (descended :
    quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    quotientObj B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
  closed_range : IsClosed (Set.range (descended :
    quotientObj B (cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    quotientObj B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)))

/--
Concrete W352 input package.  The mathematical relation input is the pullback
condition; the remaining topological input is the descended map being closed.
-/
structure RelationPullbackDescendedFieldsInputsW352
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iA : A ⟶ A') (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  square_left : f ≫ iB = iA ≫ f'
  square_right : g ≫ iB = iA ≫ g'
  relation_pullback : relationPreimagePullbackConditionW352 f g f' g' iB
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

theorem RelationPullbackDescendedFieldsInputsW352.reverse_preimage
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW352 A B A' B' f g f' g' iA iB descended) :
    relationPreimageReverseConditionW352 f g f' g' iB :=
  relationPreimageReverseOfPullbackConditionW352 iB h.relation_pullback

theorem RelationPullbackDescendedFieldsInputsW352.relation_preimage_exact
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW352 A B A' B' f g f' g' iA iB descended) :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
      b ∈ cokernelSubgroup (f - g) := by
  intro b
  exact ⟨h.reverse_preimage b,
    relationPreimageForwardOfSquaresW352 iA iB h.square_left h.square_right b⟩

theorem RelationPullbackDescendedFieldsInputsW352.descended_injective
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW352 A B A' B' f g f' g' iA iB descended) :
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

theorem RelationPullbackDescendedFieldsInputsW352.descended_closedEmbedding
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW352 A B A' B' f g f' g' iA iB descended) :
    IsClosedEmbedding (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    descended.hom.continuous h.descended_injective h.descended_closedMap

/--
Main W352 bridge: relation-pullback plus quotient compatibility and closed-map
input gives exactly the three descended fields consumed downstream.
-/
theorem RelationPullbackDescendedFieldsInputsW352.descended_fields
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW352 A B A' B' f g f' g' iA iB descended) :
    DescendedQuotientFieldsW352 f g f' g' descended := by
  have hclosedEmbedding := h.descended_closedEmbedding
  exact
    ⟨h.descended_injective, hclosedEmbedding.toIsEmbedding.toIsInducing,
      hclosedEmbedding.isClosed_range⟩

/-- Machine-readable W352 state. -/
structure RelationPullbackDescendedFieldsV369SupportStateW352 : Type where
  seed : String
  checkedFacts : List String
  packagedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentRelationPullbackDescendedFieldsV369SupportStateW352 :
    RelationPullbackDescendedFieldsV369SupportStateW352 where
  seed := "58dc46f38e5ca73da6aadb8eca58abac"
  checkedFacts :=
    ["MetrizableLCA.relationPreimagePullbackConditionIffReverseW352",
      "MetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW352",
      "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.reverse_preimage",
      "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.relation_preimage_exact",
      "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_injective",
      "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_closedEmbedding",
      "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_fields"]
  packagedInputs :=
    ["square equations for f/g and f'/g'",
      "relationPreimagePullbackConditionW352",
      "quotient compatibility for the descended quotient map",
      "IsClosedMap for the descended quotient map"]
  remainingInputs :=
    ["instantiate the package for the concrete WPP-op quotient/coequalizer descended map",
      "prove the concrete quotient compatibility equation",
      "prove the relation-pullback equality, or equivalently the reverse preimage/closed-range preimage equality",
      "prove the descended quotient map is closed"]
  productSuccessClaimed := false

theorem currentRelationPullbackDescendedFieldsV369SupportStateW352_productSuccess :
    currentRelationPullbackDescendedFieldsV369SupportStateW352.productSuccessClaimed = false := rfl

def relationPullbackDescendedFieldsV369SupportDeclarationNamesW352 : List String :=
  ["MetrizableLCA.relationPreimagePullbackConditionW352",
    "MetrizableLCA.relationPreimageReverseConditionW352",
    "MetrizableLCA.relationClosedRangePreimageEqualityW352",
    "MetrizableLCA.relationPreimageForwardOfSquaresW352",
    "MetrizableLCA.relationPreimageReverseOfPullbackConditionW352",
    "MetrizableLCA.relationPreimagePullbackConditionOfReverseW352",
    "MetrizableLCA.relationPreimagePullbackConditionIffReverseW352",
    "MetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW352",
    "MetrizableLCA.DescendedQuotientFieldsW352",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.reverse_preimage",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.relation_preimage_exact",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_injective",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_closedEmbedding",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_fields",
    "MetrizableLCA.currentRelationPullbackDescendedFieldsV369SupportStateW352",
    "MetrizableLCA.currentRelationPullbackDescendedFieldsV369SupportStateW352_productSuccess"]

theorem relationPullbackDescendedFieldsV369SupportDeclarationNamesW352_count :
    relationPullbackDescendedFieldsV369SupportDeclarationNamesW352.length = 17 := rfl

section Checks

#check MetrizableLCA.relationPreimagePullbackConditionW352
#check MetrizableLCA.relationPreimageReverseConditionW352
#check MetrizableLCA.relationClosedRangePreimageEqualityW352
#check MetrizableLCA.relationPreimageForwardOfSquaresW352
#check MetrizableLCA.relationPreimageReverseOfPullbackConditionW352
#check MetrizableLCA.relationPreimagePullbackConditionOfReverseW352
#check MetrizableLCA.relationPreimagePullbackConditionIffReverseW352
#check MetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW352
#check MetrizableLCA.DescendedQuotientFieldsW352
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW352
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.reverse_preimage
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.relation_preimage_exact
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_injective
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_closedEmbedding
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW352.descended_fields
#check MetrizableLCA.currentRelationPullbackDescendedFieldsV369SupportStateW352
#check MetrizableLCA.currentRelationPullbackDescendedFieldsV369SupportStateW352_productSuccess
#check MetrizableLCA.relationPullbackDescendedFieldsV369SupportDeclarationNamesW352
#check MetrizableLCA.relationPullbackDescendedFieldsV369SupportDeclarationNamesW352_count
#check MetrizableLCA.quotientObj
#check MetrizableLCA.quotientMap
#check MetrizableLCA.quotientMap_surjective
#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.map_mem_cokernelSubgroup
#check Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
