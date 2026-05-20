import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W349: relation-preimage pullback condition support for the left LCA frontier.

This file keeps the v368 boundary narrow.  It does not claim that component
closed embedding proves the relation pullback condition.  Instead it checks two
usable reductions:

* under the commuting squares, the subgroup pullback equality is equivalent to
  the reverse elementwise relation-preimage condition isolated by W340/W343;
* the same equality can be stated definitionally as a closed-range preimage
  equality, since `cokernelSubgroup` is a topological closure of the algebraic
  range.

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

/-- W349-local spelling of W343's target relation pullback equality. -/
abbrev relationPreimagePullbackConditionW349
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W349-local spelling of the reverse elementwise relation-preimage condition. -/
abbrev relationPreimageReverseConditionW349
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
    b ∈ cokernelSubgroup (f - g)

/--
The commuting squares give the forward inclusion needed to compare the two
closed relation subgroups.
-/
theorem relationPreimageForwardOfSquaresW349
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

/-- The pullback equality immediately gives the reverse elementwise condition. -/
theorem relationPreimageReverseOfPullbackConditionW349
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW349 f g f' g' iB) :
    relationPreimageReverseConditionW349 f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) := hb
  simpa [relationPreimagePullbackConditionW349] using (hpullback ▸ hbcomap)

/--
Under the square equations, the reverse elementwise condition is exactly what is
needed to upgrade the forward inclusion to the full subgroup pullback equality.
-/
theorem relationPreimagePullbackConditionOfReverseW349
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationPreimageReverseConditionW349 f g f' g' iB) :
    relationPreimagePullbackConditionW349 f g f' g' iB := by
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · intro b hb
    exact relationPreimageForwardOfSquaresW349 iA iB hsquare_left hsquare_right b hb

/--
The v368 pullback condition is equivalent to the W340 reverse condition once the
two component squares are available.
-/
theorem relationPreimagePullbackConditionIffReverseW349
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    relationPreimagePullbackConditionW349 f g f' g' iB ↔
      relationPreimageReverseConditionW349 f g f' g' iB := by
  constructor
  · exact relationPreimageReverseOfPullbackConditionW349 iB
  · exact relationPreimagePullbackConditionOfReverseW349 iA iB hsquare_left hsquare_right

/--
Closed-range spelling of the same condition.  This is definitionally equivalent
to `relationPreimagePullbackConditionW349`.
-/
abbrev relationClosedRangePreimageEqualityW349
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A)).topologicalClosure

theorem relationPreimagePullbackConditionIffClosedRangeEqualityW349
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B') :
    relationPreimagePullbackConditionW349 f g f' g' iB ↔
      relationClosedRangePreimageEqualityW349 f g f' g' iB := by
  rfl

/--
Boundary package: component closed embedding is recorded as context, while the
checked mathematical reduction identifies the remaining algebraic input.
-/
structure RelationPullbackConditionBoundaryW349
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iA : A ⟶ A') (iB : B ⟶ B') : Prop where
  square_left : f ≫ iB = iA ≫ f'
  square_right : g ≫ iB = iA ≫ g'
  component_closedEmbedding : IsClosedEmbedding (iB : B → B')
  reverse_relation_preimage : relationPreimageReverseConditionW349 f g f' g' iB

theorem RelationPullbackConditionBoundaryW349.pullback_condition
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : RelationPullbackConditionBoundaryW349 A B A' B' f g f' g' iA iB) :
    relationPreimagePullbackConditionW349 f g f' g' iB :=
  relationPreimagePullbackConditionOfReverseW349
    iA iB h.square_left h.square_right h.reverse_relation_preimage

theorem RelationPullbackConditionBoundaryW349.iff_reverse
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    (h : RelationPullbackConditionBoundaryW349 A B A' B' f g f' g' iA iB) :
    relationPreimagePullbackConditionW349 f g f' g' iB ↔
      relationPreimageReverseConditionW349 f g f' g' iB :=
  relationPreimagePullbackConditionIffReverseW349 iA iB h.square_left h.square_right

/-- Machine-readable v368/W349 state. -/
structure RelationPullbackConditionV368SupportStateW349 : Type where
  seed : String
  checkedFacts : List String
  reductionBoundary : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentRelationPullbackConditionV368SupportStateW349 :
    RelationPullbackConditionV368SupportStateW349 where
  seed := "1c3c9c05677903ca"
  checkedFacts :=
    ["MetrizableLCA.relationPreimagePullbackConditionIffReverseW349",
      "MetrizableLCA.relationPreimagePullbackConditionOfReverseW349",
      "MetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW349",
      "MetrizableLCA.RelationPullbackConditionBoundaryW349.pullback_condition"]
  reductionBoundary :=
    "with square equations, the subgroup pullback equality is equivalent to the reverse relation-preimage condition"
  remainingInputs :=
    ["prove reverse relation-preimage from the actual target/source relation geometry",
      "or prove the equivalent closed-range preimage equality",
      "component closed embedding is recorded but not used as a sufficient standalone proof"]
  productSuccessClaimed := false

theorem currentRelationPullbackConditionV368SupportStateW349_productSuccess :
    currentRelationPullbackConditionV368SupportStateW349.productSuccessClaimed = false := rfl

def relationPullbackConditionV368SupportDeclarationNamesW349 : List String :=
  ["MetrizableLCA.relationPreimagePullbackConditionW349",
    "MetrizableLCA.relationPreimageReverseConditionW349",
    "MetrizableLCA.relationPreimageForwardOfSquaresW349",
    "MetrizableLCA.relationPreimageReverseOfPullbackConditionW349",
    "MetrizableLCA.relationPreimagePullbackConditionOfReverseW349",
    "MetrizableLCA.relationPreimagePullbackConditionIffReverseW349",
    "MetrizableLCA.relationClosedRangePreimageEqualityW349",
    "MetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW349",
    "MetrizableLCA.RelationPullbackConditionBoundaryW349",
    "MetrizableLCA.RelationPullbackConditionBoundaryW349.pullback_condition",
    "MetrizableLCA.RelationPullbackConditionBoundaryW349.iff_reverse",
    "MetrizableLCA.currentRelationPullbackConditionV368SupportStateW349",
    "MetrizableLCA.currentRelationPullbackConditionV368SupportStateW349_productSuccess"]

theorem relationPullbackConditionV368SupportDeclarationNamesW349_count :
    relationPullbackConditionV368SupportDeclarationNamesW349.length = 13 := rfl

section Checks

#check MetrizableLCA.relationPreimagePullbackConditionW349
#check MetrizableLCA.relationPreimageReverseConditionW349
#check MetrizableLCA.relationPreimageForwardOfSquaresW349
#check MetrizableLCA.relationPreimageReverseOfPullbackConditionW349
#check MetrizableLCA.relationPreimagePullbackConditionOfReverseW349
#check MetrizableLCA.relationPreimagePullbackConditionIffReverseW349
#check MetrizableLCA.relationClosedRangePreimageEqualityW349
#check MetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW349
#check MetrizableLCA.RelationPullbackConditionBoundaryW349
#check MetrizableLCA.RelationPullbackConditionBoundaryW349.pullback_condition
#check MetrizableLCA.RelationPullbackConditionBoundaryW349.iff_reverse
#check MetrizableLCA.currentRelationPullbackConditionV368SupportStateW349
#check MetrizableLCA.currentRelationPullbackConditionV368SupportStateW349_productSuccess
#check MetrizableLCA.relationPullbackConditionV368SupportDeclarationNamesW349
#check MetrizableLCA.relationPullbackConditionV368SupportDeclarationNamesW349_count
#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.map_mem_cokernelSubgroup

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
