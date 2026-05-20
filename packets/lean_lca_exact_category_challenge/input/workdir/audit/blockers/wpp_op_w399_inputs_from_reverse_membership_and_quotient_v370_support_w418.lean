import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W418: W399 input assembly from reverse membership and quotient compatibility.

This standalone audit file combines the W415 reverse-membership route with the
W405 quotient-lift descended map.  The checked constructor specializes the
ordinary descended quotient map to the concrete map induced by
`ordinaryMap.app WalkingParallelPair.one`, fills the W399 relation-pullback
field from reverse closed-range membership, fills quotient compatibility by the
quotient-lift equation, and leaves only closedness of the descended quotient map
as an explicit analytic input.

Porting map:

* `relationReverseClosedRangeMembershipW407` is W407/W415's reverse closed-range
  membership proposition.
* `relationPreimagePullbackConditionW399` and
  `RelationPullbackDescendedFieldsInputsW399` are the W399 input names.
* `ordinaryDescendedOfOrdinaryMapW418` is W405's
  `ordinaryDescendedOfOrdinaryMapW405`.
* `relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap`
  is the W418 assembly constructor.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

universe u

namespace MetrizableLCA

/-- W407 closed-range membership spelling of the reverse-preimage input. -/
abbrev relationReverseClosedRangeMembershipW407
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ b : B,
    iB b ∈
        (AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure →
      b ∈
        (AddSubgroup.map (f - g).hom.toAddMonoidHom
          (⊤ : AddSubgroup A)).topologicalClosure

/-- W399 relation-pullback equality for cokernel-relation subgroups. -/
abbrev relationPreimagePullbackConditionW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W399 closed-range spelling of the same relation-pullback equality. -/
abbrev relationClosedRangePreimageEqualityW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

/-- W399's relation-pullback and closed-range spellings are definitionally equal. -/
theorem relationPreimagePullbackConditionIffClosedRangeEqualityW399
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B') :
    relationPreimagePullbackConditionW399 f g f' g' iB ↔
      relationClosedRangePreimageEqualityW399 f g f' g' iB := by
  rfl

/-- Under square equations, the source closed range maps into the target closed range. -/
theorem relationClosedRangeForwardOfSquaresW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
        (⊤ : AddSubgroup A)).topologicalClosure ≤
      AddSubgroup.comap iB.hom.toAddMonoidHom
        ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A')).topologicalClosure) := by
  let sourceRange : AddSubgroup B :=
    AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A)
  let targetClosed : AddSubgroup B' :=
    (AddSubgroup.map (f' - g').hom.toAddMonoidHom
      (⊤ : AddSubgroup A')).topologicalClosure
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom targetClosed
  have hrange_le : sourceRange ≤ targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ targetClosed
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
    exact AddSubgroup.le_topologicalClosure _
      (show (f' - g') (iA a) ∈
        AddSubgroup.map (f' - g').hom.toAddMonoidHom
          (⊤ : AddSubgroup A') from
        ⟨iA a, trivial, rfl⟩)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed ((fun b : B => iB b) ⁻¹' (targetClosed : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  exact AddSubgroup.topologicalClosure_minimal sourceRange hrange_le htargetPreimage_closed

/-- W407 reverse closed-range membership and square equations imply W399 relation pullback. -/
theorem relationPreimagePullbackCondition_of_reverseMembership_and_squares
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB) :
    relationPreimagePullbackConditionW399 f g f' g' iB := by
  apply (relationPreimagePullbackConditionIffClosedRangeEqualityW399 iB).mpr
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · exact relationClosedRangeForwardOfSquaresW418 iA iB hsquare_left hsquare_right

/-- Source relation maps forward to the target relation under compatible squares. -/
theorem relationPreimageForwardOfSquaresW418
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

/-- Kernel condition needed to descend the ordinary component map through quotient objects. -/
theorem ordinaryDescendedTargetKernel_leW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    cokernelSubgroup (f - g) ≤
      (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.toAddMonoidHom.ker := by
  intro b hb
  change ((iB b : B') : B' ⧸ cokernelSubgroup (f' - g')) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact relationPreimageForwardOfSquaresW418 iA iB hsquare_left hsquare_right b hb

/-- The concrete ordinary descended quotient map induced by compatible component squares. -/
def ordinaryDescendedQuotientMapW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientObj B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW418 iA iB hsquare_left hsquare_right)

/-- The concrete ordinary descended quotient map satisfies W399's quotient-compatibility field. -/
theorem ordinaryDescendedQuotientMap_quotient_compatW418
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedQuotientMapW418 iA iB hsquare_left hsquare_right =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift_quotientMap B (cokernelSubgroup (f - g))
    (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW418 iA iB hsquare_left hsquare_right)

/-- W399 ordinary descended quotient topology input shape. -/
structure RelationPullbackDescendedFieldsInputsW399
    (A B A' B' : MetrizableLCA.{u}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iA : A ⟶ A') (iB : B ⟶ B')
    (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  square_left : f ≫ iB = iA ≫ f'
  square_right : g ≫ iB = iA ≫ g'
  relation_pullback : relationPreimagePullbackConditionW399 f g f' g' iB
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

/-- W399 input constructor using the W405 descended quotient map. -/
theorem RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationReverseClosedRangeMembershipW407 f g f' g' iB)
    (hclosed : IsClosedMap
      (ordinaryDescendedQuotientMapW418 iA iB hsquare_left hsquare_right :
        quotientObj B (cokernelSubgroup (f - g))
          (AddSubgroup.isClosed_topologicalClosure _) →
        quotientObj B' (cokernelSubgroup (f' - g'))
          (AddSubgroup.isClosed_topologicalClosure _))) :
    RelationPullbackDescendedFieldsInputsW399 A B A' B' f g f' g' iA iB
      (ordinaryDescendedQuotientMapW418 iA iB hsquare_left hsquare_right) where
  square_left := hsquare_left
  square_right := hsquare_right
  relation_pullback :=
    relationPreimagePullbackCondition_of_reverseMembership_and_squares
      iA iB hsquare_left hsquare_right hreverse
  quotient_compat :=
    ordinaryDescendedQuotientMap_quotient_compatW418
      iA iB hsquare_left hsquare_right
  descended_closedMap := hclosed

end MetrizableLCA

namespace WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagram (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeft (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRight (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.right

/-- Ordinary quotient point used by the WPP-op adapter. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- WPP-op closed-range membership spelling of W407's reverse-preimage input. -/
abbrev WppOpRelationReverseClosedRangeMembershipW407
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  MetrizableLCA.relationReverseClosedRangeMembershipW407
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.one)

/-- Ordinary left square equation, from naturality. -/
theorem ordinarySquareLeftW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpLeft X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpLeft Y := by
  simpa [wppOpLeft] using ordinaryMap.naturality WalkingParallelPairHom.left

/-- Ordinary right square equation, from naturality. -/
theorem ordinarySquareRightW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpRight X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpRight Y := by
  simpa [wppOpRight] using ordinaryMap.naturality WalkingParallelPairHom.right

/-- The ordinary descended quotient map induced by `ordinaryMap.app WalkingParallelPair.one`. -/
def ordinaryDescendedOfOrdinaryMapW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y :=
  MetrizableLCA.ordinaryDescendedQuotientMapW418
    (ordinaryMap.app WalkingParallelPair.zero)
    (ordinaryMap.app WalkingParallelPair.one)
    (ordinarySquareLeftW418 ordinaryMap)
    (ordinarySquareRightW418 ordinaryMap)

/-- W405 quotient compatibility for the concrete ordinary descended map. -/
theorem ordinaryDescendedOfOrdinaryMap_quotient_compatW418
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedOfOrdinaryMapW418 ordinaryMap =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _) := by
  simpa [ordinaryDescendedOfOrdinaryMapW418] using
    MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW418
      (ordinaryMap.app WalkingParallelPair.zero)
      (ordinaryMap.app WalkingParallelPair.one)
      (ordinarySquareLeftW418 ordinaryMap)
      (ordinarySquareRightW418 ordinaryMap)

/-- WPP-op W399 ordinary input shape using the concrete descended quotient map. -/
abbrev WppOpRelationPullbackDescendedFieldsInputsW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    Prop :=
  MetrizableLCA.RelationPullbackDescendedFieldsInputsW399
    (wppOpDomain X) (wppOpCodomain X)
    (wppOpDomain Y) (wppOpCodomain Y)
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (ordinaryMap.app WalkingParallelPair.zero)
    (ordinaryMap.app WalkingParallelPair.one)
    (ordinaryDescendedOfOrdinaryMapW418 ordinaryMap)

/--
Checked WPP-op assembly: reverse closed-range membership fills W399's
relation-pullback field, W405's quotient-lift map fills quotient compatibility,
and the only remaining explicit input is closedness of the descended map.
-/
theorem relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (hreverse : WppOpRelationReverseClosedRangeMembershipW407 ordinaryMap)
    (hclosed : IsClosedMap (ordinaryDescendedOfOrdinaryMapW418 ordinaryMap :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)) :
    WppOpRelationPullbackDescendedFieldsInputsW399 ordinaryMap :=
  MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended
    (ordinarySquareLeftW418 ordinaryMap)
    (ordinarySquareRightW418 ordinaryMap)
    hreverse hclosed

/-- Remaining input after W418 combines W407/W415 relation pullback and W405 quotient compatibility. -/
def remainingInputsAfterW418Assembly : List String :=
  ["IsClosedMap for ordinaryDescendedOfOrdinaryMapW418 ordinaryMap"]

theorem remainingInputsAfterW418Assembly_count :
    remainingInputsAfterW418Assembly.length = 1 := rfl

/-- Declaration names exported by this W418 support layer. -/
def w418SupportDeclarationNames : List String :=
  ["MetrizableLCA.relationPreimagePullbackCondition_of_reverseMembership_and_squares",
    "MetrizableLCA.ordinaryDescendedQuotientMapW418",
    "MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW418",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended",
    "ordinaryDescendedOfOrdinaryMapW418",
    "ordinaryDescendedOfOrdinaryMap_quotient_compatW418",
    "relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap",
    "remainingInputsAfterW418Assembly"]

theorem w418SupportDeclarationNames_count :
    w418SupportDeclarationNames.length = 8 := rfl

/-- Machine-readable W418 state. -/
structure WppOpW399InputsFromReverseMembershipAndQuotientV370StateW418 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  w399InputsAssemblyResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418 :
    WppOpW399InputsFromReverseMembershipAndQuotientV370StateW418 where
  seed := "6e5c083ed385eff326e065695060c97b"
  checkedFacts :=
    ["proved the W407 reverse-membership to W399 relation-pullback bridge with ordinary square equations",
      "defined the W405-shaped ordinary descended quotient map by quotientLift",
      "proved quotient compatibility for the concrete ordinary descended quotient map",
      "constructed the W399 relation/topology input package from reverse membership and IsClosedMap only"]
  remainingInputs := remainingInputsAfterW418Assembly
  w399InputsAssemblyResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418_productSuccess :
    currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418.productSuccessClaimed =
      false := rfl

section Checks

#check MetrizableLCA.relationReverseClosedRangeMembershipW407
#check MetrizableLCA.relationPreimagePullbackConditionW399
#check MetrizableLCA.relationPreimagePullbackCondition_of_reverseMembership_and_squares
#check MetrizableLCA.ordinaryDescendedQuotientMapW418
#check MetrizableLCA.ordinaryDescendedQuotientMap_quotient_compatW418
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.of_reverseMembership_ordinaryDescended
#check WppOpRelationReverseClosedRangeMembershipW407
#check ordinaryDescendedOfOrdinaryMapW418
#check ordinaryDescendedOfOrdinaryMap_quotient_compatW418
#check WppOpRelationPullbackDescendedFieldsInputsW399
#check relationPullbackDescendedFieldsInputsW399_of_reverseMembership_and_closedMap
#check remainingInputsAfterW418Assembly
#check remainingInputsAfterW418Assembly_count
#check w418SupportDeclarationNames
#check w418SupportDeclarationNames_count
#check currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418
#check currentWppOpW399InputsFromReverseMembershipAndQuotientV370StateW418_productSuccess

end Checks

end WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418

end LeanLCAExactChallenge
