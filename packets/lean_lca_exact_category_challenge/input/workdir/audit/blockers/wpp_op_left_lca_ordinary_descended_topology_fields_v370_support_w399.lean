import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W399: ordinary descended topology fields for the W352-to-W396 route.

This standalone audit file specializes the checked W352 relation-pullback input
package to the ordinary quotient object used by the WPP-op adapter.  The bridge
keeps the remaining concrete assumptions explicit: square equations, relation
pullback equality, quotient compatibility, and closedness of the descended map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

universe u

namespace MetrizableLCA

/-- W352 relation-pullback equality for cokernel-relation subgroups. -/
abbrev relationPreimagePullbackConditionW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- Elementwise reverse relation-preimage condition. -/
abbrev relationPreimageReverseConditionW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') →
    b ∈ cokernelSubgroup (f - g)

/-- Closed-range/preimage spelling of the same relation-pullback equality. -/
abbrev relationClosedRangePreimageEqualityW399
    {A B A' B' : MetrizableLCA.{u}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom
      ((AddSubgroup.map (f' - g').hom.toAddMonoidHom
        (⊤ : AddSubgroup A')).topologicalClosure) =
    (AddSubgroup.map (f - g).hom.toAddMonoidHom
      (⊤ : AddSubgroup A)).topologicalClosure

theorem relationPreimageForwardOfSquaresW399
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

theorem relationPreimageReverseOfPullbackConditionW399
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B')
    (hpullback : relationPreimagePullbackConditionW399 f g f' g' iB) :
    relationPreimageReverseConditionW399 f g f' g' iB := by
  intro b hb
  have hbcomap :
      b ∈ AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) := hb
  simpa [relationPreimagePullbackConditionW399] using (hpullback ▸ hbcomap)

theorem relationPreimagePullbackConditionOfReverseW399
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g')
    (hreverse : relationPreimageReverseConditionW399 f g f' g' iB) :
    relationPreimagePullbackConditionW399 f g f' g' iB := by
  apply le_antisymm
  · intro b hb
    exact hreverse b hb
  · intro b hb
    exact relationPreimageForwardOfSquaresW399 iA iB hsquare_left hsquare_right b hb

theorem relationPreimagePullbackConditionIffClosedRangeEqualityW399
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iB : B ⟶ B') :
    relationPreimagePullbackConditionW399 f g f' g' iB ↔
      relationClosedRangePreimageEqualityW399 f g f' g' iB := by
  rfl

/-- Concrete W352 input package, keeping algebraic and topological assumptions separate. -/
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

theorem RelationPullbackDescendedFieldsInputsW399.relation_preimage_exact
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW399 A B A' B' f g f' g' iA iB descended) :
    ∀ b : B, iB b ∈ cokernelSubgroup (f' - g') ↔
      b ∈ cokernelSubgroup (f - g) := by
  intro b
  exact ⟨relationPreimageReverseOfPullbackConditionW399 iB h.relation_pullback b,
    relationPreimageForwardOfSquaresW399 iA iB h.square_left h.square_right b⟩

theorem RelationPullbackDescendedFieldsInputsW399.descended_injective
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW399 A B A' B' f g f' g' iA iB descended) :
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

theorem RelationPullbackDescendedFieldsInputsW399.descended_closedEmbedding
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW399 A B A' B' f g f' g' iA iB descended) :
    IsClosedEmbedding (descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) →
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    descended.hom.continuous h.descended_injective h.descended_closedMap

/-- The three descended quotient topology fields produced from W352 inputs. -/
structure DescendedQuotientTopologyFieldsW399
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

theorem RelationPullbackDescendedFieldsInputsW399.descended_topology_fields
    {A B A' B' : MetrizableLCA.{u}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      quotientObj B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW399 A B A' B' f g f' g' iA iB descended) :
    DescendedQuotientTopologyFieldsW399 f g f' g' descended := by
  have hclosedEmbedding := h.descended_closedEmbedding
  exact
    ⟨h.descended_injective, hclosedEmbedding.toIsEmbedding.toIsInducing,
      hclosedEmbedding.isClosed_range⟩

end MetrizableLCA

namespace WppOpLeftLcaOrdinaryDescendedTopologyFieldsV370SupportW399

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

/-- The ordinary quotient point used by the W352-to-W393 adapter. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W393-shaped ordinary descended quotient fields. -/
structure OrdinaryDescendedQuotientTopologyFieldsW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    Prop where
  injective : Function.Injective (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)
  inducing : IsInducing (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)
  closed_range : IsClosed (Set.range (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y))

/-- W399 concrete ordinary certificate from the W352 topology fields. -/
def ordinaryTopologyFields_of_descendedTopologyFieldsW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (h : MetrizableLCA.DescendedQuotientTopologyFieldsW399
      (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y) ordinaryDescended) :
    OrdinaryDescendedQuotientTopologyFieldsW399 ordinaryDescended where
  injective := h.injective
  inducing := h.inducing
  closed_range := h.closed_range

/-- W399 concrete ordinary certificate directly from W352 relation-pullback inputs. -/
def ordinaryTopologyFields_of_relationPullbackInputsW399
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {iA : wppOpDomain X ⟶ wppOpDomain Y}
    {iB : wppOpCodomain X ⟶ wppOpCodomain Y}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (h : MetrizableLCA.RelationPullbackDescendedFieldsInputsW399
      (wppOpDomain X) (wppOpCodomain X) (wppOpDomain Y) (wppOpCodomain Y)
      (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
      iA iB ordinaryDescended) :
    OrdinaryDescendedQuotientTopologyFieldsW399 ordinaryDescended :=
  ordinaryTopologyFields_of_descendedTopologyFieldsW399 h.descended_topology_fields

/-- Remaining concrete inputs distinguished for the parent W352-to-W396 route. -/
def remainingOrdinaryDescendedTopologyInputsW399 : List String :=
  ["instantiate the W352 relation-pullback input package on the concrete ordinary descended quotient map",
    "prove the algebraic square equations for the ordinary parallel pairs",
    "prove the relation-pullback equality, equivalently reverse preimage or closed-range preimage equality",
    "prove quotient compatibility for the ordinary descended quotient map",
    "prove IsClosedMap for the ordinary descended quotient map"]

theorem remainingOrdinaryDescendedTopologyInputsW399_count :
    remainingOrdinaryDescendedTopologyInputsW399.length = 5 := rfl

/-- Declaration names exported by this support file. -/
def w399SupportDeclarationNames : List String :=
  ["MetrizableLCA.relationPreimagePullbackConditionW399",
    "MetrizableLCA.relationClosedRangePreimageEqualityW399",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.relation_preimage_exact",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.descended_injective",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.descended_closedEmbedding",
    "MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.descended_topology_fields",
    "ordinaryTopologyFields_of_descendedTopologyFieldsW399",
    "ordinaryTopologyFields_of_relationPullbackInputsW399",
    "remainingOrdinaryDescendedTopologyInputsW399"]

theorem w399SupportDeclarationNames_count :
    w399SupportDeclarationNames.length = 10 := rfl

/-- Machine-readable state for this checked W399 support file. -/
structure WppOpLeftLcaOrdinaryDescendedTopologyFieldsV370StateW399 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  ordinaryDescendedTopologyFieldsResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaOrdinaryDescendedTopologyFieldsV370StateW399 :
    WppOpLeftLcaOrdinaryDescendedTopologyFieldsV370StateW399 where
  seed := "w399-3403f7198e5d69e585680d504e55b575"
  checkedFacts :=
    ["proved injectivity of the ordinary descended quotient map from relation-pullback exactness and quotient compatibility",
      "proved IsClosedEmbedding from continuity, injectivity, and the IsClosedMap input",
      "extracted IsInducing and closed range from the closed embedding",
      "repackaged the three topology fields as a WPP-op ordinary quotient-point certificate"]
  remainingInputs := remainingOrdinaryDescendedTopologyInputsW399
  ordinaryDescendedTopologyFieldsResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaOrdinaryDescendedTopologyFieldsV370StateW399_productSuccess :
    currentWppOpLeftLcaOrdinaryDescendedTopologyFieldsV370StateW399.productSuccessClaimed = false := rfl

section Checks

#check MetrizableLCA.relationPreimagePullbackConditionW399
#check MetrizableLCA.relationClosedRangePreimageEqualityW399
#check MetrizableLCA.relationPreimagePullbackConditionIffClosedRangeEqualityW399
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.relation_preimage_exact
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.descended_injective
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.descended_closedEmbedding
#check MetrizableLCA.RelationPullbackDescendedFieldsInputsW399.descended_topology_fields
#check OrdinaryDescendedQuotientTopologyFieldsW399
#check ordinaryTopologyFields_of_descendedTopologyFieldsW399
#check ordinaryTopologyFields_of_relationPullbackInputsW399
#check remainingOrdinaryDescendedTopologyInputsW399
#check remainingOrdinaryDescendedTopologyInputsW399_count
#check w399SupportDeclarationNames
#check w399SupportDeclarationNames_count
#check currentWppOpLeftLcaOrdinaryDescendedTopologyFieldsV370StateW399
#check currentWppOpLeftLcaOrdinaryDescendedTopologyFieldsV370StateW399_productSuccess

end Checks

end WppOpLeftLcaOrdinaryDescendedTopologyFieldsV370SupportW399

end LeanLCAExactChallenge
