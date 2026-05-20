import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W384: transported point-isomorphism support for W381.

This standalone audit file sharpens W381's ordinary-to-transported boundary.
It constructs the reusable package that identifies W352's ordinary concrete
quotient points with W381's transported concrete quotient cocone points, records
the descended-map conjugacy, and derives the three transported topological
fields consumed by W381.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaTransportedPointIsoV370SupportW384

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

namespace ConcreteMetrizableLCA

open LeanLCAExactChallenge.MetrizableLCA

variable {A B : MetrizableLCA.{0}}

/-- Concrete quotient cofork for a parallel pair, presented as the cokernel of `f - g`. -/
def concreteQuotientCofork (f g : A ⟶ B) : Cofork f g :=
  Preadditive.coforkOfCokernelCofork
    (CokernelCofork.ofπ (cokernelπ (f - g)) (comp_cokernelπ (f - g)))

/-- The concrete quotient cofork is a colimit by the local cokernel construction. -/
def concreteQuotientCoforkIsColimit (f g : A ⟶ B) :
    IsColimit (concreteQuotientCofork f g) :=
  Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsColimit (f - g))

end ConcreteMetrizableLCA

/-- Concrete quotient cocone on the ordinary diagram associated to a WPP-op diagram. -/
def wppOpConcreteQuotientCoconeOnOrdinary
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    Cocone (wppOpOrdinaryDiagram X) :=
  (Cocone.precompose (diagramIsoParallelPair (wppOpOrdinaryDiagram X)).hom).obj
    (ConcreteMetrizableLCA.concreteQuotientCofork (wppOpLeft X) (wppOpRight X))

/-- The ordinary concrete quotient cocone associated to a WPP-op diagram is a colimit. -/
def wppOpConcreteQuotientCoconeOnOrdinaryIsColimit
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    IsColimit (wppOpConcreteQuotientCoconeOnOrdinary X) :=
  (IsColimit.precomposeHomEquiv
    (diagramIsoParallelPair (wppOpOrdinaryDiagram X))
    (ConcreteMetrizableLCA.concreteQuotientCofork (wppOpLeft X) (wppOpRight X))).symm
    (ConcreteMetrizableLCA.concreteQuotientCoforkIsColimit (wppOpLeft X) (wppOpRight X))

/-- Concrete quotient cocone after whiskering through the inverse equivalence. -/
def wppOpWhiskeredConcreteQuotientCocone
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    Cocone (walkingParallelPairOpEquiv.inverse ⋙ wppOpOrdinaryDiagram X) :=
  Cocone.whisker walkingParallelPairOpEquiv.inverse
    (wppOpConcreteQuotientCoconeOnOrdinary X)

/-- The whiskered concrete quotient cocone is still a colimit. -/
def wppOpWhiskeredConcreteQuotientCoconeIsColimit
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    IsColimit (wppOpWhiskeredConcreteQuotientCocone X) :=
  IsColimit.whiskerEquivalence
    (wppOpConcreteQuotientCoconeOnOrdinaryIsColimit X)
    walkingParallelPairOpEquiv.symm

/-- Counit-based diagram isomorphism from the whiskered ordinary diagram back to `X`. -/
def wppOpWhiskeredDiagramIso
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    walkingParallelPairOpEquiv.inverse ⋙ wppOpOrdinaryDiagram X ≅ X :=
  (Functor.associator walkingParallelPairOpEquiv.inverse walkingParallelPairOpEquiv.functor X).symm ≪≫
    Functor.isoWhiskerRight walkingParallelPairOpEquiv.counitIso X ≪≫
      Functor.leftUnitor X

/-- The concrete quotient cocone transported to an actual cocone over `X`. -/
def wppOpTransportedConcreteQuotientCocone
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : Cocone X :=
  (Cocone.precompose (wppOpWhiskeredDiagramIso X).symm.hom).obj
    (wppOpWhiskeredConcreteQuotientCocone X)

/-- The transported concrete quotient cocone is a colimit. -/
def wppOpTransportedConcreteQuotientCoconeIsColimit
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    IsColimit (wppOpTransportedConcreteQuotientCocone X) :=
  (IsColimit.precomposeHomEquiv
    (wppOpWhiskeredDiagramIso X).symm
    (wppOpWhiskeredConcreteQuotientCocone X)).symm
    (wppOpWhiskeredConcreteQuotientCoconeIsColimit X)

/-- W378's transported relation-pullback topological field package. -/
structure TransportedRelationPullbackTopologicalFieldsW378
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/-- W375/W354 relation-input shape consumed downstream. -/
structure RelationPullbackDescendedFieldsInputsW354Shape
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/-- Repackage W378 fields into the W375/W354 relation-input shape. -/
def transportedRelationPullbackFieldsW378
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : TransportedRelationPullbackTopologicalFieldsW378 source target descended) :
    RelationPullbackDescendedFieldsInputsW354Shape source target descended where
  injective := h.injective
  inducing := h.inducing
  closed_range := h.closed_range

/-- Ordinary W352-descended fields before transport across point identifications. -/
structure OrdinaryRelationPullbackDescendedFieldsW381
    (ordinarySource ordinaryTarget : MetrizableLCA.{0})
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) : Prop where
  injective : Function.Injective (ordinaryDescended : ordinarySource → ordinaryTarget)
  inducing : IsInducing (ordinaryDescended : ordinarySource → ordinaryTarget)
  closed_range : IsClosed (Set.range (ordinaryDescended : ordinarySource → ordinaryTarget))

/-- Ordinary W352-style fields package as a closed embedding. -/
theorem OrdinaryRelationPullbackDescendedFieldsW381.closedEmbedding
    {ordinarySource ordinaryTarget : MetrizableLCA.{0}}
    {ordinaryDescended : ordinarySource ⟶ ordinaryTarget}
    (h : OrdinaryRelationPullbackDescendedFieldsW381
      ordinarySource ordinaryTarget ordinaryDescended) :
    IsClosedEmbedding (ordinaryDescended : ordinarySource → ordinaryTarget) :=
  WppOpExactAcyclicFrontierConsolidatedW318.closedEmbedding_of_injective_inducing_closedImage
    (ordinaryDescended : ordinarySource → ordinaryTarget) h.injective h.inducing h.closed_range

/-- Adapter inputs for moving ordinary W352 fields to W378 fields on transported cocone points. -/
structure OrdinaryToTransportedRelationFieldInputsW381
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinarySource ordinaryTarget : MetrizableLCA.{0})
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget)
    (transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt) : Type 1 where
  source_point_iso :
    ordinarySource ≅ (wppOpTransportedConcreteQuotientCocone X).pt
  target_point_iso :
    ordinaryTarget ≅ (wppOpTransportedConcreteQuotientCocone Y).pt
  ordinary_fields :
    OrdinaryRelationPullbackDescendedFieldsW381
      ordinarySource ordinaryTarget ordinaryDescended
  transported_injective :
    Function.Injective (transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt →
        (wppOpTransportedConcreteQuotientCocone Y).pt)
  transported_inducing :
    IsInducing (transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt →
        (wppOpTransportedConcreteQuotientCocone Y).pt)
  transported_closed_range :
    IsClosed (Set.range (transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt →
        (wppOpTransportedConcreteQuotientCocone Y).pt))

/-- W381 bridge: transported fields form W378's relation-field package. -/
theorem ordinary_fields_to_transportedRelationPullbackTopologicalFieldsW381
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinarySource ordinaryTarget : MetrizableLCA.{0}}
    {ordinaryDescended : ordinarySource ⟶ ordinaryTarget}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (h :
      OrdinaryToTransportedRelationFieldInputsW381
        ordinarySource ordinaryTarget ordinaryDescended transportedDescended) :
    TransportedRelationPullbackTopologicalFieldsW378
      (wppOpTransportedConcreteQuotientCocone X)
      (wppOpTransportedConcreteQuotientCocone Y)
      transportedDescended where
  injective := h.transported_injective
  inducing := h.transported_inducing
  closed_range := h.transported_closed_range

/-- W381 consumer theorem in the W375/W354 relation-input shape. -/
theorem ordinary_fields_to_w375_transport_relation_consumerW381
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinarySource ordinaryTarget : MetrizableLCA.{0}}
    {ordinaryDescended : ordinarySource ⟶ ordinaryTarget}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (h :
      OrdinaryToTransportedRelationFieldInputsW381
        ordinarySource ordinaryTarget ordinaryDescended transportedDescended) :
    RelationPullbackDescendedFieldsInputsW354Shape
      (wppOpTransportedConcreteQuotientCocone X)
      (wppOpTransportedConcreteQuotientCocone Y)
      transportedDescended :=
  transportedRelationPullbackFieldsW378
    (ordinary_fields_to_transportedRelationPullbackTopologicalFieldsW381 h)

/--
Point-isomorphism and conjugacy package for the W352 ordinary quotient points
and W381 transported concrete quotient cocone points.
-/
structure TransportedPointIsoConjugacyPackageW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinarySource ordinaryTarget : MetrizableLCA.{0})
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget)
    (transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt) : Type 1 where
  source_point_iso :
    ordinarySource ≅ (wppOpTransportedConcreteQuotientCocone X).pt
  target_point_iso :
    ordinaryTarget ≅ (wppOpTransportedConcreteQuotientCocone Y).pt
  ordinary_fields :
    OrdinaryRelationPullbackDescendedFieldsW381
      ordinarySource ordinaryTarget ordinaryDescended
  transported_descended_conjugacy :
    ∀ x : (wppOpTransportedConcreteQuotientCocone X).pt,
      transportedDescended x =
        target_point_iso.hom (ordinaryDescended (source_point_iso.inv x))

/-- Conjugacy across point isomorphisms transports ordinary fields to a closed embedding. -/
theorem transported_closedEmbedding_of_pointIsoConjugacyW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinarySource ordinaryTarget : MetrizableLCA.{0}}
    {ordinaryDescended : ordinarySource ⟶ ordinaryTarget}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (h :
      TransportedPointIsoConjugacyPackageW384
        ordinarySource ordinaryTarget ordinaryDescended transportedDescended) :
    IsClosedEmbedding (transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt →
        (wppOpTransportedConcreteQuotientCocone Y).pt) := by
  let sourceHomeomorph :
      (wppOpTransportedConcreteQuotientCocone X).pt ≃ₜ+ ordinarySource :=
    MetrizableLCA.isoToContinuousAddEquiv h.source_point_iso.symm
  let targetHomeomorph :
      ordinaryTarget ≃ₜ+ (wppOpTransportedConcreteQuotientCocone Y).pt :=
    MetrizableLCA.isoToContinuousAddEquiv h.target_point_iso
  have hcomp :
      IsClosedEmbedding
        (fun x : (wppOpTransportedConcreteQuotientCocone X).pt =>
          targetHomeomorph (ordinaryDescended (sourceHomeomorph x))) :=
    targetHomeomorph.toHomeomorph.isClosedEmbedding.comp
      ((h.ordinary_fields.closedEmbedding).comp sourceHomeomorph.toHomeomorph.isClosedEmbedding)
  have hfun :
      (fun x : (wppOpTransportedConcreteQuotientCocone X).pt =>
          targetHomeomorph (ordinaryDescended (sourceHomeomorph x))) =
        (transportedDescended :
          (wppOpTransportedConcreteQuotientCocone X).pt →
            (wppOpTransportedConcreteQuotientCocone Y).pt) := by
    funext x
    exact (h.transported_descended_conjugacy x).symm
  simpa [hfun] using hcomp

/-- Conjugacy package supplies the full W381 adapter input automatically. -/
def pointIsoConjugacy_to_ordinaryToTransportedRelationFieldInputsW381
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinarySource ordinaryTarget : MetrizableLCA.{0}}
    {ordinaryDescended : ordinarySource ⟶ ordinaryTarget}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (h :
      TransportedPointIsoConjugacyPackageW384
        ordinarySource ordinaryTarget ordinaryDescended transportedDescended) :
    OrdinaryToTransportedRelationFieldInputsW381
      ordinarySource ordinaryTarget ordinaryDescended transportedDescended :=
  let hclosed := transported_closedEmbedding_of_pointIsoConjugacyW384 h
  { source_point_iso := h.source_point_iso
    target_point_iso := h.target_point_iso
    ordinary_fields := h.ordinary_fields
    transported_injective := hclosed.injective
    transported_inducing := hclosed.isInducing
    transported_closed_range := hclosed.isClosed_range }

/-- Direct W384 consumer into W381's transported relation-field package. -/
theorem pointIsoConjugacy_to_transportedRelationPullbackTopologicalFieldsW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinarySource ordinaryTarget : MetrizableLCA.{0}}
    {ordinaryDescended : ordinarySource ⟶ ordinaryTarget}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (h :
      TransportedPointIsoConjugacyPackageW384
        ordinarySource ordinaryTarget ordinaryDescended transportedDescended) :
    TransportedRelationPullbackTopologicalFieldsW378
      (wppOpTransportedConcreteQuotientCocone X)
      (wppOpTransportedConcreteQuotientCocone Y)
      transportedDescended :=
  ordinary_fields_to_transportedRelationPullbackTopologicalFieldsW381
    (pointIsoConjugacy_to_ordinaryToTransportedRelationFieldInputsW381 h)

/-- Direct W384 consumer into the W375/W354 relation-input shape. -/
theorem pointIsoConjugacy_to_w375_transport_relation_consumerW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinarySource ordinaryTarget : MetrizableLCA.{0}}
    {ordinaryDescended : ordinarySource ⟶ ordinaryTarget}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (h :
      TransportedPointIsoConjugacyPackageW384
        ordinarySource ordinaryTarget ordinaryDescended transportedDescended) :
    RelationPullbackDescendedFieldsInputsW354Shape
      (wppOpTransportedConcreteQuotientCocone X)
      (wppOpTransportedConcreteQuotientCocone Y)
      transportedDescended :=
  ordinary_fields_to_w375_transport_relation_consumerW381
    (pointIsoConjugacy_to_ordinaryToTransportedRelationFieldInputsW381 h)

/-- Remaining external inputs after W384 packages point isomorphism and conjugacy. -/
def remainingTransportedPointIsoInputsW384 : List String :=
  ["construct the source point isomorphism from W352's ordinary quotient object to wppOpTransportedConcreteQuotientCocone X point",
    "construct the target point isomorphism from W352's ordinary quotient object to wppOpTransportedConcreteQuotientCocone Y point",
    "prove the pointwise descended-map conjugacy against those two point isomorphisms",
    "supply W352 ordinary descended quotient fields for the ordinary descended map"]

theorem remainingTransportedPointIsoInputsW384_count :
    remainingTransportedPointIsoInputsW384.length = 4 := rfl

/-- Declaration names exported by this support file. -/
def w384SupportDeclarationNames : List String :=
  ["TransportedPointIsoConjugacyPackageW384",
    "OrdinaryRelationPullbackDescendedFieldsW381.closedEmbedding",
    "transported_closedEmbedding_of_pointIsoConjugacyW384",
    "pointIsoConjugacy_to_ordinaryToTransportedRelationFieldInputsW381",
    "pointIsoConjugacy_to_transportedRelationPullbackTopologicalFieldsW384",
    "pointIsoConjugacy_to_w375_transport_relation_consumerW384",
    "remainingTransportedPointIsoInputsW384"]

theorem w384SupportDeclarationNames_count :
    w384SupportDeclarationNames.length = 7 := rfl

/-- Machine-readable state for this checked W384 support file. -/
structure WppOpLeftLcaTransportedPointIsoV370StateW384 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  transportedPointIsoResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaTransportedPointIsoV370StateW384 :
    WppOpLeftLcaTransportedPointIsoV370StateW384 where
  seed := "1862aa26b5fe6a7998efe4261215d238"
  checkedFacts :=
    ["defined a point-isomorphism and descended-map conjugacy package",
      "proved ordinary W352-style fields give a closed embedding",
      "proved conjugacy across point isomorphisms transports closed embedding fields",
      "constructed the W381 ordinary-to-transported adapter from the W384 package",
      "provided direct consumers into W378 and the W375/W354 relation-input shape"]
  remainingInputs := remainingTransportedPointIsoInputsW384
  transportedPointIsoResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaTransportedPointIsoV370StateW384_productSuccess :
    currentWppOpLeftLcaTransportedPointIsoV370StateW384.productSuccessClaimed = false := rfl

section Checks

#check wppOpTransportedConcreteQuotientCocone
#check wppOpTransportedConcreteQuotientCoconeIsColimit
#check TransportedPointIsoConjugacyPackageW384
#check OrdinaryRelationPullbackDescendedFieldsW381.closedEmbedding
#check transported_closedEmbedding_of_pointIsoConjugacyW384
#check pointIsoConjugacy_to_ordinaryToTransportedRelationFieldInputsW381
#check pointIsoConjugacy_to_transportedRelationPullbackTopologicalFieldsW384
#check pointIsoConjugacy_to_w375_transport_relation_consumerW384
#check remainingTransportedPointIsoInputsW384
#check remainingTransportedPointIsoInputsW384_count
#check w384SupportDeclarationNames
#check w384SupportDeclarationNames_count
#check currentWppOpLeftLcaTransportedPointIsoV370StateW384
#check currentWppOpLeftLcaTransportedPointIsoV370StateW384_productSuccess

end Checks

end WppOpLeftLcaTransportedPointIsoV370SupportW384

end LeanLCAExactChallenge
