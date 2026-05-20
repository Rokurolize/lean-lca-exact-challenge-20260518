import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W381: ordinary-to-transported relation-field adapter for the left-LCA route.

The copied W352/W375/W378 audit files are checked directly rather than imported
as modules.  This standalone support file therefore repeats only the stable
typed boundary needed by the parent thread: ordinary descended quotient fields,
the transported W378 relation-field package, and a checked adapter that names
the point-identification and field-transport obligations needed to move from
ordinary quotient/cofork points to W375's transported concrete quotient cocones.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaOrdinaryFieldsToTransportedV370SupportW381

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

/--
Ordinary W352-descended fields before transport across the cocone-point
identifications.
-/
structure OrdinaryRelationPullbackDescendedFieldsW381
    (ordinarySource ordinaryTarget : MetrizableLCA.{0})
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) : Prop where
  injective : Function.Injective (ordinaryDescended : ordinarySource → ordinaryTarget)
  inducing : IsInducing (ordinaryDescended : ordinarySource → ordinaryTarget)
  closed_range : IsClosed (Set.range (ordinaryDescended : ordinarySource → ordinaryTarget))

/--
Adapter inputs for moving ordinary W352 fields to W378 fields on transported
concrete quotient cocones.

The point isomorphisms identify the ordinary quotient/cofork points with the
transported cocone points.  The three `transported_*` fields are the exact
field-transport lemmas still required to complete a fully automatic transport
from `ordinary_fields`.
-/
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

/--
Checked W381 bridge: once the ordinary fields have been transported across the
named point isomorphisms, they form W378's transported relation-field package.
-/
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

/--
Consumer theorem for W375's `transportedConcreteQuotientW354Inputs_of_w357_ordinary_projection`.
-/
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

/-- Remaining proof obligations for turning W352 ordinary fields into W378 fields automatically. -/
def remainingOrdinaryToTransportedRelationFieldInputsW381 : List String :=
  ["identify W352's ordinary quotient/cofork source point with wppOpTransportedConcreteQuotientCocone X point",
    "identify W352's ordinary quotient/cofork target point with wppOpTransportedConcreteQuotientCocone Y point",
    "prove the transported descended map is conjugate to the ordinary descended quotient map",
    "transport injectivity across the source and target point isomorphisms",
    "transport IsInducing across the source and target point isomorphisms",
    "transport closed range across the source and target point isomorphisms"]

theorem remainingOrdinaryToTransportedRelationFieldInputsW381_count :
    remainingOrdinaryToTransportedRelationFieldInputsW381.length = 6 := rfl

/-- Declaration names exported by this support file. -/
def w381SupportDeclarationNames : List String :=
  ["wppOpTransportedConcreteQuotientCocone",
    "OrdinaryRelationPullbackDescendedFieldsW381",
    "OrdinaryToTransportedRelationFieldInputsW381",
    "ordinary_fields_to_transportedRelationPullbackTopologicalFieldsW381",
    "ordinary_fields_to_w375_transport_relation_consumerW381",
    "remainingOrdinaryToTransportedRelationFieldInputsW381"]

theorem w381SupportDeclarationNames_count :
    w381SupportDeclarationNames.length = 6 := rfl

/-- Machine-readable state for this checked W381 support file. -/
structure WppOpLeftLcaOrdinaryFieldsToTransportedV370StateW381 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  ordinaryToTransportedFieldsResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaOrdinaryFieldsToTransportedV370StateW381 :
    WppOpLeftLcaOrdinaryFieldsToTransportedV370StateW381 where
  seed := "36265d1fa733fa30e3605e17dcdaa8a6"
  checkedFacts :=
    ["defined the ordinary W352-style descended field boundary",
      "named the point isomorphisms and field-transport lemmas required for ordinary-to-transported transfer",
      "proved a checked adapter into W378's transported relation-field package",
      "proved a checked consumer theorem in W375's relation-input shape for transported concrete quotient cocones"]
  remainingInputs := remainingOrdinaryToTransportedRelationFieldInputsW381
  ordinaryToTransportedFieldsResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaOrdinaryFieldsToTransportedV370StateW381_productSuccess :
    currentWppOpLeftLcaOrdinaryFieldsToTransportedV370StateW381.productSuccessClaimed = false := rfl

section Checks

#check wppOpTransportedConcreteQuotientCocone
#check wppOpTransportedConcreteQuotientCoconeIsColimit
#check OrdinaryRelationPullbackDescendedFieldsW381
#check OrdinaryToTransportedRelationFieldInputsW381
#check ordinary_fields_to_transportedRelationPullbackTopologicalFieldsW381
#check ordinary_fields_to_w375_transport_relation_consumerW381
#check remainingOrdinaryToTransportedRelationFieldInputsW381
#check remainingOrdinaryToTransportedRelationFieldInputsW381_count
#check w381SupportDeclarationNames
#check w381SupportDeclarationNames_count
#check currentWppOpLeftLcaOrdinaryFieldsToTransportedV370StateW381
#check currentWppOpLeftLcaOrdinaryFieldsToTransportedV370StateW381_productSuccess

end Checks

end WppOpLeftLcaOrdinaryFieldsToTransportedV370SupportW381

end LeanLCAExactChallenge
