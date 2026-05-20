import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W393: ordinary descended quotient-field support for W390.

This standalone audit file keeps the work on the ordinary quotient side.  It
names the W352-shaped ordinary descended-field certificate on the quotient
points of two `WalkingParallelPairᵒᵖ` diagrams, repackages it as W381's
ordinary field boundary, and feeds that boundary into W390's canonical
transported descended-map consumer.

No transported-side field obligations are introduced here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaOrdinaryDescendedFieldsV370SupportW393

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

/-- The W352-style ordinary quotient/cofork point for the WPP-op diagram. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- Source point isomorphism from the W352 ordinary quotient point to the transported point. -/
def transportedQuotientSourcePointIsoW387
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpOrdinaryQuotientPoint X ≅ (wppOpTransportedConcreteQuotientCocone X).pt :=
  Iso.refl _

/-- Target point isomorphism from the W352 ordinary quotient point to the transported point. -/
def transportedQuotientTargetPointIsoW387
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpOrdinaryQuotientPoint Y ≅ (wppOpTransportedConcreteQuotientCocone Y).pt :=
  Iso.refl _

/-- Ordinary W352-descended fields before transport across point identifications. -/
structure OrdinaryRelationPullbackDescendedFieldsW381
    (ordinarySource ordinaryTarget : MetrizableLCA.{0})
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) : Prop where
  injective : Function.Injective (ordinaryDescended : ordinarySource → ordinaryTarget)
  inducing : IsInducing (ordinaryDescended : ordinarySource → ordinaryTarget)
  closed_range : IsClosed (Set.range (ordinaryDescended : ordinarySource → ordinaryTarget))

/--
The smallest W393 ordinary-side certificate: the three W352 descended quotient
fields on W387's ordinary quotient points.
-/
structure OrdinaryDescendedQuotientFieldsW393
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    Prop where
  injective : Function.Injective (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)
  inducing : IsInducing (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)
  closed_range : IsClosed (Set.range (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y))

/-- Repackage the W393 ordinary quotient certificate as W381's ordinary field boundary. -/
def ordinaryDescendedQuotientFieldsW393_to_w381
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (h : OrdinaryDescendedQuotientFieldsW393 ordinaryDescended) :
    OrdinaryRelationPullbackDescendedFieldsW381
      (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
      ordinaryDescended where
  injective := h.injective
  inducing := h.inducing
  closed_range := h.closed_range

/-- W384-shaped point-isomorphism and descended-map conjugacy package. -/
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

/-- Checked W387 point-isomorphism input package. -/
structure TransportedQuotientPointIsoInputsW387
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : Type 1 where
  source_point_iso :
    wppOpOrdinaryQuotientPoint X ≅ (wppOpTransportedConcreteQuotientCocone X).pt
  target_point_iso :
    wppOpOrdinaryQuotientPoint Y ≅ (wppOpTransportedConcreteQuotientCocone Y).pt

/-- The concrete W387 point-isomorphism inputs for a source and target diagram. -/
def transportedQuotientPointIsoInputsW387
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    TransportedQuotientPointIsoInputsW387 X Y where
  source_point_iso := transportedQuotientSourcePointIsoW387 X
  target_point_iso := transportedQuotientTargetPointIsoW387 Y

/-- W387 consumer into the W384-shaped point-isomorphism conjugacy package. -/
def transportedQuotientPointIsoInputs_to_pointIsoConjugacyPackageW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    (hfields :
      OrdinaryRelationPullbackDescendedFieldsW381
        (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
        ordinaryDescended)
    (hconj :
      ∀ x : (wppOpTransportedConcreteQuotientCocone X).pt,
        transportedDescended x =
          hiso.target_point_iso.hom (ordinaryDescended (hiso.source_point_iso.inv x))) :
    TransportedPointIsoConjugacyPackageW384
      (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
      ordinaryDescended transportedDescended where
  source_point_iso := hiso.source_point_iso
  target_point_iso := hiso.target_point_iso
  ordinary_fields := hfields
  transported_descended_conjugacy := hconj

/-- Canonical transported descended map obtained by point-isomorphism conjugacy. -/
def transportedDescendedByPointIsoConjugacyW390
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    (wppOpTransportedConcreteQuotientCocone X).pt ⟶
      (wppOpTransportedConcreteQuotientCocone Y).pt :=
  hiso.source_point_iso.inv ≫ ordinaryDescended ≫ hiso.target_point_iso.hom

/-- The canonical transported descended map satisfies W387's pointwise conjugacy by reduction. -/
theorem transportedDescendedByPointIsoConjugacyW390_pointwise
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    ∀ x : (wppOpTransportedConcreteQuotientCocone X).pt,
      transportedDescendedByPointIsoConjugacyW390 hiso ordinaryDescended x =
        hiso.target_point_iso.hom (ordinaryDescended (hiso.source_point_iso.inv x)) := by
  intro x
  rfl

/-- W390's canonical consumer, parameterized by W381 ordinary fields. -/
def transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (hfields :
      OrdinaryRelationPullbackDescendedFieldsW381
        (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
        ordinaryDescended) :
    TransportedPointIsoConjugacyPackageW384
      (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
      ordinaryDescended
      (transportedDescendedByPointIsoConjugacyW390 hiso ordinaryDescended) :=
  transportedQuotientPointIsoInputs_to_pointIsoConjugacyPackageW384
    hiso hfields
    (transportedDescendedByPointIsoConjugacyW390_pointwise hiso ordinaryDescended)

/--
W393 consumer: a W352-shaped ordinary quotient-field certificate is enough for
W390's canonical transported descended-map package.
-/
def ordinaryDescendedQuotientFieldsW393_to_pointIsoConjugacyPackageW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (hfields : OrdinaryDescendedQuotientFieldsW393 ordinaryDescended) :
    TransportedPointIsoConjugacyPackageW384
      (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
      ordinaryDescended
      (transportedDescendedByPointIsoConjugacyW390 hiso ordinaryDescended) :=
  transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384
    hiso (ordinaryDescendedQuotientFieldsW393_to_w381 hfields)

/-- Remaining external inputs after W393. -/
def remainingOrdinaryDescendedFieldsInputsW393 : List String :=
  ["instantiate OrdinaryDescendedQuotientFieldsW393 from the concrete W352 relation-pullback quotient-map package"]

theorem remainingOrdinaryDescendedFieldsInputsW393_count :
    remainingOrdinaryDescendedFieldsInputsW393.length = 1 := rfl

/-- Declaration names exported by this support file. -/
def w393SupportDeclarationNames : List String :=
  ["OrdinaryDescendedQuotientFieldsW393",
    "ordinaryDescendedQuotientFieldsW393_to_w381",
    "ordinaryDescendedQuotientFieldsW393_to_pointIsoConjugacyPackageW384",
    "remainingOrdinaryDescendedFieldsInputsW393"]

theorem w393SupportDeclarationNames_count :
    w393SupportDeclarationNames.length = 4 := rfl

/-- Machine-readable state for this checked W393 support file. -/
structure WppOpLeftLcaOrdinaryDescendedFieldsV370StateW393 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  ordinaryDescendedFieldsResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaOrdinaryDescendedFieldsV370StateW393 :
    WppOpLeftLcaOrdinaryDescendedFieldsV370StateW393 where
  seed := "w393-20260520T221513Z-439e6a851e5ba28a"
  checkedFacts :=
    ["named the smallest ordinary quotient-field certificate on W387's ordinary quotient points",
      "repackaged that certificate as W381 OrdinaryRelationPullbackDescendedFieldsW381",
      "provided a consumer into W390's canonical transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384 path"]
  remainingInputs := remainingOrdinaryDescendedFieldsInputsW393
  ordinaryDescendedFieldsResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaOrdinaryDescendedFieldsV370StateW393_productSuccess :
    currentWppOpLeftLcaOrdinaryDescendedFieldsV370StateW393.productSuccessClaimed = false := rfl

section Checks

#check wppOpOrdinaryQuotientPoint
#check OrdinaryRelationPullbackDescendedFieldsW381
#check OrdinaryDescendedQuotientFieldsW393
#check ordinaryDescendedQuotientFieldsW393_to_w381
#check transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384
#check ordinaryDescendedQuotientFieldsW393_to_pointIsoConjugacyPackageW384
#check remainingOrdinaryDescendedFieldsInputsW393
#check remainingOrdinaryDescendedFieldsInputsW393_count
#check w393SupportDeclarationNames
#check w393SupportDeclarationNames_count
#check currentWppOpLeftLcaOrdinaryDescendedFieldsV370StateW393
#check currentWppOpLeftLcaOrdinaryDescendedFieldsV370StateW393_productSuccess

end Checks

end WppOpLeftLcaOrdinaryDescendedFieldsV370SupportW393

end LeanLCAExactChallenge
