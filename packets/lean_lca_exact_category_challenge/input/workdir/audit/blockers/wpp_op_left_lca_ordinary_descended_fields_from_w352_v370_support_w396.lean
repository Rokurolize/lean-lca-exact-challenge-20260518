import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W396: instantiate ordinary descended fields from W352 support.

This standalone audit file isolates the definitional bridge left by W393:
the ordinary quotient point used by W393 is the concrete W352 quotient object
for the ordinary parallel pair obtained from a `WalkingParallelPairᵒᵖ` diagram.
Consequently W352's concrete quotient-map fields repackage directly as W393's
`OrdinaryDescendedQuotientFieldsW393`, and that certificate feeds the canonical
W390 point-isomorphism transported descended-map package.

The W352 relation-pullback hypotheses themselves remain the concrete inputs.
No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaOrdinaryDescendedFieldsFromW352V370SupportW396

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

/-- The W352 concrete quotient point for the WPP-op diagram. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W352's three concrete descended quotient-map fields, specialized to universe 0. -/
structure DescendedQuotientFieldsW352
    {A B A' B' : MetrizableLCA.{0}} (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (descended :
      MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  injective : Function.Injective (descended :
    MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
  inducing : IsInducing (descended :
    MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
  closed_range : IsClosed (Set.range (descended :
    MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
      (AddSubgroup.isClosed_topologicalClosure _) →
    MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)))

/-- W352 relation-pullback input package specialized to the concrete quotient object. -/
structure RelationPullbackDescendedFieldsInputsW352
    (A B A' B' : MetrizableLCA.{0}) (f g : A ⟶ B) (f' g' : A' ⟶ B')
    (iA : A ⟶ A') (iB : B ⟶ B')
    (descended :
      MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)) : Prop where
  descended_fields : DescendedQuotientFieldsW352 f g f' g' descended

/-- The W352 input package exposes exactly the quotient-map fields. -/
theorem RelationPullbackDescendedFieldsInputsW352.to_descended_fields
    {A B A' B' : MetrizableLCA.{0}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    {iA : A ⟶ A'} {iB : B ⟶ B'}
    {descended :
      MetrizableLCA.quotientObj B (MetrizableLCA.cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _) ⟶
      MetrizableLCA.quotientObj B' (MetrizableLCA.cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)}
    (h : RelationPullbackDescendedFieldsInputsW352 A B A' B' f g f' g' iA iB descended) :
    DescendedQuotientFieldsW352 f g f' g' descended :=
  h.descended_fields

/-- W393's ordinary quotient-field certificate. -/
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

/--
Main W396 adapter: W352's concrete quotient-map fields instantiate W393's
ordinary descended quotient fields by definitional equality of quotient points.
-/
def ordinaryDescendedQuotientFieldsW393_of_descendedQuotientFieldsW352
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (h : DescendedQuotientFieldsW352
      (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y) ordinaryDescended) :
    OrdinaryDescendedQuotientFieldsW393 ordinaryDescended where
  injective := h.injective
  inducing := h.inducing
  closed_range := h.closed_range

/-- Instantiate W393 directly from the concrete W352 relation-pullback package. -/
def ordinaryDescendedQuotientFieldsW393_of_relationPullbackInputsW352
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {iA : wppOpDomain X ⟶ wppOpDomain Y}
    {iB : wppOpCodomain X ⟶ wppOpCodomain Y}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (h : RelationPullbackDescendedFieldsInputsW352
      (wppOpDomain X) (wppOpCodomain X) (wppOpDomain Y) (wppOpCodomain Y)
      (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
      iA iB ordinaryDescended) :
    OrdinaryDescendedQuotientFieldsW393 ordinaryDescended :=
  ordinaryDescendedQuotientFieldsW393_of_descendedQuotientFieldsW352 h.to_descended_fields

/-- W381-shaped ordinary field boundary used by the transported consumer. -/
structure OrdinaryRelationPullbackDescendedFieldsW381
    (ordinarySource ordinaryTarget : MetrizableLCA.{0})
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) : Prop where
  injective : Function.Injective (ordinaryDescended : ordinarySource → ordinaryTarget)
  inducing : IsInducing (ordinaryDescended : ordinarySource → ordinaryTarget)
  closed_range : IsClosed (Set.range (ordinaryDescended : ordinarySource → ordinaryTarget))

/-- Repackage W393 as the W381 ordinary relation-pullback field boundary. -/
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

/-- Checked point-isomorphism input package. -/
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

/-- Canonical transported descended map obtained by point-isomorphism conjugacy. -/
def transportedDescendedByPointIsoConjugacyW390
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    (wppOpTransportedConcreteQuotientCocone X).pt ⟶
      (wppOpTransportedConcreteQuotientCocone Y).pt :=
  hiso.source_point_iso.inv ≫ ordinaryDescended ≫ hiso.target_point_iso.hom

/-- The canonical transported descended map satisfies the pointwise conjugacy formula. -/
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
      (transportedDescendedByPointIsoConjugacyW390 hiso ordinaryDescended) where
  source_point_iso := hiso.source_point_iso
  target_point_iso := hiso.target_point_iso
  ordinary_fields := hfields
  transported_descended_conjugacy :=
    transportedDescendedByPointIsoConjugacyW390_pointwise hiso ordinaryDescended

/-- W396 consumer: concrete W352 quotient-map fields feed W390's canonical package. -/
def descendedQuotientFieldsW352_to_pointIsoConjugacyPackageW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (hfields : DescendedQuotientFieldsW352
      (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y) ordinaryDescended) :
    TransportedPointIsoConjugacyPackageW384
      (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
      ordinaryDescended
      (transportedDescendedByPointIsoConjugacyW390 hiso ordinaryDescended) :=
  transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384
    hiso
    (ordinaryDescendedQuotientFieldsW393_to_w381
      (ordinaryDescendedQuotientFieldsW393_of_descendedQuotientFieldsW352 hfields))

/-- W396 consumer directly from concrete W352 relation-pullback inputs. -/
def relationPullbackInputsW352_to_pointIsoConjugacyPackageW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    {iA : wppOpDomain X ⟶ wppOpDomain Y}
    {iB : wppOpCodomain X ⟶ wppOpCodomain Y}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    (h : RelationPullbackDescendedFieldsInputsW352
      (wppOpDomain X) (wppOpCodomain X) (wppOpDomain Y) (wppOpCodomain Y)
      (wppOpLeft X) (wppOpRight X) (wppOpLeft Y) (wppOpRight Y)
      iA iB ordinaryDescended) :
    TransportedPointIsoConjugacyPackageW384
      (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
      ordinaryDescended
      (transportedDescendedByPointIsoConjugacyW390 hiso ordinaryDescended) :=
  descendedQuotientFieldsW352_to_pointIsoConjugacyPackageW384 hiso h.to_descended_fields

/-- Remaining concrete inputs after W396. -/
def remainingOrdinaryDescendedFieldsInputsFromW352W396 : List String :=
  ["W352 DescendedQuotientFieldsW352.injective for the concrete ordinary descended quotient map",
    "W352 DescendedQuotientFieldsW352.inducing for the concrete ordinary descended quotient map",
    "W352 DescendedQuotientFieldsW352.closed_range for the concrete ordinary descended quotient map"]

theorem remainingOrdinaryDescendedFieldsInputsFromW352W396_count :
    remainingOrdinaryDescendedFieldsInputsFromW352W396.length = 3 := rfl

/-- Declaration names exported by this support file. -/
def w396SupportDeclarationNames : List String :=
  ["DescendedQuotientFieldsW352",
    "RelationPullbackDescendedFieldsInputsW352",
    "ordinaryDescendedQuotientFieldsW393_of_descendedQuotientFieldsW352",
    "ordinaryDescendedQuotientFieldsW393_of_relationPullbackInputsW352",
    "descendedQuotientFieldsW352_to_pointIsoConjugacyPackageW384",
    "relationPullbackInputsW352_to_pointIsoConjugacyPackageW384",
    "remainingOrdinaryDescendedFieldsInputsFromW352W396"]

theorem w396SupportDeclarationNames_count :
    w396SupportDeclarationNames.length = 7 := rfl

/-- Machine-readable state for this checked W396 support file. -/
structure WppOpLeftLcaOrdinaryDescendedFieldsFromW352V370StateW396 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  ordinaryDescendedFieldsFromW352Result : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaOrdinaryDescendedFieldsFromW352V370StateW396 :
    WppOpLeftLcaOrdinaryDescendedFieldsFromW352V370StateW396 where
  seed := "crimson-quartz-7391"
  checkedFacts :=
    ["proved W352 concrete descended quotient fields instantiate W393 ordinary descended quotient fields",
      "proved W352 relation-pullback input package exposes the exact W352 quotient-map fields needed by W393",
      "provided consumers from both W352 field and W352 relation-pullback packages into W390's canonical point-isomorphism transported package"]
  remainingInputs := remainingOrdinaryDescendedFieldsInputsFromW352W396
  ordinaryDescendedFieldsFromW352Result := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaOrdinaryDescendedFieldsFromW352V370StateW396_productSuccess :
    currentWppOpLeftLcaOrdinaryDescendedFieldsFromW352V370StateW396.productSuccessClaimed = false := rfl

section Checks

#check wppOpOrdinaryQuotientPoint
#check DescendedQuotientFieldsW352
#check RelationPullbackDescendedFieldsInputsW352
#check RelationPullbackDescendedFieldsInputsW352.to_descended_fields
#check OrdinaryDescendedQuotientFieldsW393
#check ordinaryDescendedQuotientFieldsW393_of_descendedQuotientFieldsW352
#check ordinaryDescendedQuotientFieldsW393_of_relationPullbackInputsW352
#check transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384
#check descendedQuotientFieldsW352_to_pointIsoConjugacyPackageW384
#check relationPullbackInputsW352_to_pointIsoConjugacyPackageW384
#check remainingOrdinaryDescendedFieldsInputsFromW352W396
#check remainingOrdinaryDescendedFieldsInputsFromW352W396_count
#check w396SupportDeclarationNames
#check w396SupportDeclarationNames_count
#check currentWppOpLeftLcaOrdinaryDescendedFieldsFromW352V370StateW396
#check currentWppOpLeftLcaOrdinaryDescendedFieldsFromW352V370StateW396_productSuccess

end Checks

end WppOpLeftLcaOrdinaryDescendedFieldsFromW352V370SupportW396

end LeanLCAExactChallenge
