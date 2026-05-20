import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W387: transported quotient-point isomorphism support for W384.

This standalone audit file constructs the two point isomorphisms left open by
W384.  The ordinary quotient point is the W352-style quotient object
`quotientObj B (cokernelSubgroup (f - g))`, and the transported concrete
quotient cocone point reduces to the same object after the ordinary WPP diagram
is whiskered and precomposed back across the equivalence.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387

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

/--
Source point isomorphism from the W352 ordinary quotient point to W384's
transported concrete quotient cocone point.
-/
def transportedQuotientSourcePointIsoW387
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpOrdinaryQuotientPoint X ≅ (wppOpTransportedConcreteQuotientCocone X).pt :=
  Iso.refl _

/--
Target point isomorphism from the W352 ordinary quotient point to W384's
transported concrete quotient cocone point.
-/
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
Point-isomorphism and conjugacy package matching W384's boundary for the W352
ordinary quotient points and the transported concrete quotient cocone points.
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

/--
Checked W387 input package.  Its fields are exactly the two point
isomorphisms left open by W384.
-/
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

/--
Consumer: after W352 ordinary fields and the descended-map conjugacy are
supplied, W387's two concrete point isomorphisms build the W384 package.
-/
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

/-- Remaining non-point-isomorphism inputs after W387. -/
def remainingTransportedQuotientPointIsoInputsW387 : List String :=
  ["prove the pointwise descended-map conjugacy against W387's two point isomorphisms",
    "supply W352 ordinary descended quotient fields for the ordinary descended map"]

theorem remainingTransportedQuotientPointIsoInputsW387_count :
    remainingTransportedQuotientPointIsoInputsW387.length = 2 := rfl

/-- Declaration names exported by this support file. -/
def w387SupportDeclarationNames : List String :=
  ["wppOpOrdinaryQuotientPoint",
    "transportedQuotientSourcePointIsoW387",
    "transportedQuotientTargetPointIsoW387",
    "TransportedQuotientPointIsoInputsW387",
    "transportedQuotientPointIsoInputsW387",
    "transportedQuotientPointIsoInputs_to_pointIsoConjugacyPackageW384",
    "remainingTransportedQuotientPointIsoInputsW387"]

theorem w387SupportDeclarationNames_count :
    w387SupportDeclarationNames.length = 7 := rfl

/-- Machine-readable state for this checked W387 support file. -/
structure WppOpLeftLcaTransportedQuotientPointIsoV370StateW387 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  quotientPointIsoResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaTransportedQuotientPointIsoV370StateW387 :
    WppOpLeftLcaTransportedQuotientPointIsoV370StateW387 where
  seed := "w387-20260520T220242Z-g8p0565yxx78"
  checkedFacts :=
    ["named the W352 ordinary quotient point for a WPP-op diagram",
      "constructed the source point isomorphism to the transported concrete quotient cocone point",
      "constructed the target point isomorphism to the transported concrete quotient cocone point",
      "exposed a two-field input package containing exactly those point isomorphisms",
      "provided a consumer that builds the W384-shaped point-isomorphism conjugacy package"]
  remainingInputs := remainingTransportedQuotientPointIsoInputsW387
  quotientPointIsoResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaTransportedQuotientPointIsoV370StateW387_productSuccess :
    currentWppOpLeftLcaTransportedQuotientPointIsoV370StateW387.productSuccessClaimed = false := rfl

section Checks

#check wppOpTransportedConcreteQuotientCocone
#check wppOpTransportedConcreteQuotientCoconeIsColimit
#check wppOpOrdinaryQuotientPoint
#check transportedQuotientSourcePointIsoW387
#check transportedQuotientTargetPointIsoW387
#check TransportedQuotientPointIsoInputsW387
#check transportedQuotientPointIsoInputsW387
#check transportedQuotientPointIsoInputs_to_pointIsoConjugacyPackageW384
#check remainingTransportedQuotientPointIsoInputsW387
#check remainingTransportedQuotientPointIsoInputsW387_count
#check w387SupportDeclarationNames
#check w387SupportDeclarationNames_count
#check currentWppOpLeftLcaTransportedQuotientPointIsoV370StateW387
#check currentWppOpLeftLcaTransportedQuotientPointIsoV370StateW387_productSuccess

end Checks

end WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387

end LeanLCAExactChallenge
