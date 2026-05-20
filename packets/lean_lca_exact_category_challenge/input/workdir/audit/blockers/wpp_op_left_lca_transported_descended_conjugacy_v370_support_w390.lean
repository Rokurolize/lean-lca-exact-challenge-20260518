import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W390: transported descended-map conjugacy support for W387/W384.

This standalone audit file sharpens W387's remaining descended-map boundary.
It records the pointwise equality as a one-field input for arbitrary transported
descended maps, and proves the equality by `rfl` for the canonical transported
map obtained by conjugating the ordinary W352 descended map across W387's point
isomorphisms.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390

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

/--
Canonical transported descended map obtained by conjugating an ordinary W352
descended map across W387's source and target point isomorphisms.
-/
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

/--
Single-field W390 input for an arbitrary transported descended map.  The field
is exactly W387's remaining pointwise descended-map equality.
-/
structure TransportedDescendedConjugacyInputW390
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y)
    (transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt) : Type 1 where
  transported_descended_conjugacy :
    ∀ x : (wppOpTransportedConcreteQuotientCocone X).pt,
      transportedDescended x =
        hiso.target_point_iso.hom (ordinaryDescended (hiso.source_point_iso.inv x))

/-- The canonical conjugated transported descended map supplies the one-field W390 input. -/
def transportedDescendedConjugacyInputW390_of_pointIsoConjugacy
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    TransportedDescendedConjugacyInputW390 hiso ordinaryDescended
      (transportedDescendedByPointIsoConjugacyW390 hiso ordinaryDescended) where
  transported_descended_conjugacy :=
    transportedDescendedByPointIsoConjugacyW390_pointwise hiso ordinaryDescended

/--
Consumer: W390's one-field conjugacy input plus W352 ordinary descended fields
builds W387/W384's point-isomorphism conjugacy package.
-/
def transportedDescendedConjugacyInputW390_to_pointIsoConjugacyPackageW384
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y}
    {transportedDescended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (hiso : TransportedQuotientPointIsoInputsW387 X Y)
    (hconj :
      TransportedDescendedConjugacyInputW390 hiso ordinaryDescended transportedDescended)
    (hfields :
      OrdinaryRelationPullbackDescendedFieldsW381
        (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
        ordinaryDescended) :
    TransportedPointIsoConjugacyPackageW384
      (wppOpOrdinaryQuotientPoint X) (wppOpOrdinaryQuotientPoint Y)
      ordinaryDescended transportedDescended :=
  transportedQuotientPointIsoInputs_to_pointIsoConjugacyPackageW384
    hiso hfields hconj.transported_descended_conjugacy

/--
Consumer for the canonical conjugated descended map.  After this support file,
the only mathematical input to form the W384 package for that map is the W352
ordinary descended quotient fields.
-/
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
  transportedDescendedConjugacyInputW390_to_pointIsoConjugacyPackageW384
    hiso
    (transportedDescendedConjugacyInputW390_of_pointIsoConjugacy hiso ordinaryDescended)
    hfields

/-- Remaining external inputs after W390 discharges the canonical pointwise conjugacy. -/
def remainingTransportedDescendedConjugacyInputsW390 : List String :=
  ["supply W352 ordinary descended quotient fields for the ordinary descended map",
    "identify any externally supplied transported descended map with transportedDescendedByPointIsoConjugacyW390, or provide TransportedDescendedConjugacyInputW390 for that map"]

theorem remainingTransportedDescendedConjugacyInputsW390_count :
    remainingTransportedDescendedConjugacyInputsW390.length = 2 := rfl

/-- Declaration names exported by this support file. -/
def w390SupportDeclarationNames : List String :=
  ["transportedDescendedByPointIsoConjugacyW390",
    "transportedDescendedByPointIsoConjugacyW390_pointwise",
    "TransportedDescendedConjugacyInputW390",
    "transportedDescendedConjugacyInputW390_of_pointIsoConjugacy",
    "transportedDescendedConjugacyInputW390_to_pointIsoConjugacyPackageW384",
    "transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384",
    "remainingTransportedDescendedConjugacyInputsW390"]

theorem w390SupportDeclarationNames_count :
    w390SupportDeclarationNames.length = 7 := rfl

/-- Machine-readable state for this checked W390 support file. -/
structure WppOpLeftLcaTransportedDescendedConjugacyV370StateW390 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  transportedDescendedConjugacyResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaTransportedDescendedConjugacyV370StateW390 :
    WppOpLeftLcaTransportedDescendedConjugacyV370StateW390 where
  seed := "6860e7c8a464e5db36a411125b365a73"
  checkedFacts :=
    ["defined the canonical transported descended map by point-isomorphism conjugacy",
      "proved the canonical transported descended map satisfies W387's pointwise equality by reduction",
      "exposed TransportedDescendedConjugacyInputW390 with exactly the pointwise equality field",
      "provided a consumer from the W390 input and W352 ordinary fields into the W384 package",
      "provided a canonical consumer leaving only W352 ordinary descended quotient fields for the conjugated map"]
  remainingInputs := remainingTransportedDescendedConjugacyInputsW390
  transportedDescendedConjugacyResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaTransportedDescendedConjugacyV370StateW390_productSuccess :
    currentWppOpLeftLcaTransportedDescendedConjugacyV370StateW390.productSuccessClaimed = false := rfl

section Checks

#check transportedQuotientPointIsoInputs_to_pointIsoConjugacyPackageW384
#check transportedDescendedByPointIsoConjugacyW390
#check transportedDescendedByPointIsoConjugacyW390_pointwise
#check TransportedDescendedConjugacyInputW390
#check transportedDescendedConjugacyInputW390_of_pointIsoConjugacy
#check transportedDescendedConjugacyInputW390_to_pointIsoConjugacyPackageW384
#check transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384
#check remainingTransportedDescendedConjugacyInputsW390
#check remainingTransportedDescendedConjugacyInputsW390_count
#check w390SupportDeclarationNames
#check w390SupportDeclarationNames_count
#check currentWppOpLeftLcaTransportedDescendedConjugacyV370StateW390
#check currentWppOpLeftLcaTransportedDescendedConjugacyV370StateW390_productSuccess

end Checks

end WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390

end LeanLCAExactChallenge
