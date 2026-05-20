import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W372: checked proof support for the W369 whiskered naturality boundary.

The audit files under `audit/blockers` are checked directly with `lake env lean`,
so this file repeats the small W369 boundary needed to provide a standalone
consumer theorem with the naturality hypothesis discharged.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaWhiskeredNaturalityProofV370SupportW372

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

/-- Counit-based diagram isomorphism from the whiskered W357 diagram back to `X`. -/
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

/-- Transport formula for the cocone leg at an object of `WalkingParallelPairᵒᵖ`. -/
theorem wppOpTransportedConcreteQuotientCocone_ι_app
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (j : WalkingParallelPairᵒᵖ) :
    (wppOpTransportedConcreteQuotientCocone X).ι.app j =
      (wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
        (wppOpWhiskeredConcreteQuotientCocone X).ι.app j :=
  rfl

/-- Natural transformation obtained by whiskering a WPP-op natural transformation through the inverse equivalence. -/
def wppOpInverseWhiskeredNatTrans
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    walkingParallelPairOpEquiv.inverse ⋙ wppOpOrdinaryDiagram X ⟶
      walkingParallelPairOpEquiv.inverse ⋙ wppOpOrdinaryDiagram Y :=
  Functor.whiskerLeft walkingParallelPairOpEquiv.inverse
    (Functor.whiskerLeft walkingParallelPairOpEquiv.functor α)

/-- The objectwise naturality square needed to compare ordinary and transported diagrams. -/
def WhiskeredNaturalityEquation
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ,
    (wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
        (wppOpInverseWhiskeredNatTrans α).app j =
      α.app j ≫ (wppOpWhiskeredDiagramIso Y).symm.hom.app j

/-- The W369 whiskered naturality boundary follows by naturality of the equivalence counit. -/
theorem whiskeredNaturalityEquation
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y) :
    WhiskeredNaturalityEquation X Y α := by
  intro j
  dsimp [WhiskeredNaturalityEquation, wppOpWhiskeredDiagramIso,
    wppOpInverseWhiskeredNatTrans]
  simp

/-- Topological relation-pullback fields in the same shape consumed by W354. -/
structure RelationPullbackDescendedFieldsInputsW354Shape
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/-- W354-ready data with source and target fixed to the transported concrete quotient cocones. -/
structure TransportedConcreteQuotientW354Inputs
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 2 where
  hcx : IsColimit cx
  hcy : IsColimit cy
  descended :
    (wppOpTransportedConcreteQuotientCocone X).pt ⟶
      (wppOpTransportedConcreteQuotientCocone Y).pt
  descended_leg :
    ∀ j : WalkingParallelPairᵒᵖ,
      (wppOpTransportedConcreteQuotientCocone X).ι.app j ≫ descended =
        α.app j ≫ (wppOpTransportedConcreteQuotientCocone Y).ι.app j
  relation_inputs :
    RelationPullbackDescendedFieldsInputsW354Shape
      (wppOpTransportedConcreteQuotientCocone X)
      (wppOpTransportedConcreteQuotientCocone Y)
      descended

/-- Pointwise transported leg data needed to consume the ordinary W357 projection equations. -/
structure TransportedDescendedLegEquations
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y) : Type 1 where
  descended :
    (wppOpTransportedConcreteQuotientCocone X).pt ⟶
      (wppOpTransportedConcreteQuotientCocone Y).pt
  ordinary_projection_equation_name : String
  transported_leg :
    ∀ j : WalkingParallelPairᵒᵖ,
      (wppOpTransportedConcreteQuotientCocone X).ι.app j ≫ descended =
        α.app j ≫ (wppOpTransportedConcreteQuotientCocone Y).ι.app j

/--
The ordinary whiskered projection equation plus objectwise whiskered naturality
implies the transported W366 leg equation.
-/
theorem transported_leg_of_ordinary_projection_of_whiskered_naturality
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {descended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt}
    (hordinary :
      ∀ j : WalkingParallelPairᵒᵖ,
        (wppOpWhiskeredConcreteQuotientCocone X).ι.app j ≫ descended =
          (wppOpInverseWhiskeredNatTrans α).app j ≫
            (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j)
    (hnaturality : WhiskeredNaturalityEquation X Y α) :
    ∀ j : WalkingParallelPairᵒᵖ,
      (wppOpTransportedConcreteQuotientCocone X).ι.app j ≫ descended =
        α.app j ≫ (wppOpTransportedConcreteQuotientCocone Y).ι.app j := by
  intro j
  rw [wppOpTransportedConcreteQuotientCocone_ι_app X j,
    wppOpTransportedConcreteQuotientCocone_ι_app Y j]
  calc
    ((wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
          (wppOpWhiskeredConcreteQuotientCocone X).ι.app j) ≫ descended =
        (wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
        ((wppOpWhiskeredConcreteQuotientCocone X).ι.app j ≫ descended) := by
          simp [Category.assoc]
    _ = (wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
        ((wppOpInverseWhiskeredNatTrans α).app j ≫
          (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j) := by
          exact congrArg
            (fun f => (wppOpWhiskeredDiagramIso X).symm.hom.app j ≫ f)
            (hordinary j)
    _ = ((wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
        (wppOpInverseWhiskeredNatTrans α).app j) ≫
          (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j := by
          simp [Category.assoc]
    _ = (α.app j ≫ (wppOpWhiskeredDiagramIso Y).symm.hom.app j) ≫
          (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j := by
          exact congrArg
            (fun f => f ≫ (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j)
            (hnaturality j)
    _ = α.app j ≫
        ((wppOpWhiskeredDiagramIso Y).symm.hom.app j ≫
          (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j) := by
          simp [Category.assoc]

/-- Constructor for W362's W354 package once the transported leg equations are supplied. -/
def transportedConcreteQuotientW354Inputs_of_transportedDescendedLegEquations
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx) (hcy : IsColimit cy)
    (legs : TransportedDescendedLegEquations X Y α)
    (relation_inputs :
      RelationPullbackDescendedFieldsInputsW354Shape
        (wppOpTransportedConcreteQuotientCocone X)
        (wppOpTransportedConcreteQuotientCocone Y)
        legs.descended) :
    TransportedConcreteQuotientW354Inputs X Y α cx cy where
  hcx := hcx
  hcy := hcy
  descended := legs.descended
  descended_leg := legs.transported_leg
  relation_inputs := relation_inputs

/-- Ordinary W357 projection data can be packaged as W366 transported leg data after whiskered naturality. -/
def transportedDescendedLegEquations_of_ordinary_projection
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (descended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt)
    (ordinary_projection_equation_name : String)
    (hordinary :
      ∀ j : WalkingParallelPairᵒᵖ,
        (wppOpWhiskeredConcreteQuotientCocone X).ι.app j ≫ descended =
          (wppOpInverseWhiskeredNatTrans α).app j ≫
            (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j) :
    TransportedDescendedLegEquations X Y α where
  descended := descended
  ordinary_projection_equation_name := ordinary_projection_equation_name
  transported_leg :=
    transported_leg_of_ordinary_projection_of_whiskered_naturality hordinary
      (whiskeredNaturalityEquation X Y α)

/-- Consumer theorem linking ordinary projection equations directly to the W354 constructor. -/
def transportedConcreteQuotientW354Inputs_of_ordinary_projection
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx) (hcy : IsColimit cy)
    (descended :
      (wppOpTransportedConcreteQuotientCocone X).pt ⟶
        (wppOpTransportedConcreteQuotientCocone Y).pt)
    (ordinary_projection_equation_name : String)
    (hordinary :
      ∀ j : WalkingParallelPairᵒᵖ,
        (wppOpWhiskeredConcreteQuotientCocone X).ι.app j ≫ descended =
          (wppOpInverseWhiskeredNatTrans α).app j ≫
            (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j)
    (relation_inputs :
      RelationPullbackDescendedFieldsInputsW354Shape
        (wppOpTransportedConcreteQuotientCocone X)
        (wppOpTransportedConcreteQuotientCocone Y)
        descended) :
    TransportedConcreteQuotientW354Inputs X Y α cx cy :=
  transportedConcreteQuotientW354Inputs_of_transportedDescendedLegEquations hcx hcy
    (transportedDescendedLegEquations_of_ordinary_projection
      descended ordinary_projection_equation_name hordinary)
    relation_inputs

/-- Declaration names exported by this support file. -/
def w372SupportDeclarationNames : List String :=
  ["whiskeredNaturalityEquation",
    "transported_leg_of_ordinary_projection_of_whiskered_naturality",
    "transportedDescendedLegEquations_of_ordinary_projection",
    "transportedConcreteQuotientW354Inputs_of_ordinary_projection"]

theorem w372SupportDeclarationNames_count :
    w372SupportDeclarationNames.length = 4 := rfl

/-- Machine-readable state for this checked W372 support file. -/
structure WppOpLeftLcaWhiskeredNaturalityProofV370StateW372 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  objectwiseNaturalityResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaWhiskeredNaturalityProofV370StateW372 :
    WppOpLeftLcaWhiskeredNaturalityProofV370StateW372 where
  seed := "w372-left-lca-whiskered-naturality-20260520T212622Z-2dad6c73ff7b655c"
  checkedFacts :=
    ["proved WhiskeredNaturalityEquation X Y α from the concrete definitions of wppOpWhiskeredDiagramIso and wppOpInverseWhiskeredNatTrans",
      "removed the objectwise naturality hypothesis from the ordinary-projection-to-transported-leg packaging",
      "provided a W354-shaped consumer theorem whose remaining mathematical input is the ordinary whiskered projection equation plus topological relation fields"]
  remainingInputs :=
    ["supply the ordinary W357 whiskered projection equation",
      "supply the transported relation-pullback topological fields"]
  objectwiseNaturalityResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaWhiskeredNaturalityProofV370StateW372_productSuccess :
    currentWppOpLeftLcaWhiskeredNaturalityProofV370StateW372.productSuccessClaimed = false := rfl

section Checks

#check whiskeredNaturalityEquation
#check transported_leg_of_ordinary_projection_of_whiskered_naturality
#check transportedDescendedLegEquations_of_ordinary_projection
#check transportedConcreteQuotientW354Inputs_of_ordinary_projection
#check w372SupportDeclarationNames
#check w372SupportDeclarationNames_count
#check currentWppOpLeftLcaWhiskeredNaturalityProofV370StateW372
#check currentWppOpLeftLcaWhiskeredNaturalityProofV370StateW372_productSuccess

end Checks

end WppOpLeftLcaWhiskeredNaturalityProofV370SupportW372

end LeanLCAExactChallenge
