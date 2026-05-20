import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W369: objectwise whiskered naturality support for the left-LCA concrete quotient route.

This standalone audit file isolates the exact categorical square needed to turn
the ordinary W357 descended quotient projection equation on the inverse-whiskered
diagram into the W366 transported cocone leg equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaWhiskeredNaturalityV370SupportW369

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
  have hcalc :
      ((wppOpWhiskeredDiagramIso X).symm.hom.app j ≫
            (wppOpWhiskeredConcreteQuotientCocone X).ι.app j) ≫ descended =
        α.app j ≫
          ((wppOpWhiskeredDiagramIso Y).symm.hom.app j ≫
            (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j) := by
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
  exact hcalc

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
            (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j)
    (hnaturality : WhiskeredNaturalityEquation X Y α) :
    TransportedDescendedLegEquations X Y α where
  descended := descended
  ordinary_projection_equation_name := ordinary_projection_equation_name
  transported_leg :=
    transported_leg_of_ordinary_projection_of_whiskered_naturality hordinary hnaturality

/-- Consumer theorem linking the W369 boundary directly to the W366-shaped W354 constructor. -/
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
    (hnaturality : WhiskeredNaturalityEquation X Y α)
    (relation_inputs :
      RelationPullbackDescendedFieldsInputsW354Shape
        (wppOpTransportedConcreteQuotientCocone X)
        (wppOpTransportedConcreteQuotientCocone Y)
        descended) :
    TransportedConcreteQuotientW354Inputs X Y α cx cy :=
  transportedConcreteQuotientW354Inputs_of_transportedDescendedLegEquations hcx hcy
    (transportedDescendedLegEquations_of_ordinary_projection
      descended ordinary_projection_equation_name hordinary hnaturality)
    relation_inputs

/-- Declaration names exported by this support file. -/
def w369SupportDeclarationNames : List String :=
  ["wppOpInverseWhiskeredNatTrans",
    "WhiskeredNaturalityEquation",
    "transported_leg_of_ordinary_projection_of_whiskered_naturality",
    "transportedDescendedLegEquations_of_ordinary_projection",
    "transportedConcreteQuotientW354Inputs_of_ordinary_projection"]

theorem w369SupportDeclarationNames_count :
    w369SupportDeclarationNames.length = 5 := rfl

/-- Machine-readable state for this checked W369 support file. -/
structure WppOpLeftLcaWhiskeredNaturalityV370StateW369 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  objectwiseNaturalityResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaWhiskeredNaturalityV370StateW369 :
    WppOpLeftLcaWhiskeredNaturalityV370StateW369 where
  seed := "w369-left-lca-whiskered-naturality-v370-27669-20260520T211851Z"
  checkedFacts :=
    ["defined the inverse-equivalence-whiskered natural transformation attached to α",
      "stated the exact objectwise whiskered naturality equation through the transported counit isomorphisms",
      "proved that ordinary whiskered projection compatibility plus that equation gives W366 transported leg equations",
      "provided a consumer into the W366-shaped transportedConcreteQuotientW354Inputs constructor"]
  remainingInputs :=
    ["prove WhiskeredNaturalityEquation for wppOpInverseWhiskeredNatTrans α from the concrete definition of wppOpWhiskeredDiagramIso",
      "supply the transported relation-pullback topological fields"]
  objectwiseNaturalityResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaWhiskeredNaturalityV370StateW369_productSuccess :
    currentWppOpLeftLcaWhiskeredNaturalityV370StateW369.productSuccessClaimed = false := rfl

section Checks

#check wppOpInverseWhiskeredNatTrans
#check WhiskeredNaturalityEquation
#check transported_leg_of_ordinary_projection_of_whiskered_naturality
#check transportedDescendedLegEquations_of_ordinary_projection
#check transportedConcreteQuotientW354Inputs_of_ordinary_projection
#check w369SupportDeclarationNames
#check w369SupportDeclarationNames_count
#check currentWppOpLeftLcaWhiskeredNaturalityV370StateW369
#check currentWppOpLeftLcaWhiskeredNaturalityV370StateW369_productSuccess

end Checks

end WppOpLeftLcaWhiskeredNaturalityV370SupportW369

end LeanLCAExactChallenge
