import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W366: transported descended-leg support for the left-LCA concrete quotient route.

This standalone audit file carries forward the W362 transported concrete quotient
cocone package and isolates the exact input still needed to turn the ordinary
W357 descended quotient projection equations into W354-shaped transported cocone
leg equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaTransportedDescendedLegV369SupportW366

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

variable {A B A' B' : MetrizableLCA.{0}}

/-- Concrete quotient cofork for a parallel pair, presented as the cokernel of `f - g`. -/
def concreteQuotientCofork (f g : A ⟶ B) : Cofork f g :=
  Preadditive.coforkOfCokernelCofork
    (CokernelCofork.ofπ (cokernelπ (f - g)) (comp_cokernelπ (f - g)))

@[simp]
theorem concreteQuotientCofork_π (f g : A ⟶ B) :
    (concreteQuotientCofork f g).π = cokernelπ (f - g) := by
  simp [concreteQuotientCofork]

/-- The concrete quotient cofork is a colimit by the local cokernel construction. -/
def concreteQuotientCoforkIsColimit (f g : A ⟶ B) :
    IsColimit (concreteQuotientCofork f g) :=
  Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsColimit (f - g))

/-- Source relation maps forward to the target relation under compatible squares. -/
theorem concreteQuotient_relationForward
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
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

/-- Kernel condition needed to descend the component map through quotient objects. -/
theorem concreteQuotient_targetKernel_le
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    cokernelSubgroup (f - g) ≤
      (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.toAddMonoidHom.ker := by
  intro b hb
  change ((iB b : B') : B' ⧸ cokernelSubgroup (f' - g')) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact concreteQuotient_relationForward iA iB hsquare_left hsquare_right b hb

/-- The concrete descended quotient map induced by compatible component squares. -/
def concreteDescendedQuotientMap
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientObj B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ⟶
      quotientObj B' (cokernelSubgroup (f' - g')) (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (concreteQuotient_targetKernel_le iA iB hsquare_left hsquare_right)

/-- The descended quotient map is compatible with the concrete quotient projections. -/
theorem concreteDescendedQuotientMap_quotient_compat
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    quotientMap B (cokernelSubgroup (f - g)) (AddSubgroup.isClosed_topologicalClosure _) ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right =
      iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _) :=
  quotientLift_quotientMap B (cokernelSubgroup (f - g))
    (AddSubgroup.isClosed_topologicalClosure _)
    (iB ≫ quotientMap B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _))
    (concreteQuotient_targetKernel_le iA iB hsquare_left hsquare_right)

/-- The target-object cofork leg equation needed by the descended certificate route. -/
theorem concreteDescendedQuotientMap_cofork_π
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    (concreteQuotientCofork f g).π ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right =
      iB ≫ (concreteQuotientCofork f' g').π := by
  simpa using
    concreteDescendedQuotientMap_quotient_compat iA iB hsquare_left hsquare_right

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

/--
Boundary naming the exact equation not yet derived from W357: after expanding
`wppOpTransportedConcreteQuotientCocone_ι_app`, the ordinary projection equation
must be whiskered through `wppOpWhiskeredDiagramIso` and rewritten against
`α.app j` for every object `j`.
-/
structure TransportedDescendedLegBoundary
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y) : Type 3 where
  ordinary_projection_equation_available : Bool
  transported_cocone_leg_formula_available : Bool
  missing_whiskered_naturality_equation : String
  produces_w354_constructor :
    ∀ legs : TransportedDescendedLegEquations X Y α,
      RelationPullbackDescendedFieldsInputsW354Shape
        (wppOpTransportedConcreteQuotientCocone X)
        (wppOpTransportedConcreteQuotientCocone Y)
        legs.descended →
      TransportedConcreteQuotientW354Inputs X Y α
        (wppOpTransportedConcreteQuotientCocone X)
        (wppOpTransportedConcreteQuotientCocone Y)

/-- Canonical checked boundary for the transported descended-leg gap. -/
def transportedDescendedLegBoundary
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y) :
    TransportedDescendedLegBoundary X Y α where
  ordinary_projection_equation_available := true
  transported_cocone_leg_formula_available := true
  missing_whiskered_naturality_equation :=
    "derive, for every j, the equality obtained by moving the ordinary W357 projection equation through (wppOpWhiskeredDiagramIso X).symm.hom.app j and (wppOpWhiskeredDiagramIso Y).symm.hom.app j, then rewriting the result to α.app j"
  produces_w354_constructor := by
    intro legs relation_inputs
    exact transportedConcreteQuotientW354Inputs_of_transportedDescendedLegEquations
      (wppOpTransportedConcreteQuotientCoconeIsColimit X)
      (wppOpTransportedConcreteQuotientCoconeIsColimit Y)
      legs relation_inputs

/-- Declaration names exported by this support file. -/
def w366SupportDeclarationNames : List String :=
  ["ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_π",
    "wppOpWhiskeredDiagramIso",
    "wppOpTransportedConcreteQuotientCocone_ι_app",
    "TransportedConcreteQuotientW354Inputs",
    "TransportedDescendedLegEquations",
    "transportedConcreteQuotientW354Inputs_of_transportedDescendedLegEquations",
    "TransportedDescendedLegBoundary",
    "transportedDescendedLegBoundary"]

theorem w366SupportDeclarationNames_count :
    w366SupportDeclarationNames.length = 8 := rfl

/-- Machine-readable state for this checked W366 support file. -/
structure WppOpLeftLcaTransportedDescendedLegV369StateW366 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaTransportedDescendedLegV369StateW366 :
    WppOpLeftLcaTransportedDescendedLegV369StateW366 where
  seed := "W366-saffron-hinge-714923"
  checkedFacts :=
    ["ordinary W357 concrete descended projection equation is copied and checked",
      "W362 counit diagram isomorphism and transported concrete quotient cocone are copied and checked",
      "a W354 constructor consumes transported descended leg equations plus relation-pullback fields",
      "the boundary names the missing objectwise whiskered naturality equation"]
  remainingInputs :=
    ["prove the objectwise whiskered naturality equation for every WalkingParallelPairᵒᵖ object",
      "use that equation to instantiate TransportedDescendedLegEquations from the ordinary W357 projection equation",
      "supply the transported relation-pullback topological fields"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaTransportedDescendedLegV369StateW366_productSuccess :
    currentWppOpLeftLcaTransportedDescendedLegV369StateW366.productSuccessClaimed = false := rfl

section Checks

#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_π
#check wppOpWhiskeredDiagramIso
#check wppOpTransportedConcreteQuotientCocone_ι_app
#check TransportedConcreteQuotientW354Inputs
#check TransportedDescendedLegEquations
#check transportedConcreteQuotientW354Inputs_of_transportedDescendedLegEquations
#check TransportedDescendedLegBoundary
#check transportedDescendedLegBoundary
#check w366SupportDeclarationNames
#check w366SupportDeclarationNames_count
#check currentWppOpLeftLcaTransportedDescendedLegV369StateW366
#check currentWppOpLeftLcaTransportedDescendedLegV369StateW366_productSuccess

end Checks

end WppOpLeftLcaTransportedDescendedLegV369SupportW366

end LeanLCAExactChallenge
