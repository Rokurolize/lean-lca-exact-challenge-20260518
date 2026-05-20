import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W375: ordinary whiskered projection support for the left-LCA concrete quotient route.

This standalone audit file packages W357's ordinary descended quotient projection
equations into the ordinary whiskered projection hypothesis consumed by W372, and
then exposes a direct W354-shaped consumer theorem.  The only remaining inputs
are the transported relation-pullback topological fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaOrdinaryWhiskeredProjectionV370SupportW375

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

/-- The ordinary natural transformation obtained from a WPP-op natural transformation. -/
def wppOpOrdinaryNatTrans
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y :=
  Functor.whiskerLeft walkingParallelPairOpEquiv.functor α

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

/-- The source-object cofork leg equation obtained from the left square. -/
theorem concreteDescendedQuotientMap_cofork_leftLeg
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    (f ≫ (concreteQuotientCofork f g).π) ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right =
      iA ≫ (f' ≫ (concreteQuotientCofork f' g').π) := by
  calc
    (f ≫ (concreteQuotientCofork f g).π) ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right =
      f ≫ ((concreteQuotientCofork f g).π ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right) := by
        simp [Category.assoc]
    _ = f ≫ (iB ≫ (concreteQuotientCofork f' g').π) := by
        exact congrArg (fun q => f ≫ q)
          (concreteDescendedQuotientMap_cofork_π iA iB hsquare_left hsquare_right)
    _ = (f ≫ iB) ≫ (concreteQuotientCofork f' g').π := by
        rfl
    _ = (iA ≫ f') ≫ (concreteQuotientCofork f' g').π := by
        rw [hsquare_left]
    _ = iA ≫ (f' ≫ (concreteQuotientCofork f' g').π) := by
        simp [Category.assoc]

/-- The source-object cofork leg can equally be expressed using the right square. -/
theorem concreteDescendedQuotientMap_cofork_rightLeg
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    (g ≫ (concreteQuotientCofork f g).π) ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right =
      iA ≫ (g' ≫ (concreteQuotientCofork f' g').π) := by
  calc
    (g ≫ (concreteQuotientCofork f g).π) ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right =
      g ≫ ((concreteQuotientCofork f g).π ≫
        concreteDescendedQuotientMap iA iB hsquare_left hsquare_right) := by
        simp [Category.assoc]
    _ = g ≫ (iB ≫ (concreteQuotientCofork f' g').π) := by
        exact congrArg (fun q => g ≫ q)
          (concreteDescendedQuotientMap_cofork_π iA iB hsquare_left hsquare_right)
    _ = (g ≫ iB) ≫ (concreteQuotientCofork f' g').π := by
        rfl
    _ = (iA ≫ g') ≫ (concreteQuotientCofork f' g').π := by
        rw [hsquare_right]
    _ = iA ≫ (g' ≫ (concreteQuotientCofork f' g').π) := by
        simp [Category.assoc]

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
    (wppOpOrdinaryNatTrans α)

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
    wppOpInverseWhiskeredNatTrans, wppOpOrdinaryNatTrans]
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

/-- Naturality of the ordinary left component square. -/
theorem wppOpOrdinaryNatTrans_naturality_left
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ (wppOpOrdinaryNatTrans α).app WalkingParallelPair.one =
      (wppOpOrdinaryNatTrans α).app WalkingParallelPair.zero ≫ wppOpLeft Y := by
  simp [wppOpLeft, wppOpOrdinaryNatTrans]

/-- Naturality of the ordinary right component square. -/
theorem wppOpOrdinaryNatTrans_naturality_right
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ (wppOpOrdinaryNatTrans α).app WalkingParallelPair.one =
      (wppOpOrdinaryNatTrans α).app WalkingParallelPair.zero ≫ wppOpRight Y := by
  simp [wppOpRight, wppOpOrdinaryNatTrans]

/-- Descended quotient map induced by the ordinary components of a WPP-op natural transformation. -/
def wppOpOrdinaryConcreteDescendedQuotientMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    (wppOpWhiskeredConcreteQuotientCocone X).pt ⟶
      (wppOpWhiskeredConcreteQuotientCocone Y).pt :=
  ConcreteMetrizableLCA.concreteDescendedQuotientMap
    ((wppOpOrdinaryNatTrans α).app WalkingParallelPair.zero)
    ((wppOpOrdinaryNatTrans α).app WalkingParallelPair.one)
    (wppOpOrdinaryNatTrans_naturality_left α)
    (wppOpOrdinaryNatTrans_naturality_right α)

/-- Ordinary source-object projection equation obtained from W357's left-leg theorem. -/
theorem ordinaryConcreteDescendedQuotientMap_zero
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    (wppOpConcreteQuotientCoconeOnOrdinary X).ι.app WalkingParallelPair.zero ≫
        wppOpOrdinaryConcreteDescendedQuotientMap α =
      (wppOpOrdinaryNatTrans α).app WalkingParallelPair.zero ≫
        (wppOpConcreteQuotientCoconeOnOrdinary Y).ι.app WalkingParallelPair.zero := by
  simpa [wppOpConcreteQuotientCoconeOnOrdinary, wppOpOrdinaryConcreteDescendedQuotientMap,
    wppOpLeft, wppOpRight, Category.assoc] using
    ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_leftLeg
      ((wppOpOrdinaryNatTrans α).app WalkingParallelPair.zero)
      ((wppOpOrdinaryNatTrans α).app WalkingParallelPair.one)
      (wppOpOrdinaryNatTrans_naturality_left α)
      (wppOpOrdinaryNatTrans_naturality_right α)

/-- Ordinary target-object projection equation obtained from W357's cofork-π theorem. -/
theorem ordinaryConcreteDescendedQuotientMap_one
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    (wppOpConcreteQuotientCoconeOnOrdinary X).ι.app WalkingParallelPair.one ≫
        wppOpOrdinaryConcreteDescendedQuotientMap α =
      (wppOpOrdinaryNatTrans α).app WalkingParallelPair.one ≫
        (wppOpConcreteQuotientCoconeOnOrdinary Y).ι.app WalkingParallelPair.one := by
  simpa [wppOpConcreteQuotientCoconeOnOrdinary, wppOpOrdinaryConcreteDescendedQuotientMap,
    wppOpLeft, wppOpRight] using
    ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_π
      ((wppOpOrdinaryNatTrans α).app WalkingParallelPair.zero)
      ((wppOpOrdinaryNatTrans α).app WalkingParallelPair.one)
      (wppOpOrdinaryNatTrans_naturality_left α)
      (wppOpOrdinaryNatTrans_naturality_right α)

/-- W357's ordinary projection equations as the objectwise whiskered equation consumed by W372. -/
theorem ordinaryWhiskeredProjectionEquation
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    ∀ j : WalkingParallelPairᵒᵖ,
      (wppOpWhiskeredConcreteQuotientCocone X).ι.app j ≫
          wppOpOrdinaryConcreteDescendedQuotientMap α =
        (wppOpInverseWhiskeredNatTrans α).app j ≫
          (wppOpWhiskeredConcreteQuotientCocone Y).ι.app j := by
  intro j
  induction j with
  | op j =>
      cases j
      · simpa [wppOpWhiskeredConcreteQuotientCocone, wppOpInverseWhiskeredNatTrans,
          wppOpOrdinaryNatTrans, Category.assoc] using
          ordinaryConcreteDescendedQuotientMap_one α
      · simpa [wppOpWhiskeredConcreteQuotientCocone, wppOpInverseWhiskeredNatTrans,
          wppOpOrdinaryNatTrans, Category.assoc] using
          ordinaryConcreteDescendedQuotientMap_zero α

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

/-- W357's projection data packaged as W366 transported leg data after whiskered naturality. -/
def transportedDescendedLegEquations_of_w357_ordinary_projection
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    TransportedDescendedLegEquations X Y α where
  descended := wppOpOrdinaryConcreteDescendedQuotientMap α
  ordinary_projection_equation_name := "ordinaryWhiskeredProjectionEquation"
  transported_leg :=
    transported_leg_of_ordinary_projection_of_whiskered_naturality
      (ordinaryWhiskeredProjectionEquation α)
      (whiskeredNaturalityEquation X Y α)

/-- Consumer theorem linking W357's ordinary projection equations directly to the W354 constructor. -/
def transportedConcreteQuotientW354Inputs_of_w357_ordinary_projection
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx) (hcy : IsColimit cy)
    (relation_inputs :
      RelationPullbackDescendedFieldsInputsW354Shape
        (wppOpTransportedConcreteQuotientCocone X)
        (wppOpTransportedConcreteQuotientCocone Y)
        (wppOpOrdinaryConcreteDescendedQuotientMap α)) :
    TransportedConcreteQuotientW354Inputs X Y α cx cy :=
  transportedConcreteQuotientW354Inputs_of_transportedDescendedLegEquations hcx hcy
    (transportedDescendedLegEquations_of_w357_ordinary_projection α)
    relation_inputs

/-- Declaration names exported by this support file. -/
def w375SupportDeclarationNames : List String :=
  ["wppOpOrdinaryNatTrans",
    "wppOpOrdinaryConcreteDescendedQuotientMap",
    "ordinaryConcreteDescendedQuotientMap_zero",
    "ordinaryConcreteDescendedQuotientMap_one",
    "ordinaryWhiskeredProjectionEquation",
    "transportedDescendedLegEquations_of_w357_ordinary_projection",
    "transportedConcreteQuotientW354Inputs_of_w357_ordinary_projection"]

theorem w375SupportDeclarationNames_count :
    w375SupportDeclarationNames.length = 7 := rfl

/-- Machine-readable state for this checked W375 support file. -/
structure WppOpLeftLcaOrdinaryWhiskeredProjectionV370StateW375 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  ordinaryProjectionResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaOrdinaryWhiskeredProjectionV370StateW375 :
    WppOpLeftLcaOrdinaryWhiskeredProjectionV370StateW375 where
  seed := "455bcb1a21046da55882c517cfb5b740"
  checkedFacts :=
    ["proved ordinary source-object projection from W357 left-leg equation",
      "proved ordinary target-object projection from W357 cofork-π equation",
      "proved the objectwise ordinary whiskered projection equation by cases on WalkingParallelPairᵒᵖ",
      "provided a W354-shaped consumer from W357 ordinary projection plus W372 whiskered naturality"]
  remainingInputs :=
    ["supply the transported relation-pullback topological fields"]
  ordinaryProjectionResult := "proved"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaOrdinaryWhiskeredProjectionV370StateW375_productSuccess :
    currentWppOpLeftLcaOrdinaryWhiskeredProjectionV370StateW375.productSuccessClaimed = false := rfl

section Checks

#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_π
#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_leftLeg
#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_rightLeg
#check wppOpOrdinaryNatTrans
#check wppOpOrdinaryConcreteDescendedQuotientMap
#check ordinaryConcreteDescendedQuotientMap_zero
#check ordinaryConcreteDescendedQuotientMap_one
#check ordinaryWhiskeredProjectionEquation
#check transportedDescendedLegEquations_of_w357_ordinary_projection
#check transportedConcreteQuotientW354Inputs_of_w357_ordinary_projection
#check w375SupportDeclarationNames
#check w375SupportDeclarationNames_count
#check currentWppOpLeftLcaOrdinaryWhiskeredProjectionV370StateW375
#check currentWppOpLeftLcaOrdinaryWhiskeredProjectionV370StateW375_productSuccess

end Checks

end WppOpLeftLcaOrdinaryWhiskeredProjectionV370SupportW375

end LeanLCAExactChallenge
