import LeanLCAExactChallenge.LCA.Cokernel

/-!
W357: concrete quotient-cocone support for the left LCA route.

This file builds the concrete quotient cofork attached to an ordinary parallel
pair, proves that it is a colimit by the local `cokernelIsColimit` API, defines
the descended quotient morphism from square equations, and proves the projection
compatibility equations needed by the W354 certificate route.

For a `WalkingParallelPairᵒᵖ` diagram `X`, the file also packages the same
concrete quotient construction on the ordinary diagram obtained through
`walkingParallelPairOpEquiv.functor ⋙ X`, then transports it across the inverse
equivalence.  The remaining boundary is the final cocone-iso transport from
`walkingParallelPairOpEquiv.inverse ⋙ walkingParallelPairOpEquiv.functor ⋙ X`
back to `X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaConcreteQuotientCoconeV369SupportW357

universe u

namespace ConcreteMetrizableLCA

open LeanLCAExactChallenge.MetrizableLCA

variable {A B A' B' : MetrizableLCA.{u}}

/-- Concrete quotient cofork for a parallel pair, presented as the cokernel of `f - g`. -/
def concreteQuotientCofork (f g : A ⟶ B) : Cofork f g :=
  Preadditive.coforkOfCokernelCofork
    (CokernelCofork.ofπ (cokernelπ (f - g)) (comp_cokernelπ (f - g)))

@[simp]
theorem concreteQuotientCofork_pt (f g : A ⟶ B) :
    (concreteQuotientCofork f g).pt = cokernelObj (f - g) :=
  rfl

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

/--
Concrete quotient cocone on the ordinary diagram associated to a WPP-op
diagram.  Its point is the quotient/cokernel object of the two parallel arrows.
-/
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

/--
Concrete quotient cocone after whiskering through the inverse equivalence.  This
is the checked transport target immediately before identifying the resulting
diagram with the original WPP-op diagram.
-/
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

/-- The concrete data produced by this file for a WPP-op diagram. -/
structure WppOpConcreteQuotientCoconeBoundary
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : Type 1 where
  ordinary_cocone : Cocone (wppOpOrdinaryDiagram X)
  ordinary_isColimit : IsColimit ordinary_cocone
  whiskered_cocone : Cocone (walkingParallelPairOpEquiv.inverse ⋙ wppOpOrdinaryDiagram X)
  whiskered_isColimit : IsColimit whiskered_cocone
  ordinary_point_eq :
    ordinary_cocone.pt =
      MetrizableLCA.cokernelObj (wppOpLeft X - wppOpRight X)

/-- Canonical boundary package for a WPP-op diagram. -/
def wppOpConcreteQuotientCoconeBoundary
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WppOpConcreteQuotientCoconeBoundary X where
  ordinary_cocone := wppOpConcreteQuotientCoconeOnOrdinary X
  ordinary_isColimit := wppOpConcreteQuotientCoconeOnOrdinaryIsColimit X
  whiskered_cocone := wppOpWhiskeredConcreteQuotientCocone X
  whiskered_isColimit := wppOpWhiskeredConcreteQuotientCoconeIsColimit X
  ordinary_point_eq := by
    simp [wppOpConcreteQuotientCoconeOnOrdinary,
      ConcreteMetrizableLCA.concreteQuotientCofork]

/-- Declaration names exported by this support file. -/
def w357SupportDeclarationNames : List String :=
  ["ConcreteMetrizableLCA.concreteQuotientCofork",
    "ConcreteMetrizableLCA.concreteQuotientCoforkIsColimit",
    "ConcreteMetrizableLCA.concreteQuotient_relationForward",
    "ConcreteMetrizableLCA.concreteQuotient_targetKernel_le",
    "ConcreteMetrizableLCA.concreteDescendedQuotientMap",
    "ConcreteMetrizableLCA.concreteDescendedQuotientMap_quotient_compat",
    "ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_π",
    "ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_leftLeg",
    "ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_rightLeg",
    "wppOpConcreteQuotientCoconeOnOrdinary",
    "wppOpConcreteQuotientCoconeOnOrdinaryIsColimit",
    "wppOpWhiskeredConcreteQuotientCocone",
    "wppOpWhiskeredConcreteQuotientCoconeIsColimit",
    "WppOpConcreteQuotientCoconeBoundary",
    "wppOpConcreteQuotientCoconeBoundary"]

theorem w357SupportDeclarationNames_count :
    w357SupportDeclarationNames.length = 15 := rfl

/-- Machine-readable state for this checked W357 support file. -/
structure WppOpLeftLcaConcreteQuotientCoconeV369StateW357 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaConcreteQuotientCoconeV369StateW357 :
    WppOpLeftLcaConcreteQuotientCoconeV369StateW357 where
  seed := "W357-seed-hnoeHUe1QFWe23bAyw5or9hW"
  checkedFacts :=
    ["ordinary concrete quotient cofork is built from cokernelObj/cokernelπ",
      "ordinary concrete quotient cofork is an IsColimit via cokernelIsColimit",
      "compatible component squares define a descended quotient morphism by quotientLift",
      "descended quotient morphism satisfies the projection compatibility equation",
      "left and right ordinary cofork leg equations are proved",
      "WPP-op ordinary diagram and inverse-equivalence whiskered concrete cocones are packaged with IsColimit proofs"]
  remainingInputs :=
    ["transport the whiskered cocone along the counit diagram isomorphism to a Cocone X",
      "rewrite the ordinary cofork leg equations into W354's source.ι.app j equations for every WalkingParallelPairᵒᵖ object",
      "combine the concrete descended topological fields from W352/W355 with the transported W354 cocone package"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaConcreteQuotientCoconeV369StateW357_productSuccess :
    currentWppOpLeftLcaConcreteQuotientCoconeV369StateW357.productSuccessClaimed = false := rfl

section Checks

#check ConcreteMetrizableLCA.concreteQuotientCofork
#check ConcreteMetrizableLCA.concreteQuotientCoforkIsColimit
#check ConcreteMetrizableLCA.concreteQuotient_relationForward
#check ConcreteMetrizableLCA.concreteQuotient_targetKernel_le
#check ConcreteMetrizableLCA.concreteDescendedQuotientMap
#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_quotient_compat
#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_π
#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_leftLeg
#check ConcreteMetrizableLCA.concreteDescendedQuotientMap_cofork_rightLeg
#check wppOpConcreteQuotientCoconeOnOrdinary
#check wppOpConcreteQuotientCoconeOnOrdinaryIsColimit
#check wppOpWhiskeredConcreteQuotientCocone
#check wppOpWhiskeredConcreteQuotientCoconeIsColimit
#check WppOpConcreteQuotientCoconeBoundary
#check wppOpConcreteQuotientCoconeBoundary
#check w357SupportDeclarationNames
#check w357SupportDeclarationNames_count
#check currentWppOpLeftLcaConcreteQuotientCoconeV369StateW357
#check currentWppOpLeftLcaConcreteQuotientCoconeV369StateW357_productSuccess

end Checks

end WppOpLeftLcaConcreteQuotientCoconeV369SupportW357

end LeanLCAExactChallenge
