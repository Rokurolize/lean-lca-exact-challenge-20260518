import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Maps.Basic

/-!
W374: WPP-op square equations from naturality.

This standalone audit file isolates the two square equations that W371 left for
callers to provide manually.  For a natural transformation
`α : X ⟶ Y` of `WalkingParallelPairᵒᵖ`-indexed diagrams, the ordinary parallel
pair obtained through `walkingParallelPairOpEquiv.functor` has component maps
at the ordinary source and target objects.  Naturality at the images of
`WalkingParallelPairHom.left` and `WalkingParallelPairHom.right` gives exactly
the two W371 square equations.

No product-completion claim is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpSquareEquationsV370SupportW374

open LeanLCAExactChallenge.MetrizableLCA

/- The next abbreviations intentionally match the W371 WPP-op names so that the
   checked square lemmas can be copied into the W371 support boundary directly. -/

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

/-- Concrete WPP-op component at the ordinary source object. -/
abbrev wppOpOrdinaryDomainMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpDomain X ⟶ wppOpDomain Y :=
  α.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero)

/-- Concrete WPP-op component at the ordinary target object. -/
abbrev wppOpOrdinaryCodomainMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpCodomain X ⟶ wppOpCodomain Y :=
  α.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one)

/-- W374's named left square equation, exactly W371's `hsquare_left`. -/
theorem wppOpLeftSquareEquationW374
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpLeft Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- W374's named right square equation, exactly W371's `hsquare_right`. -/
theorem wppOpRightSquareEquationW374
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
      wppOpOrdinaryDomainMap α ≫ wppOpRight Y := by
  exact α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- The naturality component whose value is the checked left square. -/
theorem wppOpLeftSquareEquationW374_naturality_component
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left) =
      wppOpLeftSquareEquationW374 α := by
  rfl

/-- The naturality component whose value is the checked right square. -/
theorem wppOpRightSquareEquationW374_naturality_component
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) :
    α.naturality (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right) =
      wppOpRightSquareEquationW374 α := by
  rfl

namespace ConcreteMetrizableLCA

universe u

variable {A B A' B' : MetrizableLCA.{u}}

/-- W374-local spelling of the relation-pullback input used by W368/W371. -/
abbrev relationPreimagePullbackConditionW374
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  AddSubgroup.comap iB.hom.toAddMonoidHom (cokernelSubgroup (f' - g')) =
    cokernelSubgroup (f - g)

/-- W374-local spelling of the target relation lifting input used by W368/W371. -/
abbrev targetRelationLiftsThroughComponentW374
    (f' g' : A' ⟶ B') (iB : B ⟶ B') : Prop :=
  ∀ n : B', n ∈ cokernelSubgroup (f' - g') →
    ∃ d : B, iB d = n

/-- A set is saturated for a quotient-like map when it contains full fibers over its image. -/
def IsSaturatedForW374 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/-- Target quotient closed-on-saturated package used by W368/W371. -/
structure TargetQuotientClosedOnSaturatedSetsW374
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    Prop where
  closed_image :
    ∀ S : Set B', IsClosed S →
      IsSaturatedForW374 (quotientMap B' N' hN' : B' → quotientObj B' N' hN') S →
        IsClosed ((quotientMap B' N' hN' : B' → quotientObj B' N' hN') '' S)

/--
The W371 concrete input package shape, with square equations still explicit.

The fields are the remaining topological and relation inputs after W374 has
supplied the two square equations by naturality.
-/
structure ConcreteQuotientClosedMapInputsW371
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') : Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW374 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW374 f' g' iB
  target_closed_on_saturated :
    TargetQuotientClosedOnSaturatedSetsW374 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/-- The same remaining fields, before inserting square equations. -/
structure ConcreteQuotientClosedMapRemainingInputsW374
    (f g : A ⟶ B) (f' g' : A' ⟶ B') (_iA : A ⟶ A') (iB : B ⟶ B') :
    Prop where
  component_closedMap : IsClosedMap (iB : B → B')
  relation_pullback : relationPreimagePullbackConditionW374 f g f' g' iB
  target_relation_lifts : targetRelationLiftsThroughComponentW374 f' g' iB
  target_closed_on_saturated :
    TargetQuotientClosedOnSaturatedSetsW374 B' (cokernelSubgroup (f' - g'))
      (AddSubgroup.isClosed_topologicalClosure _)

/--
Consumer constructor: once the non-square fields are supplied, any checked
square equations build W371's concrete input package.
-/
theorem ConcreteQuotientClosedMapRemainingInputsW374.to_w371_inputs
    {f g : A ⟶ B} {f' g' : A' ⟶ B'} {iA : A ⟶ A'} {iB : B ⟶ B'}
    {hsquare_left : f ≫ iB = iA ≫ f'}
    {hsquare_right : g ≫ iB = iA ≫ g'}
    (h : ConcreteQuotientClosedMapRemainingInputsW374 f g f' g' iA iB) :
    ConcreteQuotientClosedMapInputsW371 f g f' g' iA iB hsquare_left hsquare_right where
  component_closedMap := h.component_closedMap
  relation_pullback := h.relation_pullback
  target_relation_lifts := h.target_relation_lifts
  target_closed_on_saturated := h.target_closed_on_saturated

end ConcreteMetrizableLCA

/-- WPP-op specialization of the concrete W371 input package. -/
abbrev WppOpConcreteQuotientClosedMapInputsW371
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    (hsquare_left :
      wppOpLeft X ≫ wppOpOrdinaryCodomainMap α =
        wppOpOrdinaryDomainMap α ≫ wppOpLeft Y)
    (hsquare_right :
      wppOpRight X ≫ wppOpOrdinaryCodomainMap α =
        wppOpOrdinaryDomainMap α ≫ wppOpRight Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)
    hsquare_left hsquare_right

/-- The non-square WPP-op fields needed after W374 supplies naturality squares. -/
abbrev WppOpConcreteQuotientClosedMapRemainingInputsW374
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y) : Prop :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRemainingInputsW374
    (wppOpLeft X) (wppOpRight X)
    (wppOpLeft Y) (wppOpRight Y)
    (wppOpOrdinaryDomainMap α) (wppOpOrdinaryCodomainMap α)

/--
Consumer theorem requested by W374: callers supply only the remaining
topological/relation fields, and W374 inserts both square equations from
naturality.
-/
theorem WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    (h : WppOpConcreteQuotientClosedMapRemainingInputsW374 α) :
    WppOpConcreteQuotientClosedMapInputsW371 α
      (wppOpLeftSquareEquationW374 α)
      (wppOpRightSquareEquationW374 α) :=
  ConcreteMetrizableLCA.ConcreteQuotientClosedMapRemainingInputsW374.to_w371_inputs h

/-- Machine-readable W374 state. -/
structure WppOpSquareEquationsV370SupportStateW374 : Type where
  seed : String
  checkedFacts : List String
  packagedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentWppOpSquareEquationsV370SupportStateW374 :
    WppOpSquareEquationsV370SupportStateW374 where
  seed := "e616694768fd8a8bb69edc343d97b7be"
  checkedFacts :=
    ["WppOpSquareEquationsV370SupportW374.wppOpLeftSquareEquationW374",
      "WppOpSquareEquationsV370SupportW374.wppOpRightSquareEquationW374",
      "WppOpSquareEquationsV370SupportW374.wppOpLeftSquareEquationW374_naturality_component",
      "WppOpSquareEquationsV370SupportW374.wppOpRightSquareEquationW374_naturality_component",
      "WppOpSquareEquationsV370SupportW374.WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374"]
  packagedInputs :=
    ["hsquare_left from naturality at WalkingParallelPairHom.left",
      "hsquare_right from naturality at WalkingParallelPairHom.right"]
  remainingInputs :=
    ["component closed map for the ordinary codomain component",
      "relation-pullback equality",
      "target relation lifting through the ordinary codomain component",
      "target quotient closed-on-saturated support"]
  productSuccessClaimed := false

theorem currentWppOpSquareEquationsV370SupportStateW374_productSuccess :
    currentWppOpSquareEquationsV370SupportStateW374.productSuccessClaimed = false := rfl

def wppOpSquareEquationsV370SupportDeclarationNamesW374 : List String :=
  ["WppOpSquareEquationsV370SupportW374.wppOpOrdinaryDiagram",
    "WppOpSquareEquationsV370SupportW374.wppOpDomain",
    "WppOpSquareEquationsV370SupportW374.wppOpCodomain",
    "WppOpSquareEquationsV370SupportW374.wppOpLeft",
    "WppOpSquareEquationsV370SupportW374.wppOpRight",
    "WppOpSquareEquationsV370SupportW374.wppOpOrdinaryDomainMap",
    "WppOpSquareEquationsV370SupportW374.wppOpOrdinaryCodomainMap",
    "WppOpSquareEquationsV370SupportW374.wppOpLeftSquareEquationW374",
    "WppOpSquareEquationsV370SupportW374.wppOpRightSquareEquationW374",
    "WppOpSquareEquationsV370SupportW374.wppOpLeftSquareEquationW374_naturality_component",
    "WppOpSquareEquationsV370SupportW374.wppOpRightSquareEquationW374_naturality_component",
    "WppOpSquareEquationsV370SupportW374.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371",
    "WppOpSquareEquationsV370SupportW374.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRemainingInputsW374",
    "WppOpSquareEquationsV370SupportW374.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRemainingInputsW374.to_w371_inputs",
    "WppOpSquareEquationsV370SupportW374.WppOpConcreteQuotientClosedMapInputsW371",
    "WppOpSquareEquationsV370SupportW374.WppOpConcreteQuotientClosedMapRemainingInputsW374",
    "WppOpSquareEquationsV370SupportW374.WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374",
    "WppOpSquareEquationsV370SupportW374.currentWppOpSquareEquationsV370SupportStateW374",
    "WppOpSquareEquationsV370SupportW374.currentWppOpSquareEquationsV370SupportStateW374_productSuccess"]

theorem wppOpSquareEquationsV370SupportDeclarationNamesW374_count :
    wppOpSquareEquationsV370SupportDeclarationNamesW374.length = 19 := rfl

section Checks

#check WppOpSquareEquationsV370SupportW374.wppOpLeftSquareEquationW374
#check WppOpSquareEquationsV370SupportW374.wppOpRightSquareEquationW374
#check WppOpSquareEquationsV370SupportW374.wppOpLeftSquareEquationW374_naturality_component
#check WppOpSquareEquationsV370SupportW374.wppOpRightSquareEquationW374_naturality_component
#check WppOpSquareEquationsV370SupportW374.ConcreteMetrizableLCA.ConcreteQuotientClosedMapInputsW371
#check WppOpSquareEquationsV370SupportW374.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRemainingInputsW374
#check WppOpSquareEquationsV370SupportW374.ConcreteMetrizableLCA.ConcreteQuotientClosedMapRemainingInputsW374.to_w371_inputs
#check WppOpSquareEquationsV370SupportW374.WppOpConcreteQuotientClosedMapInputsW371
#check WppOpSquareEquationsV370SupportW374.WppOpConcreteQuotientClosedMapRemainingInputsW374
#check WppOpSquareEquationsV370SupportW374.WppOpConcreteQuotientClosedMapInputsW371.of_remaining_inputsW374
#check WppOpSquareEquationsV370SupportW374.currentWppOpSquareEquationsV370SupportStateW374
#check WppOpSquareEquationsV370SupportW374.currentWppOpSquareEquationsV370SupportStateW374_productSuccess
#check WppOpSquareEquationsV370SupportW374.wppOpSquareEquationsV370SupportDeclarationNamesW374
#check WppOpSquareEquationsV370SupportW374.wppOpSquareEquationsV370SupportDeclarationNamesW374_count

end Checks

end WppOpSquareEquationsV370SupportW374

end LeanLCAExactChallenge
