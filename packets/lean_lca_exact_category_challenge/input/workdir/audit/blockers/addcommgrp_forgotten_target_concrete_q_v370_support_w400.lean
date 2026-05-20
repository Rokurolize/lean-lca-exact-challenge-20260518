import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W400: concrete forgotten-target quotient-map support.

This standalone audit file isolates the concrete quotient map on the forgotten
target side.  The map is the appropriate WPP-op colimit cocone leg after
applying `forget₂ MetrizableLCA AddCommGrpCat` to short complexes.  The adapter
below feeds W398's forgotten cofork-map input and the W394 colimit-uniqueness
route without asking for the whole W394 package again.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgottenTargetConcreteQV370SupportW400

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- The functor forgetting a short complex of metrizable LCA groups to abelian groups. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/--
The concrete forgotten cocone leg at a WPP-op object.  This is the promised
source of the `qForgotten` map: it is not an abstract W394 field, but the
ordinary cocone leg `cs.ι.app j` mapped by `forget₂`.
-/
def concreteForgottenCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) (j : WalkingParallelPairᵒᵖ) :
    (S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (cs.ι.app j)

/-- W398-shaped forgotten cofork-map input, repeated locally for standalone checking. -/
structure ForgottenTargetCoforkMapInputW398Shape
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  qForgotten : L₂ ⟶ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  wForgotten : (u - v) ≫ qForgotten = 0 := by cat_disch
  hForgotten : IsColimit (CokernelCofork.ofπ qForgotten wForgotten)

/-- The cofork carried by the W398-shaped input. -/
def ForgottenTargetCoforkMapInputW398Shape.cofork
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (I : ForgottenTargetCoforkMapInputW398Shape u v S cs) :
    CokernelCofork (u - v) :=
  CokernelCofork.ofπ I.qForgotten I.wForgotten

/--
Concrete W400 input.  Compared with W394, this asks only for:

* the object identification selecting which concrete WPP-op cocone leg has
  source `L₂`;
* the proof that this leg coequalizes `(u - v, 0)`;
* the cokernel-colimit proof for that concrete cofork.

The quotient map itself is definitionally `sourceIso.hom` followed by the
forgotten cocone leg.
-/
structure ConcreteForgottenTargetLegInputW400
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  j : WalkingParallelPairᵒᵖ
  sourceIso : L₂ ≅ (S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  qForgotten : L₂ ⟶ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  qForgotten_eq_concreteLeg :
    qForgotten = sourceIso.hom ≫ concreteForgottenCoconeLeg S cs j
  wForgotten : (u - v) ≫ qForgotten = 0 := by cat_disch
  hForgotten : IsColimit (CokernelCofork.ofπ qForgotten wForgotten)

@[simp]
theorem ConcreteForgottenTargetLegInputW400.qForgotten_concreteLeg_formula
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (I : ConcreteForgottenTargetLegInputW400 u v S cs) :
    I.qForgotten = I.sourceIso.hom ≫ concreteForgottenCoconeLeg S cs I.j :=
  I.qForgotten_eq_concreteLeg

/-- W400's concrete leg package feeds the W398 forgotten cofork-map input. -/
def ConcreteForgottenTargetLegInputW400.toW398CoforkMapInput
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S} (I : ConcreteForgottenTargetLegInputW400 u v S cs) :
    ForgottenTargetCoforkMapInputW398Shape u v S cs where
  qForgotten := I.qForgotten
  wForgotten := I.wForgotten
  hForgotten := I.hForgotten

/-- Canonical-side input repeated locally, matching W398's adapter shape. -/
structure ForgottenTargetCanonicalCoforkInputW398Shape
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (canonicalTarget : ShortComplex AddCommGrpCat.{0})
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hcs : IsColimit cs
  qCanonical : L₂ ⟶ canonicalTarget
  wCanonical : (u - v) ≫ qCanonical = 0 := by cat_disch
  hCanonical : IsColimit (CokernelCofork.ofπ qCanonical wCanonical)

/-- W394-shaped colimit-iso input repeated locally for a checked consumer. -/
structure ForgottenTargetColimitIsoInputW394Shape
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (canonicalTarget : ShortComplex AddCommGrpCat.{0})
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hcs : IsColimit cs
  qCanonical : L₂ ⟶ canonicalTarget
  wCanonical : (u - v) ≫ qCanonical = 0 := by cat_disch
  hCanonical : IsColimit (CokernelCofork.ofπ qCanonical wCanonical)
  qForgotten : L₂ ⟶ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  wForgotten : (u - v) ≫ qForgotten = 0 := by cat_disch
  hForgotten : IsColimit (CokernelCofork.ofπ qForgotten wForgotten)

/--
Consumer into W394's input shape.  The forgotten side comes from W400's concrete
cocone leg, while the canonical side remains the already-separated W398 input.
-/
def ConcreteForgottenTargetLegInputW400.toW394ColimitIsoInput
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (canonical : ForgottenTargetCanonicalCoforkInputW398Shape u v canonicalTarget S cs)
    (concrete : ConcreteForgottenTargetLegInputW400 u v S cs) :
    ForgottenTargetColimitIsoInputW394Shape u v canonicalTarget S cs where
  hcs := canonical.hcs
  qCanonical := canonical.qCanonical
  wCanonical := canonical.wCanonical
  hCanonical := canonical.hCanonical
  qForgotten := concrete.qForgotten
  wForgotten := concrete.wForgotten
  hForgotten := concrete.hForgotten

/-- The W394 colimit-uniqueness target isomorphism obtained from W400 data. -/
def ConcreteForgottenTargetLegInputW400.targetIso
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (canonical : ForgottenTargetCanonicalCoforkInputW398Shape u v canonicalTarget S cs)
    (concrete : ConcreteForgottenTargetLegInputW400 u v S cs) :
    canonicalTarget ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  IsColimit.coconePointUniqueUpToIso canonical.hCanonical concrete.hForgotten

@[simp]
theorem ConcreteForgottenTargetLegInputW400.qCanonical_targetIso_hom
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    {canonicalTarget : ShortComplex AddCommGrpCat.{0}}
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (canonical : ForgottenTargetCanonicalCoforkInputW398Shape u v canonicalTarget S cs)
    (concrete : ConcreteForgottenTargetLegInputW400 u v S cs) :
    canonical.qCanonical ≫ (concrete.targetIso canonical).hom = concrete.qForgotten := by
  simpa [ConcreteForgottenTargetLegInputW400.targetIso,
    CokernelCofork.π_ofπ] using
      (canonical.hCanonical.comp_coconePointUniqueUpToIso_hom
        concrete.hForgotten WalkingParallelPair.one)

/-- W400 checked support state. -/
structure AddCommGrpForgottenTargetConcreteQV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  concreteQForgottenResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgottenTargetConcreteQV370SupportState :
    AddCommGrpForgottenTargetConcreteQV370SupportState where
  seed := "W400-concrete-q-5f9b2e71a4c3"
  checkedConstructors :=
    ["forgottenShortComplexFunctor",
      "concreteForgottenCoconeLeg",
      "ConcreteForgottenTargetLegInputW400.qForgotten",
      "ConcreteForgottenTargetLegInputW400.wForgotten",
      "ConcreteForgottenTargetLegInputW400.hForgotten",
      "ConcreteForgottenTargetLegInputW400.toW398CoforkMapInput",
      "ConcreteForgottenTargetLegInputW400.toW394ColimitIsoInput",
      "ConcreteForgottenTargetLegInputW400.targetIso",
      "ConcreteForgottenTargetLegInputW400.qCanonical_targetIso_hom"]
  concreteQForgottenResult := "partial"
  remainingInputs :=
    ["identify the WPP-op object whose forgotten cocone leg has source L₂",
      "prove the selected concrete cocone leg coequalizes (u - v, 0)",
      "prove the selected concrete cocone leg is an AddCommGrp cokernel cofork"]
  productSuccessClaimed := false

theorem currentAddCommGrpForgottenTargetConcreteQV370SupportState_productSuccess :
    currentAddCommGrpForgottenTargetConcreteQV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check forgottenShortComplexFunctor
#check concreteForgottenCoconeLeg
#check ForgottenTargetCoforkMapInputW398Shape
#check ForgottenTargetCoforkMapInputW398Shape.cofork
#check ConcreteForgottenTargetLegInputW400
#check ConcreteForgottenTargetLegInputW400.qForgotten
#check ConcreteForgottenTargetLegInputW400.wForgotten
#check ConcreteForgottenTargetLegInputW400.hForgotten
#check ConcreteForgottenTargetLegInputW400.toW398CoforkMapInput
#check ForgottenTargetCanonicalCoforkInputW398Shape
#check ForgottenTargetColimitIsoInputW394Shape
#check ConcreteForgottenTargetLegInputW400.toW394ColimitIsoInput
#check ConcreteForgottenTargetLegInputW400.targetIso
#check ConcreteForgottenTargetLegInputW400.qCanonical_targetIso_hom
#check currentAddCommGrpForgottenTargetConcreteQV370SupportState_productSuccess

end Checks

end AddCommGrpForgottenTargetConcreteQV370SupportW400

end LeanLCAExactChallenge
