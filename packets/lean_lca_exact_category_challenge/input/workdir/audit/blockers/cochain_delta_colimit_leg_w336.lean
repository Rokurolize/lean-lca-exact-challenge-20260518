import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W336: commute `δ` past a colimit leg.

W335 reduces W308's global `descEq` to equations after each colimit leg.  To use
W334 objectwise, we also need to rewrite those legged equations by commuting
`δ` past precomposition with the leg.  Mathlib already has the core lemma
`HomComplex.δ_ofHom_comp`; this file packages the exact form needed for the
mapping-cone frontier.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory

namespace CochainDeltaColimitLegW336

open CochainComplex

/-- `δ` commutes with precomposition by a morphism, in the W308 legged form. -/
theorem delta_of_colimit_leg_comp {A B T : CochainComplex MetrizableLCA.{0} ℤ}
    (ι : A ⟶ B) (z : HomComplex.Cochain B T (-1)) :
    HomComplex.δ (-1) 0
        ((HomComplex.Cochain.ofHom ι).comp z (zero_add (-1))) =
      (HomComplex.Cochain.ofHom ι).comp
        (HomComplex.δ (-1) 0 z) (zero_add 0) := by
  simp

/--
If the precomposed left cochain is an objectwise left cochain, then its
differential is the precomposition of the global differential.
-/
theorem colimit_leg_delta_eq_of_precomp_eq
    {A B T : CochainComplex MetrizableLCA.{0} ℤ}
    (ι : A ⟶ B) (z : HomComplex.Cochain B T (-1))
    (zObj : HomComplex.Cochain A T (-1))
    (h : (HomComplex.Cochain.ofHom ι).comp z (zero_add (-1)) = zObj) :
    (HomComplex.Cochain.ofHom ι).comp
        (HomComplex.δ (-1) 0 z) (zero_add 0) =
      HomComplex.δ (-1) 0 zObj := by
  rw [← h, delta_of_colimit_leg_comp]

/-- Machine-readable W336 state. -/
structure CochainDeltaColimitLegState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W336 state. -/
def currentCochainDeltaColimitLegState :
    CochainDeltaColimitLegState where
  checkedLemma := "delta_of_colimit_leg_comp"
  remainingInputs :=
    ["use W333's leftCochainOfMappingConeLegs_comp_fac as the precomp equality",
      "combine with W334 objectwiseLeftCochain_descEq",
      "identify the right mediator side after colimit legs"]
  productSuccessClaimed := false

theorem currentCochainDeltaColimitLegState_productSuccess :
    currentCochainDeltaColimitLegState.productSuccessClaimed = false := rfl

section Checks

#check delta_of_colimit_leg_comp
#check colimit_leg_delta_eq_of_precomp_eq
#check currentCochainDeltaColimitLegState
#check currentCochainDeltaColimitLegState_productSuccess

end Checks

end CochainDeltaColimitLegW336

end LeanLCAExactChallenge
