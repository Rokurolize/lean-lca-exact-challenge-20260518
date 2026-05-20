import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W335: extensionality for cochains out of a colimit complex.

After W333/W334, the remaining W308 `descEq` is a cochain equality out of the
colimit object `c₁.pt`.  This file proves the general extensionality principle:
two cochains out of a colimit complex are equal if they agree after every
colimit leg, provided each evaluation functor preserves that colimit.

This is the missing global colimit-descent wrapper for the W334 objectwise
`descEq` calculation.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace CochainExtOfColimitLegsW335

open CochainComplex

/-- Cech-style extensionality for cochains out of a colimit cochain complex. -/
theorem cochain_ext_of_colimit_legs {J : Type} [Category J]
    {X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {cX : Cocone X} (hcX : IsColimit cX)
    [∀ p : ℤ, PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {T : CochainComplex MetrizableLCA.{0} ℤ} {n : ℤ}
    {z₁ z₂ : HomComplex.Cochain cX.pt T n}
    (hlegs : ∀ j : J,
      (HomComplex.Cochain.ofHom (cX.ι.app j)).comp z₁ (zero_add n) =
        (HomComplex.Cochain.ofHom (cX.ι.app j)).comp z₂ (zero_add n)) :
    z₁ = z₂ := by
  apply HomComplex.Cochain.ext
  intro p q hpq
  apply (isColimitOfPreserves
    (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hcX).hom_ext
  intro j
  have h := HomComplex.Cochain.congr_v (hlegs j) p q hpq
  simpa [HomComplex.Cochain.ofHom_comp] using h

/-- The same extensionality with hypotheses written as component equations. -/
theorem cochain_ext_of_colimit_legs_component {J : Type} [Category J]
    {X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {cX : Cocone X} (hcX : IsColimit cX)
    [∀ p : ℤ, PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {T : CochainComplex MetrizableLCA.{0} ℤ} {n : ℤ}
    {z₁ z₂ : HomComplex.Cochain cX.pt T n}
    (hlegs : ∀ (j : J) (p q : ℤ) (hpq : p + n = q),
      (cX.ι.app j).f p ≫ z₁.v p q hpq =
        (cX.ι.app j).f p ≫ z₂.v p q hpq) :
    z₁ = z₂ := by
  apply cochain_ext_of_colimit_legs hcX
  intro j
  apply HomComplex.Cochain.ext
  intro p q hpq
  simpa [HomComplex.Cochain.ofHom_comp] using hlegs j p q hpq

/-- Machine-readable W335 state. -/
structure CochainExtOfColimitLegsState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W335 state. -/
def currentCochainExtOfColimitLegsState :
    CochainExtOfColimitLegsState where
  checkedLemma := "cochain_ext_of_colimit_legs"
  remainingInputs :=
    ["instantiate this with W308/W333's assembled left cochain",
      "rewrite each leg of the global descEq to W334's objectwise descEq",
      "identify the right side with the ambient right mediator"]
  productSuccessClaimed := false

theorem currentCochainExtOfColimitLegsState_productSuccess :
    currentCochainExtOfColimitLegsState.productSuccessClaimed = false := rfl

section Checks

#check cochain_ext_of_colimit_legs
#check cochain_ext_of_colimit_legs_component
#check currentCochainExtOfColimitLegsState
#check currentCochainExtOfColimitLegsState_productSuccess

end Checks

end CochainExtOfColimitLegsW335

end LeanLCAExactChallenge
