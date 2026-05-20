import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W331: construct a left cochain from degreewise colimit data.

W308's remaining mapping-cone obstruction is the left degree `-1` cochain.
Since `HomComplex.Cochain` is just a family of degree-shifted morphisms, the
candidate left cochain can be built degreewise from colimit desc maps, provided
the objectwise left legs form compatible cocones after each evaluation functor.

This file proves that reusable constructor and its leg equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeLeftCochainColimitW331

open CochainComplex

/-- Compatibility of objectwise degree `-1` cochains with a diagram `X`. -/
abbrev LeftCochainCompatible {J : Type} [Category J]
    (X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ)
    (T : CochainComplex MetrizableLCA.{0} ℤ)
    (left : ∀ j : J, HomComplex.Cochain (X.obj j) T (-1)) : Prop :=
  ∀ {j j' : J} (α : j ⟶ j') (p q : ℤ) (hpq : p + (-1 : ℤ) = q),
    (X.map α).f p ≫ (left j').v p q hpq = (left j).v p q hpq

/-- The degreewise cocone used to define one component of the descended left cochain. -/
noncomputable def leftCochainEvalCocone {J : Type} [Category J]
    {X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (left : ∀ j : J, HomComplex.Cochain (X.obj j) T (-1))
    (hcompat : LeftCochainCompatible X T left)
    (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    Cocone (X ⋙ HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) where
  pt := T.X q
  ι :=
    { app := fun j => (left j).v p q hpq
      naturality := by
        intro j j' α
        exact hcompat α p q hpq }

/--
Descend compatible objectwise degree `-1` cochains along a colimit cocone of
cochain complexes.
-/
noncomputable def leftCochainOfColimit {J : Type} [Category J]
    {X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {cX : Cocone X} (hcX : IsColimit cX)
    [∀ p : ℤ, PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (left : ∀ j : J, HomComplex.Cochain (X.obj j) T (-1))
    (hcompat : LeftCochainCompatible X T left) :
    HomComplex.Cochain cX.pt T (-1) :=
  HomComplex.Cochain.mk (fun p q hpq =>
    (isColimitOfPreserves
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hcX).desc
      (leftCochainEvalCocone left hcompat p q hpq))

/-- The descended left cochain has the expected componentwise leg equation. -/
theorem leftCochainOfColimit_fac {J : Type} [Category J]
    {X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {cX : Cocone X} (hcX : IsColimit cX)
    [∀ p : ℤ, PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (left : ∀ j : J, HomComplex.Cochain (X.obj j) T (-1))
    (hcompat : LeftCochainCompatible X T left)
    (j : J) (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    (cX.ι.app j).f p ≫ (leftCochainOfColimit hcX left hcompat).v p q hpq =
      (left j).v p q hpq := by
  exact (isColimitOfPreserves
    (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hcX).fac
      (leftCochainEvalCocone left hcompat p q hpq) j

/-- The descended left cochain equation as a `HomComplex.Cochain` equality. -/
theorem leftCochainOfColimit_comp_fac {J : Type} [Category J]
    {X : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {cX : Cocone X} (hcX : IsColimit cX)
    [∀ p : ℤ, PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (left : ∀ j : J, HomComplex.Cochain (X.obj j) T (-1))
    (hcompat : LeftCochainCompatible X T left)
    (j : J) :
    (HomComplex.Cochain.ofHom (cX.ι.app j)).comp
        (leftCochainOfColimit hcX left hcompat) (zero_add (-1)) =
      left j := by
  apply HomComplex.Cochain.ext
  intro p q hpq
  simpa [HomComplex.Cochain.ofHom_comp] using
    leftCochainOfColimit_fac hcX left hcompat j p q hpq

/-- Machine-readable W331 state. -/
structure WppOpMappingConeLeftCochainColimitState : Type where
  checkedConstructor : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W331 state. -/
def currentWppOpMappingConeLeftCochainColimitState :
    WppOpMappingConeLeftCochainColimitState where
  checkedConstructor := "leftCochainOfColimit"
  remainingInputs :=
    ["instantiate X as the included X₁ diagram for W308",
      "build objectwise left cochains from mappingCone.inl followed by the test cocone legs",
      "prove their naturality/compatibility",
      "prove the desc differential compatibility equation"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeLeftCochainColimitState_productSuccess :
    currentWppOpMappingConeLeftCochainColimitState.productSuccessClaimed = false := rfl

section Checks

#check LeftCochainCompatible
#check leftCochainEvalCocone
#check leftCochainOfColimit
#check leftCochainOfColimit_fac
#check leftCochainOfColimit_comp_fac
#check currentWppOpMappingConeLeftCochainColimitState
#check currentWppOpMappingConeLeftCochainColimitState_productSuccess

end Checks

end WppOpMappingConeLeftCochainColimitW331

end LeanLCAExactChallenge
