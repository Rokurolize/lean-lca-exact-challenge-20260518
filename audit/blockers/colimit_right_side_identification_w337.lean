import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W337: identify the right side of the global W308 `descEq`.

W334 gives objectwise equations whose right side is
`f.app j ≫ right_j`.  W308's global right side is instead `φ ≫ β`, where
`φ : c₁.pt ⟶ c₂.pt` is induced by the natural transformation and `β` is the
ambient right mediator out of `c₂.pt`.  This file proves the abstract colimit
identification: if `φ` and `β` have the expected leg equations, then `φ ≫ β`
is the colimit descent of the objectwise right sides.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ColimitRightSideIdentificationW337

/-- The cocone on `X₁` whose legs are `f.app j ≫ right_j`. -/
noncomputable def rightSideObjectwiseCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (right : ∀ j : J, X₂.obj j ⟶ T)
    (hright : ∀ {j j' : J} (α : j ⟶ j'),
      (X₂.map α) ≫ right j' = right j) :
    Cocone X₁ where
  pt := T
  ι :=
    { app := fun j => f.app j ≫ right j
      naturality := by
        intro j j' α
        calc
          X₁.map α ≫ (f.app j' ≫ right j') =
              (X₁.map α ≫ f.app j') ≫ right j' := by simp [Category.assoc]
          _ = (f.app j ≫ X₂.map α) ≫ right j' := by
              rw [f.naturality α]
          _ = f.app j ≫ (X₂.map α ≫ right j') := by simp [Category.assoc]
          _ = f.app j ≫ right j := by rw [hright α] }

/--
If `φ` and `β` have the expected leg equations, then `φ ≫ β` is the descent of
the objectwise right-side cocone.
-/
theorem phi_comp_rightMediator_eq_desc_objectwise {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {c₁ : Cocone X₁} (hc₁ : IsColimit c₁)
    {c₂ : Cocone X₂}
    (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (β : c₂.pt ⟶ T)
    (right : ∀ j : J, X₂.obj j ⟶ T)
    (hright : ∀ {j j' : J} (α : j ⟶ j'),
      (X₂.map α) ≫ right j' = right j)
    (hβ : ∀ j : J, c₂.ι.app j ≫ β = right j) :
    φ ≫ β = hc₁.desc (rightSideObjectwiseCocone f right hright) := by
  apply hc₁.hom_ext
  intro j
  calc
    c₁.ι.app j ≫ (φ ≫ β) =
        (c₁.ι.app j ≫ φ) ≫ β := by simp [Category.assoc]
    _ = (f.app j ≫ c₂.ι.app j) ≫ β := by
        rw [hφ j]
        rfl
    _ = f.app j ≫ (c₂.ι.app j ≫ β) := by simp [Category.assoc]
    _ = f.app j ≫ right j := by rw [hβ j]
    _ = c₁.ι.app j ≫ hc₁.desc (rightSideObjectwiseCocone f right hright) := by
        exact (hc₁.fac (rightSideObjectwiseCocone f right hright) j).symm

/-- Machine-readable W337 state. -/
structure ColimitRightSideIdentificationState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W337 state. -/
def currentColimitRightSideIdentificationState :
    ColimitRightSideIdentificationState where
  checkedLemma := "phi_comp_rightMediator_eq_desc_objectwise"
  remainingInputs :=
    ["instantiate right_j as mappingCone.inr (f.app j) ≫ test leg_j",
      "use W334 objectwise descEq and W335/W336 to complete global descEq",
      "instantiate c₁/c₂ as the included bounded colimits in W308"]
  productSuccessClaimed := false

theorem currentColimitRightSideIdentificationState_productSuccess :
    currentColimitRightSideIdentificationState.productSuccessClaimed = false := rfl

section Checks

#check rightSideObjectwiseCocone
#check phi_comp_rightMediator_eq_desc_objectwise
#check currentColimitRightSideIdentificationState
#check currentColimitRightSideIdentificationState_productSuccess

end Checks

end ColimitRightSideIdentificationW337

end LeanLCAExactChallenge
