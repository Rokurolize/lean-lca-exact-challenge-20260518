import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W329: right-component uniqueness for the W308 mapping-cone mediator.

W327/W328 split mapping-cone fac/uniq into left and right components.  This
file checks the categorical right side: once the included `c₂` cocone is
colimiting, two candidate right components are equal if they agree after every
included leg of `c₂`.

This keeps the remaining W308 uniqueness work focused on the left cochain
component and the differential compatibility equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeRightUniquenessW329

/--
The preserved ambient colimit of `c₂` gives the right-component hom ext needed
by the W308 uniqueness split.
-/
theorem ambientRightComponent_ext_of_colimit {J : Type} [Category J]
    {X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₂ : Cocone X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    {β₁ β₂ : (BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt ⟶ T}
    (hβ : ∀ j : J,
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β₁ =
        (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β₂) :
    β₁ = β₂ := by
  exact (isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₂).hom_ext hβ

/-- A small wrapper matching the W308 phrasing: right equality is not an extra mapping-cone theorem. -/
theorem w308_right_uniqueness_component_of_legs {J : Type} [Category J]
    {X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₂ : Cocone X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    {β₁ β₂ : (BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt ⟶ T}
    (hβ : ∀ j : J,
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β₁ =
        (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β₂) :
    β₁ = β₂ :=
  ambientRightComponent_ext_of_colimit hc₂ hβ

/-- Machine-readable W329 boundary state. -/
structure WppOpMappingConeRightUniquenessState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W329 state. -/
def currentWppOpMappingConeRightUniquenessState :
    WppOpMappingConeRightUniquenessState where
  checkedLemma := "ambientRightComponent_ext_of_colimit"
  remainingInputs :=
    ["left mappingCone.inl cochain construction",
      "left mappingCone.inl cochain compatibility/equality",
      "mappingCone.desc differential compatibility equation",
      "full W308 assembly wiring that combines W327/W328/W329"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeRightUniquenessState_productSuccess :
    currentWppOpMappingConeRightUniquenessState.productSuccessClaimed = false := rfl

section Checks

#check ambientRightComponent_ext_of_colimit
#check w308_right_uniqueness_component_of_legs
#check currentWppOpMappingConeRightUniquenessState
#check currentWppOpMappingConeRightUniquenessState_productSuccess
#check isColimitOfPreserves

end Checks

end WppOpMappingConeRightUniquenessW329

end LeanLCAExactChallenge
