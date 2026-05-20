import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W302: mapping-cone left-cochain uniqueness support.

W327 splits equality of maps out of a mapping cone into a left
`mappingCone.inl` cochain equality and a right `mappingCone.inr` morphism
equality. W329 proves the right equality from the preserved ambient `c₂`
colimit.

This file checks the combined uniqueness consumer: after the right component is
forced by `c₂` leg equality, uniqueness of the mapping-cone mediator has only
the left cochain equality as a remaining input. It does not construct the left
cochain or prove the `mappingCone.desc` differential equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeLeftCochainUniquenessW302

open CochainComplex

variable {K L T : CochainComplex MetrizableLCA.{0} ℤ}
variable (φ : K ⟶ L)

/--
Local mapping-cone extensionality in the form needed by the W308 uniqueness
frontier: two maps out of a mapping cone are equal once their left cochain
components and right morphism components are equal.
-/
theorem mappingCone_hom_ext_of_left_right
    (m n : mappingCone φ ⟶ T)
    (hleft :
      (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom m) (add_zero (-1)) =
        (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom n) (add_zero (-1)))
    (hright : mappingCone.inr φ ≫ m = mappingCone.inr φ ≫ n) :
    m = n := by
  apply HomologicalComplex.hom_ext
  intro p
  apply mappingCone.ext_from φ (p + 1) p rfl
  · replace hleft := HomComplex.Cochain.congr_v hleft (p + 1) p (by omega)
    simpa using hleft
  · simpa using congrArg (fun q => q.f p) hright

/--
The preserved ambient colimit of `c₂` gives right-component equality from
agreement after every included `c₂` leg.
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

/--
Combined W327/W329 uniqueness consumer.

For a mapping cone over the included colimit arrow into `c₂.pt`, the right
component equality is forced by preserved `c₂` colimit uniqueness. Therefore
the only mapping-cone-specific uniqueness input left here is equality of the
left `mappingCone.inl` cochain components.
-/
theorem mappingCone_mediator_unique_of_left_cochain_and_c2_legs
    {J : Type} [Category J]
    {X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₂ : Cocone X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    {K : BoundedComplexCategory MetrizableLCA.{0}}
    (φ : K ⟶ c₂.pt)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (m n :
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ⟶ T)
    (hleft :
      (mappingCone.inl ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
          (HomComplex.Cochain.ofHom m) (add_zero (-1)) =
        (mappingCone.inl ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
          (HomComplex.Cochain.ofHom n) (add_zero (-1)))
    (hright_legs : ∀ j : J,
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫
          mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ m =
        (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫
          mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ n) :
    m = n := by
  have hright :
      mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ m =
        mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ n := by
    exact ambientRightComponent_ext_of_colimit hc₂ (fun j => by
      simpa [Category.assoc] using hright_legs j)
  exact mappingCone_hom_ext_of_left_right
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) m n hleft hright

/--
The checked W302 boundary: uniqueness is reduced to one left cochain equality
plus the already-categorical `c₂` leg equalities.
-/
structure MappingConeLeftCochainUniquenessState : Type where
  seed : String
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W302 state. -/
def currentMappingConeLeftCochainUniquenessState :
    MappingConeLeftCochainUniquenessState where
  seed := "w302-20260520T175036Z-0e9c10e7abe2"
  checkedLemma := "mappingCone_mediator_unique_of_left_cochain_and_c2_legs"
  remainingInputs :=
    ["construct the degree -1 left cochain for every test cocone",
      "prove left mappingCone.inl cochain compatibility against each fixed cocone leg",
      "prove the mappingCone.desc differential equation",
      "wire the checked uniqueness consumer into the full W308 assembly"]
  productSuccessClaimed := false

theorem currentMappingConeLeftCochainUniquenessState_productSuccess :
    currentMappingConeLeftCochainUniquenessState.productSuccessClaimed = false := rfl

section Checks

#check mappingCone_hom_ext_of_left_right
#check ambientRightComponent_ext_of_colimit
#check mappingCone_mediator_unique_of_left_cochain_and_c2_legs
#check currentMappingConeLeftCochainUniquenessState
#check currentMappingConeLeftCochainUniquenessState_productSuccess
#check CochainComplex.mappingCone.ext_from
#check CochainComplex.mappingCone.inl_desc
#check CochainComplex.mappingCone.inr_desc
#check isColimitOfPreserves

end Checks

end WppOpMappingConeLeftCochainUniquenessW302

end LeanLCAExactChallenge
