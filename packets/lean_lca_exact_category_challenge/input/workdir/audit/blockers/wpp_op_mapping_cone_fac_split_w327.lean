import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W327: split the W308 mapping-cone leg equation.

W308's ambient desc assembly still asks for the full leg equation of the
assembled `mappingCone.desc`.  This file checks the local mapping-cone algebra:
for one fixed diagram object, that leg equation is implied by the right-leg
equation already supplied by W308 plus a left-cochain compatibility equation.

This does not construct the left cochain; it removes one bundled obligation from
the W308 frontier.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeFacSplitW327

open CochainComplex

variable {K₁ K₂ L₁ L₂ T : CochainComplex MetrizableLCA.{0} ℤ}
variable (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
variable (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
variable (comm : φ₁ ≫ b = a ≫ φ₂)
variable (α : HomComplex.Cochain K₂ T (-1)) (β : L₂ ⟶ T)
variable (eq : HomComplex.δ (-1) 0 α = HomComplex.Cochain.ofHom (φ₂ ≫ β))
variable (sleg : mappingCone φ₁ ⟶ T)

/--
For a single object of the WPP-op diagram, the fixed mapping-cone leg equation
is equivalent to its left `mappingCone.inl` component and right `mappingCone.inr`
component.
-/
theorem mappingCone_map_desc_fac_of_left_right
    (hleft :
      (mappingCone.inl φ₁).comp (HomComplex.Cochain.ofHom sleg) (add_zero (-1)) =
        (HomComplex.Cochain.ofHom a).comp α (zero_add (-1)))
    (hright : mappingCone.inr φ₁ ≫ sleg = b ≫ β) :
    mappingCone.map φ₁ φ₂ a b comm ≫ mappingCone.desc φ₂ α β eq = sleg := by
  apply HomologicalComplex.hom_ext
  intro p
  apply mappingCone.ext_from φ₁ (p + 1) p rfl
  · replace hleft := HomComplex.Cochain.congr_v hleft (p + 1) p (by omega)
    calc
      (mappingCone.inl φ₁).v (p + 1) p (by omega) ≫
          (mappingCone.map φ₁ φ₂ a b comm).f p ≫
          (mappingCone.desc φ₂ α β eq).f p =
          a.f (p + 1) ≫ α.v (p + 1) p (by omega) := by
        simp [mappingCone.map, Category.assoc]
      _ = (mappingCone.inl φ₁).v (p + 1) p (by omega) ≫ sleg.f p := by
        simpa [HomComplex.Cochain.ofHom_comp] using hleft.symm
  · simpa [Category.assoc, mappingCone.map] using congrArg (fun q => q.f p) hright.symm

/-- Machine-readable W327 boundary state. -/
structure WppOpMappingConeFacSplitState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W327 state. -/
def currentWppOpMappingConeFacSplitState : WppOpMappingConeFacSplitState where
  checkedLemma := "mappingCone_map_desc_fac_of_left_right"
  remainingInputs :=
    ["construct the left degree -1 cochain for each test cocone",
      "prove left-cochain compatibility against every fixed cocone leg",
      "prove the mappingCone.desc compatibility equation",
      "prove uniqueness after splitting into left/right mapping-cone components"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeFacSplitState_productSuccess :
    currentWppOpMappingConeFacSplitState.productSuccessClaimed = false := rfl

section Checks

#check mappingCone_map_desc_fac_of_left_right
#check currentWppOpMappingConeFacSplitState
#check currentWppOpMappingConeFacSplitState_productSuccess
#check CochainComplex.mappingCone.ext_from
#check CochainComplex.mappingCone.inl_desc
#check CochainComplex.mappingCone.inr_desc

end Checks

end WppOpMappingConeFacSplitW327

end LeanLCAExactChallenge
