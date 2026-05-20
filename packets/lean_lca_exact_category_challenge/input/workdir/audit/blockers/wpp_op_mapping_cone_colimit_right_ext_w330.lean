import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W330: mapping-cone uniqueness with a colimit-controlled right component.

This is the import-safe version of the W330 split-assembly probe.  Audit files
are not Lake modules, so this file states the reusable local theorem directly:
to prove uniqueness of two maps out of a mapping cone, it suffices to prove the
left `mappingCone.inl` cochain equality and to prove the right `mappingCone.inr`
equality only after every leg of a colimit cocone.

For W308, the relevant colimit cocone is the included ambient image of `c₂`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeColimitRightExtW330

open CochainComplex

/--
Mapping-cone hom ext where the right component is checked only after a
colimit-cocone family of legs.
-/
theorem mappingCone_hom_ext_of_left_and_colimit_right {J : Type} [Category J]
    {G : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    {cG : Cocone G} (hcG : IsColimit cG)
    {K T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ cG.pt)
    (m n : mappingCone φ ⟶ T)
    (hleft :
      (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom m) (add_zero (-1)) =
        (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom n) (add_zero (-1)))
    (hright_legs : ∀ j : J,
      cG.ι.app j ≫ mappingCone.inr φ ≫ m =
        cG.ι.app j ≫ mappingCone.inr φ ≫ n) :
    m = n := by
  apply HomologicalComplex.hom_ext
  intro p
  apply mappingCone.ext_from φ (p + 1) p rfl
  · replace hleft := HomComplex.Cochain.congr_v hleft (p + 1) p (by omega)
    simpa using hleft
  · have hright : mappingCone.inr φ ≫ m = mappingCone.inr φ ≫ n := by
      exact hcG.hom_ext (fun j => by simpa [Category.assoc] using hright_legs j)
    simpa using congrArg (fun q => q.f p) hright

/-- Machine-readable W330 boundary state. -/
structure WppOpMappingConeColimitRightExtState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W330 state. -/
def currentWppOpMappingConeColimitRightExtState :
    WppOpMappingConeColimitRightExtState where
  checkedLemma := "mappingCone_hom_ext_of_left_and_colimit_right"
  remainingInputs :=
    ["instantiate G as the included c₂ diagram in the full W308 assembly",
      "construct and verify the left mappingCone.inl cochain component",
      "prove mappingCone.desc differential compatibility"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeColimitRightExtState_productSuccess :
    currentWppOpMappingConeColimitRightExtState.productSuccessClaimed = false := rfl

section Checks

#check mappingCone_hom_ext_of_left_and_colimit_right
#check currentWppOpMappingConeColimitRightExtState
#check currentWppOpMappingConeColimitRightExtState_productSuccess

end Checks

end WppOpMappingConeColimitRightExtW330

end LeanLCAExactChallenge
