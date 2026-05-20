import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W332: objectwise left cochains from mapping-cone cocone legs.

W331 reduces W308's left cochain to compatible objectwise degree `-1`
cochains.  This file supplies the intended objectwise family: for each diagram
object, compose `mappingCone.inl` with the corresponding leg of a test cocone.

The checked theorem proves that this family is compatible whenever the test
legs form a cocone over the mapping-cone diagram.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory

namespace WppOpMappingConeObjectwiseLeftW332

open CochainComplex

/-- Objectwise left degree `-1` cochain obtained from a mapping-cone cocone leg. -/
noncomputable def objectwiseLeftCochain
    {K L T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (leg : mappingCone φ ⟶ T) :
    HomComplex.Cochain K T (-1) :=
  (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom leg) (add_zero (-1))

/--
Compatibility condition for a family of mapping-cone cocone legs against a
diagram morphism.
-/
abbrev MappingConeLegNaturality
    {K₁ K₂ L₁ L₂ T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂)
    (leg₁ : mappingCone φ₁ ⟶ T) (leg₂ : mappingCone φ₂ ⟶ T) : Prop :=
  mappingCone.map φ₁ φ₂ a b comm ≫ leg₂ = leg₁

/--
The objectwise left cochains are compatible with the source diagram whenever
the mapping-cone legs are natural.
-/
theorem objectwiseLeftCochain_compatible_of_leg_naturality
    {K₁ K₂ L₁ L₂ T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂)
    (leg₁ : mappingCone φ₁ ⟶ T) (leg₂ : mappingCone φ₂ ⟶ T)
    (hleg : MappingConeLegNaturality φ₁ φ₂ a b comm leg₁ leg₂)
    (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    a.f p ≫ (objectwiseLeftCochain φ₂ leg₂).v p q hpq =
      (objectwiseLeftCochain φ₁ leg₁).v p q hpq := by
  calc
    a.f p ≫ (objectwiseLeftCochain φ₂ leg₂).v p q hpq =
        (mappingCone.inl φ₁).v p q hpq ≫
          (mappingCone.map φ₁ φ₂ a b comm ≫ leg₂).f q := by
        simp [objectwiseLeftCochain, mappingCone.map, Category.assoc]
    _ = (mappingCone.inl φ₁).v p q hpq ≫ leg₁.f q := by
        rw [hleg]
    _ = (objectwiseLeftCochain φ₁ leg₁).v p q hpq := by
        simp [objectwiseLeftCochain]

/-- Machine-readable W332 state. -/
structure WppOpMappingConeObjectwiseLeftState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W332 state. -/
def currentWppOpMappingConeObjectwiseLeftState :
    WppOpMappingConeObjectwiseLeftState where
  checkedLemma := "objectwiseLeftCochain_compatible_of_leg_naturality"
  remainingInputs :=
    ["combine W332 with W331 to instantiate the W308 left cochain",
      "supply evaluation-colimit preservation for the included X₁ diagram",
      "prove mappingCone.desc differential compatibility"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeObjectwiseLeftState_productSuccess :
    currentWppOpMappingConeObjectwiseLeftState.productSuccessClaimed = false := rfl

section Checks

#check objectwiseLeftCochain
#check MappingConeLegNaturality
#check objectwiseLeftCochain_compatible_of_leg_naturality
#check currentWppOpMappingConeObjectwiseLeftState
#check currentWppOpMappingConeObjectwiseLeftState_productSuccess

end Checks

end WppOpMappingConeObjectwiseLeftW332

end LeanLCAExactChallenge
