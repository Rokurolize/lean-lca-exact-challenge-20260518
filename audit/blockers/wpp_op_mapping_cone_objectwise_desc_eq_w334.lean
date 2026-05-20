import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W334: objectwise descEq for the W308 left cochain.

W333 constructs the W308-style left cochain by descending objectwise cochains of
the form `mappingCone.inl φ` followed by a test leg.  This file proves the
corresponding objectwise differential equation: the differential of that
objectwise left cochain is exactly `ofHom (φ ≫ mappingCone.inr φ ≫ leg)`.

The remaining global W308 `descEq` is now a colimit-descent compatibility
problem comparing this objectwise equation with the descended right mediator.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory

namespace WppOpMappingConeObjectwiseDescEqW334

open CochainComplex

/-- Objectwise left degree `-1` cochain from a mapping-cone test leg. -/
noncomputable def objectwiseLeftCochain
    {K L T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (leg : mappingCone φ ⟶ T) :
    HomComplex.Cochain K T (-1) :=
  (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom leg) (add_zero (-1))

/-- Objectwise differential equation for the W308 left-cochain candidate. -/
theorem objectwiseLeftCochain_descEq
    {K L T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (leg : mappingCone φ ⟶ T) :
    HomComplex.δ (-1) 0 (objectwiseLeftCochain φ leg) =
      HomComplex.Cochain.ofHom (φ ≫ mappingCone.inr φ ≫ leg) := by
  simp [objectwiseLeftCochain, HomComplex.Cochain.ofHom_comp]

/-- Machine-readable W334 state. -/
structure WppOpMappingConeObjectwiseDescEqState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W334 state. -/
def currentWppOpMappingConeObjectwiseDescEqState :
    WppOpMappingConeObjectwiseDescEqState where
  checkedLemma := "objectwiseLeftCochain_descEq"
  remainingInputs :=
    ["descend this objectwise equation through the included c₁ colimit",
      "identify the descended objectwise right leg with W308's ambient right mediator",
      "combine with W333's assembled left cochain"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeObjectwiseDescEqState_productSuccess :
    currentWppOpMappingConeObjectwiseDescEqState.productSuccessClaimed = false := rfl

section Checks

#check objectwiseLeftCochain
#check objectwiseLeftCochain_descEq
#check currentWppOpMappingConeObjectwiseDescEqState
#check currentWppOpMappingConeObjectwiseDescEqState_productSuccess

end Checks

end WppOpMappingConeObjectwiseDescEqW334

end LeanLCAExactChallenge
