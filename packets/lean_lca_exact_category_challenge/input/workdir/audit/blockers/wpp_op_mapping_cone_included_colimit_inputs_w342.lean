import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
W342: included-colimit inputs needed by W341 for WPP/WPP-op diagrams.

W341 reduces the W308 bounded left-cochain and descEq construction to two
structural inputs: the included `c₁` cocone is still colimiting, and each
evaluation functor preserves the included colimit.  For the WPP and WPP-op
shapes used in the finite-colimit route, both inputs are available from the
existing bounded-inclusion preservation and mathlib's homological-complex
colimit instances.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeIncludedColimitInputsW342

/-- WPP-op bounded colimits remain colimits after inclusion into all cochain complexes. -/
def includedWppOpColimit_isColimit
    {X : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c : Cocone X} (hc : IsColimit c) :
    IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c) :=
  isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc

/-- WPP bounded colimits remain colimits after inclusion into all cochain complexes. -/
def includedWppColimit_isColimit
    {X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c : Cocone X} (hc : IsColimit c) :
    IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c) :=
  isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc

/-- Evaluation preserves WPP-op colimits of cochain complexes. -/
example
    (X : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ) (p : ℤ) :
    PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) := by
  infer_instance

/-- Evaluation preserves WPP colimits of cochain complexes. -/
example
    (X : WalkingParallelPair ⥤ CochainComplex MetrizableLCA.{0} ℤ) (p : ℤ) :
    PreservesColimit X
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) := by
  infer_instance

/-- The exact evaluation-preservation input needed by W341 for an included WPP-op source. -/
example
    (X : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0}) (p : ℤ) :
    PreservesColimit (X ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) := by
  infer_instance

/-- The exact evaluation-preservation input needed by W341 for an included WPP source. -/
example
    (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) (p : ℤ) :
    PreservesColimit (X ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) := by
  infer_instance

/-- Machine-readable W342 state. -/
structure WppOpMappingConeIncludedColimitInputsState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W342 state. -/
def currentWppOpMappingConeIncludedColimitInputsState :
    WppOpMappingConeIncludedColimitInputsState where
  checkedLemma := "includedWppOpColimit_isColimit"
  remainingInputs :=
    ["instantiate W341 with W308's actual WPP-op source diagram and ambientRightLegMediator",
      "package mappingCone.desc fac and uniqueness fields"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeIncludedColimitInputsState_productSuccess :
    currentWppOpMappingConeIncludedColimitInputsState.productSuccessClaimed = false := rfl

section Checks

#check includedWppOpColimit_isColimit
#check includedWppColimit_isColimit
#check currentWppOpMappingConeIncludedColimitInputsState
#check currentWppOpMappingConeIncludedColimitInputsState_productSuccess

end Checks

end WppOpMappingConeIncludedColimitInputsW342

end LeanLCAExactChallenge
