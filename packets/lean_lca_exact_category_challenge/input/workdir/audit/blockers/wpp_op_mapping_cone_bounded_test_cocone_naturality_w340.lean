import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W340: W308's bounded mapping-cone test cocones supply W338 naturality.

W339 handled the ambient cochain-complex mapping-cone diagram.  W308 uses the
same diagram after applying `BoundedComplexCategory.ι MetrizableLCA` to a
bounded-complex diagram.  This file isolates the bounded version so the W338
`MappingConeTestLegNaturality` input can be discharged directly from any W308
test cocone.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeBoundedTestCoconeNaturalityW340

open CochainComplex

/-- The W308 bounded objectwise mapping-cone diagram. -/
noncomputable def boundedMappingConeDiagram {J : Type} [Category J]
    (X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}) (f : X₁ ⟶ X₂) :
    J ⥤ CochainComplex MetrizableLCA.{0} ℤ where
  obj j :=
    mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
  map {j j'} α :=
    mappingCone.map
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
      (by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg
          (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
          (f.naturality α).symm)
  map_id j := by
    simpa using
      mappingCone.map_id ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
  map_comp {i j k} α β := by
    simpa [Functor.map_comp] using
      (mappingCone.map_comp
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app i))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app k))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
            (f.naturality α).symm)
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map β))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map β))
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
            (f.naturality β).symm))

/-- The bounded-inclusion version of W338's test-leg naturality input. -/
abbrev BoundedMappingConeTestLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T) : Prop :=
  ∀ {j j' : J} (α : j ⟶ j'),
    mappingCone.map
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
            (f.naturality α).symm) ≫
      leg j' = leg j

/-- A W308 test cocone supplies the bounded-inclusion W338 naturality input. -/
theorem boundedTestCoconeLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    (s : Cocone (boundedMappingConeDiagram X₁ X₂ f)) :
    BoundedMappingConeTestLegNaturality f (fun j => s.ι.app j) := by
  intro j j' α
  simpa [boundedMappingConeDiagram] using s.w α

/-- Machine-readable W340 state. -/
structure WppOpMappingConeBoundedTestCoconeNaturalityState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W340 state. -/
def currentWppOpMappingConeBoundedTestCoconeNaturalityState :
    WppOpMappingConeBoundedTestCoconeNaturalityState where
  checkedLemma := "boundedTestCoconeLegNaturality"
  remainingInputs :=
    ["instantiate W338 with X₁ ⋙ BoundedComplexCategory.ι and X₂ ⋙ BoundedComplexCategory.ι",
      "identify W308's φ and ambientRightLegMediator β with the W338 right-side inputs",
      "combine W338 descEq with W327-W330 fac/uniq packaging"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeBoundedTestCoconeNaturalityState_productSuccess :
    currentWppOpMappingConeBoundedTestCoconeNaturalityState.productSuccessClaimed = false := rfl

section Checks

#check boundedTestCoconeLegNaturality
#check currentWppOpMappingConeBoundedTestCoconeNaturalityState
#check currentWppOpMappingConeBoundedTestCoconeNaturalityState_productSuccess

end Checks

end WppOpMappingConeBoundedTestCoconeNaturalityW340

end LeanLCAExactChallenge
