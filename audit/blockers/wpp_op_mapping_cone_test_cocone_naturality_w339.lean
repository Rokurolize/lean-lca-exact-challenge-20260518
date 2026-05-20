import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W339: test-cocone legs are natural for the objectwise mapping-cone diagram.

W338 packages the global `descEq` theorem under an explicit
`MappingConeTestLegNaturality` input.  In W308 that input should come directly
from the fact that the supplied test object is a cocone over the mapping-cone
diagram.  This file isolates the generic cochain-complex fact needed for that
instantiation.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory

namespace WppOpMappingConeTestCoconeNaturalityW339

open CochainComplex

/-- The objectwise mapping-cone diagram attached to a natural transformation. -/
noncomputable def mappingConeDiagram {J : Type} [Category J]
    (X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ) (f : X₁ ⟶ X₂) :
    J ⥤ CochainComplex MetrizableLCA.{0} ℤ where
  obj j := mappingCone (f.app j)
  map {j j'} α :=
    mappingCone.map (f.app j) (f.app j') (X₁.map α) (X₂.map α) (f.naturality α).symm
  map_id j := by
    simpa using mappingCone.map_id (f.app j)
  map_comp {i j k} α β := by
    simpa using
      (mappingCone.map_comp
        (f.app i) (f.app j) (f.app k)
        (X₁.map α) (X₂.map α) (f.naturality α).symm
        (X₁.map β) (X₂.map β) (f.naturality β).symm)

/-- Naturality of test legs over the objectwise mapping-cone diagram. -/
abbrev MappingConeTestLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J, mappingCone (f.app j) ⟶ T) : Prop :=
  ∀ {j j' : J} (α : j ⟶ j'),
    mappingCone.map (f.app j) (f.app j') (X₁.map α) (X₂.map α) (f.naturality α).symm ≫
      leg j' = leg j

/-- A cocone over the objectwise mapping-cone diagram supplies natural test legs. -/
theorem testCoconeLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ CochainComplex MetrizableLCA.{0} ℤ}
    (f : X₁ ⟶ X₂)
    (s : CategoryTheory.Limits.Cocone (mappingConeDiagram X₁ X₂ f)) :
    MappingConeTestLegNaturality f (fun j => s.ι.app j) := by
  intro j j' α
  simpa [mappingConeDiagram] using s.w α

/-- Machine-readable W339 state. -/
structure WppOpMappingConeTestCoconeNaturalityState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W339 state. -/
def currentWppOpMappingConeTestCoconeNaturalityState :
    WppOpMappingConeTestCoconeNaturalityState where
  checkedLemma := "testCoconeLegNaturality"
  remainingInputs :=
    ["identify W308's bounded mappingConeDiagram with this ambient cochain-complex diagram",
      "instantiate W338 global_descEq_of_mappingConeLegs using the included c₁/c₂ cocones",
      "package the resulting descEq with W327-W330 fac/uniq fields"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeTestCoconeNaturalityState_productSuccess :
    currentWppOpMappingConeTestCoconeNaturalityState.productSuccessClaimed = false := rfl

section Checks

#check testCoconeLegNaturality
#check currentWppOpMappingConeTestCoconeNaturalityState
#check currentWppOpMappingConeTestCoconeNaturalityState_productSuccess

end Checks

end WppOpMappingConeTestCoconeNaturalityW339

end LeanLCAExactChallenge
