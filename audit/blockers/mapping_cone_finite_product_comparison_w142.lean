import LeanLCAExactChallenge.Derived.MappingConeBiprod

/-!
W142 audit: lower mapping-cone finite-product comparison frontier.

The v187 product API now proves exact-acyclic binary biproduct closure for MetrizableLCA
cochain complexes as `MetrizableLCA.exactAcyclic_biprod`.  This file isolates the next
lower input: to use that closure for finite-product stability of `boundedExactWeakEquivalence`,
one still needs a comparison between the mapping cone of a product/biproduct map and the
product/biproduct of the component mapping cones.

This is an obstruction/frontier audit, not a finite-product stability proof.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MappingConeFiniteProductComparisonW142

/--
Binary mapping-cone comparison for the product-map route.

For finite-product stability this is the lower missing bridge: component weak equivalences give
`exactAcyclic` for the two component mapping cones, and v187 supplies binary biproduct closure,
but those facts apply to `mappingCone f₁ ⊞ mappingCone f₂`, not directly to the cone of the
biproduct map `biprod.map f₁ f₂`.
-/
structure BinaryMappingConeBiprodComparisonInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  iso : ∀ {K₁ K₂ L₁ L₂ : CochainComplex C ℤ}
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂),
      CochainComplex.mappingCone (biprod.map f₁ f₂) ≅
        CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂

/-- The exact-acyclic closure fact supplied by the v187 product API. -/
abbrev BinaryExactAcyclicBiprodClosure
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Prop :=
  ∀ (K L : CochainComplex C ℤ),
    exactAcyclic C K → exactAcyclic C L → exactAcyclic C (K ⊞ L)

/--
Consumer theorem: biproduct exact-acyclic closure becomes useful for a product map only after
the mapping-cone comparison is supplied.
-/
theorem exactAcyclic_mappingCone_biprodMap_of_comparison
    (comparison : BinaryMappingConeBiprodComparisonInput MetrizableLCA.{u})
    (closure : BinaryExactAcyclicBiprodClosure MetrizableLCA.{u})
    {K₁ K₂ L₁ L₂ : CochainComplex MetrizableLCA.{u} ℤ}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (hf₁ : exactAcyclic MetrizableLCA (CochainComplex.mappingCone f₁))
    (hf₂ : exactAcyclic MetrizableLCA (CochainComplex.mappingCone f₂)) :
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (biprod.map f₁ f₂)) := by
  exact exactAcyclic_of_iso MetrizableLCA (comparison.iso f₁ f₂).symm
    (closure (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) hf₁ hf₂)

/-- The current product API supplies the closure argument for the binary MetrizableLCA route. -/
theorem exactAcyclic_mappingCone_biprodMap_of_v187_comparison
    (comparison : BinaryMappingConeBiprodComparisonInput MetrizableLCA.{u})
    {K₁ K₂ L₁ L₂ : CochainComplex MetrizableLCA.{u} ℤ}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (hf₁ : exactAcyclic MetrizableLCA (CochainComplex.mappingCone f₁))
    (hf₂ : exactAcyclic MetrizableLCA (CochainComplex.mappingCone f₂)) :
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (biprod.map f₁ f₂)) :=
  exactAcyclic_mappingCone_biprodMap_of_comparison comparison
    (fun K L => MetrizableLCA.exactAcyclic_biprod K L) hf₁ hf₂

/-- The v204 component-map comparison supplies the binary mapping-cone input. -/
noncomputable def binaryMappingConeBiprodComparisonInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    BinaryMappingConeBiprodComparisonInput C where
  iso f₁ f₂ := MappingConeBiprodComparison.binaryMappingConeBiprodIso f₁ f₂

/--
The current parent route now closes the lower binary comparison input for MetrizableLCA
product-map exact-acyclicity.
-/
theorem exactAcyclic_mappingCone_biprodMap_of_v204
    {K₁ K₂ L₁ L₂ : CochainComplex MetrizableLCA.{u} ℤ}
    {f₁ : K₁ ⟶ L₁} {f₂ : K₂ ⟶ L₂}
    (hf₁ : exactAcyclic MetrizableLCA (CochainComplex.mappingCone f₁))
    (hf₂ : exactAcyclic MetrizableLCA (CochainComplex.mappingCone f₂)) :
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (biprod.map f₁ f₂)) :=
  exactAcyclic_mappingCone_biprodMap_of_v187_comparison
    (binaryMappingConeBiprodComparisonInput MetrizableLCA) hf₁ hf₂

/-- Product-map finite-product stability requires one more input than biproduct closure. -/
def binaryProductMapRequiredInputNames : List String :=
  ["component mapping-cone exact-acyclicity",
    "binary exact-acyclic biproduct closure",
    "mapping-cone comparison for biprod.map"]

/-- The v187 product API supplies closure, but not the comparison map. -/
def v187SuppliedInputNames : List String :=
  ["component mapping-cone exact-acyclicity",
    "binary exact-acyclic biproduct closure"]

theorem v187SuppliedInputs_are_not_all_binaryProductInputs :
    v187SuppliedInputNames.length < binaryProductMapRequiredInputNames.length := by
  decide

/--
State record for the lower finite-product frontier.

`comparisonConstructor` is deliberately optional: at v187/w142 the audit found the closure
consumer shape, but no named constructor proving the mapping-cone comparison.
-/
structure BinaryMappingConeProductFrontierState : Type where
  exactAcyclicBiprodClosure : String
  comparisonConstructor : Option String
  upperFiniteProductConsumer : String

/-- Current v187 state for the lower mapping-cone finite-product route. -/
def currentBinaryMappingConeProductFrontierState : BinaryMappingConeProductFrontierState where
  exactAcyclicBiprodClosure := "MetrizableLCA.exactAcyclic_biprod"
  comparisonConstructor := some "MappingConeBiprodComparison.binaryMappingConeBiprodIso"
  upperFiniteProductConsumer :=
    "BoundedExactWeakEquivalenceFiniteProductsBoundary.FiniteProductMappingConeInput"

theorem currentBinaryMappingConeProductFrontierState_comparison_supplied :
    currentBinaryMappingConeProductFrontierState.comparisonConstructor =
      some "MappingConeBiprodComparison.binaryMappingConeBiprodIso" := rfl

def completedMappingConeComparisonSteps : List String :=
  ["constructed the biproduct-map cone object comparison",
    "proved componentwise differential compatibility",
    "packaged the comparison as MappingConeBiprodComparison.binaryMappingConeBiprodIso",
    "used the comparison with exactAcyclic_of_iso and MetrizableLCA.exactAcyclic_biprod"]

theorem completedMappingConeComparisonSteps_count :
    completedMappingConeComparisonSteps.length = 4 := rfl

section Checks

#check BinaryMappingConeBiprodComparisonInput
#check BinaryExactAcyclicBiprodClosure
#check exactAcyclic_mappingCone_biprodMap_of_comparison
#check exactAcyclic_mappingCone_biprodMap_of_v187_comparison
#check binaryMappingConeBiprodComparisonInput
#check exactAcyclic_mappingCone_biprodMap_of_v204
#check binaryProductMapRequiredInputNames
#check v187SuppliedInputNames
#check v187SuppliedInputs_are_not_all_binaryProductInputs
#check BinaryMappingConeProductFrontierState
#check currentBinaryMappingConeProductFrontierState
#check currentBinaryMappingConeProductFrontierState_comparison_supplied
#check completedMappingConeComparisonSteps
#check completedMappingConeComparisonSteps_count
#check boundedExactWeakEquivalence
#check exactAcyclic_of_iso
#check MetrizableLCA.exactAcyclic_biprod
#check MappingConeBiprodComparison.binaryMappingConeBiprodIso
#check CochainComplex.mappingCone
#check biprod.map

end Checks

end MappingConeFiniteProductComparisonW142

end LeanLCAExactChallenge
