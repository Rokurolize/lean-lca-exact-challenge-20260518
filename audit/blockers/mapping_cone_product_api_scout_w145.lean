import LeanLCAExactChallenge.Derived.Bounded

/-!
W145 audit: finite-product mapping-cone API scout.

The support worker selected the `finite-generalization` route: isolate the API needed to pass
from the binary `biprod.map` comparison frontier to finite `Limits.Pi.map`.

This file does not construct the comparison. It records a compiling consumer shape and the
currently visible API layers for the next proof.
-/

set_option autoImplicit false

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MappingConeProductApiScoutW145

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/--
Finite mapping-cone/product comparison needed by the `Limits.Pi.map` route.

This is the finite analogue of W142's binary
`CochainComplex.mappingCone (biprod.map f₁ f₂) ≅ mappingCone f₁ ⊞ mappingCone f₂`.
The comparison is stated directly at the product-map level used by
`MorphismProperty.IsStableUnderProductsOfShape.mk`.
-/
structure FiniteMappingConeProductComparisonInput :
    Type (max (max (w + 1) (u + 1)) (v + 1)) where
  iso : ∀ (J : Type w) [Finite J]
    (K L : J → CochainComplex C ℤ) [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j) [HasProduct (fun j => CochainComplex.mappingCone (f j))],
      CochainComplex.mappingCone (Limits.Pi.map f) ≅
        ∏ᶜ (fun j => CochainComplex.mappingCone (f j))

/--
Exact-acyclic finite-product closure for cochain complexes.

For `MetrizableLCA`, v187 supplies only the binary biproduct case
`MetrizableLCA.exactAcyclic_biprod`; the finite-product route still needs either an induction
from that binary theorem plus terminal/zero cases, or a direct finite-product closure theorem.
-/
abbrev FiniteExactAcyclicProductClosure : Prop :=
  ∀ (J : Type w) [Finite J]
    (K : J → CochainComplex C ℤ) [HasProduct K],
      (∀ j, exactAcyclic C (K j)) → exactAcyclic C (∏ᶜ K)

/--
Conditional finite-product consumer.

Once the cone/product comparison and exact-acyclic finite-product closure are supplied, component
exact acyclicity proves exact acyclicity of the mapping cone of `Limits.Pi.map`.
-/
theorem exactAcyclic_mappingCone_piMap_of_comparison
    (comparison : FiniteMappingConeProductComparisonInput.{w, v, u} C)
    (closure : FiniteExactAcyclicProductClosure.{w, v, u} C)
    {J : Type w} [Finite J]
    {K L : J → CochainComplex C ℤ} [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j) [HasProduct (fun j => CochainComplex.mappingCone (f j))]
    (hf : ∀ j, exactAcyclic C (CochainComplex.mappingCone (f j))) :
    exactAcyclic C (CochainComplex.mappingCone (Limits.Pi.map f)) := by
  exact exactAcyclic_of_iso C (comparison.iso J K L f).symm
    (closure J (fun j => CochainComplex.mappingCone (f j)) hf)

/-- Names of the concrete API ingredients found for the finite generalization route. -/
def finiteGeneralizationAvailableApi : List String :=
  ["Limits.Pi.map is the product-map API used by IsStableUnderProductsOfShape.mk",
    "HomologicalComplex.isLimitOfEval builds limits degreewise in complex categories",
    "HomologicalComplex.coneOfHasLimitEval exposes product objects degreewise",
    "CochainComplex.mappingCone.ext_to/ext_from reduce cone object equalities to summands",
    "CochainComplex.mappingCone.lift/desc construct maps to and from a cone",
    "CochainComplex.mappingCone.d_fst_v and d_snd_v expose the differential equations",
    "HomologicalComplex.biprodXIso is available only for the binary specialization"]

/-- Current finite route state after source inspection. -/
structure FiniteProductApiLayerState : Type where
  productMapApi : String
  complexProductApi : String
  coneExtensionalityApi : String
  binaryComplexBiprodIso : String
  finiteConeProductComparisonConstructor : Option String
  finiteExactAcyclicProductClosure : Option String

/-- W145's current finite-product API frontier. -/
def currentFiniteProductApiLayerState : FiniteProductApiLayerState where
  productMapApi := "Limits.Pi.map"
  complexProductApi := "HomologicalComplex.isLimitOfEval / coneOfHasLimitEval"
  coneExtensionalityApi := "CochainComplex.mappingCone.ext_to, ext_from, lift, desc"
  binaryComplexBiprodIso := "HomologicalComplex.biprodXIso"
  finiteConeProductComparisonConstructor := none
  finiteExactAcyclicProductClosure := none

theorem currentFiniteProductApiLayerState_comparison_missing :
    currentFiniteProductApiLayerState.finiteConeProductComparisonConstructor = none := rfl

theorem currentFiniteProductApiLayerState_closure_missing :
    currentFiniteProductApiLayerState.finiteExactAcyclicProductClosure = none := rfl

/-- Next proof obligations for the finite generalization route. -/
def finiteGeneralizationNextObligations : List String :=
  ["build a product-object comparison for mappingCone (Limits.Pi.map f)",
    "prove the comparison commutes with cone differentials using mappingCone.d_fst_v/d_snd_v",
    "package the comparison as FiniteMappingConeProductComparisonInput",
    "derive FiniteExactAcyclicProductClosure for MetrizableLCA from exactAcyclic_biprod",
    "feed both inputs to exactAcyclic_mappingCone_piMap_of_comparison"]

theorem finiteGeneralizationNextObligations_count :
    finiteGeneralizationNextObligations.length = 5 := rfl

section Checks

#check FiniteMappingConeProductComparisonInput
#check FiniteExactAcyclicProductClosure
#check exactAcyclic_mappingCone_piMap_of_comparison
#check finiteGeneralizationAvailableApi
#check currentFiniteProductApiLayerState
#check currentFiniteProductApiLayerState_comparison_missing
#check currentFiniteProductApiLayerState_closure_missing
#check finiteGeneralizationNextObligations
#check finiteGeneralizationNextObligations_count
#check Limits.Pi.map
#check CategoryTheory.MorphismProperty.IsStableUnderProductsOfShape.mk
#check HomologicalComplex.isLimitOfEval
#check HomologicalComplex.coneOfHasLimitEval
#check CochainComplex.mappingCone.ext_to
#check CochainComplex.mappingCone.ext_from
#check CochainComplex.mappingCone.lift
#check CochainComplex.mappingCone.desc
#check CochainComplex.mappingCone.d_fst_v
#check CochainComplex.mappingCone.d_snd_v
#check HomologicalComplex.biprodXIso
#check MetrizableLCA.exactAcyclic_biprod

end Checks

end MappingConeProductApiScoutW145

end LeanLCAExactChallenge
