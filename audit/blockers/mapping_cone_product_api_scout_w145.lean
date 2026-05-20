import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.FiniteProductExactness
import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

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
  finiteConeProductComparisonConstructor :=
    some "MappingConeFiniteProduct.tailFiniteMappingConeComparisonInput_direct"
  finiteExactAcyclicProductClosure :=
    some "FiniteProductExactness.finiteExactAcyclicProductClosure_of_w151"

theorem currentFiniteProductApiLayerState_comparison_supplied :
      currentFiniteProductApiLayerState.finiteConeProductComparisonConstructor =
        some "MappingConeFiniteProduct.tailFiniteMappingConeComparisonInput_direct" := rfl

theorem currentFiniteProductApiLayerState_closure_supplied :
    currentFiniteProductApiLayerState.finiteExactAcyclicProductClosure =
      some "FiniteProductExactness.finiteExactAcyclicProductClosure_of_w151" := rfl

/--
After v224, the finite exact-acyclic product closure input is supplied for MetrizableLCA.
The remaining finite-product mapping-cone route input is the cone/product comparison.
-/
theorem exactAcyclic_mappingCone_piMap_of_w151_comparison
    (comparison : FiniteMappingConeProductComparisonInput.{u, u, u + 1} MetrizableLCA.{u})
    {J : Type u} [Finite J]
    {K L : J → CochainComplex MetrizableLCA.{u} ℤ} [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j) [HasProduct (fun j => CochainComplex.mappingCone (f j))]
    (hf : ∀ j, exactAcyclic MetrizableLCA (CochainComplex.mappingCone (f j))) :
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map f)) := by
  exact exactAcyclic_mappingCone_piMap_of_comparison MetrizableLCA comparison
    (fun J _ K _ hK =>
      FiniteProductExactness.finiteExactAcyclicProductClosure_of_w151 K hK) f hf

/-- W146 supplies the finite mapping-cone/product comparison needed by this API layer. -/
noncomputable def finiteMappingConeProductComparisonInput_of_w146 :
    FiniteMappingConeProductComparisonInput.{u, u, u + 1} MetrizableLCA.{u} where
  iso := by
    intro J _ K L _ _ f _
    exact
      MappingConeFiniteProduct.tailFiniteMappingConeComparisonInput_direct.iso f

/--
After v231, the W145 finite-product mapping-cone exactness consumer no longer needs an external
comparison input for MetrizableLCA: W146 supplies it directly.
-/
theorem exactAcyclic_mappingCone_piMap_of_w151
    {J : Type u} [Finite J]
    {K L : J → CochainComplex MetrizableLCA.{u} ℤ} [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j) [HasProduct (fun j => CochainComplex.mappingCone (f j))]
    (hf : ∀ j, exactAcyclic MetrizableLCA (CochainComplex.mappingCone (f j))) :
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map f)) :=
  exactAcyclic_mappingCone_piMap_of_w151_comparison
    finiteMappingConeProductComparisonInput_of_w146 f hf

/-- Next proof obligations for the finite generalization route. -/
def finiteGeneralizationNextObligations : List String :=
  []

theorem finiteGeneralizationNextObligations_count :
    finiteGeneralizationNextObligations.length = 0 := rfl

section Checks

#check FiniteMappingConeProductComparisonInput
#check FiniteExactAcyclicProductClosure
#check exactAcyclic_mappingCone_piMap_of_comparison
#check exactAcyclic_mappingCone_piMap_of_w151_comparison
#check finiteMappingConeProductComparisonInput_of_w146
#check exactAcyclic_mappingCone_piMap_of_w151
#check finiteGeneralizationAvailableApi
#check currentFiniteProductApiLayerState
#check currentFiniteProductApiLayerState_comparison_supplied
#check currentFiniteProductApiLayerState_closure_supplied
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
