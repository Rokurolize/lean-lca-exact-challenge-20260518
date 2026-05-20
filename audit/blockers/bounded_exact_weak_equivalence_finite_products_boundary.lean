import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
Bounded exact weak equivalence finite-product boundary.

The MetrizableLCA route is currently blocked below this level by the degreewise comparison
between mapping cones and products.  This file records the exact upper interface: once finite
products of bounded morphisms are known to have exact-acyclic mapping cones, mathlib's
`MorphismProperty.IsStableUnderFiniteProducts` instance follows immediately.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedExactWeakEquivalenceFiniteProductsBoundary

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
  [HasBinaryBiproducts C]

/--
The remaining finite-product mapping-cone input for `boundedExactWeakEquivalence`.

It is intentionally stated at the `Limits.Pi.map` level because that is exactly the API used by
`MorphismProperty.IsStableUnderProductsOfShape.mk`.
-/
abbrev FiniteProductMappingConeInput : Prop :=
  ∀ (J : Type) [Finite J]
    (X₁ X₂ : J → BoundedComplexCategory C) [HasProduct X₁] [HasProduct X₂]
    (f : ∀ j, X₁ j ⟶ X₂ j),
    (∀ j, boundedExactWeakEquivalence C (f j)) →
      boundedExactWeakEquivalence C (Limits.Pi.map f)

/--
The upper closure step for finite products of bounded exact weak equivalences.

This does not prove the mapping-cone comparison.  It proves that no further localization API is
missing above that comparison: the input above directly gives the class required by
`Dbounded.hasFiniteProductsOfStableFiniteProducts`.
-/
theorem isStableUnderFiniteProducts_of_finiteProductMappingConeInput
    (h : FiniteProductMappingConeInput C) :
    (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ := by
    exact MorphismProperty.IsStableUnderProductsOfShape.mk
      (boundedExactWeakEquivalence C) J
      (h J)

/-- The Dbounded finite-product API that becomes available after the same input is installed. -/
noncomputable abbrev dboundedHasFiniteProductsOf_finiteProductMappingConeInput
    [HasFiniteLimits C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    (h : FiniteProductMappingConeInput C) :
    HasFiniteProducts (Dbounded C) := by
  haveI : (boundedExactWeakEquivalence C).IsStableUnderFiniteProducts :=
    isStableUnderFiniteProducts_of_finiteProductMappingConeInput C h
  exact Dbounded.hasFiniteProductsOfStableFiniteProducts C

section MetrizableLCA

/--
The product of bounded complexes, included into cochain complexes, is the cochain-complex product
of the included components.
-/
noncomputable def includedProductIso
    {J : Type w} [Finite J]
    (X : J → BoundedComplexCategory MetrizableLCA.{u}) [HasProduct X] :
    (BoundedComplexCategory.ι MetrizableLCA).obj (∏ᶜ X) ≅
      ∏ᶜ fun j => (BoundedComplexCategory.ι MetrizableLCA).obj (X j) :=
  preservesLimitIso (BoundedComplexCategory.ι MetrizableLCA) (Discrete.functor X) ≪≫
    (Limits.Pi.isoLimit
      (Discrete.functor X ⋙ BoundedComplexCategory.ι MetrizableLCA)).symm

theorem includedProductIso_hom_π
    {J : Type w} [Finite J]
    (X : J → BoundedComplexCategory MetrizableLCA.{u}) [HasProduct X] (j : J) :
    (includedProductIso X).hom ≫
        Limits.Pi.π (fun j => (BoundedComplexCategory.ι MetrizableLCA).obj (X j)) j =
      (BoundedComplexCategory.ι MetrizableLCA).map (Limits.Pi.π X j) := by
  dsimp [includedProductIso]
  rw [Category.assoc]
  exact
    (congrArg
        (fun g =>
          (preservesLimitIso (BoundedComplexCategory.ι MetrizableLCA)
              (Discrete.functor X)).hom ≫ g)
        (Limits.Pi.isoLimit_inv_π
          (X := Discrete.functor X ⋙ BoundedComplexCategory.ι MetrizableLCA) j)).trans
      (preservesLimitIso_hom_π
        (G := BoundedComplexCategory.ι MetrizableLCA) (F := Discrete.functor X)
        (Discrete.mk j))

/--
The bounded-category finite product map agrees, after inclusion, with the cochain-complex finite
product map, up to the canonical product-preservation isomorphisms.
-/
theorem includedProductMap_naturality
    {J : Type w} [Finite J]
    {X Y : J → BoundedComplexCategory MetrizableLCA.{u}}
    [HasProduct X] [HasProduct Y]
    (f : ∀ j, X j ⟶ Y j) :
    (BoundedComplexCategory.ι MetrizableLCA).map (Limits.Pi.map f) ≫
        (includedProductIso Y).hom =
      (includedProductIso X).hom ≫
        Limits.Pi.map (fun j => (BoundedComplexCategory.ι MetrizableLCA).map (f j)) := by
  apply Limits.Pi.hom_ext
  intro j
  rw [Category.assoc]
  rw [includedProductIso_hom_π]
  rw [Category.assoc]
  rw [Limits.Pi.map_π]
  rw [← Category.assoc]
  rw [includedProductIso_hom_π]
  rw [← Functor.map_comp, ← Functor.map_comp]
  change ((Limits.Pi.map f ≫ Limits.Pi.π Y j).hom = (Limits.Pi.π X j ≫ f j).hom)
  exact congrArg (fun g : (∏ᶜ X) ⟶ Y j => g.hom) (Limits.Pi.map_π f j)

/-- The cochain-complex finite product mapping-cone exactness supplied by v232. -/
theorem exactAcyclic_mappingCone_cochain_piMap_of_v232
    {J : Type u} [Finite J]
    {K L : J → CochainComplex MetrizableLCA.{u} ℤ} [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j) [HasProduct (fun j => CochainComplex.mappingCone (f j))]
    (hf : ∀ j, exactAcyclic MetrizableLCA (CochainComplex.mappingCone (f j))) :
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map f)) := by
  have hProduct :
      exactAcyclic MetrizableLCA (∏ᶜ fun j => CochainComplex.mappingCone (f j)) :=
    FiniteProductExactness.finiteExactAcyclicProductClosure_of_w151
      (fun j => CochainComplex.mappingCone (f j)) hf
  exact exactAcyclic_of_iso MetrizableLCA
    (MappingConeFiniteProduct.tailFiniteMappingConeComparisonInput_direct.iso f).symm hProduct

/--
Finite products of bounded exact weak equivalences over `MetrizableLCA` are again bounded exact
weak equivalences.
-/
theorem finiteProductMappingConeInput_metrizableLCA :
    FiniteProductMappingConeInput MetrizableLCA.{0} := by
  intro J _ X₁ X₂ _ _ f hf
  let K : J → CochainComplex MetrizableLCA.{0} ℤ :=
    fun j => (BoundedComplexCategory.ι MetrizableLCA).obj (X₁ j)
  let L : J → CochainComplex MetrizableLCA.{0} ℤ :=
    fun j => (BoundedComplexCategory.ι MetrizableLCA).obj (X₂ j)
  let fι : ∀ j, K j ⟶ L j :=
    fun j => (BoundedComplexCategory.ι MetrizableLCA).map (f j)
  have hfι : ∀ j, exactAcyclic MetrizableLCA (CochainComplex.mappingCone (fι j)) := by
    intro j
    simpa [boundedExactWeakEquivalence, fι] using hf j
  have hCochain :
      exactAcyclic MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map fι)) :=
    exactAcyclic_mappingCone_cochain_piMap_of_v232 fι hfι
  have hcomm :
      (BoundedComplexCategory.ι MetrizableLCA).map (Limits.Pi.map f) ≫
          (includedProductIso X₂).hom =
        (includedProductIso X₁).hom ≫ Limits.Pi.map fι := by
    simpa [fι] using includedProductMap_naturality f
  have hBounded :
      exactAcyclic MetrizableLCA
        (CochainComplex.mappingCone
          ((BoundedComplexCategory.ι MetrizableLCA).map (Limits.Pi.map f))) :=
    (exactAcyclic_mappingCone_congr_iff MetrizableLCA
      (includedProductIso X₁) (includedProductIso X₂) hcomm).2 hCochain
  simpa [boundedExactWeakEquivalence] using hBounded

/-- The resulting finite-product stability instance for bounded exact weak equivalences. -/
theorem isStableUnderFiniteProducts_metrizableLCA :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
  isStableUnderFiniteProducts_of_finiteProductMappingConeInput
    MetrizableLCA.{0} finiteProductMappingConeInput_metrizableLCA

/-- Finite products in `Dbounded MetrizableLCA` after the v232 bounded transfer. -/
noncomputable abbrev dboundedHasFiniteProducts_metrizableLCA
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    HasFiniteProducts (Dbounded MetrizableLCA.{0}) := by
  haveI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
    isStableUnderFiniteProducts_metrizableLCA
  exact Dbounded.hasFiniteProductsOfStableFiniteProducts (C := MetrizableLCA.{0})

end MetrizableLCA

section Checks

#check FiniteProductMappingConeInput
#check isStableUnderFiniteProducts_of_finiteProductMappingConeInput
#check dboundedHasFiniteProductsOf_finiteProductMappingConeInput
#check Dbounded.hasFiniteProductsOfStableFiniteProducts
#check MorphismProperty.IsStableUnderProductsOfShape.mk
#check boundedExactWeakEquivalence
#check includedProductIso
#check includedProductIso_hom_π
#check includedProductMap_naturality
#check exactAcyclic_mappingCone_cochain_piMap_of_v232
#check finiteProductMappingConeInput_metrizableLCA
#check isStableUnderFiniteProducts_metrizableLCA
#check dboundedHasFiniteProducts_metrizableLCA

end Checks

end BoundedExactWeakEquivalenceFiniteProductsBoundary

end LeanLCAExactChallenge
