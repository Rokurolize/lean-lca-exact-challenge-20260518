import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
Finite products of bounded exact weak equivalences over metrizable LCA complexes.

This module transports the cochain-complex finite mapping-cone product comparison through the
bounded-complex inclusion functor.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

universe w u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedFiniteProducts

/-- The included bounded product is the product of the included cochain complexes. -/
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

/-- The included bounded product map agrees with the cochain-complex product map. -/
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

/-- The cochain-complex finite product mapping-cone exactness produced by the finite comparison. -/
theorem exactAcyclic_mappingCone_cochain_piMap
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

/-- Finite products of bounded exact weak equivalences over default-universe `MetrizableLCA`. -/
theorem finiteProductMappingConeInput_metrizableLCA :
    ∀ (J : Type) [Finite J]
      (X₁ X₂ : J → BoundedComplexCategory MetrizableLCA.{0})
      [HasProduct X₁] [HasProduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j),
      (∀ j, boundedExactWeakEquivalence MetrizableLCA (f j)) →
        boundedExactWeakEquivalence MetrizableLCA (Limits.Pi.map f) := by
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
    exactAcyclic_mappingCone_cochain_piMap fι hfι
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

/-- Bounded exact weak equivalences over default-universe `MetrizableLCA` are stable under finite products. -/
theorem isStableUnderFiniteProducts_metrizableLCA :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ := by
    exact MorphismProperty.IsStableUnderProductsOfShape.mk
      (boundedExactWeakEquivalence MetrizableLCA.{0}) J
      (finiteProductMappingConeInput_metrizableLCA J)

/--
Finite products in `Dbounded MetrizableLCA` after the finite mapping-cone transfer.

The remaining premise is the left calculus of fractions for the direct bounded exact weak
equivalences; source finite limits and finite-product stability are supplied by the project.
-/
noncomputable abbrev dboundedHasFiniteProducts_metrizableLCA
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    HasFiniteProducts (Dbounded MetrizableLCA.{0}) := by
  haveI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
    isStableUnderFiniteProducts_metrizableLCA
  exact Dbounded.hasFiniteProductsOfStableFiniteProducts (C := MetrizableLCA.{0})

section Checks

#check includedProductIso
#check includedProductIso_hom_π
#check includedProductMap_naturality
#check exactAcyclic_mappingCone_cochain_piMap
#check finiteProductMappingConeInput_metrizableLCA
#check isStableUnderFiniteProducts_metrizableLCA
#check dboundedHasFiniteProducts_metrizableLCA

end Checks

end BoundedFiniteProducts

end LeanLCAExactChallenge
