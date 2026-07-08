import LeanLCAExactChallenge.Derived.ExactAcyclicCorrect
import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
# Closure API for cycle-object exact acyclicity

This file ports the reusable closure surface from the legacy degreewise
`exactAcyclic` predicate to the corrected cycle-object predicate
`exactAcyclicWithCycles`.

The declarations here intentionally keep the corrected route separate from the
legacy `boundedExactWeakEquivalence` route in `Derived.Bounded`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace ExactAcyclicWithCyclesClosure

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- Extract the corrected mapping-cone acyclicity witness from a corrected bounded weak equivalence. -/
theorem exactAcyclicWithCycles_mappingCone_of_boundedExactWeakEquivalenceWithCycles
    [HasBinaryBiproducts C]
    {K L : BoundedComplexCategory C} {f : K ⟶ L}
    (hf : boundedExactWeakEquivalenceWithCycles C f) :
    exactAcyclicWithCycles C
      (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f)) :=
  hf

/-- Build a corrected bounded weak equivalence from corrected mapping-cone acyclicity. -/
theorem boundedExactWeakEquivalenceWithCycles_of_exactAcyclicWithCycles_mappingCone
    [HasBinaryBiproducts C]
    {K L : BoundedComplexCategory C} {f : K ⟶ L}
    (hf : exactAcyclicWithCycles C
      (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f))) :
    boundedExactWeakEquivalenceWithCycles C f :=
  hf

/-- Corrected bounded weak equivalences are invariant under isomorphism of arrows. -/
noncomputable instance boundedExactWeakEquivalenceWithCycles_respectsIso
    [HasBinaryBiproducts C] :
    (boundedExactWeakEquivalenceWithCycles C).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf
  let eK : (BoundedComplexCategory.ι C).obj f.left ≅
      (BoundedComplexCategory.ι C).obj g.left :=
    (BoundedComplexCategory.ι C).mapIso (asIso e.hom.left)
  let eL : (BoundedComplexCategory.ι C).obj f.right ≅
      (BoundedComplexCategory.ι C).obj g.right :=
    (BoundedComplexCategory.ι C).mapIso (asIso e.hom.right)
  have comm : (BoundedComplexCategory.ι C).map f.hom ≫ eL.hom =
      eK.hom ≫ (BoundedComplexCategory.ι C).map g.hom := by
    dsimp [eK, eL]
    change f.hom.hom ≫ e.hom.right.hom = e.hom.left.hom ≫ g.hom.hom
    exact congrArg (fun k : f.left ⟶ g.right => k.hom) e.hom.w.symm
  exact (exactAcyclicWithCycles_mappingCone_congr_iff C eK eL comm).1 hf

/-- Corrected bounded weak equivalences are invariant under cochain shifts. -/
theorem boundedExactWeakEquivalenceWithCycles_shift_iff [HasBinaryBiproducts C]
    {K L : BoundedComplexCategory C} (f : K ⟶ L) (n : ℤ) :
    boundedExactWeakEquivalenceWithCycles C (f⟦n⟧') ↔
      boundedExactWeakEquivalenceWithCycles C f := by
  let ι : BoundedComplexCategory C ⥤ CochainComplex C ℤ := BoundedComplexCategory.ι C
  change exactAcyclicWithCycles C (CochainComplex.mappingCone (ι.map (f⟦n⟧'))) ↔
    exactAcyclicWithCycles C (CochainComplex.mappingCone (ι.map f))
  exact (exactAcyclicWithCycles_mappingCone_congr_iff C ((ι.commShiftIso n).app K)
    ((ι.commShiftIso n).app L) (by
      simp)).trans
    (exactAcyclicWithCycles_mappingCone_shift_iff C (ι.map f) n)

/-- The corrected weak equivalences on bounded complexes are compatible with shifts. -/
noncomputable instance boundedExactWeakEquivalenceWithCycles_isCompatibleWithShift
    [HasBinaryBiproducts C] :
    (boundedExactWeakEquivalenceWithCycles C).IsCompatibleWithShift ℤ where
  condition n := by
    ext K L f
    exact boundedExactWeakEquivalenceWithCycles_shift_iff C f n

namespace MetrizableLCA

/-- Corrected finite product closure target for metrizable LCA cochain complexes. -/
abbrev FiniteExactAcyclicWithCyclesProductClosure : Prop :=
  ∀ {J : Type u} [Finite J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K],
      (∀ j, exactAcyclicWithCycles MetrizableLCA (K j)) →
        exactAcyclicWithCycles MetrizableLCA (∏ᶜ K)

/-- Corrected acyclicity for an empty finite product, transported from the zero complex. -/
theorem exactAcyclicWithCycles_emptyProduct
    {J : Type u} [IsEmpty J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K] :
    exactAcyclicWithCycles MetrizableLCA (∏ᶜ K) :=
  exactAcyclicWithCycles_of_iso MetrizableLCA
    (FiniteProductExactness.emptyProductIsoZero K).symm
    (exactAcyclicWithCycles_zero MetrizableLCA)

/-- The Option induction step from product decomposition and corrected binary closure. -/
theorem exactAcyclicWithCycles_optionProduct_of_optionProductIsoBiprod
    (input : FiniteProductExactness.FiniteProductOptionDecompositionInput.{u})
    {J : Type u} [Finite J]
    (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
    [HasProduct K] [HasProduct (fun j : J => K (some j))]
    (hK : ∀ j, exactAcyclicWithCycles MetrizableLCA (K j))
    (hTail : exactAcyclicWithCycles MetrizableLCA (∏ᶜ (fun j : J => K (some j)))) :
    exactAcyclicWithCycles MetrizableLCA (∏ᶜ K) := by
  exact exactAcyclicWithCycles_of_iso MetrizableLCA (input.optionProductIsoBiprod K).symm
    (MetrizableLCA.exactAcyclicWithCycles_biprod (K none)
      (∏ᶜ (fun j : J => K (some j))) (hK none) hTail)

/-- Corrected finite product closure from the empty product base case and Option step. -/
theorem finiteExactAcyclicWithCyclesProductClosure_of_optionProductIsoBiprod
    (input : FiniteProductExactness.FiniteProductOptionDecompositionInput.{u}) :
    FiniteExactAcyclicWithCyclesProductClosure.{u} := by
  let P : Type u → Prop :=
    fun J =>
      ∀ (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K],
        (∀ j, exactAcyclicWithCycles MetrizableLCA (K j)) →
          exactAcyclicWithCycles MetrizableLCA (∏ᶜ K)
  refine Finite.induction_empty_option (P := P) ?of_equiv ?h_empty ?h_option
  · intro α β e hα K _ hK
    letI : HasProduct (K ∘ e) :=
      hasProduct_of_equiv_of_iso K (K ∘ e) e (fun _ => Iso.refl _)
    exact exactAcyclicWithCycles_of_iso MetrizableLCA (Pi.reindex e K)
      (hα (K ∘ e) (fun j => hK (e j)))
  · intro K _ _
    exact exactAcyclicWithCycles_emptyProduct K
  · intro α _ hα K _ hK
    letI : HasProduct (fun j : α => K (some j)) := by infer_instance
    exact exactAcyclicWithCycles_optionProduct_of_optionProductIsoBiprod input K hK
      (hα (fun j : α => K (some j)) (fun j => hK (some j)))

/-- The W151 Option-product comparison closes corrected finite product closure. -/
theorem finiteExactAcyclicWithCyclesProductClosure_of_w151 :
    FiniteExactAcyclicWithCyclesProductClosure.{u} :=
  finiteExactAcyclicWithCyclesProductClosure_of_optionProductIsoBiprod
    FiniteProductExactness.finiteProductOptionDecompositionInput_of_w151

/-- Corrected cochain-complex finite product mapping-cone exactness. -/
theorem exactAcyclicWithCycles_mappingCone_cochain_piMap
    {J : Type u} [Finite J]
    {K L : J → CochainComplex MetrizableLCA.{u} ℤ} [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j) [HasProduct (fun j => CochainComplex.mappingCone (f j))]
    (hf : ∀ j, exactAcyclicWithCycles MetrizableLCA (CochainComplex.mappingCone (f j))) :
    exactAcyclicWithCycles MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map f)) := by
  have hProduct :
      exactAcyclicWithCycles MetrizableLCA (∏ᶜ fun j => CochainComplex.mappingCone (f j)) :=
    finiteExactAcyclicWithCyclesProductClosure_of_w151
      (fun j => CochainComplex.mappingCone (f j)) hf
  exact exactAcyclicWithCycles_of_iso MetrizableLCA
    (MappingConeFiniteProduct.tailFiniteMappingConeComparisonInput_direct.iso f).symm hProduct

/-- Finite products of corrected bounded weak equivalences over default-universe `MetrizableLCA`. -/
theorem finiteProductMappingConeInput_metrizableLCA :
    ∀ (J : Type) [Finite J]
      (X₁ X₂ : J → BoundedComplexCategory MetrizableLCA.{0})
      [HasProduct X₁] [HasProduct X₂]
      (f : ∀ j, X₁ j ⟶ X₂ j),
      (∀ j, boundedExactWeakEquivalenceWithCycles MetrizableLCA (f j)) →
        boundedExactWeakEquivalenceWithCycles MetrizableLCA (Limits.Pi.map f) := by
  intro J _ X₁ X₂ _ _ f hf
  let K : J → CochainComplex MetrizableLCA.{0} ℤ :=
    fun j => (BoundedComplexCategory.ι MetrizableLCA).obj (X₁ j)
  let L : J → CochainComplex MetrizableLCA.{0} ℤ :=
    fun j => (BoundedComplexCategory.ι MetrizableLCA).obj (X₂ j)
  let fι : ∀ j, K j ⟶ L j :=
    fun j => (BoundedComplexCategory.ι MetrizableLCA).map (f j)
  have hfι :
      ∀ j, exactAcyclicWithCycles MetrizableLCA (CochainComplex.mappingCone (fι j)) := by
    intro j
    simpa [boundedExactWeakEquivalenceWithCycles, fι] using hf j
  have hCochain :
      exactAcyclicWithCycles MetrizableLCA
        (CochainComplex.mappingCone (Limits.Pi.map fι)) :=
    exactAcyclicWithCycles_mappingCone_cochain_piMap fι hfι
  have hcomm :
      (BoundedComplexCategory.ι MetrizableLCA).map (Limits.Pi.map f) ≫
          (BoundedFiniteProducts.includedProductIso X₂).hom =
        (BoundedFiniteProducts.includedProductIso X₁).hom ≫ Limits.Pi.map fι := by
    simpa [fι] using BoundedFiniteProducts.includedProductMap_naturality f
  have hBounded :
      exactAcyclicWithCycles MetrizableLCA
        (CochainComplex.mappingCone
          ((BoundedComplexCategory.ι MetrizableLCA).map (Limits.Pi.map f))) :=
    (exactAcyclicWithCycles_mappingCone_congr_iff MetrizableLCA
      (BoundedFiniteProducts.includedProductIso X₁)
      (BoundedFiniteProducts.includedProductIso X₂) hcomm).2 hCochain
  simpa [boundedExactWeakEquivalenceWithCycles] using hBounded

/-- Corrected bounded weak equivalences over default-universe `MetrizableLCA` are stable under finite products. -/
theorem isStableUnderFiniteProducts_metrizableLCA :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ := by
    exact MorphismProperty.IsStableUnderProductsOfShape.mk
      (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}) J
      (finiteProductMappingConeInput_metrizableLCA J)

end MetrizableLCA

end ExactAcyclicWithCyclesClosure

end LeanLCAExactChallenge
