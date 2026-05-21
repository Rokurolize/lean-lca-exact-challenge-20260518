import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
Finite products of bounded exact weak equivalences over metrizable LCA complexes.

This module transports the cochain-complex finite mapping-cone product comparison through the
bounded-complex inclusion functor.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

universe w v v1 v2 u u1 u2

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {J : Type w} [Category.{v} J]
variable {C : Type u1} {D : Type u2} [Category.{v1} C] [Category.{v2} D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

instance finiteShapeConstCatCommSq :
    CatCommSq (Functor.const J) L
      ((whiskeringRight J C D).obj L) (Functor.const J) where
  iso := (Functor.compConstIso J L).symm

namespace FiniteShapeLimitTransferAux

variable (J) [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]

lemma inverts :
    (W.functorCategory J).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)]

/-- The limit functor on the localized category induced by the source limit functor. -/
noncomputable abbrev limitFunctor :
    (J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts (L := L) (W := W) J) ((whiskeringRight J C D).obj L)

/-- The localized limit functor is induced by `lim ⋙ L`. -/
noncomputable def compLimitFunctorIso :
    ((whiskeringRight J C D).obj L) ⋙ limitFunctor (L := L) (W := W) J ≅
      lim ⋙ L := by
  apply Localization.fac

noncomputable instance :
    CatCommSq lim ((whiskeringRight J C D).obj L) L
      (limitFunctor (L := L) (W := W) J) where
  iso := (compLimitFunctorIso (L := L) (W := W) J).symm

/-- The source constant/limit adjunction descends through the localization functors. -/
noncomputable def adj :
    Functor.const J ⊣ limitFunctor (L := L) (W := W) J :=
  constLimAdj.localization L W ((whiskeringRight J C D).obj L)
    (W.functorCategory J) (Functor.const J) (limitFunctor (L := L) (W := W) J)

end FiniteShapeLimitTransferAux

namespace FiniteShapeColimitTransferAux

variable (J) [HasColimitsOfShape J C] [W.IsStableUnderColimitsOfShape J]

lemma inverts :
    (W.functorCategory J).IsInvertedBy (colim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.colimMap f hf)

variable [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)]

/-- The colimit functor on the localized category induced by the source colimit functor. -/
noncomputable abbrev colimitFunctor :
    (J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts (L := L) (W := W) J) ((whiskeringRight J C D).obj L)

/-- The localized colimit functor is induced by `colim ⋙ L`. -/
noncomputable def compColimitFunctorIso :
    ((whiskeringRight J C D).obj L) ⋙ colimitFunctor (L := L) (W := W) J ≅
      colim ⋙ L := by
  apply Localization.fac

noncomputable instance :
    CatCommSq colim ((whiskeringRight J C D).obj L) L
      (colimitFunctor (L := L) (W := W) J) where
  iso := (compColimitFunctorIso (L := L) (W := W) J).symm

/-- The source colimit/constant adjunction descends through the localization functors. -/
noncomputable def adj :
    colimitFunctor (L := L) (W := W) J ⊣ Functor.const J :=
  colimConstAdj.localization ((whiskeringRight J C D).obj L) (W.functorCategory J)
    L W (colimitFunctor (L := L) (W := W) J) (Functor.const J)

end FiniteShapeColimitTransferAux

include L W in
/-- Transfer limits of one shape through a localization from a functor-category
localization input. -/
lemma hasLimitsOfShape_of_functorCategoryLocalization
    (J : Type w) [Category.{v} J]
    [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]
    [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)] :
    HasLimitsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (FiniteShapeLimitTransferAux.adj (L := L) (W := W) J).isLeftAdjoint

include L W in
/-- Transfer colimits of one shape through a localization from a functor-category
localization input. -/
lemma hasColimitsOfShape_of_functorCategoryLocalization
    (J : Type w) [Category.{v} J]
    [HasColimitsOfShape J C] [W.IsStableUnderColimitsOfShape J]
    [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)] :
    HasColimitsOfShape J D :=
  hasColimitsOfShape_iff_isRightAdjoint_const.2
    (FiniteShapeColimitTransferAux.adj (L := L) (W := W) J).isRightAdjoint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

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
In a preadditive category, finite coproduct stability follows from finite product stability:
finite coproducts are finite biproducts, hence also products, and the product and coproduct
comparison maps are isomorphic as arrows.
-/
theorem finiteCoproductStability_of_finiteProductStability
    {C : Type u} [Category.{v} C] [Preadditive C]
    (W : MorphismProperty C) [HasFiniteCoproducts C]
    [W.RespectsIso] [W.IsStableUnderFiniteProducts] :
    W.IsStableUnderFiniteCoproducts where
  isStableUnderCoproductsOfShape J _ := by
    refine MorphismProperty.IsStableUnderCoproductsOfShape.mk W J ?_
    intro X₁ X₂ _ _ f hf
    letI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
    let F₁ : Discrete J ⥤ C := Discrete.functor X₁
    let F₂ : Discrete J ⥤ C := Discrete.functor X₂
    let η : F₁ ⟶ F₂ := Discrete.natTrans (fun j => f j.as)
    have hη : W.functorCategory (Discrete J) η := by
      intro j
      exact hf j.as
    have hLimitMap : W (Limits.limMap η) :=
      MorphismProperty.limMap (W := W) (J := Discrete J) η hη
    have hColimitMap : W (Limits.colimMap η) := by
      refine (W.arrow_mk_iso_iff ?_).2 hLimitMap
      refine Arrow.isoMk
        ((HasBiproductsOfShape.colimIsoLim (J := J) (C := C)).app F₁)
        ((HasBiproductsOfShape.colimIsoLim (J := J) (C := C)).app F₂) ?_
      exact (HasBiproductsOfShape.colimIsoLim (J := J) (C := C)).hom.naturality η |>.symm
    simpa [Limits.Sigma.map, η, F₁, F₂] using hColimitMap

/-- Bounded exact weak equivalences over default-universe `MetrizableLCA` are stable under finite coproducts. -/
theorem isStableUnderFiniteCoproducts_metrizableLCA :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteCoproducts := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
    isStableUnderFiniteProducts_metrizableLCA
  exact finiteCoproductStability_of_finiteProductStability
    (boundedExactWeakEquivalence MetrizableLCA.{0})

/-- A product of opposite objects gives a coproduct of the original objects. -/
lemma hasCoproduct_unop_of_hasProduct_op
    {C : Type u} [Category.{v} C] {J : Type w}
    (X : J → Cᵒᵖ) [HasProduct X] :
    HasCoproduct (fun j => (X j).unop) := by
  let F : Discrete J ⥤ C := Discrete.functor (fun j => (X j).unop)
  have e : (Discrete.opposite J).symm.functor ⋙ F.op ≅ Discrete.functor X := by
    refine Discrete.natIso ?_
    intro j
    cases j
    rfl
  haveI : HasLimit ((Discrete.opposite J).symm.functor ⋙ F.op) :=
    hasLimit_of_iso e.symm
  haveI : HasLimit F.op :=
    hasLimit_of_equivalence_comp (Discrete.opposite J).symm
  exact hasColimit_of_hasLimit_op F

/-- Stability under coproducts of shape `J` transports to stability under products in `Cᵒᵖ`. -/
theorem op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape
    {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) [W.RespectsIso] {J : Type w}
    [W.IsStableUnderCoproductsOfShape J] :
    W.op.IsStableUnderProductsOfShape J := by
  refine MorphismProperty.IsStableUnderProductsOfShape.mk W.op J ?_
  intro X₁ X₂ _ _ f hf
  let Z₁ : J → C := fun j => (X₁ j).unop
  let Z₂ : J → C := fun j => (X₂ j).unop
  let g : ∀ j, Z₂ j ⟶ Z₁ j := fun j => (f j).unop
  haveI : HasCoproduct Z₁ := hasCoproduct_unop_of_hasProduct_op X₁
  haveI : HasCoproduct Z₂ := hasCoproduct_unop_of_hasProduct_op X₂
  have hg : ∀ j, W (g j) := by
    intro j
    exact hf j
  let F₂ : Discrete J ⥤ C := Discrete.functor Z₂
  let F₁ : Discrete J ⥤ C := Discrete.functor Z₁
  let η : F₂ ⟶ F₁ := Discrete.natTrans (fun i => g i.as)
  have hη : W.functorCategory (Discrete J) η := by
    intro j
    exact hg j.as
  have hSigma : W (Limits.Sigma.map g) := by
    simpa [Limits.Sigma.map, η, F₁, F₂] using
      (MorphismProperty.colimMap (W := W) (J := Discrete J) η hη)
  let eo₁ : op (∐ Z₁) ≅ ∏ᶜ X₁ := by
    simpa [Z₁] using (opCoproductIsoProduct Z₁)
  let eo₂ : op (∐ Z₂) ≅ ∏ᶜ X₂ := by
    simpa [Z₂] using (opCoproductIsoProduct Z₂)
  let e₁ : (∏ᶜ X₁).unop ≅ ∐ Z₁ := eo₁.unop
  let e₂ : (∏ᶜ X₂).unop ≅ ∐ Z₂ := eo₂.unop
  refine (W.arrow_mk_iso_iff ?_).2 hSigma
  refine Arrow.isoMk e₂ e₁ ?_
  apply Quiver.Hom.op_inj
  apply Limits.Pi.hom_ext
  intro j
  dsimp [e₁, e₂, eo₁, eo₂]
  rw [Category.assoc, opCoproductIsoProduct_hom_comp_π]
  rw [Category.assoc, Limits.Pi.map_π]
  have hπ₁ : (opCoproductIsoProduct Z₁).hom ≫ Pi.π X₁ j = (Sigma.ι Z₁ j).op := by
    simpa [Z₁] using (opCoproductIsoProduct_hom_comp_π (Z := Z₁) j)
  conv_rhs => rw [← Category.assoc, hπ₁]
  rw [← op_comp, Limits.Sigma.ι_map]
  simp [g, Z₁, Z₂]

/-- Finite-coproduct stability transports to finite-product stability of the opposite property. -/
theorem op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
    {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) [W.RespectsIso] [W.IsStableUnderFiniteCoproducts] :
    W.op.IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ :=
    op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape W (J := J)

/-- Opposite bounded exact weak equivalences over `MetrizableLCA` are stable under finite
products. -/
theorem isStableUnderFiniteProducts_op_metrizableLCA :
    ((boundedExactWeakEquivalence MetrizableLCA.{0}).op).IsStableUnderFiniteProducts := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteCoproducts :=
    isStableUnderFiniteCoproducts_metrizableLCA
  exact op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
    (boundedExactWeakEquivalence MetrizableLCA.{0})

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
#check finiteCoproductStability_of_finiteProductStability
#check isStableUnderFiniteCoproducts_metrizableLCA
#check op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape
#check op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
#check isStableUnderFiniteProducts_op_metrizableLCA
#check dboundedHasFiniteProducts_metrizableLCA

end Checks

end BoundedFiniteProducts

/--
Finite-limit and finite-colimit data still needed after W530 and the finite-product route.

Finite products in `Dbounded MetrizableLCA` are supplied by
`BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA` under direct bounded left
calculus; preadditivity then turns those finite products into finite coproducts. The remaining
finite (co)limit inputs are therefore equalizers and coequalizers.
-/
structure Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus : Type 1 where
  equalizers : HasEqualizers (Dbounded MetrizableLCA.{0})
  coequalizers : HasCoequalizers (Dbounded MetrizableLCA.{0})

/-- Objectwise localization functor for `WalkingParallelPair` diagrams. -/
noncomputable abbrev Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor :
    (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) :=
  ((Functor.whiskeringRight WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0})
      (Dbounded MetrizableLCA.{0})).obj
      (Dbounded.localization MetrizableLCA.{0}))

/-- Functor-category localization input for the `WalkingParallelPair` finite-shape transfer. -/
abbrev Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.IsLocalization
    ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)

/--
The objectwise functor inverts objectwise bounded exact weak equivalences. After this formal
field, the non-discrete functor-category localization input is reduced to fixed-target
`lift`, `fac`, and `uniq` data.
-/
lemma Dbounded.metrizableWalkingParallelPairObjectwiseLocalization_inverts :
    MorphismProperty.IsInvertedBy
      ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor :=
  fun _ _ f hf => by
    haveI :
        ∀ j : WalkingParallelPair,
          IsIso
            ((Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map f).app j) :=
      fun j =>
        CategoryTheory.Localization.inverts
          (Dbounded.localization MetrizableLCA.{0})
          (boundedExactWeakEquivalence MetrizableLCA.{0})
          (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/-- Expanded fixed-target fields for the `WalkingParallelPair` objectwise localization. -/
structure Dbounded.MetrizableWalkingParallelPairFunctorCategoryFixedTargetFields
    (E : Type*) [Category E] where
  inverts :
    MorphismProperty.IsInvertedBy
      ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor
  lift :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E),
      MorphismProperty.IsInvertedBy
        ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
        F →
        (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤ E
  fac :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E)
      (hF :
        MorphismProperty.IsInvertedBy
          ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
          F),
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤ E),
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
        Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
      F₁ = F₂

/-- Convert the expanded fixed-target package into mathlib's localization input. -/
def Dbounded.MetrizableWalkingParallelPairFunctorCategoryFixedTargetFields.toStrictUniversalProperty
    {E : Type*} [Category E]
    (fields : Dbounded.MetrizableWalkingParallelPairFunctorCategoryFixedTargetFields E) :
    CategoryTheory.Localization.StrictUniversalPropertyFixedTarget
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor
      ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
      E where
  inverts := fields.inverts
  lift := fields.lift
  fac := fields.fac
  uniq := fields.uniq

/--
Remaining fixed-target data after the formal objectwise inversion field has been proved.
These are the two universal-property targets required by `Functor.IsLocalization.mk'`.
-/
structure Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetData
    (E : Type*) [Category E] where
  lift :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E),
      MorphismProperty.IsInvertedBy
        ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
        F →
        (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤ E
  fac :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E)
      (hF :
        MorphismProperty.IsInvertedBy
          ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
          F),
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤ E),
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
        Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
      F₁ = F₂

/-- Add the formal inversion field to a remaining fixed-target package. -/
def Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetData.toFields
    {E : Type*} [Category E]
    (data :
      Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetData E) :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryFixedTargetFields E where
  inverts := Dbounded.metrizableWalkingParallelPairObjectwiseLocalization_inverts
  lift := data.lift
  fac := data.fac
  uniq := data.uniq

/--
The two fixed targets sufficient to prove the `WalkingParallelPair` functor-category
localization: the diagram target category and the canonical localization model.
-/
structure Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetInputs :
    Type 1 where
  targetData :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetData
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  modelData :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetData
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)

/-- Build the W532 functor-category localization input from the two fixed-target packages. -/
theorem Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
    (inputs :
      Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetInputs) :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput :=
  Functor.IsLocalization.mk'
    (L := Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor)
    (W := (boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
      WalkingParallelPair)
    inputs.targetData.toFields.toStrictUniversalProperty
    inputs.modelData.toFields.toStrictUniversalProperty

/-- Strict source data representing one localized `WalkingParallelPair` diagram. -/
structure Dbounded.MetrizableWalkingParallelPairStrictPreimageData
    (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) where
  zeroSrc : BoundedComplexCategory MetrizableLCA.{0}
  oneSrc : BoundedComplexCategory MetrizableLCA.{0}
  zeroIso :
    (Dbounded.localization MetrizableLCA.{0}).obj zeroSrc ≅
      Y.obj WalkingParallelPair.zero
  oneIso :
    (Dbounded.localization MetrizableLCA.{0}).obj oneSrc ≅
      Y.obj WalkingParallelPair.one
  leftSrc : zeroSrc ⟶ oneSrc
  rightSrc : zeroSrc ⟶ oneSrc
  left_fac :
    (Dbounded.localization MetrizableLCA.{0}).map leftSrc =
      zeroIso.hom ≫ Y.map WalkingParallelPairHom.left ≫ oneIso.inv
  right_fac :
    (Dbounded.localization MetrizableLCA.{0}).map rightSrc =
      zeroIso.hom ≫ Y.map WalkingParallelPairHom.right ≫ oneIso.inv

namespace Dbounded.MetrizableWalkingParallelPairStrictPreimageData

/-- The source parallel-pair diagram represented by strict preimage data. -/
def diagram {Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (data : Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y) :
    WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0} :=
  parallelPair data.leftSrc data.rightSrc

/-- The objectwise comparison from the localized strict preimage to the target diagram. -/
noncomputable def comparisonIso {Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (data : Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y) :
    Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj data.diagram ≅ Y :=
  parallelPairIsoMk data.zeroIso data.oneIso
    (by
      dsimp [diagram]
      rw [data.left_fac]
      simp [Category.assoc])
    (by
      dsimp [diagram]
      rw [data.right_fac]
      simp [Category.assoc])

end Dbounded.MetrizableWalkingParallelPairStrictPreimageData

/-- Strict source data representing one natural transformation after localization. -/
structure Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
    {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    (dataY : Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y)
    (dataZ : Dbounded.MetrizableWalkingParallelPairStrictPreimageData Z)
    (τ : Y ⟶ Z) where
  zeroMap : dataY.zeroSrc ⟶ dataZ.zeroSrc
  oneMap : dataY.oneSrc ⟶ dataZ.oneSrc
  zero_fac :
    (Dbounded.localization MetrizableLCA.{0}).map zeroMap =
      dataY.zeroIso.hom ≫ τ.app WalkingParallelPair.zero ≫ dataZ.zeroIso.inv
  one_fac :
    (Dbounded.localization MetrizableLCA.{0}).map oneMap =
      dataY.oneIso.hom ≫ τ.app WalkingParallelPair.one ≫ dataZ.oneIso.inv
  left_naturality : dataY.leftSrc ≫ oneMap = zeroMap ≫ dataZ.leftSrc
  right_naturality : dataY.rightSrc ≫ oneMap = zeroMap ≫ dataZ.rightSrc

namespace Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData

/-- The source natural transformation represented by strict map data. -/
def natTrans {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
    {dataY : Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y}
    {dataZ : Dbounded.MetrizableWalkingParallelPairStrictPreimageData Z}
    {τ : Y ⟶ Z}
    (mapData :
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData dataY dataZ τ) :
    dataY.diagram ⟶ dataZ.diagram :=
  parallelPairHomMk mapData.zeroMap mapData.oneMap
    (by
      dsimp [Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram]
      exact mapData.left_naturality)
    (by
      dsimp [Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram]
      exact mapData.right_naturality)

end Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData

/-- Coherent strict representatives for all localized `WalkingParallelPair` diagrams. -/
structure Dbounded.MetrizableWalkingParallelPairLiftBlueprint where
  objData : ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
    Dbounded.MetrizableWalkingParallelPairStrictPreimageData Y
  mapData :
    ∀ {Y Z : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}} (τ : Y ⟶ Z),
      Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
        (objData Y) (objData Z) τ
  map_id : ∀ (Y : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}),
    (mapData (𝟙 Y)).natTrans = 𝟙 (objData Y).diagram
  map_comp :
    ∀ {Y Z T : WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (mapData (τ ≫ σ)).natTrans = (mapData τ).natTrans ≫ (mapData σ).natTrans

namespace Dbounded.MetrizableWalkingParallelPairLiftBlueprint

/-- Candidate fixed-target `lift` functor from coherent strict representatives. -/
@[simps obj map]
def liftFunctor (blueprint : Dbounded.MetrizableWalkingParallelPairLiftBlueprint)
    {E : Type*} [Category E]
    (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E) :
    (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤ E where
  obj Y := F.obj (blueprint.objData Y).diagram
  map {Y Z} τ := F.map ((blueprint.mapData τ).natTrans)
  map_id Y := by
    rw [blueprint.map_id Y]
    exact F.map_id _
  map_comp τ σ := by
    rw [blueprint.map_comp τ σ]
    exact F.map_comp _ _

end Dbounded.MetrizableWalkingParallelPairLiftBlueprint

/-- Fixed-target factorization equation left after the strict-representative lift is chosen. -/
abbrev Dbounded.MetrizableWalkingParallelPairFixedTargetFacObligation
    (blueprint : Dbounded.MetrizableWalkingParallelPairLiftBlueprint)
    (E : Type*) [Category E] : Prop :=
  ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E)
    (_hF :
      MorphismProperty.IsInvertedBy
        ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)
        F),
    Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙
        blueprint.liftFunctor F = F

/--
Strict-representative lift data normalized on diagrams already coming from the bounded-complex
source category.
-/
structure Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint where
  blueprint : Dbounded.MetrizableWalkingParallelPairLiftBlueprint
  obj_image :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (blueprint.objData
        (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  map_image :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (blueprint.mapData
          (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (obj_image Y) =
      eqToHom (obj_image X) ≫ τ

namespace Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint

/-- Normalization on the source image supplies a natural-isomorphism factorization. -/
noncomputable def facNatIso {E : Type*} [Category E]
    (normalized : Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint)
    (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E) :
    Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙
        normalized.blueprint.liftFunctor F ≅ F :=
  NatIso.ofComponents
    (fun X => F.mapIso (eqToIso (normalized.obj_image X)))
    (fun {X Y} τ => by
      dsimp [Functor.comp_map,
        Dbounded.MetrizableWalkingParallelPairLiftBlueprint.liftFunctor]
      change F.map
            ((normalized.blueprint.mapData
              (Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans) ≫
          F.map (eqToHom (normalized.obj_image Y)) =
        F.map (eqToHom (normalized.obj_image X)) ≫ F.map τ
      rw [← F.map_comp, normalized.map_image, F.map_comp])

/-- Normalized strict representatives supply the equality-level fixed-target `fac` field. -/
theorem fac {E : Type*} [Category E]
    (normalized : Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint) :
    Dbounded.MetrizableWalkingParallelPairFixedTargetFacObligation normalized.blueprint E := by
  intro F _hF
  exact CategoryTheory.Functor.ext
    (fun X => congrArg F.obj (normalized.obj_image X))
    (fun X Y τ => by
      dsimp [Functor.comp_map,
        Dbounded.MetrizableWalkingParallelPairLiftBlueprint.liftFunctor]
      apply (cancel_mono (eqToHom (congrArg F.obj (normalized.obj_image Y)))).1
      simpa [Category.assoc, CategoryTheory.eqToHom_map] using
        congrArg F.map (normalized.map_image τ))

end Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint

/-- Fixed-target uniqueness equation for the objectwise localization functor. -/
abbrev Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
    (E : Type*) [Category E] : Prop :=
  ∀ (F₁ F₂ : (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0}) ⥤ E),
    Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
      Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
    F₁ = F₂

structure Dbounded.MetrizableWalkingParallelPairFixedTargetBlueprintInputs : Type 1 where
  blueprint : Dbounded.MetrizableWalkingParallelPairLiftBlueprint
  target_fac :
    Dbounded.MetrizableWalkingParallelPairFixedTargetFacObligation blueprint
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  target_uniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  model_fac :
    Dbounded.MetrizableWalkingParallelPairFixedTargetFacObligation blueprint
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  model_uniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)

structure Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs : Type 1 where
  normalized : Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
  target_uniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ Dbounded MetrizableLCA.{0})
  model_uniq :
    Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)

/-- Build W537 fixed-target blueprint inputs from normalized representatives and uniqueness. -/
def Dbounded.metrizableWalkingParallelPairFixedTargetInputs_of_normalized
    (inputs : Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs) :
    Dbounded.MetrizableWalkingParallelPairFixedTargetBlueprintInputs where
  blueprint := inputs.normalized.blueprint
  target_fac :=
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint.fac inputs.normalized
  target_uniq := inputs.target_uniq
  model_fac :=
    Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint.fac inputs.normalized
  model_uniq := inputs.model_uniq

/-- Build the two fixed-target packages from one strict-representative lift blueprint. -/
def Dbounded.metrizableWalkingParallelPairFixedTargetInputs_of_blueprint
    (inputs : Dbounded.MetrizableWalkingParallelPairFixedTargetBlueprintInputs) :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetInputs where
  targetData :=
    { lift := fun F _ => inputs.blueprint.liftFunctor F
      fac := inputs.target_fac
      uniq := inputs.target_uniq }
  modelData :=
    { lift := fun F _ => inputs.blueprint.liftFunctor F
      fac := inputs.model_fac
      uniq := inputs.model_uniq }

/-- Build functor-category localization from strict representatives plus `fac` and `uniq`. -/
theorem Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_blueprint
    (inputs : Dbounded.MetrizableWalkingParallelPairFixedTargetBlueprintInputs) :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput :=
  Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
    (Dbounded.metrizableWalkingParallelPairFixedTargetInputs_of_blueprint inputs)

/-- Build functor-category localization from normalized strict representatives and uniqueness. -/
theorem Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
    (inputs : Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs) :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput :=
  Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_blueprint
    (Dbounded.metrizableWalkingParallelPairFixedTargetInputs_of_normalized inputs)

/--
Inputs that transfer equalizers and coequalizers for `Dbounded MetrizableLCA` from the
bounded-complex source category.
-/
structure Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs : Type 1 where
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  functorCategoryLocalization :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput

/--
Finite-shape transfer inputs with the functor-category localization supplied by the two
fixed-target universal-property packages instead of as an opaque instance.
-/
structure Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromFixedTargets :
    Type 1 where
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  fixedTargetInputs :
    Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetInputs

/-- Build W532 transfer inputs from fixed-target functor-category localization data. -/
def Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_fixedTargets
    (inputs : Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromFixedTargets) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability := inputs.colimitStability
  functorCategoryLocalization :=
    Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
      inputs.fixedTargetInputs

/--
Finite-shape transfer inputs with functor-category localization supplied by strict
representatives and the fixed-target `fac`/`uniq` equations.
-/
structure Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromBlueprint :
    Type 1 where
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  blueprintInputs :
    Dbounded.MetrizableWalkingParallelPairFixedTargetBlueprintInputs

/-- Build W532 transfer inputs from strict-representative fixed-target data. -/
def Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_blueprint
    (inputs : Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromBlueprint) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability := inputs.colimitStability
  functorCategoryLocalization :=
    Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_blueprint
      inputs.blueprintInputs

/--
Finite-shape transfer inputs with functor-category localization supplied by normalized
strict representatives and the two fixed-target uniqueness equations.
-/
structure Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromNormalized :
    Type 1 where
  limitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  normalizedInputs :
    Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs

/-- Build W532 transfer inputs from normalized strict-representative fixed-target data. -/
def Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_normalized
    (inputs : Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromNormalized) :
    Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability := inputs.colimitStability
  functorCategoryLocalization :=
    Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
      inputs.normalizedInputs

/-- Equalizers in `Dbounded MetrizableLCA` from finite-shape localization transfer. -/
noncomputable abbrev Dbounded.metrizableHasEqualizersOfWalkingParallelPairTransfer
    (inputs : Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs) :
    HasEqualizers (Dbounded MetrizableLCA.{0}) := by
  letI :
      (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderLimitsOfShape
        WalkingParallelPair := inputs.limitStability
  letI : Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput :=
    inputs.functorCategoryLocalization
  haveI : HasLimitsOfShape WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0}) := by
    infer_instance
  exact CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization
    (Dbounded.localization MetrizableLCA.{0})
    (boundedExactWeakEquivalence MetrizableLCA.{0}) WalkingParallelPair

/-- Coequalizers in `Dbounded MetrizableLCA` from finite-shape localization transfer. -/
noncomputable abbrev Dbounded.metrizableHasCoequalizersOfWalkingParallelPairTransfer
    (inputs : Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs) :
    HasCoequalizers (Dbounded MetrizableLCA.{0}) := by
  letI :
      (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
        WalkingParallelPair := inputs.colimitStability
  letI : Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput :=
    inputs.functorCategoryLocalization
  haveI : HasColimitsOfShape WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0}) := by
    infer_instance
  exact CategoryTheory.Localization.hasColimitsOfShape_of_functorCategoryLocalization
    (Dbounded.localization MetrizableLCA.{0})
    (boundedExactWeakEquivalence MetrizableLCA.{0}) WalkingParallelPair

/-- Build the W531 finite-limit/finite-colimit remainder from finite-shape transfer inputs. -/
noncomputable def Dbounded.metrizableFiniteLimitColimitRemainderOfWalkingParallelPairTransfer
    (inputs : Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs) :
    Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus where
  equalizers := Dbounded.metrizableHasEqualizersOfWalkingParallelPairTransfer inputs
  coequalizers := Dbounded.metrizableHasCoequalizersOfWalkingParallelPairTransfer inputs

/-- Finite limits from the W530 left-calculus fields, finite products, and equalizers. -/
noncomputable abbrev Dbounded.metrizableFiniteLimitsOfLeftCalculusProducts
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (remaining : Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus) :
    HasFiniteLimits (Dbounded MetrizableLCA.{0}) := by
  letI : HasFiniteProducts (Dbounded MetrizableLCA.{0}) :=
    BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA
  letI : HasEqualizers (Dbounded MetrizableLCA.{0}) := remaining.equalizers
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Finite colimits from W530 preadditivity, finite products, and coequalizers. -/
noncomputable abbrev Dbounded.metrizableFiniteColimitsOfLeftCalculusProducts
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (remaining : Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus) :
    HasFiniteColimits (Dbounded MetrizableLCA.{0}) := by
  let available : Dbounded.MetrizableLeftCalculusSemanticFields :=
    Dbounded.metrizableLeftCalculusSemanticFields
  letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
  letI : HasFiniteProducts (Dbounded MetrizableLCA.{0}) :=
    BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA
  haveI : HasFiniteBiproducts (Dbounded MetrizableLCA.{0}) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  letI : HasFiniteCoproducts (Dbounded MetrizableLCA.{0}) := inferInstance
  letI : HasCoequalizers (Dbounded MetrizableLCA.{0}) := remaining.coequalizers
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/--
Remaining stable semantic fields after W530 and the finite-product finite-(co)limit reducer.
-/
structure Dbounded.MetrizablePostFiniteLimitColimitRemainingStableSemanticFields
    (available : Dbounded.MetrizableLeftCalculusSemanticFields) : Type 1 where
  finiteLimitColimitRemainder :
    Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus
  pretriangulated :
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated (Dbounded MetrizableLCA.{0})
  triangulated :
    letI : Preadditive (Dbounded MetrizableLCA.{0}) := available.preadditive
    letI : HasZeroObject (Dbounded MetrizableLCA.{0}) := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
    IsTriangulated (Dbounded MetrizableLCA.{0})

/--
Build the W530 remaining-field record once equalizers, coequalizers, and triangulated data exist.
-/
noncomputable def Dbounded.metrizableRemainingStableSemanticFieldsOfFiniteLimitColimitRemainder
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (remaining :
      Dbounded.MetrizablePostFiniteLimitColimitRemainingStableSemanticFields
        Dbounded.metrizableLeftCalculusSemanticFields) :
    Dbounded.MetrizableRemainingStableSemanticFields
      Dbounded.metrizableLeftCalculusSemanticFields where
  finiteLimits :=
    Dbounded.metrizableFiniteLimitsOfLeftCalculusProducts
      remaining.finiteLimitColimitRemainder
  finiteColimits :=
    Dbounded.metrizableFiniteColimitsOfLeftCalculusProducts
      remaining.finiteLimitColimitRemainder
  pretriangulated := remaining.pretriangulated
  triangulated := remaining.triangulated

/-- Field names remaining after W530 plus finite-product finite-(co)limit reduction. -/
def Dbounded.metrizablePostFiniteLimitColimitRemainingFieldNames : List String :=
  ["HasEqualizers (Dbounded MetrizableLCA)", "HasCoequalizers (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)", "IsTriangulated (Dbounded MetrizableLCA)"]

/-- Four fields remain after finite products reduce the finite-limit and finite-colimit inputs. -/
theorem Dbounded.metrizablePostFiniteLimitColimitRemainingFieldNames_count :
    Dbounded.metrizablePostFiniteLimitColimitRemainingFieldNames.length = 4 :=
  rfl

/-- Finite-shape transfer input names used by the equalizer/coequalizer constructor. -/
def Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputNames : List String :=
  ["IsStableUnderLimitsOfShape WalkingParallelPair",
    "IsStableUnderColimitsOfShape WalkingParallelPair",
    "WalkingParallelPair functor-category localization"]

/-- Three inputs feed the finite-shape transfer constructor. -/
theorem Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputNames_count :
    Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputNames.length = 3 :=
  rfl

/-- Fixed-target data replacing the opaque WPP functor-category localization input. -/
def Dbounded.metrizableWppFunctorCategoryFixedTargetInputNames : List String :=
  ["lift/fac/uniq for WalkingParallelPair ⥤ Dbounded MetrizableLCA",
    "lift/fac/uniq for the WalkingParallelPair localization model"]

theorem Dbounded.metrizableWppFunctorCategoryFixedTargetInputNames_count :
    Dbounded.metrizableWppFunctorCategoryFixedTargetInputNames.length = 2 :=
  rfl

/-- Finite-shape transfer input names when localization is supplied by fixed targets. -/
def Dbounded.metrizableWppFiniteShapeTransferFromFixedTargetsInputNames : List String :=
  ["IsStableUnderLimitsOfShape WalkingParallelPair",
    "IsStableUnderColimitsOfShape WalkingParallelPair",
    "fixed-target lift/fac/uniq for WalkingParallelPair ⥤ Dbounded MetrizableLCA",
    "fixed-target lift/fac/uniq for the WalkingParallelPair localization model"]

theorem Dbounded.metrizableWppFiniteShapeTransferFromFixedTargetsInputNames_count :
    Dbounded.metrizableWppFiniteShapeTransferFromFixedTargetsInputNames.length = 4 :=
  rfl

/-- Fixed-target data when the `lift` field is supplied by strict representatives. -/
def Dbounded.metrizableWppFunctorCategoryBlueprintInputNames : List String :=
  ["coherent strict representatives for WalkingParallelPair diagrams and maps",
    "fac for WalkingParallelPair ⥤ Dbounded MetrizableLCA",
    "uniq for WalkingParallelPair ⥤ Dbounded MetrizableLCA",
    "fac for the WalkingParallelPair localization model",
    "uniq for the WalkingParallelPair localization model"]

theorem Dbounded.metrizableWppFunctorCategoryBlueprintInputNames_count :
    Dbounded.metrizableWppFunctorCategoryBlueprintInputNames.length = 5 :=
  rfl

/-- Finite-shape transfer input names when localization comes from strict representatives. -/
def Dbounded.metrizableWppFiniteShapeTransferFromBlueprintInputNames : List String :=
  ["IsStableUnderLimitsOfShape WalkingParallelPair",
    "IsStableUnderColimitsOfShape WalkingParallelPair",
    "coherent strict representatives for fixed-target lift",
    "fixed-target fac/uniq equations for the target and localization model"]

theorem Dbounded.metrizableWppFiniteShapeTransferFromBlueprintInputNames_count :
    Dbounded.metrizableWppFiniteShapeTransferFromBlueprintInputNames.length = 4 :=
  rfl

/-- Input names for the normalized strict-representative lift route. -/
def Dbounded.metrizableWppNormalizedLiftBlueprintInputNames : List String :=
  ["coherent strict representatives for WalkingParallelPair diagrams and maps",
    "source-image object normalization",
    "source-image map normalization",
    "target uniqueness",
    "localization-model uniqueness"]

theorem Dbounded.metrizableWppNormalizedLiftBlueprintInputNames_count :
    Dbounded.metrizableWppNormalizedLiftBlueprintInputNames.length = 5 :=
  rfl

/-- Finite-shape transfer input names when localization comes from normalized representatives. -/
def Dbounded.metrizableWppFiniteShapeTransferFromNormalizedInputNames : List String :=
  ["IsStableUnderLimitsOfShape WalkingParallelPair",
    "IsStableUnderColimitsOfShape WalkingParallelPair",
    "normalized strict representatives for fixed-target lift",
    "target and localization-model uniqueness"]

theorem Dbounded.metrizableWppFiniteShapeTransferFromNormalizedInputNames_count :
    Dbounded.metrizableWppFiniteShapeTransferFromNormalizedInputNames.length = 4 :=
  rfl

section DboundedFiniteShapeTransferChecks

#check CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization
#check CategoryTheory.Localization.hasColimitsOfShape_of_functorCategoryLocalization
#check Dbounded.metrizableWalkingParallelPairObjectwiseLocalizationFunctor
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
#check Dbounded.metrizableWalkingParallelPairObjectwiseLocalization_inverts
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryFixedTargetFields
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetData
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryRemainingFixedTargetInputs
#check Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
#check Dbounded.MetrizableWalkingParallelPairStrictPreimageData
#check Dbounded.MetrizableWalkingParallelPairStrictPreimageData.diagram
#check Dbounded.MetrizableWalkingParallelPairStrictPreimageData.comparisonIso
#check Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData
#check Dbounded.MetrizableWalkingParallelPairStrictPreimageMapData.natTrans
#check Dbounded.MetrizableWalkingParallelPairLiftBlueprint
#check Dbounded.MetrizableWalkingParallelPairLiftBlueprint.liftFunctor
#check Dbounded.MetrizableWalkingParallelPairFixedTargetFacObligation
#check Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint
#check Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint.facNatIso
#check Dbounded.MetrizableWalkingParallelPairNormalizedLiftBlueprint.fac
#check Dbounded.MetrizableWalkingParallelPairFixedTargetUniqObligation
#check Dbounded.MetrizableWalkingParallelPairFixedTargetBlueprintInputs
#check Dbounded.MetrizableWalkingParallelPairNormalizedFixedTargetInputs
#check Dbounded.metrizableWalkingParallelPairFixedTargetInputs_of_normalized
#check Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_normalized
#check Dbounded.metrizableWalkingParallelPairFixedTargetInputs_of_blueprint
#check Dbounded.metrizableWalkingParallelPairFunctorCategoryLocalization_of_blueprint
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromFixedTargets
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_fixedTargets
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromBlueprint
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_blueprint
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputsFromNormalized
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputs_of_normalized
#check Dbounded.metrizableHasEqualizersOfWalkingParallelPairTransfer
#check Dbounded.metrizableHasCoequalizersOfWalkingParallelPairTransfer
#check Dbounded.metrizableFiniteLimitColimitRemainderOfWalkingParallelPairTransfer
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputNames
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputNames_count
#check Dbounded.metrizableWppFunctorCategoryFixedTargetInputNames
#check Dbounded.metrizableWppFunctorCategoryFixedTargetInputNames_count
#check Dbounded.metrizableWppFiniteShapeTransferFromFixedTargetsInputNames
#check Dbounded.metrizableWppFiniteShapeTransferFromFixedTargetsInputNames_count
#check Dbounded.metrizableWppFunctorCategoryBlueprintInputNames
#check Dbounded.metrizableWppFunctorCategoryBlueprintInputNames_count
#check Dbounded.metrizableWppFiniteShapeTransferFromBlueprintInputNames
#check Dbounded.metrizableWppFiniteShapeTransferFromBlueprintInputNames_count
#check Dbounded.metrizableWppNormalizedLiftBlueprintInputNames
#check Dbounded.metrizableWppNormalizedLiftBlueprintInputNames_count
#check Dbounded.metrizableWppFiniteShapeTransferFromNormalizedInputNames
#check Dbounded.metrizableWppFiniteShapeTransferFromNormalizedInputNames_count

end DboundedFiniteShapeTransferChecks

end LeanLCAExactChallenge
