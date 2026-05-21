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

/-- Functor-category localization input for the `WalkingParallelPair` finite-shape transfer. -/
abbrev Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  ((Functor.whiskeringRight WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0})
      (Dbounded MetrizableLCA.{0})).obj
      (Dbounded.localization MetrizableLCA.{0})).IsLocalization
    ((boundedExactWeakEquivalence MetrizableLCA.{0}).functorCategory WalkingParallelPair)

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

section DboundedFiniteShapeTransferChecks

#check CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization
#check CategoryTheory.Localization.hasColimitsOfShape_of_functorCategoryLocalization
#check Dbounded.MetrizableWalkingParallelPairFunctorCategoryLocalizationInput
#check Dbounded.MetrizableWalkingParallelPairFiniteShapeTransferInputs
#check Dbounded.metrizableHasEqualizersOfWalkingParallelPairTransfer
#check Dbounded.metrizableHasCoequalizersOfWalkingParallelPairTransfer
#check Dbounded.metrizableFiniteLimitColimitRemainderOfWalkingParallelPairTransfer
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputNames
#check Dbounded.metrizableWalkingParallelPairFiniteShapeTransferInputNames_count

end DboundedFiniteShapeTransferChecks

end LeanLCAExactChallenge
