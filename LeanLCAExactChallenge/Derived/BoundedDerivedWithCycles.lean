import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesClosure

/-!
# Corrected bounded derived localization surface

This module introduces a separate corrected bounded-derived namespace whose
weak equivalences are `boundedExactWeakEquivalenceWithCycles`. It deliberately
does not replace the legacy `Dbounded` declarations in `Derived.Bounded`.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- The corrected bounded derived ordinary category, localizing bounded complexes at the
cycle-object mapping-cone weak equivalences. -/
abbrev BoundedDerivedCategoryWithCycles [HasBinaryBiproducts C] : Type (max u v) :=
  (boundedExactWeakEquivalenceWithCycles C).Localization

/-- Short name for the corrected bounded derived category. -/
abbrev DboundedWithCycles [HasBinaryBiproducts C] : Type (max u v) :=
  BoundedDerivedCategoryWithCycles C

/-- The localization functor for the corrected bounded derived category. -/
abbrev DboundedWithCycles.localization [HasBinaryBiproducts C] :
    BoundedComplexCategory C ⥤ DboundedWithCycles C :=
  (boundedExactWeakEquivalenceWithCycles C).Q

/-- The ordinary quasicategory nerve attached to the corrected bounded derived localization. -/
abbrev BoundedDerivedOrdinaryQuasicategoryWithCycles [HasBinaryBiproducts C] : SSet.QCat :=
  ⟨CategoryTheory.nerve (BoundedDerivedCategoryWithCycles C), inferInstance⟩

namespace DboundedWithCycles

/-- Under a left-calculus hypothesis, the corrected localization has a preadditive structure. -/
abbrev preadditiveOfHasLeftCalculusOfFractions [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions] :
    Preadditive (DboundedWithCycles C) := by
  infer_instance

/-- Under a left-calculus hypothesis, the corrected localization functor is additive. -/
theorem localization_additiveOfHasLeftCalculusOfFractions [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions] :
    (DboundedWithCycles.localization C).Additive := by
  infer_instance

/-- Under a left-calculus hypothesis, the corrected localization has a zero object. -/
theorem hasZeroObjectOfHasLeftCalculusOfFractions [HasBinaryBiproducts C] [HasZeroObject C]
    [(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions] :
    HasZeroObject (DboundedWithCycles C) := by
  infer_instance

/-- Under a left-calculus hypothesis, corrected localized shifts are additive. -/
theorem shiftFunctor_additiveOfHasLeftCalculusOfFractions [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions] (n : ℤ) :
    (shiftFunctor (DboundedWithCycles C) n).Additive := by
  rw [Localization.functor_additive_iff (DboundedWithCycles.localization C)
    (boundedExactWeakEquivalenceWithCycles C) (shiftFunctor (DboundedWithCycles C) n)]
  exact Functor.additive_of_iso ((DboundedWithCycles.localization C).commShiftIso n)

/-- Under finite limits in the base and finite-product stability of the corrected weak
equivalences, the corrected bounded derived category has finite products. -/
abbrev hasFiniteProductsOfStableFiniteProducts [HasFiniteLimits C]
    [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalenceWithCycles C).IsStableUnderFiniteProducts] :
    HasFiniteProducts (DboundedWithCycles C) := by
  change HasFiniteProducts (boundedExactWeakEquivalenceWithCycles C).Localization
  infer_instance

/-- In the preadditive corrected localization, finite products upgrade to finite biproducts. -/
abbrev hasFiniteBiproductsOfStableFiniteProducts [HasFiniteLimits C]
    [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalenceWithCycles C).IsStableUnderFiniteProducts] :
    HasFiniteBiproducts (DboundedWithCycles C) := by
  letI : Preadditive (DboundedWithCycles C) :=
    DboundedWithCycles.preadditiveOfHasLeftCalculusOfFractions C
  letI : HasFiniteProducts (DboundedWithCycles C) :=
    DboundedWithCycles.hasFiniteProductsOfStableFiniteProducts C
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Finite biproducts supply finite coproducts in the corrected localization. -/
abbrev hasFiniteCoproductsOfStableFiniteProducts [HasFiniteLimits C]
    [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalenceWithCycles C).IsStableUnderFiniteProducts] :
    HasFiniteCoproducts (DboundedWithCycles C) := by
  letI : HasFiniteBiproducts (DboundedWithCycles C) :=
    DboundedWithCycles.hasFiniteBiproductsOfStableFiniteProducts C
  infer_instance

namespace MetrizableLCA

/-- The corrected default-universe metrizable bounded derived category has finite products
once the corrected weak equivalences have a left calculus of fractions. -/
abbrev hasFiniteProducts
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    HasFiniteProducts (DboundedWithCycles MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
    ExactAcyclicWithCyclesClosure.MetrizableLCA.isStableUnderFiniteProducts_metrizableLCA
  exact DboundedWithCycles.hasFiniteProductsOfStableFiniteProducts (C := MetrizableLCA.{0})

/-- The corrected default-universe metrizable bounded derived category has finite biproducts
once the corrected weak equivalences have a left calculus of fractions. -/
abbrev hasFiniteBiproducts
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    HasFiniteBiproducts (DboundedWithCycles MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
    ExactAcyclicWithCyclesClosure.MetrizableLCA.isStableUnderFiniteProducts_metrizableLCA
  exact DboundedWithCycles.hasFiniteBiproductsOfStableFiniteProducts (C := MetrizableLCA.{0})

/-- The corrected default-universe metrizable bounded derived category has finite coproducts
once the corrected weak equivalences have a left calculus of fractions. -/
abbrev hasFiniteCoproducts
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    HasFiniteCoproducts (DboundedWithCycles MetrizableLCA.{0}) := by
  letI : HasFiniteBiproducts (DboundedWithCycles MetrizableLCA.{0}) :=
    DboundedWithCycles.MetrizableLCA.hasFiniteBiproducts
  infer_instance

/-- Equalizers plus the corrected finite products give finite limits in the corrected
metrizable bounded derived category. -/
abbrev hasFiniteLimitsOfEqualizers
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (equalizers : HasEqualizers (DboundedWithCycles MetrizableLCA.{0})) :
    HasFiniteLimits (DboundedWithCycles MetrizableLCA.{0}) := by
  letI : HasFiniteProducts (DboundedWithCycles MetrizableLCA.{0}) :=
    DboundedWithCycles.MetrizableLCA.hasFiniteProducts
  letI : HasEqualizers (DboundedWithCycles MetrizableLCA.{0}) := equalizers
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Coequalizers plus the corrected finite coproducts give finite colimits in the corrected
metrizable bounded derived category. -/
abbrev hasFiniteColimitsOfCoequalizers
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (coequalizers : HasCoequalizers (DboundedWithCycles MetrizableLCA.{0})) :
    HasFiniteColimits (DboundedWithCycles MetrizableLCA.{0}) := by
  letI : HasFiniteCoproducts (DboundedWithCycles MetrizableLCA.{0}) :=
    DboundedWithCycles.MetrizableLCA.hasFiniteCoproducts
  letI : HasCoequalizers (DboundedWithCycles MetrizableLCA.{0}) := coequalizers
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-- Inputs that transfer equalizers and coequalizers for the corrected metrizable
bounded derived category from bounded complexes. -/
structure WalkingParallelPairFiniteShapeTransferInputs : Type 1 where
  limitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  functorCategoryLocalization :
    (((Functor.whiskeringRight WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0})
      (DboundedWithCycles MetrizableLCA.{0})).obj
      (DboundedWithCycles.localization MetrizableLCA.{0})).IsLocalization
        ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
          WalkingParallelPair))

/-- Objectwise corrected localization functor for `WalkingParallelPair` diagrams. -/
noncomputable abbrev walkingParallelPairObjectwiseLocalizationFunctor :
    (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤
      (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) :=
  ((Functor.whiskeringRight WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0})
      (DboundedWithCycles MetrizableLCA.{0})).obj
      (DboundedWithCycles.localization MetrizableLCA.{0}))

/-- Functor-category localization input for corrected `WalkingParallelPair` transfer. -/
abbrev WalkingParallelPairFunctorCategoryLocalizationInput : Prop :=
  walkingParallelPairObjectwiseLocalizationFunctor.IsLocalization
    ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
      WalkingParallelPair)

/-- The objectwise corrected localization functor inverts objectwise corrected weak
equivalences. -/
lemma walkingParallelPairObjectwiseLocalization_inverts :
    MorphismProperty.IsInvertedBy
      ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
        WalkingParallelPair)
      walkingParallelPairObjectwiseLocalizationFunctor :=
  fun _ _ f hf => by
    haveI :
        ∀ j : WalkingParallelPair,
          IsIso ((walkingParallelPairObjectwiseLocalizationFunctor.map f).app j) :=
      fun j =>
        CategoryTheory.Localization.inverts
          (DboundedWithCycles.localization MetrizableLCA.{0})
          (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0})
          (f.app j) (hf j)
    exact NatIso.isIso_of_isIso_app _

/-- Expanded fixed-target fields for the corrected objectwise WPP localization. -/
structure WalkingParallelPairFunctorCategoryFixedTargetFields
    (E : Type*) [Category E] where
  inverts :
    MorphismProperty.IsInvertedBy
      ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
        WalkingParallelPair)
      walkingParallelPairObjectwiseLocalizationFunctor
  lift :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E),
      MorphismProperty.IsInvertedBy
        ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
          WalkingParallelPair) F →
        (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) ⥤ E
  fac :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E)
      (hF :
        MorphismProperty.IsInvertedBy
          ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
            WalkingParallelPair) F),
      walkingParallelPairObjectwiseLocalizationFunctor ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) ⥤ E),
      walkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
        walkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
      F₁ = F₂

/-- Convert corrected fixed-target fields into mathlib's strict universal property. -/
def WalkingParallelPairFunctorCategoryFixedTargetFields.toStrictUniversalProperty
    {E : Type*} [Category E]
    (fields : WalkingParallelPairFunctorCategoryFixedTargetFields E) :
    CategoryTheory.Localization.StrictUniversalPropertyFixedTarget
      walkingParallelPairObjectwiseLocalizationFunctor
      ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
        WalkingParallelPair)
      E where
  inverts := fields.inverts
  lift := fields.lift
  fac := fields.fac
  uniq := fields.uniq

/-- Remaining corrected fixed-target data after formal objectwise inversion is proved. -/
structure WalkingParallelPairFunctorCategoryRemainingFixedTargetData
    (E : Type*) [Category E] where
  lift :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E),
      MorphismProperty.IsInvertedBy
        ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
          WalkingParallelPair) F →
        (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) ⥤ E
  fac :
    ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E)
      (hF :
        MorphismProperty.IsInvertedBy
          ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
            WalkingParallelPair) F),
      walkingParallelPairObjectwiseLocalizationFunctor ⋙ lift F hF = F
  uniq :
    ∀ (F₁ F₂ : (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) ⥤ E),
      walkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
        walkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
      F₁ = F₂

/-- Add formal objectwise inversion to corrected remaining fixed-target data. -/
def WalkingParallelPairFunctorCategoryRemainingFixedTargetData.toFields
    {E : Type*} [Category E]
    (data : WalkingParallelPairFunctorCategoryRemainingFixedTargetData E) :
    WalkingParallelPairFunctorCategoryFixedTargetFields E where
  inverts := walkingParallelPairObjectwiseLocalization_inverts
  lift := data.lift
  fac := data.fac
  uniq := data.uniq

/-- The two fixed targets sufficient for corrected WPP functor-category localization. -/
structure WalkingParallelPairFunctorCategoryRemainingFixedTargetInputs : Type 1 where
  targetData :
    WalkingParallelPairFunctorCategoryRemainingFixedTargetData
      (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0})
  modelData :
    WalkingParallelPairFunctorCategoryRemainingFixedTargetData
      (((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)

/-- Build corrected WPP functor-category localization from fixed-target data. -/
theorem walkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
    (inputs : WalkingParallelPairFunctorCategoryRemainingFixedTargetInputs) :
    WalkingParallelPairFunctorCategoryLocalizationInput :=
  Functor.IsLocalization.mk'
    (L := walkingParallelPairObjectwiseLocalizationFunctor)
    (W := (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
      WalkingParallelPair)
    inputs.targetData.toFields.toStrictUniversalProperty
    inputs.modelData.toFields.toStrictUniversalProperty

/-- Corrected finite-shape transfer with functor-category localization reduced to
fixed-target universal-property data. -/
structure WalkingParallelPairFiniteShapeTransferInputsFromFixedTargets : Type 1 where
  limitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  fixedTargetInputs :
    WalkingParallelPairFunctorCategoryRemainingFixedTargetInputs

/-- Build corrected WPP transfer inputs from fixed-target functor-category data. -/
def walkingParallelPairFiniteShapeTransferInputs_of_fixedTargets
    (inputs : WalkingParallelPairFiniteShapeTransferInputsFromFixedTargets) :
    WalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability := inputs.colimitStability
  functorCategoryLocalization :=
    walkingParallelPairFunctorCategoryLocalization_of_fixedTargetData inputs.fixedTargetInputs

/-- Strict source data representing one localized corrected WPP diagram. -/
structure WalkingParallelPairStrictPreimageData
    (Y : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) where
  zeroSrc : BoundedComplexCategory MetrizableLCA.{0}
  oneSrc : BoundedComplexCategory MetrizableLCA.{0}
  zeroIso :
    (DboundedWithCycles.localization MetrizableLCA.{0}).obj zeroSrc ≅
      Y.obj WalkingParallelPair.zero
  oneIso :
    (DboundedWithCycles.localization MetrizableLCA.{0}).obj oneSrc ≅
      Y.obj WalkingParallelPair.one
  leftSrc : zeroSrc ⟶ oneSrc
  rightSrc : zeroSrc ⟶ oneSrc
  left_fac :
    (DboundedWithCycles.localization MetrizableLCA.{0}).map leftSrc =
      zeroIso.hom ≫ Y.map WalkingParallelPairHom.left ≫ oneIso.inv
  right_fac :
    (DboundedWithCycles.localization MetrizableLCA.{0}).map rightSrc =
      zeroIso.hom ≫ Y.map WalkingParallelPairHom.right ≫ oneIso.inv

namespace WalkingParallelPairStrictPreimageData

/-- The strict source parallel-pair diagram represented by corrected preimage data. -/
def diagram {Y : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}}
    (data : WalkingParallelPairStrictPreimageData Y) :
    WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0} :=
  parallelPair data.leftSrc data.rightSrc

/-- The objectwise comparison from the corrected localized strict preimage to the target. -/
noncomputable def comparisonIso
    {Y : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}}
    (data : WalkingParallelPairStrictPreimageData Y) :
    walkingParallelPairObjectwiseLocalizationFunctor.obj data.diagram ≅ Y :=
  parallelPairIsoMk data.zeroIso data.oneIso
    (by
      dsimp [diagram]
      rw [data.left_fac]
      simp [Category.assoc])
    (by
      dsimp [diagram]
      rw [data.right_fac]
      simp [Category.assoc])

end WalkingParallelPairStrictPreimageData

/-- Strict source data representing one natural transformation after corrected localization. -/
structure WalkingParallelPairStrictPreimageMapData
    {Y Z : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}}
    (dataY : WalkingParallelPairStrictPreimageData Y)
    (dataZ : WalkingParallelPairStrictPreimageData Z)
    (τ : Y ⟶ Z) where
  zeroMap : dataY.zeroSrc ⟶ dataZ.zeroSrc
  oneMap : dataY.oneSrc ⟶ dataZ.oneSrc
  zero_fac :
    (DboundedWithCycles.localization MetrizableLCA.{0}).map zeroMap =
      dataY.zeroIso.hom ≫ τ.app WalkingParallelPair.zero ≫ dataZ.zeroIso.inv
  one_fac :
    (DboundedWithCycles.localization MetrizableLCA.{0}).map oneMap =
      dataY.oneIso.hom ≫ τ.app WalkingParallelPair.one ≫ dataZ.oneIso.inv
  left_naturality : dataY.leftSrc ≫ oneMap = zeroMap ≫ dataZ.leftSrc
  right_naturality : dataY.rightSrc ≫ oneMap = zeroMap ≫ dataZ.rightSrc

namespace WalkingParallelPairStrictPreimageMapData

/-- The strict source natural transformation represented by corrected map data. -/
def natTrans {Y Z : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}}
    {dataY : WalkingParallelPairStrictPreimageData Y}
    {dataZ : WalkingParallelPairStrictPreimageData Z}
    {τ : Y ⟶ Z}
    (mapData : WalkingParallelPairStrictPreimageMapData dataY dataZ τ) :
    dataY.diagram ⟶ dataZ.diagram :=
  parallelPairHomMk mapData.zeroMap mapData.oneMap
    (by
      dsimp [WalkingParallelPairStrictPreimageData.diagram]
      exact mapData.left_naturality)
    (by
      dsimp [WalkingParallelPairStrictPreimageData.diagram]
      exact mapData.right_naturality)

end WalkingParallelPairStrictPreimageMapData

/-- Coherent strict representatives for all corrected localized WPP diagrams. -/
structure WalkingParallelPairLiftBlueprint where
  objData : ∀ (Y : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}),
    WalkingParallelPairStrictPreimageData Y
  mapData :
    ∀ {Y Z : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}} (τ : Y ⟶ Z),
      WalkingParallelPairStrictPreimageMapData (objData Y) (objData Z) τ
  map_id : ∀ (Y : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}),
    (mapData (𝟙 Y)).natTrans = 𝟙 (objData Y).diagram
  map_comp :
    ∀ {Y Z T : WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}}
      (τ : Y ⟶ Z) (σ : Z ⟶ T),
      (mapData (τ ≫ σ)).natTrans = (mapData τ).natTrans ≫ (mapData σ).natTrans

namespace WalkingParallelPairLiftBlueprint

/-- Candidate corrected fixed-target lift functor from coherent strict representatives. -/
@[simps obj map]
def liftFunctor (blueprint : WalkingParallelPairLiftBlueprint)
    {E : Type*} [Category E]
    (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E) :
    (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) ⥤ E where
  obj Y := F.obj (blueprint.objData Y).diagram
  map {Y Z} τ := F.map ((blueprint.mapData τ).natTrans)
  map_id Y := by
    rw [blueprint.map_id Y]
    exact F.map_id _
  map_comp τ σ := by
    rw [blueprint.map_comp τ σ]
    exact F.map_comp _ _

end WalkingParallelPairLiftBlueprint

/-- Corrected fixed-target factorization left after a strict-representative lift is chosen. -/
abbrev WalkingParallelPairFixedTargetFacObligation
    (blueprint : WalkingParallelPairLiftBlueprint)
    (E : Type*) [Category E] : Prop :=
  ∀ (F : (WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}) ⥤ E)
    (_hF :
      MorphismProperty.IsInvertedBy
        ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
          WalkingParallelPair) F),
    walkingParallelPairObjectwiseLocalizationFunctor ⋙ blueprint.liftFunctor F = F

/-- Corrected fixed-target uniqueness for the objectwise localization functor. -/
abbrev WalkingParallelPairFixedTargetUniqObligation
    (E : Type*) [Category E] : Prop :=
  ∀ (F₁ F₂ : (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0}) ⥤ E),
    walkingParallelPairObjectwiseLocalizationFunctor ⋙ F₁ =
      walkingParallelPairObjectwiseLocalizationFunctor ⋙ F₂ →
    F₁ = F₂

/-- Corrected strict-representative lift data normalized on source-image diagrams. -/
structure WalkingParallelPairNormalizedLiftBlueprint where
  blueprint : WalkingParallelPairLiftBlueprint
  obj_image :
    ∀ (X : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}),
      (blueprint.objData (walkingParallelPairObjectwiseLocalizationFunctor.obj X)).diagram = X
  map_image :
    ∀ {X Y : WalkingParallelPair ⥤ BoundedComplexCategory MetrizableLCA.{0}} (τ : X ⟶ Y),
      (blueprint.mapData (walkingParallelPairObjectwiseLocalizationFunctor.map τ)).natTrans ≫
        eqToHom (obj_image Y) =
      eqToHom (obj_image X) ≫ τ

namespace WalkingParallelPairNormalizedLiftBlueprint

/-- Normalized corrected representatives supply the equality-level fixed-target `fac` field. -/
theorem fac {E : Type*} [Category E]
    (normalized : WalkingParallelPairNormalizedLiftBlueprint) :
    WalkingParallelPairFixedTargetFacObligation normalized.blueprint E := by
  intro F _hF
  exact CategoryTheory.Functor.ext
    (fun X => congrArg F.obj (normalized.obj_image X))
    (fun X Y τ => by
      dsimp [Functor.comp_map, WalkingParallelPairLiftBlueprint.liftFunctor]
      apply (cancel_mono (eqToHom (congrArg F.obj (normalized.obj_image Y)))).1
      simpa [Category.assoc, CategoryTheory.eqToHom_map] using
        congrArg F.map (normalized.map_image τ))

end WalkingParallelPairNormalizedLiftBlueprint

/-- Corrected blueprint inputs for the two fixed-target universal properties. -/
structure WalkingParallelPairFixedTargetBlueprintInputs : Type 1 where
  blueprint : WalkingParallelPairLiftBlueprint
  target_fac :
    WalkingParallelPairFixedTargetFacObligation blueprint
      (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0})
  target_uniq :
    WalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0})
  model_fac :
    WalkingParallelPairFixedTargetFacObligation blueprint
      (((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)
  model_uniq :
    WalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)

/-- Corrected normalized fixed-target inputs for WPP functor-category localization. -/
structure WalkingParallelPairNormalizedFixedTargetInputs : Type 1 where
  normalized : WalkingParallelPairNormalizedLiftBlueprint
  target_uniq :
    WalkingParallelPairFixedTargetUniqObligation
      (WalkingParallelPair ⥤ DboundedWithCycles MetrizableLCA.{0})
  model_uniq :
    WalkingParallelPairFixedTargetUniqObligation
      (((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
        WalkingParallelPair).Localization)

/-- Build corrected fixed-target blueprint inputs from normalized representatives. -/
def walkingParallelPairFixedTargetInputs_of_normalized
    (inputs : WalkingParallelPairNormalizedFixedTargetInputs) :
    WalkingParallelPairFixedTargetBlueprintInputs where
  blueprint := inputs.normalized.blueprint
  target_fac := WalkingParallelPairNormalizedLiftBlueprint.fac inputs.normalized
  target_uniq := inputs.target_uniq
  model_fac := WalkingParallelPairNormalizedLiftBlueprint.fac inputs.normalized
  model_uniq := inputs.model_uniq

/-- Build corrected fixed-target packages from one strict-representative lift blueprint. -/
def walkingParallelPairFixedTargetInputs_of_blueprint
    (inputs : WalkingParallelPairFixedTargetBlueprintInputs) :
    WalkingParallelPairFunctorCategoryRemainingFixedTargetInputs where
  targetData :=
    { lift := fun F _ => inputs.blueprint.liftFunctor F
      fac := inputs.target_fac
      uniq := inputs.target_uniq }
  modelData :=
    { lift := fun F _ => inputs.blueprint.liftFunctor F
      fac := inputs.model_fac
      uniq := inputs.model_uniq }

/-- Build corrected functor-category localization from strict representatives. -/
theorem walkingParallelPairFunctorCategoryLocalization_of_blueprint
    (inputs : WalkingParallelPairFixedTargetBlueprintInputs) :
    WalkingParallelPairFunctorCategoryLocalizationInput :=
  walkingParallelPairFunctorCategoryLocalization_of_fixedTargetData
    (walkingParallelPairFixedTargetInputs_of_blueprint inputs)

/-- Build corrected functor-category localization from normalized strict representatives. -/
theorem walkingParallelPairFunctorCategoryLocalization_of_normalized
    (inputs : WalkingParallelPairNormalizedFixedTargetInputs) :
    WalkingParallelPairFunctorCategoryLocalizationInput :=
  walkingParallelPairFunctorCategoryLocalization_of_blueprint
    (walkingParallelPairFixedTargetInputs_of_normalized inputs)

/-- Corrected finite-shape transfer with functor-category localization supplied by a
strict-representative lift blueprint. -/
structure WalkingParallelPairFiniteShapeTransferInputsFromBlueprint : Type 1 where
  limitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  blueprintInputs : WalkingParallelPairFixedTargetBlueprintInputs

/-- Build corrected WPP transfer inputs from strict-representative lift data. -/
def walkingParallelPairFiniteShapeTransferInputs_of_blueprint
    (inputs : WalkingParallelPairFiniteShapeTransferInputsFromBlueprint) :
    WalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability := inputs.colimitStability
  functorCategoryLocalization :=
    walkingParallelPairFunctorCategoryLocalization_of_blueprint inputs.blueprintInputs

/-- Corrected finite-shape transfer with functor-category localization supplied by normalized
strict representatives. -/
structure WalkingParallelPairFiniteShapeTransferInputsFromNormalized : Type 1 where
  limitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderLimitsOfShape
      WalkingParallelPair
  colimitStability :
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderColimitsOfShape
      WalkingParallelPair
  normalizedInputs : WalkingParallelPairNormalizedFixedTargetInputs

/-- Build corrected WPP transfer inputs from normalized strict-representative data. -/
def walkingParallelPairFiniteShapeTransferInputs_of_normalized
    (inputs : WalkingParallelPairFiniteShapeTransferInputsFromNormalized) :
    WalkingParallelPairFiniteShapeTransferInputs where
  limitStability := inputs.limitStability
  colimitStability := inputs.colimitStability
  functorCategoryLocalization :=
    walkingParallelPairFunctorCategoryLocalization_of_normalized inputs.normalizedInputs

/-- Equalizers in the corrected metrizable bounded derived category from finite-shape
localization transfer. -/
noncomputable abbrev hasEqualizersOfWalkingParallelPairTransfer
    (inputs : WalkingParallelPairFiniteShapeTransferInputs) :
    HasEqualizers (DboundedWithCycles MetrizableLCA.{0}) := by
  letI :
      (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderLimitsOfShape
        WalkingParallelPair := inputs.limitStability
  letI :
      (((Functor.whiskeringRight WalkingParallelPair
        (BoundedComplexCategory MetrizableLCA.{0})
        (DboundedWithCycles MetrizableLCA.{0})).obj
        (DboundedWithCycles.localization MetrizableLCA.{0})).IsLocalization
          ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
            WalkingParallelPair)) := inputs.functorCategoryLocalization
  haveI : HasLimitsOfShape WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0}) := by
    infer_instance
  exact CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization
    (DboundedWithCycles.localization MetrizableLCA.{0})
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}) WalkingParallelPair

/-- Coequalizers in the corrected metrizable bounded derived category from finite-shape
localization transfer. -/
noncomputable abbrev hasCoequalizersOfWalkingParallelPairTransfer
    (inputs : WalkingParallelPairFiniteShapeTransferInputs) :
    HasCoequalizers (DboundedWithCycles MetrizableLCA.{0}) := by
  letI :
      (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).IsStableUnderColimitsOfShape
        WalkingParallelPair := inputs.colimitStability
  letI :
      (((Functor.whiskeringRight WalkingParallelPair
        (BoundedComplexCategory MetrizableLCA.{0})
        (DboundedWithCycles MetrizableLCA.{0})).obj
        (DboundedWithCycles.localization MetrizableLCA.{0})).IsLocalization
          ((boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).functorCategory
            WalkingParallelPair)) := inputs.functorCategoryLocalization
  haveI : HasColimitsOfShape WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0}) := by
    infer_instance
  exact CategoryTheory.Localization.hasColimitsOfShape_of_functorCategoryLocalization
    (DboundedWithCycles.localization MetrizableLCA.{0})
    (boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}) WalkingParallelPair

/-- Corrected WPP transfer plus left calculus gives finite limits. -/
noncomputable abbrev hasFiniteLimitsOfWalkingParallelPairTransfer
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs : WalkingParallelPairFiniteShapeTransferInputs) :
    HasFiniteLimits (DboundedWithCycles MetrizableLCA.{0}) :=
  DboundedWithCycles.MetrizableLCA.hasFiniteLimitsOfEqualizers
    (DboundedWithCycles.MetrizableLCA.hasEqualizersOfWalkingParallelPairTransfer inputs)

/-- Corrected WPP transfer plus left calculus gives finite colimits. -/
noncomputable abbrev hasFiniteColimitsOfWalkingParallelPairTransfer
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (inputs : WalkingParallelPairFiniteShapeTransferInputs) :
    HasFiniteColimits (DboundedWithCycles MetrizableLCA.{0}) :=
  DboundedWithCycles.MetrizableLCA.hasFiniteColimitsOfCoequalizers
    (DboundedWithCycles.MetrizableLCA.hasCoequalizersOfWalkingParallelPairTransfer inputs)

/-- The corrected default-universe metrizable bounded derived category has a zero object
once the corrected weak equivalences have a left calculus of fractions. -/
abbrev hasZeroObject
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    HasZeroObject (DboundedWithCycles MetrizableLCA.{0}) :=
  DboundedWithCycles.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}

end MetrizableLCA

end DboundedWithCycles

end LeanLCAExactChallenge
