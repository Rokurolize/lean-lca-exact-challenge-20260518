import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesClosure

/-!
# Corrected bounded derived localization surface

This module introduces a separate corrected bounded-derived namespace whose
weak equivalences are `boundedExactWeakEquivalenceWithCycles`. It deliberately
does not replace the legacy `Dbounded` declarations in `Derived.Bounded`.
-/

set_option autoImplicit false

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

/-- The corrected default-universe metrizable bounded derived category has a zero object
once the corrected weak equivalences have a left calculus of fractions. -/
abbrev hasZeroObject
    [(boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    HasZeroObject (DboundedWithCycles MetrizableLCA.{0}) :=
  DboundedWithCycles.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}

end MetrizableLCA

end DboundedWithCycles

end LeanLCAExactChallenge
