import LeanLCAExactChallenge.Infinity.BicategoricalEquivalenceInternalHom
import LeanLCAExactChallenge.Infinity.MetrizableDGOrdinaryNerveComparison
import LeanLCAExactChallenge.Infinity.MetrizableOrdinaryLocalizationComparison

/-!
# Conditional comparison with the localized coherent direct dg carrier

The canonical base-change map forms a strict triangle with the ordinary equivalence-forcing localization map and the localized coherent dg map. Assuming only that this Dwyer--Kan or Drinfeld base-change map is a bicategorical equivalence, the proved ordinary localization property transfers to the coherent dg candidate, and the induced homotopy category is identified with the corrected bounded derived category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open CategoryTheory CategoryTheory.Limits

/-- The presentation base-change map extends the comparison from the ordinary nerve. -/
theorem metrizableOrdinaryToDirectDGPresentationBaseChange_triangle :
    relativeCategory.toEquivalenceForcingPresentation ≫
        metrizableOrdinaryToDirectDGPresentationBaseChange =
      metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
        directDGCoherentNerveToEquivalenceForcingPresentation := by
  exact pushout.inl_desc _ _ _

/-- The ordinary localization map followed by base change is the localized coherent dg map. -/
theorem metrizableOrdinaryToDirectDGBaseChange_triangle :
    metrizableEquivalenceForcingMap ≫
        metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom =
      metrizableComplexNerveToLocalizedDirectDGQCat := by
  change relativeCategory.toEquivalenceForcingPresentation ≫
      (toInnerFibrantReplacement metrizableEquivalenceForcingPresentation ≫
        innerFibrantReplacementFunctor.map
          metrizableOrdinaryToDirectDGPresentationBaseChange) =
    metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
      (directDGCoherentNerveToEquivalenceForcingPresentation ≫
        toInnerFibrantReplacement directDGEquivalenceForcingPresentation)
  have hn : toInnerFibrantReplacement
        metrizableEquivalenceForcingPresentation ≫
      innerFibrantReplacementFunctor.map
        metrizableOrdinaryToDirectDGPresentationBaseChange =
    metrizableOrdinaryToDirectDGPresentationBaseChange ≫
      toInnerFibrantReplacement directDGEquivalenceForcingPresentation := by
    exact (toInnerFibrantReplacementNatTrans.naturality
      metrizableOrdinaryToDirectDGPresentationBaseChange).symm
  slice_lhs 2 3 => rw [hn]
  rw [← Category.assoc,
    metrizableOrdinaryToDirectDGPresentationBaseChange_triangle]
  rfl

/-- Bundled form of the exact base-change triangle. -/
theorem metrizableOrdinaryToDirectDGBaseChangeQCat_triangle :
    metrizableEquivalenceForcingQCatMap ≫
        metrizableOrdinaryToDirectDGBaseChangeQCatMap =
      metrizableComplexNerveToLocalizedDirectDGQCatMap := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  exact metrizableOrdinaryToDirectDGBaseChange_triangle

/-- The Dwyer--Kan or Drinfeld base-change equivalence transfers the full mapping-localization property to the coherent dg candidate. -/
theorem metrizableDirectDGMappingLocalizationProperty_of_baseChange
    (hbase : MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence) :
    MetrizableDirectDGMappingLocalizationProperty := by
  change MappingQuasicategoryLocalizationProperty
    (relativeNerveEdgeMarking relativeCategory)
    metrizableComplexNerveToLocalizedDirectDGQCatMap
  rw [← metrizableOrdinaryToDirectDGBaseChangeQCat_triangle]
  exact MappingQuasicategoryLocalizationProperty.postcomp_of_bicategoricalEquivalence
    (relativeNerveEdgeMarking relativeCategory)
    metrizableEquivalenceForcingQCatMap
    metrizableOrdinaryToDirectDGBaseChangeQCatMap
    metrizableEquivalenceForcingMappingLocalizationProperty_direct hbase

/-- The localized direct dg candidate, bundled with its proved inversion data. -/
def metrizableLocalizedDirectDGRelativeInfinityFunctor :
    RelativeInfinityFunctor ComplexCategory relativeCategory
      directDGEquivalenceForcingQCat where
  map := metrizableComplexNerveToLocalizedDirectDGQCat
  map_weakEquivalence f hf :=
    metrizableComplexNerveToLocalizedDirectDGQCat_generatedIsEquivalence f hf

/-- The induced functor from complexes to the homotopy category of the localized direct dg candidate. -/
def metrizableLocalizedDirectDGQCatHomotopyFunctor :
    CategoryTheory.Functor ComplexCategory
      (SSet.hoFunctor.obj directDGEquivalenceForcingQCat.obj) :=
  metrizableLocalizedDirectDGRelativeInfinityFunctor.homotopyFunctor

/-- A base-change bicategorical equivalence induces an equivalence of homotopy categories. -/
noncomputable def metrizableOrdinaryToDirectDGBaseChangeHomotopyEquivalence
    (hbase : MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence) :
    SSet.hoFunctor.obj metrizableEquivalenceForcingQCat.obj ≌
      SSet.hoFunctor.obj directDGEquivalenceForcingQCat.obj := by
  haveI : (SSet.hoFunctor.map
      metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor.IsEquivalence :=
    IsBicategoricalEquivalence.hoFunctor_isEquivalence hbase
  exact (SSet.hoFunctor.map
    metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor.asEquivalence

/-- The ordinary localization followed by base change, bundled as relative infinity data. -/
def metrizableBaseChangedRelativeInfinityFunctor :
    RelativeInfinityFunctor ComplexCategory relativeCategory
      directDGEquivalenceForcingQCat where
  map := metrizableEquivalenceForcingMap ≫
    metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom
  map_weakEquivalence f hf :=
    (metrizableEquivalenceForcingMap_generated f hf).map
      metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom

/-- The exact simplicial triangle identifies the base-changed and direct relative infinity functors. -/
theorem metrizableBaseChangedRelativeInfinityFunctor_eq :
    metrizableBaseChangedRelativeInfinityFunctor =
      metrizableLocalizedDirectDGRelativeInfinityFunctor := by
  rw [RelativeInfinityFunctor.mk.injEq]
  exact metrizableOrdinaryToDirectDGBaseChange_triangle

/-- The induced homotopy functors satisfy the same strict comparison triangle. -/
theorem metrizableOrdinaryToDirectDGBaseChange_homotopyFunctor_triangle :
    metrizableEquivalenceForcingHomotopyFunctor ⋙
        (SSet.hoFunctor.map
          metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor =
      metrizableLocalizedDirectDGQCatHomotopyFunctor := by
  calc
    _ = metrizableBaseChangedRelativeInfinityFunctor.homotopyFunctor := rfl
    _ = _ := congrArg RelativeInfinityFunctor.homotopyFunctor
      metrizableBaseChangedRelativeInfinityFunctor_eq

/-- The ordinary corrected-derived comparison followed by base change. -/
def metrizableCorrectedDerivedToLocalizedDirectDGHomotopy :
    CategoryTheory.Functor (DboundedWithCycles MetrizableLCA.{0})
      (SSet.hoFunctor.obj directDGEquivalenceForcingQCat.obj) :=
  metrizableCorrectedDerivedToEquivalenceForcingHomotopy ⋙
    (SSet.hoFunctor.map
      metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor

/-- Under the base-change theorem, the corrected-derived comparison with the localized coherent dg carrier is an equivalence. -/
theorem metrizableCorrectedDerivedToLocalizedDirectDGHomotopy_isEquivalence
    (hbase : MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence) :
    metrizableCorrectedDerivedToLocalizedDirectDGHomotopy.IsEquivalence := by
  haveI : metrizableCorrectedDerivedToEquivalenceForcingHomotopy.IsEquivalence :=
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy_isEquivalence_direct
  haveI : (SSet.hoFunctor.map
      metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor.IsEquivalence :=
    IsBicategoricalEquivalence.hoFunctor_isEquivalence hbase
  dsimp only [metrizableCorrectedDerivedToLocalizedDirectDGHomotopy]
  infer_instance

/-- Conditional equivalence between the corrected bounded derived category and the homotopy category of the localized coherent dg carrier. -/
noncomputable def metrizableCorrectedDerivedLocalizedDirectDGHomotopyEquivalence
    (hbase : MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence) :
    DboundedWithCycles MetrizableLCA.{0} ≌
      SSet.hoFunctor.obj directDGEquivalenceForcingQCat.obj :=
  metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalenceDirect.trans
    (metrizableOrdinaryToDirectDGBaseChangeHomotopyEquivalence hbase)

/-- The conditional ordinary comparison retains the canonical factorization from complexes. -/
noncomputable def metrizableCorrectedDerivedToLocalizedDirectDGHomotopy_fac :
    DboundedWithCycles.localization MetrizableLCA.{0} ⋙
        metrizableCorrectedDerivedToLocalizedDirectDGHomotopy ≅
      metrizableLocalizedDirectDGQCatHomotopyFunctor :=
  ((eqToIso (Functor.assoc
      (DboundedWithCycles.localization MetrizableLCA.{0})
      metrizableCorrectedDerivedToEquivalenceForcingHomotopy
      (SSet.hoFunctor.map
        metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor)).symm.trans
    (Functor.isoWhiskerRight
      metrizableCorrectedDerivedToEquivalenceForcingHomotopy_fac
      (SSet.hoFunctor.map
        metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor)).trans
    (eqToIso metrizableOrdinaryToDirectDGBaseChange_homotopyFunctor_triangle)

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
