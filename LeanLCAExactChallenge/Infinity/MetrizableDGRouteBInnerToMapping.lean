/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGOrdinaryNerveComparison

/-! # Route B: inner-anodyne base change implies direct DG mapping localization -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open CategoryTheory CategoryTheory.Limits

/-- The presentation base change satisfies the strict pushout triangle. -/
theorem routeBPresentationBaseChange_triangle :
    relativeCategory.toEquivalenceForcingPresentation ≫
        metrizableOrdinaryToDirectDGPresentationBaseChange =
      metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
        directDGCoherentNerveToEquivalenceForcingPresentation := by
  exact pushout.inl_desc _ _ _

/-- The direct localization map factors through the ordinary and direct presentations. -/
theorem routeBDirectLocalizationMap_factorization :
    (relativeCategory.toEquivalenceForcingPresentation ≫
        metrizableOrdinaryToDirectDGPresentationBaseChange) ≫
      toInnerFibrantReplacement directDGEquivalenceForcingPresentation =
        metrizableComplexNerveToLocalizedDirectDGQCat := by
  rw [routeBPresentationBaseChange_triangle]
  rfl

/-- Precomposition along presentation base change, bundled between mapping quasicategories. -/
def routeBPresentationBaseChangePrecompQCat (Q : SSet.QCat.{1}) :
    internalHomQCat directDGEquivalenceForcingPresentation Q.obj
        (@quasicategory_ihom directDGEquivalenceForcingPresentation Q.obj Q.property) ⟶
      internalHomQCat metrizableEquivalenceForcingPresentation Q.obj
        (@quasicategory_ihom metrizableEquivalenceForcingPresentation Q.obj Q.property) :=
  ObjectProperty.homMk
    (internalHomPrecomp metrizableOrdinaryToDirectDGPresentationBaseChange Q.obj)

/-- The direct presentation comparison obtained through the strict base-change triangle. -/
def routeBDirectDGPresentationMappingComparison (Q : SSet.QCat.{1}) :
    (ihom directDGEquivalenceForcingPresentation).obj Q.obj ⟶
      (relativeInternalHom
        (relativeNerveEdgeMarking relativeCategory) Q.obj : SSet.{1}) :=
  internalHomPrecomp metrizableOrdinaryToDirectDGPresentationBaseChange Q.obj ≫
    metrizableEquivalenceForcingPresentationMappingComparison Q

/-- The direct presentation comparison bundled as a map of mapping quasicategories. -/
def routeBDirectDGPresentationMappingComparisonQCat (Q : SSet.QCat.{1}) :
    internalHomQCat directDGEquivalenceForcingPresentation Q.obj
        (@quasicategory_ihom directDGEquivalenceForcingPresentation Q.obj Q.property) ⟶
      relativeInternalHomQCat
        (relativeNerveEdgeMarking relativeCategory) Q.obj
        (@relativeInternalHom_quasicategory_of_quasicategory
          (CategoryTheory.nerve ComplexCategory) Q.obj Q.property
          (relativeNerveEdgeMarking relativeCategory)) :=
  ObjectProperty.homMk (routeBDirectDGPresentationMappingComparison Q)

/-- The specialized ordinary presentation comparison includes to ordinary precomposition. -/
@[reassoc]
theorem routeBOrdinaryPresentationMappingComparison_comp_inclusion
    (Q : SSet.QCat.{1}) :
    metrizableEquivalenceForcingPresentationMappingComparison Q ≫
        (relativeInternalHom
          (relativeNerveEdgeMarking relativeCategory) Q.obj).ι =
      internalHomPrecomp
        relativeCategory.toEquivalenceForcingPresentation Q.obj :=
  relativeCategory.equivalenceForcingPresentationMappingComparison_comp_inclusion Q

@[reassoc]
theorem routeBPresentationBaseChangePrecomp_comp_ordinaryPresentationComparison
    (Q : SSet.QCat.{1}) :
    routeBPresentationBaseChangePrecompQCat Q ≫
        metrizableEquivalenceForcingPresentationMappingComparisonQCat Q =
      routeBDirectDGPresentationMappingComparisonQCat Q := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  rfl

/-- Inner-anodyne base change induces an equivalence on presentation mapping objects. -/
theorem routeBPresentationBaseChangePrecomp_isBicategoricalEquivalence
    (Q : SSet.QCat.{1})
    (hinner : SSet.innerAnodyneExtensions
      metrizableOrdinaryToDirectDGPresentationBaseChange) :
    IsBicategoricalEquivalence (routeBPresentationBaseChangePrecompQCat Q) := by
  simpa only [routeBPresentationBaseChangePrecompQCat, internalHomPrecomp] using
    pre_innerAnodyne_isBicategoricalEquivalence
      metrizableOrdinaryToDirectDGPresentationBaseChange Q hinner

/-- The already-proved ordinary presentation comparison is targetwise an equivalence. -/
theorem routeBOrdinaryPresentationComparison_isBicategoricalEquivalence
    (Q : SSet.QCat.{1}) :
    MetrizableEquivalenceForcingPresentationComparisonIsEquivalence Q := by
  exact metrizableEquivalenceForcingPresentationComparisonIsEquivalence_of_monoRLP Q
    (metrizableEquivalenceForcingPresentationComparisonHasMonoRLP_of_interval Q
      (@intervalRestriction_mem_monomorphisms_rlp_of_specialLeftHornFillers
        Q.obj Q.property (@hasAllSpecialLeftHornFillers_direct Q.obj Q.property)))

/-- The direct presentation comparison is an equivalence under inner-anodyne base change. -/
theorem routeBDirectDGPresentationMappingComparison_isBicategoricalEquivalence
    (Q : SSet.QCat.{1})
    (hinner : SSet.innerAnodyneExtensions
      metrizableOrdinaryToDirectDGPresentationBaseChange) :
    IsBicategoricalEquivalence (routeBDirectDGPresentationMappingComparisonQCat Q) := by
  rw [← routeBPresentationBaseChangePrecomp_comp_ordinaryPresentationComparison]
  exact (routeBPresentationBaseChangePrecomp_isBicategoricalEquivalence Q hinner).comp
    (routeBOrdinaryPresentationComparison_isBicategoricalEquivalence Q)

/-- Precomposition strips the direct presentation's chosen inner-fibrant replacement. -/
def routeBDirectDGReplacementPrecompQCat (Q : SSet.QCat.{1}) :
    internalHomQCat directDGEquivalenceForcingQCat.obj Q.obj
        (@quasicategory_ihom directDGEquivalenceForcingQCat.obj Q.obj Q.property) ⟶
      internalHomQCat directDGEquivalenceForcingPresentation Q.obj
        (@quasicategory_ihom directDGEquivalenceForcingPresentation Q.obj Q.property) :=
  ObjectProperty.homMk
    (internalHomPrecomp
      (toInnerFibrantReplacement directDGEquivalenceForcingPresentation) Q.obj)

/-- Replacement precomposition is an equivalence of mapping quasicategories. -/
theorem routeBDirectDGReplacementPrecomp_isBicategoricalEquivalence
    (Q : SSet.QCat.{1}) :
    IsBicategoricalEquivalence (routeBDirectDGReplacementPrecompQCat Q) :=
  toInnerFibrantReplacement_precomp_isBicategoricalEquivalence
    directDGEquivalenceForcingPresentation Q

/-- The canonical targetwise mapping restriction for the localized direct DG carrier. -/
def routeBDirectDGCanonicalRestriction (Q : SSet.QCat.{1}) :
    (ihom directDGEquivalenceForcingQCat.obj).obj Q.obj ⟶
      (relativeInternalHom
        (relativeNerveEdgeMarking relativeCategory) Q.obj : SSet.{1}) :=
  internalHomPrecompToRelative
    (relativeNerveEdgeMarking relativeCategory)
    metrizableComplexNerveToLocalizedDirectDGQCat Q.obj
    metrizableComplexNerveToLocalizedDirectDGQCat_invertsMarkedEdges

/-- The canonical direct DG restriction bundled between mapping quasicategories. -/
def routeBDirectDGCanonicalRestrictionQCat (Q : SSet.QCat.{1}) :
    internalHomQCat directDGEquivalenceForcingQCat.obj Q.obj
        (@quasicategory_ihom directDGEquivalenceForcingQCat.obj Q.obj Q.property) ⟶
      relativeInternalHomQCat
        (relativeNerveEdgeMarking relativeCategory) Q.obj
        (@relativeInternalHom_quasicategory_of_quasicategory
          (CategoryTheory.nerve ComplexCategory) Q.obj Q.property
          (relativeNerveEdgeMarking relativeCategory)) :=
  ObjectProperty.homMk (routeBDirectDGCanonicalRestriction Q)

/-- The presentation comparison becomes the canonical restriction after replacement. -/
@[reassoc]
theorem routeBDirectDGReplacementPrecomp_comp_presentationComparison
    (Q : SSet.QCat.{1}) :
    routeBDirectDGReplacementPrecompQCat Q ≫
        routeBDirectDGPresentationMappingComparisonQCat Q =
      routeBDirectDGCanonicalRestrictionQCat Q := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  change internalHomPrecomp
        (toInnerFibrantReplacement directDGEquivalenceForcingPresentation) Q.obj ≫
      (internalHomPrecomp metrizableOrdinaryToDirectDGPresentationBaseChange Q.obj ≫
        metrizableEquivalenceForcingPresentationMappingComparison Q) =
    routeBDirectDGCanonicalRestriction Q
  apply (cancel_mono
    (relativeInternalHom
      (relativeNerveEdgeMarking relativeCategory) Q.obj).ι).1
  calc
    (internalHomPrecomp
          (toInnerFibrantReplacement directDGEquivalenceForcingPresentation) Q.obj ≫
        (internalHomPrecomp metrizableOrdinaryToDirectDGPresentationBaseChange Q.obj ≫
          metrizableEquivalenceForcingPresentationMappingComparison Q)) ≫
        (relativeInternalHom
          (relativeNerveEdgeMarking relativeCategory) Q.obj).ι =
      internalHomPrecomp
          (toInnerFibrantReplacement directDGEquivalenceForcingPresentation) Q.obj ≫
        (internalHomPrecomp metrizableOrdinaryToDirectDGPresentationBaseChange Q.obj ≫
          internalHomPrecomp
            relativeCategory.toEquivalenceForcingPresentation Q.obj) := by
      rw [Category.assoc, Category.assoc,
        routeBOrdinaryPresentationMappingComparison_comp_inclusion]
    _ = internalHomPrecomp
        ((relativeCategory.toEquivalenceForcingPresentation ≫
            metrizableOrdinaryToDirectDGPresentationBaseChange) ≫
          toInnerFibrantReplacement directDGEquivalenceForcingPresentation) Q.obj := by
      rw [internalHomPrecomp_comp, internalHomPrecomp_comp]
    _ = internalHomPrecomp metrizableComplexNerveToLocalizedDirectDGQCat Q.obj := by
      rw [routeBDirectLocalizationMap_factorization]
    _ = routeBDirectDGCanonicalRestriction Q ≫
        (relativeInternalHom
          (relativeNerveEdgeMarking relativeCategory) Q.obj).ι := by
      exact (internalHomPrecompToRelative_comp_inclusion
        (relativeNerveEdgeMarking relativeCategory)
        metrizableComplexNerveToLocalizedDirectDGQCat Q.obj
        metrizableComplexNerveToLocalizedDirectDGQCat_invertsMarkedEdges).symm

/-- The canonical direct DG restriction is targetwise an equivalence. -/
theorem routeBDirectDGCanonicalRestriction_isBicategoricalEquivalence
    (Q : SSet.QCat.{1})
    (hinner : SSet.innerAnodyneExtensions
      metrizableOrdinaryToDirectDGPresentationBaseChange) :
    IsBicategoricalEquivalence (routeBDirectDGCanonicalRestrictionQCat Q) := by
  rw [← routeBDirectDGReplacementPrecomp_comp_presentationComparison]
  exact (routeBDirectDGReplacementPrecomp_isBicategoricalEquivalence Q).comp
    (routeBDirectDGPresentationMappingComparison_isBicategoricalEquivalence Q hinner)

/-- Inner-anodyne presentation base change implies the full direct DG mapping localization
property. -/
theorem metrizableDirectDGMappingLocalizationProperty_of_presentationBaseChange_innerAnodyne
    (hinner : SSet.innerAnodyneExtensions
      metrizableOrdinaryToDirectDGPresentationBaseChange) :
    MetrizableDirectDGMappingLocalizationProperty where
  inverts := metrizableComplexNerveToLocalizedDirectDGQCat_invertsMarkedEdges
  universal Q := ⟨MappingQuasicategoryLocalizationAt.ofCanonicalUnconditional
    (relativeNerveEdgeMarking relativeCategory)
    metrizableComplexNerveToLocalizedDirectDGQCatMap Q
    metrizableComplexNerveToLocalizedDirectDGQCat_invertsMarkedEdges
    (by
      simpa only [routeBDirectDGCanonicalRestrictionQCat,
        routeBDirectDGCanonicalRestriction,
        metrizableComplexNerveToLocalizedDirectDGQCatMap,
        ObjectProperty.homMk_hom] using
          routeBDirectDGCanonicalRestriction_isBicategoricalEquivalence Q hinner)⟩

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

