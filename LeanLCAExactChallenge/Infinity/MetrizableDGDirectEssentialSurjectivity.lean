/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EquivalenceForcingVertices
import LeanLCAExactChallenge.Infinity.MetrizableDGOrdinaryNerveComparison
import LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerveVertices
import LeanLCAExactChallenge.Infinity.QuasicategoryEssentialSurjectivity

/-! # Essential surjectivity of the direct DG localization map -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open LeanLCAExactChallenge.Infinity

/-- The ordinary nerve of the direct DG simplicial category, bundled as a quasicategory. -/
def directDGOrdinaryNerveQCat : SSet.QCat.{1} :=
  ⟨CategoryTheory.nerve DirectDGSimplicialCategory, inferInstance⟩

/-- The nerve of the ordinary equivalence from bounded complexes to the direct DG carrier. -/
def metrizableComplexNerveToDirectDGOrdinaryNerveQCatMap :
    metrizableComplexNerveQCat ⟶ directDGOrdinaryNerveQCat :=
  ObjectProperty.homMk
    (nerveMap directDGSimplicialCategoryOrdinaryEquivalence.inverse)

/-- The ordinary-to-coherent nerve comparison, bundled as a map of quasicategories. -/
def directDGOrdinaryNerveToHomotopyCoherentNerveQCatMap :
    directDGOrdinaryNerveQCat ⟶ directDGHomotopyCoherentNerveQCat :=
  ObjectProperty.homMk directDGOrdinaryNerveToHomotopyCoherentNerve

/-- The bounded-complex nerve comparison with the raw coherent direct DG nerve. -/
def metrizableComplexNerveToDirectDGHomotopyCoherentNerveQCatMap :
    metrizableComplexNerveQCat ⟶ directDGHomotopyCoherentNerveQCat :=
  ObjectProperty.homMk metrizableComplexNerveToDirectDGHomotopyCoherentNerve

/-- The ordinary equivalence contributes an essentially surjective map on homotopy
categories after taking nerves. -/
theorem metrizableComplexNerveToDirectDGOrdinaryNerve_essSurj :
    (SSet.hoFunctor.map
      (nerveMap directDGSimplicialCategoryOrdinaryEquivalence.inverse)).toFunctor.EssSurj :=
  hoFunctorMap_nerveMap_essSurj
    directDGSimplicialCategoryOrdinaryEquivalence.inverse

/-- The ordinary-to-coherent nerve comparison is essentially surjective because every
coherent vertex is represented by an ordinary object. -/
theorem directDGOrdinaryNerveToHomotopyCoherentNerve_essSurj :
    (SSet.hoFunctor.map
      directDGOrdinaryNerveToHomotopyCoherentNerve).toFunctor.EssSurj := by
  change (SSet.hoFunctor.map
    directDGOrdinaryNerveToHomotopyCoherentNerveQCatMap.hom).toFunctor.EssSurj
  exact hoFunctorMap_essSurj_of_vertex_surjective
    directDGOrdinaryNerveToHomotopyCoherentNerveQCatMap
    (OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve_vertex_surjective
      DirectDGSimplicialCategory)

/-- The raw coherent direct DG nerve is essentially covered by bounded complexes. -/
theorem metrizableComplexNerveToDirectDGHomotopyCoherentNerve_essSurj :
    (SSet.hoFunctor.map
      metrizableComplexNerveToDirectDGHomotopyCoherentNerve).toFunctor.EssSurj := by
  rw [metrizableComplexNerveToDirectDGHomotopyCoherentNerve,
    SSet.hoFunctor.map_comp]
  exact functorEssSurj_comp_data _ _
    metrizableComplexNerveToDirectDGOrdinaryNerve_essSurj
    directDGOrdinaryNerveToHomotopyCoherentNerve_essSurj

/-- Adjoining coherent inverses does not alter the vertices of the coherent direct DG nerve. -/
theorem directDGCoherentNerveToEquivalenceForcingPresentation_vertex_bijective :
    Function.Bijective
      (directDGCoherentNerveToEquivalenceForcingPresentation.app (op ⦋0⦌)) :=
  pushoutInl_vertex_bijective_of_right
    directDGWeakIntervalsToCoherentNerve
    relativeCategory.weakIntervalsToEquivalences
    (RelativeCategoryData.weakIntervalsToEquivalences_vertex_bijective
      relativeCategory)

/-- The inner-fibrant replacement of the direct DG presentation preserves its vertices. -/
theorem directDGEquivalenceForcingReplacement_vertex_bijective :
    Function.Bijective
      ((toInnerFibrantReplacement directDGEquivalenceForcingPresentation).app
        (op ⦋0⦌)) :=
  innerAnodyne_vertex_bijective
    (toInnerFibrantReplacement_innerAnodyne directDGEquivalenceForcingPresentation)

/-- The complete coherent-to-localized direct DG map is bijective on vertices. -/
theorem directDGCoherentNerveToLocalizedQCat_vertex_bijective :
    Function.Bijective
      (directDGCoherentNerveToLocalizedQCat.app (op ⦋0⦌)) := by
  change Function.Bijective (fun x =>
    (toInnerFibrantReplacement directDGEquivalenceForcingPresentation).app
      (op ⦋0⦌)
      (directDGCoherentNerveToEquivalenceForcingPresentation.app
        (op ⦋0⦌) x))
  exact directDGEquivalenceForcingReplacement_vertex_bijective.comp
    directDGCoherentNerveToEquivalenceForcingPresentation_vertex_bijective

/-- The coherent-to-localized direct DG map, bundled as a map of quasicategories. -/
def directDGCoherentNerveToLocalizedQCatMap :
    directDGHomotopyCoherentNerveQCat ⟶ directDGEquivalenceForcingQCat :=
  ObjectProperty.homMk directDGCoherentNerveToLocalizedQCat

/-- The coherent-to-localized direct DG map is essentially surjective. -/
theorem directDGCoherentNerveToLocalizedQCat_essSurj :
    (SSet.hoFunctor.map
      directDGCoherentNerveToLocalizedQCat).toFunctor.EssSurj := by
  change (SSet.hoFunctor.map
    directDGCoherentNerveToLocalizedQCatMap.hom).toFunctor.EssSurj
  exact hoFunctorMap_essSurj_of_vertex_surjective
    directDGCoherentNerveToLocalizedQCatMap
    directDGCoherentNerveToLocalizedQCat_vertex_bijective.surjective

/-- The direct DG candidate localization map is essentially surjective. -/
theorem metrizableComplexNerveToLocalizedDirectDGQCat_essSurj :
    (SSet.hoFunctor.map
      metrizableComplexNerveToLocalizedDirectDGQCat).toFunctor.EssSurj := by
  rw [metrizableComplexNerveToLocalizedDirectDGQCat,
    SSet.hoFunctor.map_comp]
  exact functorEssSurj_comp_data _ _
    metrizableComplexNerveToDirectDGHomotopyCoherentNerve_essSurj
    directDGCoherentNerveToLocalizedQCat_essSurj

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
