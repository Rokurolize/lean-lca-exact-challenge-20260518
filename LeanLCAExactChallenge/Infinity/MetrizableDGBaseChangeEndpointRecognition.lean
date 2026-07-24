/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceCoherentInverse
import LeanLCAExactChallenge.Infinity.MetrizableDGDirectEssentialSurjectivity
import LeanLCAExactChallenge.Infinity.MetrizableDGLocalizationComparison

/-! # Endpoint recognition for the ordinary-to-direct-DG base change -/

set_option autoImplicit false

noncomputable section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

/-- If a composite is essentially surjective, then its second factor is essentially surjective. -/
theorem functorEssSurj_right_of_comp
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E) (h : (F ⋙ G).EssSurj) : G.EssSurj where
  mem_essImage Z := by
    letI : (F ⋙ G).EssSurj := h
    obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F ⋙ G) Z
    exact ⟨F.obj X, ⟨e⟩⟩

namespace MetrizableBoundedComplexes

/-- Essential surjectivity of the direct-DG localization map descends through the strict
base-change triangle to the base-change map. -/
theorem metrizableOrdinaryToDirectDGBaseChange_essSurj_of_direct
    (h : (SSet.hoFunctor.map
      metrizableComplexNerveToLocalizedDirectDGQCat).toFunctor.EssSurj) :
    (SSet.hoFunctor.map
      metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor.EssSurj := by
  let ordinary := (SSet.hoFunctor.map metrizableEquivalenceForcingMap).toFunctor
  let baseChange := (SSet.hoFunctor.map
    metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor
  let direct := (SSet.hoFunctor.map
    metrizableComplexNerveToLocalizedDirectDGQCat).toFunctor
  have hcat :
      SSet.hoFunctor.map metrizableEquivalenceForcingMap ≫
          SSet.hoFunctor.map metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom =
        SSet.hoFunctor.map metrizableComplexNerveToLocalizedDirectDGQCat := by
    rw [← SSet.hoFunctor.map_comp]
    rw [metrizableOrdinaryToDirectDGBaseChange_triangle]
  have hcomp : ordinary ⋙ baseChange = direct := by
    exact congrArg Cat.Hom.toFunctor hcat
  apply functorEssSurj_right_of_comp ordinary baseChange
  rw [hcomp]
  exact h

/-- The strict base-change triangle transfers the proved essential surjectivity of the direct
localization map to the base-change map. -/
theorem metrizableOrdinaryToDirectDGBaseChange_essSurj :
    (SSet.hoFunctor.map
      metrizableOrdinaryToDirectDGBaseChangeQCatMap.hom).toFunctor.EssSurj :=
  metrizableOrdinaryToDirectDGBaseChange_essSurj_of_direct
    metrizableComplexNerveToLocalizedDirectDGQCat_essSurj

private theorem metrizableEquivalenceForcingEndpointFiber_quasicategory
    (x y : metrizableEquivalenceForcingQCat.obj _⦋0⦌) :
    SSet.Quasicategory (endpointFiber metrizableEquivalenceForcingQCat.obj x y) := by
  letI : SSet.Quasicategory metrizableEquivalenceForcingQCat.obj :=
    metrizableEquivalenceForcingQCat.property
  letI : SSet.KanComplex (endpointFiber metrizableEquivalenceForcingQCat.obj x y) :=
    endpointFiber_kan metrizableEquivalenceForcingQCat.obj x y
  infer_instance

private theorem directDGEquivalenceForcingEndpointFiber_quasicategory
    (x y : directDGEquivalenceForcingQCat.obj _⦋0⦌) :
    SSet.Quasicategory (endpointFiber directDGEquivalenceForcingQCat.obj x y) := by
  letI : SSet.Quasicategory directDGEquivalenceForcingQCat.obj :=
    directDGEquivalenceForcingQCat.property
  letI : SSet.KanComplex (endpointFiber directDGEquivalenceForcingQCat.obj x y) :=
    endpointFiber_kan directDGEquivalenceForcingQCat.obj x y
  infer_instance

/-- The endpoint recognition route reduces the base-change equivalence to the two coherent
construction interfaces and local endpoint fiber equivalences. -/
theorem metrizableOrdinaryToDirectDGBaseChange_isEquivalence_of_endpointInputs
    (hsection : EndpointFiberCounitSectionExtensionContract.{1})
    (hpost : EndpointFiberPostcompositionFullyFaithfulContract.{1})
    (hlocal : EndpointFiberLocalEquivalenceInput
      metrizableOrdinaryToDirectDGBaseChangeQCatMap
      metrizableEquivalenceForcingEndpointFiber_quasicategory
      directDGEquivalenceForcingEndpointFiber_quasicategory) :
    MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence := by
  exact endpointFiberRecognition_of_sectionExtension_and_fullyFaithful hsection hpost
    metrizableOrdinaryToDirectDGBaseChangeQCatMap
    metrizableEquivalenceForcingEndpointFiber_quasicategory
    directDGEquivalenceForcingEndpointFiber_quasicategory
    metrizableOrdinaryToDirectDGBaseChange_essSurj hlocal

end MetrizableBoundedComplexes

end LeanLCAExactChallenge.Infinity
