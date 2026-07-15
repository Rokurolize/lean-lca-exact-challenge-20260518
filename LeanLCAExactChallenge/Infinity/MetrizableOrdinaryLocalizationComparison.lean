/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.OrdinaryLocalizationBridge
import Mathlib.CategoryTheory.Category.ULift

/-!
# Ordinary comparison for metrizable equivalence forcing

This file transports the ordinary localization supplied by the mapping-quasicategory
universal property from the homotopy category of the ordinary nerve back to bounded
complexes, then compares it with the corrected bounded derived localization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory
open Simplicial

/-- Raise only the hom universe of bounded complexes inside their ordinary nerve. -/
def metrizableComplexNerveToULiftHom :
    CategoryTheory.nerve ComplexCategory ⟶
      CategoryTheory.nerve (ULiftHom.{1} ComplexCategory) :=
  { app _ := ↾fun X ↦ (ULiftHom.up.mapComposableArrows _).obj X }

/-- Lower the hom universe inside the ordinary nerve of bounded complexes. -/
def metrizableComplexNerveFromULiftHom :
    CategoryTheory.nerve (ULiftHom.{1} ComplexCategory) ⟶
      CategoryTheory.nerve ComplexCategory :=
  { app _ := ↾fun X ↦ (ULiftHom.down.mapComposableArrows _).obj X }

/-- Raising and then lowering the hom universe gives an isomorphic ordinary nerve. -/
def metrizableComplexNerveULiftHomIso :
    CategoryTheory.nerve ComplexCategory ≅
      CategoryTheory.nerve (ULiftHom.{1} ComplexCategory) where
  hom := metrizableComplexNerveToULiftHom
  inv := metrizableComplexNerveFromULiftHom
  hom_inv_id := by
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro X
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro X
    rfl

/-- The homotopy category of the ordinary nerve of bounded complexes recovers bounded
complexes. -/
noncomputable def metrizableComplexNerveHomotopyEquivalence :
    SSet.hoFunctor.obj (CategoryTheory.nerve ComplexCategory) ≌ ComplexCategory :=
  (Cat.equivOfIso
      (SSet.hoFunctor.mapIso metrizableComplexNerveULiftHomIso)).trans
    ((Cat.equivOfIso
      (nerveFunctorCompHoFunctorIso.app
        (Cat.of (ULiftHom.{1} ComplexCategory)))).trans
      (ULiftHom.equiv :
        ComplexCategory ≌ ULiftHom.{1} ComplexCategory).symm)

/-- The canonical functor from bounded complexes to the homotopy category of their ordinary
nerve. -/
def metrizableComplexToNerveHomotopyFunctor :
    ComplexCategory ⥤
      SSet.hoFunctor.obj (CategoryTheory.nerve ComplexCategory) where
  obj X := homotopyObject
    (CategoryTheory.nerveEquiv.symm X)
  map {X Y} f := edgeHomotopyClass
    (CategoryTheory.nerve.edgeMk f)
  map_id X := by
    rw [CategoryTheory.nerve.edgeMk_id]
    change SSet.Truncated.HomotopyCategory.homMk
      (SSet.Edge.id (X := CategoryTheory.nerve ComplexCategory)
        (CategoryTheory.nerveEquiv.symm X)).toTruncated = _
    rw [SSet.Edge.toTruncated_id]
    exact SSet.Truncated.HomotopyCategory.homMk_id _
  map_comp {X Y Z} f g := by
    obtain ⟨s⟩ :=
      (CategoryTheory.nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
      s.toTruncated).symm

private abbrev metrizableComplexNerveTruncation : SSet.Truncated 2 :=
  (SSet.truncation 2).obj (CategoryTheory.nerve ComplexCategory)

private def metrizableComplexNerveHomotopyEdgeMap
    {x y : CategoryTheory.ComposableArrows ComplexCategory 0}
    (e : SSet.Truncated.Edge (X := metrizableComplexNerveTruncation) x y) :
    CategoryTheory.nerveEquiv x ⟶ CategoryTheory.nerveEquiv y :=
  CategoryTheory.nerve.homEquiv
    (e.map (𝟙 metrizableComplexNerveTruncation))

private theorem metrizableComplexNerveHomotopyEdgeMap_id
    (x : CategoryTheory.ComposableArrows ComplexCategory 0) :
    metrizableComplexNerveHomotopyEdgeMap (SSet.Truncated.Edge.id x) = 𝟙 _ := by
  simpa [metrizableComplexNerveHomotopyEdgeMap] using!
    CategoryTheory.nerve.homEquiv_id x

private theorem metrizableComplexNerveHomotopyEdgeMap_comp
    {x₀ x₁ x₂ : CategoryTheory.ComposableArrows ComplexCategory 0}
    {e₀₁ : SSet.Truncated.Edge (X := metrizableComplexNerveTruncation) x₀ x₁}
    {e₁₂ : SSet.Truncated.Edge (X := metrizableComplexNerveTruncation) x₁ x₂}
    {e₀₂ : SSet.Truncated.Edge (X := metrizableComplexNerveTruncation) x₀ x₂}
    (h : SSet.Truncated.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    metrizableComplexNerveHomotopyEdgeMap e₀₁ ≫
        metrizableComplexNerveHomotopyEdgeMap e₁₂ =
      metrizableComplexNerveHomotopyEdgeMap e₀₂ :=
  CategoryTheory.nerve.homEquiv_comp
    (h.map (𝟙 metrizableComplexNerveTruncation))

/-- Evaluation of a homotopy class in an ordinary nerve as its underlying bounded morphism. -/
def metrizableComplexNerveHomotopyToComplexFunctor :
    SSet.hoFunctor.obj (CategoryTheory.nerve ComplexCategory) ⥤
      ComplexCategory :=
  SSet.Truncated.HomotopyCategory.lift
    (fun x ↦ CategoryTheory.nerveEquiv x)
    metrizableComplexNerveHomotopyEdgeMap
    metrizableComplexNerveHomotopyEdgeMap_id
    metrizableComplexNerveHomotopyEdgeMap_comp

@[simp]
theorem metrizableComplexNerveHomotopyToComplexFunctor_map_edgeMk
    {K L : ComplexCategory} (f : K ⟶ L) :
    metrizableComplexNerveHomotopyToComplexFunctor.map
        (edgeHomotopyClass (CategoryTheory.nerve.edgeMk f)) = f := by
  have hmap : metrizableComplexNerveHomotopyToComplexFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (CategoryTheory.nerve.edgeMk f).toTruncated) =
      metrizableComplexNerveHomotopyEdgeMap
        (CategoryTheory.nerve.edgeMk f).toTruncated :=
    SSet.Truncated.HomotopyCategory.lift_map_homMk
      (V := metrizableComplexNerveTruncation)
      (D := ComplexCategory)
      (fun x ↦ CategoryTheory.nerveEquiv x)
      metrizableComplexNerveHomotopyEdgeMap
      metrizableComplexNerveHomotopyEdgeMap_id
      metrizableComplexNerveHomotopyEdgeMap_comp _
  rw [show metrizableComplexNerveHomotopyToComplexFunctor.map
      (edgeHomotopyClass (CategoryTheory.nerve.edgeMk f)) =
        metrizableComplexNerveHomotopyEdgeMap
          (CategoryTheory.nerve.edgeMk f).toTruncated by
    exact hmap]
  have hedge : (CategoryTheory.nerve.edgeMk f).toTruncated.map
      (𝟙 ((SSet.truncation 2).obj
        (CategoryTheory.nerve ComplexCategory))) =
      (CategoryTheory.nerve.edgeMk f).toTruncated := by
    ext
    rfl
  change CategoryTheory.nerve.homEquiv
    ((CategoryTheory.nerve.edgeMk f).toTruncated.map
      (𝟙 metrizableComplexNerveTruncation)) = f
  rw [hedge]
  exact CategoryTheory.nerve.homEquiv_edgeMk f

/-- Evaluating the canonical nerve-homotopy functor recovers the original bounded-complex
functor strictly. -/
theorem metrizableComplexToNerveHomotopyFunctor_comp_evaluation :
    metrizableComplexToNerveHomotopyFunctor ⋙
        metrizableComplexNerveHomotopyToComplexFunctor =
      𝟭 ComplexCategory := by
  exact CategoryTheory.Functor.ext (fun X ↦ by rfl) (fun X Y f ↦ by
    change metrizableComplexNerveHomotopyToComplexFunctor.map
      (edgeHomotopyClass (CategoryTheory.nerve.edgeMk f)) = f
    exact metrizableComplexNerveHomotopyToComplexFunctor_map_edgeMk f)

/-- The canonical functor to the homotopy category of the ordinary nerve is fully faithful. -/
noncomputable def metrizableComplexToNerveHomotopyFunctorFullyFaithful :
    metrizableComplexToNerveHomotopyFunctor.FullyFaithful where
  preimage f := metrizableComplexNerveHomotopyToComplexFunctor.map f
  map_preimage {X Y} f := by
    obtain ⟨e, rfl⟩ :=
      homotopyCategory_homMk_surjective_of_quasicategory
        (V := (SSet.truncation 2).obj
          (CategoryTheory.nerve ComplexCategory))
        (x := CategoryTheory.nerveEquiv.symm X)
        (y := CategoryTheory.nerveEquiv.symm Y)
        f
    obtain ⟨g, hg⟩ := CategoryTheory.nerve.edgeMk_surjective
      (SSet.Edge.ofTruncated e)
    have hg' : (CategoryTheory.nerve.edgeMk g).toTruncated = e := by
      rw [hg]
      rfl
    rw [← hg']
    change edgeHomotopyClass
        (CategoryTheory.nerve.edgeMk
          (metrizableComplexNerveHomotopyToComplexFunctor.map
            (edgeHomotopyClass (CategoryTheory.nerve.edgeMk g)))) =
      edgeHomotopyClass (CategoryTheory.nerve.edgeMk g)
    rw [metrizableComplexNerveHomotopyToComplexFunctor_map_edgeMk]
  preimage_map f :=
    metrizableComplexNerveHomotopyToComplexFunctor_map_edgeMk f

/-- Every object of the nerve homotopy category comes from its underlying bounded complex. -/
@[implicit_reducible]
noncomputable def metrizableComplexToNerveHomotopyFunctorEssSurj :
    metrizableComplexToNerveHomotopyFunctor.EssSurj where
  mem_essImage X := by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective X
    refine ⟨CategoryTheory.nerveEquiv x, ?_⟩
    exact ⟨eqToIso (congrArg homotopyObject
      (Equiv.symm_apply_apply CategoryTheory.nerveEquiv x))⟩

/-- The canonical functor from bounded complexes to the homotopy category of their ordinary
nerve is an equivalence. -/
noncomputable instance metrizableComplexToNerveHomotopyFunctor_isEquivalence :
    metrizableComplexToNerveHomotopyFunctor.IsEquivalence where
  faithful := metrizableComplexToNerveHomotopyFunctorFullyFaithful.faithful
  full := metrizableComplexToNerveHomotopyFunctorFullyFaithful.full
  essSurj := metrizableComplexToNerveHomotopyFunctorEssSurj

/-- Evaluation from the nerve homotopy category is also an equivalence. -/
noncomputable instance metrizableComplexNerveHomotopyToComplexFunctor_isEquivalence :
    metrizableComplexNerveHomotopyToComplexFunctor.IsEquivalence := by
  haveI : (metrizableComplexToNerveHomotopyFunctor ⋙
      metrizableComplexNerveHomotopyToComplexFunctor).IsEquivalence := by
    rw [metrizableComplexToNerveHomotopyFunctor_comp_evaluation]
    infer_instance
  exact CategoryTheory.Functor.isEquivalence_of_comp_left
    metrizableComplexToNerveHomotopyFunctor
    metrizableComplexNerveHomotopyToComplexFunctor

/-- A morphism represented by a relatively marked nerve edge evaluates to the isomorphism
closure of the generated corrected weak equivalences. -/
theorem markedHomotopyMorphismProperty_le_generatedIsoClosure_evaluation :
    markedHomotopyMorphismProperty
        (relativeNerveEdgeMarking relativeCategory) ≤
      GeneratedWeakEquivalence.isoClosure.inverseImage
        metrizableComplexNerveHomotopyToComplexFunctor := by
  intro X Y f hf
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨K, L, g, hg, ha⟩ := ha
  have hedge :
      Arrow.mk (edgeHomotopyClass (SSet.Edge.mk' a)) =
        Arrow.mk (edgeHomotopyClass (CategoryTheory.nerve.edgeMk g)) := by
    apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
    exact ha
  have hmap := congrArg
    metrizableComplexNerveHomotopyToComplexFunctor.mapArrow.obj
    (hfa.trans hedge)
  have hmap' :
      Arrow.mk (metrizableComplexNerveHomotopyToComplexFunctor.map f) =
        Arrow.mk g := by
    simpa using hmap
  exact ⟨K, L, g, hg, ⟨eqToIso hmap'.symm⟩⟩

/-- Evaluation followed by the relative homotopy functor agrees with the homotopy-category
map induced directly by equivalence forcing. -/
theorem metrizableComplexNerveEvaluation_comp_equivalenceForcingHomotopyFunctor :
    metrizableComplexNerveHomotopyToComplexFunctor ⋙
        metrizableEquivalenceForcingHomotopyFunctor =
      (SSet.hoFunctor.map metrizableEquivalenceForcingMap).toFunctor := by
  let hobj : ∀ X,
      (metrizableComplexNerveHomotopyToComplexFunctor ⋙
        metrizableEquivalenceForcingHomotopyFunctor).obj X =
      (SSet.hoFunctor.map metrizableEquivalenceForcingMap).toFunctor.obj X := fun X ↦ by
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective X
    obtain ⟨K, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective x
    rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro X Y f
  apply (conj_eqToHom_iff_heq _ _ (hobj X) (hobj Y)).2
  obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective X
  obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective Y
  obtain ⟨K, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective x
  obtain ⟨L, rfl⟩ := CategoryTheory.nerveEquiv.symm.surjective y
  obtain ⟨e, he⟩ :=
    homotopyCategory_homMk_surjective_of_quasicategory
      (V := metrizableComplexNerveTruncation) f
  rw [← he]
  obtain ⟨g, hg⟩ := CategoryTheory.nerve.edgeMk_surjective
    (SSet.Edge.ofTruncated e)
  have hg' : (CategoryTheory.nerve.edgeMk g).toTruncated = e := by
    rw [hg]
    rfl
  rw [← hg']
  rw [show (metrizableComplexNerveHomotopyToComplexFunctor ⋙
      metrizableEquivalenceForcingHomotopyFunctor).map
        (SSet.Truncated.HomotopyCategory.homMk
          (CategoryTheory.nerve.edgeMk g).toTruncated) =
      metrizableEquivalenceForcingHomotopyFunctor.map g by
    change metrizableEquivalenceForcingHomotopyFunctor.map
      (metrizableComplexNerveHomotopyToComplexFunctor.map
        (edgeHomotopyClass (CategoryTheory.nerve.edgeMk g))) = _
    rw [metrizableComplexNerveHomotopyToComplexFunctor_map_edgeMk]]
  rfl

/-- The mapping-quasicategory localization property makes the equivalence-forcing homotopy
functor an ordinary localization at the generated corrected weak equivalences. -/
theorem metrizableEquivalenceForcingHomotopyFunctor_isLocalization_generated
    (h : MetrizableEquivalenceForcingMappingLocalizationProperty) :
    metrizableEquivalenceForcingHomotopyFunctor.IsLocalization
      GeneratedWeakEquivalence := by
  let W := markedHomotopyMorphismProperty
    (relativeNerveEdgeMarking relativeCategory)
  let L := (SSet.hoFunctor.map metrizableEquivalenceForcingMap).toFunctor
  letI : L.IsLocalization W := by
    dsimp only [L, W]
    simpa only [metrizableEquivalenceForcingQCatMap,
      ObjectProperty.homMk_hom] using
        mappingLocalizationHomotopyFunctor_isLocalization h
  apply CategoryTheory.Functor.IsLocalization.of_equivalence_source
    L W metrizableEquivalenceForcingHomotopyFunctor
      GeneratedWeakEquivalence
      metrizableComplexNerveHomotopyToComplexFunctor.asEquivalence
  · exact markedHomotopyMorphismProperty_le_generatedIsoClosure_evaluation
  · intro K L f hf
    exact RelativeInfinityFunctor.homotopyFunctor_inverts
      metrizableEquivalenceForcingRelativeInfinityFunctor f hf
  · exact eqToIso
      metrizableComplexNerveEvaluation_comp_equivalenceForcingHomotopyFunctor

private theorem correctedLocalization_inverts_generatedWeakEquivalence :
    GeneratedWeakEquivalence.IsInvertedBy CorrectedWeakEquivalence.Q := by
  intro K L f hf
  induction hf with
  | of f hf =>
      exact Localization.inverts CorrectedWeakEquivalence.Q
        CorrectedWeakEquivalence f hf
  | id K =>
      exact CategoryTheory.Functor.map_isIso CorrectedWeakEquivalence.Q (𝟙 K)
  | comp_of f g hf hg ih =>
      haveI : IsIso (CorrectedWeakEquivalence.Q.map f) := ih
      haveI : IsIso (CorrectedWeakEquivalence.Q.map g) :=
        Localization.inverts CorrectedWeakEquivalence.Q
          CorrectedWeakEquivalence g hg
      rw [Functor.map_comp]
      infer_instance

private noncomputable def generatedToCorrectedLocalization :
    GeneratedWeakEquivalence.Localization ⥤
      CorrectedWeakEquivalence.Localization :=
  Localization.Construction.lift CorrectedWeakEquivalence.Q
    correctedLocalization_inverts_generatedWeakEquivalence

private noncomputable def correctedToGeneratedLocalization :
    CorrectedWeakEquivalence.Localization ⥤
      GeneratedWeakEquivalence.Localization :=
  Localization.Construction.lift GeneratedWeakEquivalence.Q
    (fun _ _ f hf ↦ Localization.inverts GeneratedWeakEquivalence.Q
      GeneratedWeakEquivalence f
      (correctedWeakEquivalence_le_generated f hf))

private noncomputable def generatedToCorrectedLocalizationUnitIso :
    𝟭 GeneratedWeakEquivalence.Localization ≅
      generatedToCorrectedLocalization ⋙ correctedToGeneratedLocalization :=
  eqToIso (Localization.Construction.uniq _ _ (by
    simp only [Functor.comp_id, ← Functor.assoc,
      generatedToCorrectedLocalization, correctedToGeneratedLocalization,
      Localization.Construction.fac]))

private noncomputable def generatedToCorrectedLocalizationCounitIso :
    correctedToGeneratedLocalization ⋙ generatedToCorrectedLocalization ≅
      𝟭 CorrectedWeakEquivalence.Localization :=
  eqToIso (Localization.Construction.uniq _ _ (by
    simp only [Functor.comp_id, ← Functor.assoc,
      generatedToCorrectedLocalization, correctedToGeneratedLocalization,
      Localization.Construction.fac]))

private instance generatedToCorrectedLocalization_isEquivalence :
    generatedToCorrectedLocalization.IsEquivalence :=
  CategoryTheory.Functor.IsEquivalence.mk'
    correctedToGeneratedLocalization
    generatedToCorrectedLocalizationUnitIso
    generatedToCorrectedLocalizationCounitIso

private instance correctedToGeneratedLocalization_isEquivalence :
    correctedToGeneratedLocalization.IsEquivalence :=
  CategoryTheory.Functor.IsEquivalence.mk'
    generatedToCorrectedLocalization
    generatedToCorrectedLocalizationCounitIso.symm
    generatedToCorrectedLocalizationUnitIso.symm

/-- The generated localization result is unchanged when stated for the original corrected
weak equivalences, since functors invert their multiplicative closure automatically. -/
theorem metrizableEquivalenceForcingHomotopyFunctor_isLocalization
    (h : MetrizableEquivalenceForcingMappingLocalizationProperty) :
    metrizableEquivalenceForcingHomotopyFunctor.IsLocalization
      CorrectedWeakEquivalence := by
  letI : metrizableEquivalenceForcingHomotopyFunctor.IsLocalization
      GeneratedWeakEquivalence :=
    metrizableEquivalenceForcingHomotopyFunctor_isLocalization_generated h
  let hraw : CorrectedWeakEquivalence.IsInvertedBy
      metrizableEquivalenceForcingHomotopyFunctor := fun K L f hf ↦
    Localization.inverts metrizableEquivalenceForcingHomotopyFunctor
      GeneratedWeakEquivalence f
      (correctedWeakEquivalence_le_generated f hf)
  let Hraw := Localization.Construction.lift
    metrizableEquivalenceForcingHomotopyFunctor hraw
  let Hgen := Localization.Construction.lift
    metrizableEquivalenceForcingHomotopyFunctor
      (Localization.inverts metrizableEquivalenceForcingHomotopyFunctor
        GeneratedWeakEquivalence)
  haveI : Hgen.IsEquivalence := by
    dsimp only [Hgen]
    infer_instance
  haveI : (correctedToGeneratedLocalization ⋙ Hgen).IsEquivalence := by
    infer_instance
  have heq : Hraw = correctedToGeneratedLocalization ⋙ Hgen := by
    apply Localization.Construction.uniq
    simp only [Hraw, Hgen, correctedToGeneratedLocalization,
      Localization.Construction.fac, ← Functor.assoc]
  exact
    { inverts := hraw
      isEquivalence := CategoryTheory.Functor.isEquivalence_of_iso
        (eqToIso heq.symm) }

/-- The equivalence-forcing homotopy functor is unconditionally the ordinary localization at
the corrected weak equivalences. -/
theorem metrizableEquivalenceForcingHomotopyFunctor_isLocalization_direct :
    metrizableEquivalenceForcingHomotopyFunctor.IsLocalization
      CorrectedWeakEquivalence :=
  metrizableEquivalenceForcingHomotopyFunctor_isLocalization
    metrizableEquivalenceForcingMappingLocalizationProperty_direct

/-- Under the genuine mapping-localization property, the canonical comparison from the
corrected bounded derived category is an equivalence. -/
theorem metrizableCorrectedDerivedToEquivalenceForcingHomotopy_isEquivalence
    (h : MetrizableEquivalenceForcingMappingLocalizationProperty) :
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy.IsEquivalence :=
  metrizableCorrectedDerivedToEquivalenceForcingHomotopy_isEquivalence_of_isLocalization
    (metrizableEquivalenceForcingHomotopyFunctor_isLocalization h)

/-- The canonical ordinary comparison functor is unconditionally an equivalence. -/
theorem
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy_isEquivalence_direct :
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy.IsEquivalence :=
  metrizableCorrectedDerivedToEquivalenceForcingHomotopy_isEquivalence
    metrizableEquivalenceForcingMappingLocalizationProperty_direct

/-- The ordinary comparison equivalence induced by a verified mapping-quasicategory
localization property. -/
noncomputable def metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalence
    (h : MetrizableEquivalenceForcingMappingLocalizationProperty) :
    DboundedWithCycles MetrizableLCA.{0} ≌
      SSet.hoFunctor.obj metrizableEquivalenceForcingQCat.obj := by
  letI : metrizableCorrectedDerivedToEquivalenceForcingHomotopy.IsEquivalence :=
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy_isEquivalence h
  exact metrizableCorrectedDerivedToEquivalenceForcingHomotopy.asEquivalence

/-- The corrected bounded derived category is unconditionally equivalent to the homotopy
category of the genuine infinity-localization carrier. -/
noncomputable def
    metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalenceDirect :
    DboundedWithCycles MetrizableLCA.{0} ≌
      SSet.hoFunctor.obj metrizableEquivalenceForcingQCat.obj :=
  metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalence
    metrizableEquivalenceForcingMappingLocalizationProperty_direct

/-- The ordinary comparison equivalence retains the canonical factorization of the
equivalence-forcing homotopy functor through corrected bounded localization. -/
noncomputable def metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalence_fac
    (h : MetrizableEquivalenceForcingMappingLocalizationProperty) :
    DboundedWithCycles.localization MetrizableLCA.{0} ⋙
        (metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalence h).functor ≅
      metrizableEquivalenceForcingHomotopyFunctor :=
  metrizableCorrectedDerivedToEquivalenceForcingHomotopy_fac

/-- The unconditional ordinary comparison equivalence retains the canonical localization
factorization. -/
noncomputable def
    metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalenceDirect_fac :
    DboundedWithCycles.localization MetrizableLCA.{0} ⋙
        metrizableCorrectedDerivedEquivalenceForcingHomotopyEquivalenceDirect.functor ≅
      metrizableEquivalenceForcingHomotopyFunctor :=
  metrizableCorrectedDerivedToEquivalenceForcingHomotopy_fac

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
