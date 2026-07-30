/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationCompositionPreservation

/-! # Enriched extension from the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

/-- Word evaluation packages an annihilating enriched functor as an enriched functor out of the
corrected Drinfeld quotient. -/
def enrichedExtension :
    EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D where
  obj K := E.functor.obj K
  map K L := E.evaluateCochainMap L.unop K.unop
  map_id K := E.evaluateCochainMap_id K.unop
  map_comp K L M := E.evaluateCochainMap_comp M.unop L.unop K.unop

@[simp]
theorem enrichedExtension_obj (K : CorrectedQuotientDGCategory) :
    E.enrichedExtension.obj K = E.functor.obj K :=
  rfl

@[simp]
theorem enrichedExtension_map (K L : CorrectedQuotientDGCategory) :
    E.enrichedExtension.map K L = E.evaluateCochainMap L.unop K.unop :=
  rfl

/-- Restricting the enriched extension to zero-word morphisms recovers the supplied original
enriched functor on every Hom complex. -/
theorem enrichedExtension_restricts
    (K L : OriginalCoefficientDGCategory) :
    OriginalCoefficientHomToQuotient L.unop K.unop ≫
        E.enrichedExtension.map K L =
      E.functor.map K L := by
  exact E.evaluateCochainMap_original L.unop K.unop

/-- Restrict a quotient-enriched functor to the original coefficient-changed DG category and
remember the images of the formal contracting generators. -/
noncomputable def restriction
    (G : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D) :
    AnnihilatingEnrichedFunctorData D where
  functor := EnrichedFunctor.comp QuotientDGCochain originalToCorrectedQuotientDG G
  contraction A :=
    (G.map (Opposite.op A.obj) (Opposite.op A.obj)).f (-1)
      (ULift.up (quotientContractingElement A))
  contraction_d A := by
    let K : CorrectedQuotientDGCategory := Opposite.op A.obj
    let x : (quotientDGEnrichedHom K K).X (-1) :=
      ULift.up (quotientContractingElement A)
    have hcomm := ConcreteCategory.congr_hom ((G.map K K).comm (-1) 0) x
    have hcomm' :
        ((G.obj K ⟶[QuotientDGCochain] G.obj K).d (-1) 0)
            ((G.map K K).f (-1) x) =
          (G.map K K).f 0 ((K ⟶[QuotientDGCochain] K).d (-1) 0 x) := by
      simpa only [ModuleCat.comp_apply] using hcomm
    change ((G.obj K ⟶[QuotientDGCochain] G.obj K).d (-1) 0)
        ((G.map K K).f (-1) x) = targetDGIdentityElement (G.obj K)
    rw [hcomm']
    change (G.map K K).f 0
        ((quotientCoefficientCochainComplex A.obj A.obj).d (-1) 0 x) = _
    have hd : (quotientCoefficientCochainComplex A.obj A.obj).d (-1) 0 =
        ModuleCat.ofHom
          (quotientLinearMapChangeScalars
            (quotientTotalDifferential A.obj A.obj (-1)).hom) := by
      simpa using quotientCoefficientCochainComplex_d_succ A.obj A.obj (-1)
    rw [hd]
    change (G.map K K).f 0
        (ULift.up ((quotientTotalDifferential A.obj A.obj (-1)).hom
          (quotientContractingElement A))) = _
    rw [quotientTotalDifferential_contractingElement]
    let one : (𝟙_ QuotientDGCochain).X 0 :=
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1
    have hsource : (eId QuotientDGCochain K).f 0 one =
        ULift.up ((originalHomInclusion A.obj A.obj 0).hom
          (ULift.up (identityCochain A.obj))) := by
      change (quotientDGIdentity A.obj).f 0 one = _
      rw [quotientDGIdentity_f_zero]
      let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
      have hone : e.hom.hom (e.inv.hom (1 : QuotientCoefficientRing)) = 1 := by
        have h := ConcreteCategory.congr_hom e.inv_hom_id (1 : QuotientCoefficientRing)
        simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
      change (quotientIdentitySpan A.obj).hom (e.hom.hom (e.inv.hom 1)) = _
      rw [hone]
      exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _
    have hid := G.map_id K
    have hid0 := congrArg (fun f ↦ f.f 0) hid
    have happ := ConcreteCategory.congr_hom hid0 one
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at happ
    rw [hsource] at happ
    exact happ

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
