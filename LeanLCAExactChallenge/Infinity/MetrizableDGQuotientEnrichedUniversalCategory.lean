/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedNaturalTransformationExtension

/-! # The categorical enriched universal property of the corrected Drinfeld quotient -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open Opposite

variable (D : Type*) [EnrichedCategory QuotientDGCochain D]

/-- Extension across the corrected quotient, including strict unit-graded transformations. -/
noncomputable def annihilatingEnrichedFunctorExtensionFunctor :
    AnnihilatingEnrichedFunctorCategory D ⥤
      QuotientDGEnrichedFunctorCategory CorrectedQuotientDGCategory D where
  obj E := E.enrichedExtension
  map α := annihilatingEnrichedFunctorNatTransExtension α
  map_id E := by
    apply GradedNatTrans.ext
    funext K
    rfl
  map_comp α β := by
    apply GradedNatTrans.ext
    funext K
    rfl

/-- Restriction from the corrected quotient, including strict unit-graded transformations. -/
noncomputable def quotientEnrichedFunctorRestrictionFunctor :
    QuotientDGEnrichedFunctorCategory CorrectedQuotientDGCategory D ⥤
      AnnihilatingEnrichedFunctorCategory D where
  obj G := AnnihilatingEnrichedFunctorData.restriction G
  map α := quotientDGUnitGradedNatTransRestriction α
  map_id G := by
    apply AnnihilatingEnrichedFunctorNatTrans.ext
    apply GradedNatTrans.ext
    funext K
    rfl
  map_comp α β := by
    apply AnnihilatingEnrichedFunctorNatTrans.ext
    apply GradedNatTrans.ext
    funext K
    rfl

noncomputable instance annihilatingEnrichedFunctorExtensionFunctor_faithful :
    (annihilatingEnrichedFunctorExtensionFunctor D).Faithful where
  map_injective := by
    intro E F α β h
    change annihilatingEnrichedFunctorNatTransExtension α =
      annihilatingEnrichedFunctorNatTransExtension β at h
    calc
      α = annihilatingEnrichedFunctorNatTransTransport
          E.restriction_enrichedExtension F.restriction_enrichedExtension
          (quotientDGUnitGradedNatTransRestriction
            (annihilatingEnrichedFunctorNatTransExtension α)) :=
        (restriction_annihilatingEnrichedFunctorNatTransExtension α).symm
      _ = annihilatingEnrichedFunctorNatTransTransport
          E.restriction_enrichedExtension F.restriction_enrichedExtension
          (quotientDGUnitGradedNatTransRestriction
            (annihilatingEnrichedFunctorNatTransExtension β)) := by
        rw [h]
      _ = β := restriction_annihilatingEnrichedFunctorNatTransExtension β

noncomputable instance annihilatingEnrichedFunctorExtensionFunctor_full :
    (annihilatingEnrichedFunctorExtensionFunctor D).Full where
  map_surjective := by
    intro E F β
    let raw := quotientDGUnitGradedNatTransRestriction β
    let α := annihilatingEnrichedFunctorNatTransTransport
      E.restriction_enrichedExtension F.restriction_enrichedExtension raw
    refine ⟨α, ?_⟩
    apply GradedNatTrans.ext
    funext K
    apply eq_of_heq
    exact (annihilatingEnrichedFunctorNatTransTransport_app_heq
      E.restriction_enrichedExtension F.restriction_enrichedExtension
      raw (op K.unop)).trans (by rfl)

noncomputable instance annihilatingEnrichedFunctorExtensionFunctor_essSurj :
    (annihilatingEnrichedFunctorExtensionFunctor D).EssSurj where
  mem_essImage G :=
    ⟨AnnihilatingEnrichedFunctorData.restriction G,
      ⟨eqToIso (EnrichedFunctor.enrichedExtension_restriction G)⟩⟩

noncomputable instance annihilatingEnrichedFunctorExtensionFunctor_isEquivalence :
    (annihilatingEnrichedFunctorExtensionFunctor D).IsEquivalence :=
  Functor.IsEquivalence.mk

/-- The corrected Drinfeld quotient has the full categorical enriched universal property:
extension is an equivalence between annihilating original enriched functors and enriched
functors out of the quotient. -/
noncomputable def annihilatingEnrichedFunctorCategoryEquivalence :
    AnnihilatingEnrichedFunctorCategory D ≌
      QuotientDGEnrichedFunctorCategory CorrectedQuotientDGCategory D :=
  (annihilatingEnrichedFunctorExtensionFunctor D).asEquivalence

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
