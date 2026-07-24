/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.CoherentNerveLatchingCompatibility
import LeanLCAExactChallenge.Infinity.InnerFibrantReplacement
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientChainEnrichedCategory
import LeanLCAExactChallenge.Infinity.QuotientDoldKanLaxMonoidal
import LeanLCAExactChallenge.Infinity.SimplicialAdditiveKan
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# The simplicial category of the corrected Drinfeld quotient

The verified Alexander--Whitney structure transports the smart-truncated corrected quotient
through Dold--Kan. Forgetting module structure gives a locally Kan simplicial category, whose
homotopy coherent nerve is therefore a quasicategory.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory
open QuotientDoldKanMonoidal

/-- Simplicial modules over the corrected quotient coefficient ring. -/
abbrev CorrectedQuotientDGSimp :=
  SimplicialObject (ModuleCat.{1} QuotientCoefficientRing)

@[implicit_reducible]
noncomputable instance correctedQuotientDGInverseLaxMonoidal :
    quotientModuleDoldKanEquivalence.inverse.LaxMonoidal :=
  quotientInverseLaxMonoidal

/-- The corrected quotient enrichment transported through Dold--Kan. -/
abbrev CorrectedQuotientDGSimplicialModuleCategory :=
  TransportEnrichment
    quotientModuleDoldKanEquivalence.inverse
    CorrectedQuotientDGCategory

@[implicit_reducible]
noncomputable instance correctedQuotientDGDoldKanEnrichment :
    EnrichedCategory CorrectedQuotientDGSimp CorrectedQuotientDGSimplicialModuleCategory :=
  inferInstance

/-- Restore the original arrow orientation after the quotient's opposite object convention. -/
abbrev CorrectedQuotientDGSimplicialModuleCategoryOp :=
  CorrectedQuotientDGSimplicialModuleCategoryᵒᵖ

@[implicit_reducible]
noncomputable instance correctedQuotientDGSimplicialModuleOppositeEnrichment :
    EnrichedCategory CorrectedQuotientDGSimp CorrectedQuotientDGSimplicialModuleCategoryOp :=
  inferInstance

@[implicit_reducible]
noncomputable instance quotientCoefficientModuleForgetLaxMonoidal :
    (forget (ModuleCat.{1} QuotientCoefficientRing)).LaxMonoidal := by
  exact (ModuleCat.adj QuotientCoefficientRing).rightAdjointLaxMonoidal

/-- Forget the quotient-coefficient module structure degreewise. -/
abbrev quotientCoefficientSimplicialForget :
    CorrectedQuotientDGSimp ⥤ SSet.{1} :=
  (SimplicialObject.whiskering
    (ModuleCat.{1} QuotientCoefficientRing) (Type 1)).obj
      (forget (ModuleCat.{1} QuotientCoefficientRing))

@[implicit_reducible]
noncomputable instance quotientCoefficientSimplicialForgetLaxMonoidal :
    quotientCoefficientSimplicialForget.LaxMonoidal := by
  change (((Functor.whiskeringRight SimplexCategoryᵒᵖ
    (ModuleCat.{1} QuotientCoefficientRing) (Type 1)).obj
      (forget (ModuleCat.{1} QuotientCoefficientRing))).LaxMonoidal)
  exact Functor.LaxMonoidal.whiskeringRight
    (C := SimplexCategoryᵒᵖ) (forget (ModuleCat.{1} QuotientCoefficientRing))

/-- The corrected quotient transported to a simplicial-set enrichment. -/
abbrev CorrectedQuotientDGSSetEnrichedCategory :=
  TransportEnrichment quotientCoefficientSimplicialForget
    CorrectedQuotientDGSimplicialModuleCategoryOp

@[implicit_reducible]
noncomputable instance correctedQuotientDGSSetEnrichment :
    EnrichedCategory SSet CorrectedQuotientDGSSetEnrichedCategory :=
  inferInstance

/-- The underlying simplicial category of the corrected quotient. -/
abbrev CorrectedQuotientDGSimplicialCategory :=
  ForgetEnrichment SSet CorrectedQuotientDGSSetEnrichedCategory

noncomputable instance correctedQuotientDGSimplicialCategoryStructure :
    SimplicialCategory CorrectedQuotientDGSimplicialCategory :=
  inferInstance

/-- Regard a bounded complex as an object of the corrected quotient simplicial category. -/
def correctedQuotientDGObject (K : ComplexCategory) :
    CorrectedQuotientDGSimplicialCategory :=
  ForgetEnrichment.of SSet
    (show CorrectedQuotientDGSSetEnrichedCategory from
      Opposite.op
        (show CorrectedQuotientDGSimplicialModuleCategory from Opposite.op K))

/-- The corrected quotient simplicial category has the bounded complexes as its objects. -/
def correctedQuotientDGObjectEquiv :
    ComplexCategory ≃ CorrectedQuotientDGSimplicialCategory where
  toFun := correctedQuotientDGObject
  invFun K :=
    (show CorrectedQuotientDGSimplicialModuleCategoryᵒᵖ from K).unop.unop
  left_inv _ := rfl
  right_inv _ := rfl

/-- The Dold--Kan mapping simplicial module of the corrected quotient. -/
abbrev correctedQuotientDGMappingSimplicialModule (K L : ComplexCategory) :
    CorrectedQuotientDGSimp :=
  quotientModuleDoldKanEquivalence.inverse.obj
    (quotientDGChainEnrichedHom (Opposite.op L) (Opposite.op K))

/-- The underlying mapping simplicial set of the corrected quotient. -/
abbrev correctedQuotientDGMappingSSet (K L : ComplexCategory) : SSet.{1} :=
  quotientCoefficientSimplicialForget.obj
    (correctedQuotientDGMappingSimplicialModule K L)

/-- Forget a quotient-coefficient simplicial module to an additive simplicial group. -/
abbrev correctedQuotientDGMappingAddCommGrpSimplicialObject
    (K L : ComplexCategory) : SimplicialObject (AddCommGrpCat.{1}) :=
  ((SimplicialObject.whiskering
    (ModuleCat.{1} QuotientCoefficientRing) (AddCommGrpCat.{1})).obj
      (forget₂ (ModuleCat.{1} QuotientCoefficientRing) (AddCommGrpCat.{1}))).obj
        (correctedQuotientDGMappingSimplicialModule K L)

/-- Every corrected quotient mapping simplicial set is a Kan complex. -/
noncomputable instance correctedQuotientDGMappingSSet_kanComplex
    (K L : ComplexCategory) :
    SSet.KanComplex (correctedQuotientDGMappingSSet K L) := by
  change SSet.KanComplex
    (additiveUnderlyingSSet
      (correctedQuotientDGMappingAddCommGrpSimplicialObject K L))
  infer_instance

/-- The enriched Hom is definitionally the corrected quotient Dold--Kan mapping set. -/
theorem correctedQuotientDG_enrichedHom_eq (K L : ComplexCategory) :
    (ForgetEnrichment.to SSet (correctedQuotientDGObject K) ⟶[SSet]
      ForgetEnrichment.to SSet (correctedQuotientDGObject L)) =
        correctedQuotientDGMappingSSet K L :=
  rfl

/-- The corrected quotient simplicial category is locally Kan. -/
noncomputable instance correctedQuotientDG_enrichedHom_kanComplex
    (K L : CorrectedQuotientDGSimplicialCategory) :
    SSet.KanComplex (K ⟶[SSet] L) := by
  change SSet.KanComplex (correctedQuotientDGMappingSSet
    (show CorrectedQuotientDGSimplicialModuleCategory from K.unop).unop
    (show CorrectedQuotientDGSimplicialModuleCategory from L.unop).unop)
  infer_instance

/-- The homotopy coherent nerve of the corrected quotient simplicial category. -/
def correctedQuotientDGHomotopyCoherentNerve : SSet.{1} :=
  CategoryTheory.SimplicialNerve CorrectedQuotientDGSimplicialCategory

noncomputable instance correctedQuotientDGHomotopyCoherentNerve_quasicategory :
    SSet.Quasicategory correctedQuotientDGHomotopyCoherentNerve :=
  LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration.simplicialNerve_quasicategory
    CorrectedQuotientDGSimplicialCategory

/-- The corrected quotient coherent nerve bundled as a quasicategory. -/
def correctedQuotientDGHomotopyCoherentNerveQCat : SSet.QCat.{1} :=
  ⟨correctedQuotientDGHomotopyCoherentNerve, inferInstance⟩

/-- The corrected quotient quasicategory. -/
def correctedQuotientDGQCat : SSet.QCat.{1} :=
  correctedQuotientDGHomotopyCoherentNerveQCat

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
