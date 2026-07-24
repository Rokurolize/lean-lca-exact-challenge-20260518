/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EnrichedFunctorTransport
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientInclusionChainFunctor
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientSimplicialCategory

/-! # The zero-word comparison of homotopy coherent nerves -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open Opposite
open Simplicial
open QuotientDoldKanMonoidal

/-- Simplicial modules used for the coefficient-changed original enrichment. -/
abbrev OriginalCoefficientDGSimp :=
  SimplicialObject (ModuleCat.{1} QuotientCoefficientRing)

/-- The coefficient-changed original DG category transported through Dold--Kan. -/
abbrev OriginalCoefficientDGSimplicialModuleCategory :=
  TransportEnrichment quotientModuleDoldKanEquivalence.inverse
    OriginalCoefficientDGCategory

@[implicit_reducible]
noncomputable instance originalCoefficientDGDoldKanEnrichment :
    EnrichedCategory OriginalCoefficientDGSimp
      OriginalCoefficientDGSimplicialModuleCategory :=
  inferInstance

/-- The zero-word chain functor transported through Dold--Kan. -/
noncomputable def originalToCorrectedQuotientDGSimplicialModule :
    EnrichedFunctor OriginalCoefficientDGSimp
      OriginalCoefficientDGSimplicialModuleCategory
      CorrectedQuotientDGSimplicialModuleCategory :=
  CategoryTheory.EnrichedFunctor.transport quotientModuleDoldKanEquivalence.inverse
    originalToCorrectedQuotientDGChain

/-- Restore geometric arrow orientation. -/
abbrev OriginalCoefficientDGSimplicialModuleCategoryOp :=
  OriginalCoefficientDGSimplicialModuleCategoryᵒᵖ

@[implicit_reducible]
noncomputable instance originalCoefficientDGSimplicialModuleOppositeEnrichment :
    EnrichedCategory OriginalCoefficientDGSimp
      OriginalCoefficientDGSimplicialModuleCategoryOp :=
  inferInstance

/-- The Dold--Kan zero-word functor after restoring geometric orientation. -/
noncomputable def originalToCorrectedQuotientDGSimplicialModuleOp :
    EnrichedFunctor OriginalCoefficientDGSimp
      OriginalCoefficientDGSimplicialModuleCategoryOp
      CorrectedQuotientDGSimplicialModuleCategoryOp :=
  CategoryTheory.EnrichedFunctor.op originalToCorrectedQuotientDGSimplicialModule

/-- The coefficient-changed original carrier enriched in simplicial sets. -/
abbrev OriginalCoefficientDGSSetEnrichedCategory :=
  TransportEnrichment quotientCoefficientSimplicialForget
    OriginalCoefficientDGSimplicialModuleCategoryOp

@[implicit_reducible]
noncomputable instance originalCoefficientDGSSetEnrichment :
    EnrichedCategory SSet OriginalCoefficientDGSSetEnrichedCategory :=
  inferInstance

/-- The zero-word functor after forgetting module structure. -/
noncomputable def originalToCorrectedQuotientDGSSetEnriched :
    EnrichedFunctor SSet
      OriginalCoefficientDGSSetEnrichedCategory
      CorrectedQuotientDGSSetEnrichedCategory :=
  CategoryTheory.EnrichedFunctor.transport quotientCoefficientSimplicialForget
    originalToCorrectedQuotientDGSimplicialModuleOp

/-- The underlying simplicial category of the coefficient-changed original carrier. -/
abbrev OriginalCoefficientDGSimplicialCategory :=
  ForgetEnrichment SSet OriginalCoefficientDGSSetEnrichedCategory

noncomputable instance originalCoefficientDGSimplicialCategoryStructure :
    SimplicialCategory OriginalCoefficientDGSimplicialCategory :=
  inferInstance

/-- Regard the simplicial-set-enriched zero-word functor as a functor of the underlying
simplicial categories. -/
noncomputable def originalToCorrectedQuotientDGSimplicialCategory :
    EnrichedFunctor SSet
      OriginalCoefficientDGSimplicialCategory CorrectedQuotientDGSimplicialCategory :=
  originalToCorrectedQuotientDGSSetEnriched

/-- Postcomposition by the zero-word functor on homotopy coherent nerves. -/
def originalToCorrectedQuotientDGHomotopyCoherentNerve :
    CategoryTheory.SimplicialNerve OriginalCoefficientDGSimplicialCategory ⟶
      CategoryTheory.SimplicialNerve CorrectedQuotientDGSimplicialCategory where
  app _ := ↾fun G ↦ CategoryTheory.EnrichedFunctor.comp SSet G
    originalToCorrectedQuotientDGSimplicialCategory
  naturality _ _ _ := rfl

/-- The Dold--Kan mapping simplicial module of the coefficient-changed original carrier. -/
abbrev originalCoefficientDGMappingSimplicialModule (K L : ComplexCategory) :
    OriginalCoefficientDGSimp :=
  quotientModuleDoldKanEquivalence.inverse.obj
    (originalCoefficientDGChainEnrichedHom (Opposite.op L) (Opposite.op K))

/-- The underlying mapping simplicial set of the coefficient-changed original carrier. -/
abbrev originalCoefficientDGMappingSSet (K L : ComplexCategory) : SSet.{1} :=
  quotientCoefficientSimplicialForget.obj
    (originalCoefficientDGMappingSimplicialModule K L)

/-- The additive-group mapping object used to certify the Kan property. -/
abbrev originalCoefficientDGMappingAddCommGrpSimplicialObject
    (K L : ComplexCategory) : SimplicialObject (AddCommGrpCat.{1}) :=
  ((SimplicialObject.whiskering
    (ModuleCat.{1} QuotientCoefficientRing) (AddCommGrpCat.{1})).obj
      (forget₂ (ModuleCat.{1} QuotientCoefficientRing) (AddCommGrpCat.{1}))).obj
        (originalCoefficientDGMappingSimplicialModule K L)

noncomputable instance originalCoefficientDGMappingSSet_kanComplex
    (K L : ComplexCategory) :
    SSet.KanComplex (originalCoefficientDGMappingSSet K L) := by
  change SSet.KanComplex
    (additiveUnderlyingSSet
      (originalCoefficientDGMappingAddCommGrpSimplicialObject K L))
  infer_instance

/-- Every enriched Hom in the coefficient-changed original simplicial category is Kan. -/
noncomputable instance originalCoefficientDG_enrichedHom_kanComplex
    (K L : OriginalCoefficientDGSimplicialCategory) :
    SSet.KanComplex (K ⟶[SSet] L) := by
  change SSet.KanComplex (originalCoefficientDGMappingSSet
    (show OriginalCoefficientDGSimplicialModuleCategory from K.unop).unop
    (show OriginalCoefficientDGSimplicialModuleCategory from L.unop).unop)
  infer_instance

/-- The homotopy coherent nerve of the coefficient-changed original DG carrier. -/
def originalCoefficientDGHomotopyCoherentNerve : SSet.{1} :=
  CategoryTheory.SimplicialNerve OriginalCoefficientDGSimplicialCategory

noncomputable instance originalCoefficientDGHomotopyCoherentNerve_quasicategory :
    SSet.Quasicategory originalCoefficientDGHomotopyCoherentNerve :=
  LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration.simplicialNerve_quasicategory
    OriginalCoefficientDGSimplicialCategory

/-- The coefficient-changed original coherent nerve bundled as a quasicategory. -/
def originalCoefficientDGHomotopyCoherentNerveQCat : SSet.QCat.{1} :=
  ⟨originalCoefficientDGHomotopyCoherentNerve, inferInstance⟩

/-- Short name for the coefficient-changed original DG quasicategory. -/
def originalCoefficientDGQCat : SSet.QCat.{1} :=
  originalCoefficientDGHomotopyCoherentNerveQCat

/-- The global zero-word comparison from the coefficient-changed original DG carrier to the
corrected quotient quasicategory. -/
def originalToCorrectedQuotientDGQCatMap :
    originalCoefficientDGQCat ⟶ correctedQuotientDGQCat :=
  ObjectProperty.homMk originalToCorrectedQuotientDGHomotopyCoherentNerve

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
