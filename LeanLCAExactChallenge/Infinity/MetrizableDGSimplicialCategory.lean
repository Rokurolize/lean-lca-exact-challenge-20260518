import LeanLCAExactChallenge.Infinity.AlexanderWhitneyAssociativity
import LeanLCAExactChallenge.Infinity.CoherentNerveLatchingCompatibility
import LeanLCAExactChallenge.Infinity.InnerAnodyneMapping
import LeanLCAExactChallenge.Infinity.InnerFibrantReplacement
import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModuleAssociativity
import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModuleUnits
import LeanLCAExactChallenge.Infinity.SimplicialAdditiveKan
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.CategoryTheory.Enriched.Opposite

/-!
# A genuine quasicategorical dg carrier for bounded metrizable complexes

The direct truncated Hom complexes form a chain-enriched category after reversing objects.
The coherent Alexander--Whitney structure transports this enrichment through Dold--Kan.
After taking the enriched opposite and forgetting module structure degreewise, this gives a
genuine simplicial category. Its homotopy coherent nerve has a chosen inner-fibrant replacement,
bundled as a quasicategory.

This is the bounded dg carrier before localization at corrected exact quasi-isomorphisms.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory
open CategoryTheory.MonoidalCategory

abbrev DirectZChain := ChainComplex (ModuleCat.{0} ℤ) ℕ

abbrev DirectZSimp := SimplicialObject (ModuleCat.{0} ℤ)

@[implicit_reducible]
noncomputable instance directZChainOppositeEnrichment :
    EnrichedCategory DirectZChain ComplexCategoryᵒᵖ where
  Hom K L := dgMappingDirectZModuleChainComplex L.unop K.unop
  id K := dgMappingDirectZModuleChainIdentity K.unop
  comp K L M := dgTruncatedCompositionReversed M.unop L.unop K.unop
  id_comp K L := dgMappingDirectZModuleChainIdentity_comp K.unop L.unop
  comp_id K L := dgMappingDirectZModuleChain_comp_identity K.unop L.unop
  assoc W X Y Z :=
    dgTruncatedCompositionReversed_assoc W.unop X.unop Y.unop Z.unop

@[implicit_reducible]
noncomputable instance directDoldKanInverseLaxMonoidal :
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.LaxMonoidal :=
  DoldKanMonoidal.inverseLaxMonoidalOfNormalizedOplax
    DoldKanMonoidal.normalizedMooreOplaxMonoidal

/-- Bounded complexes with their direct Dold--Kan enrichment, before restoring arrow order. -/
abbrev DirectDGSimplicialModuleCategory :=
  TransportEnrichment
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse
    ComplexCategoryᵒᵖ

@[implicit_reducible]
noncomputable instance directDGDoldKanEnrichment :
    EnrichedCategory DirectZSimp DirectDGSimplicialModuleCategory :=
  inferInstance

/-- Restoring arrow order gives mapping objects from `K` to `L`. -/
abbrev DirectDGSimplicialModuleCategoryOp :=
  DirectDGSimplicialModuleCategoryᵒᵖ

@[implicit_reducible]
noncomputable instance directDGSimplicialModuleOppositeEnrichment :
    EnrichedCategory DirectZSimp DirectDGSimplicialModuleCategoryOp :=
  inferInstance

@[implicit_reducible]
noncomputable instance zModuleForgetLaxMonoidal :
    (forget (ModuleCat.{0} ℤ)).LaxMonoidal := by
  exact (ModuleCat.adj ℤ).rightAdjointLaxMonoidal

/-- Forget the module structure of a simplicial integer module degreewise. -/
abbrev zModuleSimplicialForget : DirectZSimp ⥤ SSet.{0} :=
  (SimplicialObject.whiskering (ModuleCat.{0} ℤ) (Type 0)).obj
    (forget (ModuleCat.{0} ℤ))

@[implicit_reducible]
noncomputable instance zModuleSimplicialForgetLaxMonoidal :
    zModuleSimplicialForget.LaxMonoidal := by
  change (((Functor.whiskeringRight SimplexCategoryᵒᵖ
    (ModuleCat.{0} ℤ) (Type 0)).obj
      (forget (ModuleCat.{0} ℤ))).LaxMonoidal)
  exact Functor.LaxMonoidal.whiskeringRight
    (C := SimplexCategoryᵒᵖ) (forget (ModuleCat.{0} ℤ))

/-- The direct dg enrichment transported to simplicial sets. -/
abbrev DirectDGSSetEnrichedCategory :=
  TransportEnrichment zModuleSimplicialForget
    DirectDGSimplicialModuleCategoryOp

@[implicit_reducible]
noncomputable instance directDGSSetEnrichment :
    EnrichedCategory SSet DirectDGSSetEnrichedCategory :=
  inferInstance

/-- The honest underlying category of the direct simplicial enrichment. -/
abbrev DirectDGSimplicialCategory :=
  ForgetEnrichment SSet DirectDGSSetEnrichedCategory

noncomputable instance directDGSimplicialCategoryStructure :
    SimplicialCategory DirectDGSimplicialCategory :=
  inferInstance

/-- Regard a bounded complex as an object of the direct dg simplicial category. -/
def directDGObject (K : ComplexCategory) : DirectDGSimplicialCategory :=
  ForgetEnrichment.of SSet
    (show DirectDGSSetEnrichedCategory from
      Opposite.op
        (show DirectDGSimplicialModuleCategory from Opposite.op K))

/-- The dg category has exactly the bounded complexes as its objects. -/
def directDGObjectEquiv : ComplexCategory ≃ DirectDGSimplicialCategory where
  toFun := directDGObject
  invFun K :=
    (show DirectDGSimplicialModuleCategoryᵒᵖ from K).unop.unop
  left_inv _ := rfl
  right_inv _ := rfl

/-- The direct Dold--Kan mapping simplicial module. -/
abbrev dgMappingDirectZModuleSimplicialModule (K L : ComplexCategory) :
    DirectZSimp :=
  DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
    (dgMappingDirectZModuleChainComplex K L)

/-- The underlying simplicial set of the direct Dold--Kan mapping object. -/
abbrev dgMappingDirectZModuleSSet (K L : ComplexCategory) : SSet.{0} :=
  zModuleSimplicialForget.obj
    (dgMappingDirectZModuleSimplicialModule K L)

/-- Forget a simplicial integer module only as far as its additive group structure. -/
abbrev dgMappingDirectAddCommGrpSimplicialObject (K L : ComplexCategory) :
    SimplicialObject (AddCommGrpCat.{0}) :=
  ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (AddCommGrpCat.{0})).obj
    (forget₂ (ModuleCat.{0} ℤ) (AddCommGrpCat.{0}))).obj
      (dgMappingDirectZModuleSimplicialModule K L)

/-- Every direct Dold--Kan mapping simplicial set is a Kan complex. -/
noncomputable instance dgMappingDirectZModuleSSet_kanComplex (K L : ComplexCategory) :
    SSet.KanComplex (dgMappingDirectZModuleSSet K L) := by
  change SSet.KanComplex
    (additiveUnderlyingSSet (dgMappingDirectAddCommGrpSimplicialObject K L))
  infer_instance

/-- The enriched Hom is definitionally the direct Dold--Kan mapping simplicial set. -/
theorem directDG_enrichedHom_eq (K L : ComplexCategory) :
    (ForgetEnrichment.to SSet (directDGObject K) ⟶[SSet]
      ForgetEnrichment.to SSet (directDGObject L)) =
        dgMappingDirectZModuleSSet K L :=
  rfl

/-- The direct dg simplicial category is locally Kan. -/
noncomputable instance directDG_enrichedHom_kanComplex
    (K L : DirectDGSimplicialCategory) :
    SSet.KanComplex (K ⟶[SSet] L) := by
  change SSet.KanComplex (dgMappingDirectZModuleSSet
    (show DirectDGSimplicialModuleCategory from K.unop).unop
    (show DirectDGSimplicialModuleCategory from L.unop).unop)
  infer_instance

/-- The homotopy coherent nerve of the direct dg simplicial category. -/
def directDGHomotopyCoherentNerve : SSet.{1} :=
  CategoryTheory.SimplicialNerve DirectDGSimplicialCategory

noncomputable instance directDGHomotopyCoherentNerve_quasicategory :
    SSet.Quasicategory directDGHomotopyCoherentNerve :=
  LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration.simplicialNerve_quasicategory
    DirectDGSimplicialCategory

def directDGHomotopyCoherentNerveQCat : SSet.QCat.{1} :=
  ⟨directDGHomotopyCoherentNerve, inferInstance⟩

/-- A chosen quasicategorical replacement of the direct dg nerve. -/
def directDGQCat : SSet.QCat.{1} :=
  innerFibrantReplacementQCat directDGHomotopyCoherentNerve

/-- The replacement map from the dg nerve to its chosen quasicategory carrier. -/
def directDGNerveToQCat :
    directDGHomotopyCoherentNerve ⟶ directDGQCat.obj :=
  toInnerFibrantReplacement directDGHomotopyCoherentNerve

def directDGNerveToQCatMap :
    directDGHomotopyCoherentNerveQCat ⟶ directDGQCat :=
  ObjectProperty.homMk directDGNerveToQCat

theorem directDGNerveToQCat_innerAnodyne :
    SSet.innerAnodyneExtensions directDGNerveToQCat :=
  toInnerFibrantReplacement_innerAnodyne directDGHomotopyCoherentNerve

theorem directDGQCat_obj :
    directDGQCat.obj =
      innerFibrantReplacement directDGHomotopyCoherentNerve :=
  rfl

/-- Precomposition from the chosen dg quasicategory replacement to its coherent nerve. -/
def directDGNerveToQCatPrecompQCat (Q : SSet.QCat.{1}) :
    internalHomQCat directDGQCat.obj Q.obj
        (@quasicategory_ihom directDGQCat.obj Q.obj Q.property) ⟶
      internalHomQCat directDGHomotopyCoherentNerve Q.obj
        (@quasicategory_ihom directDGHomotopyCoherentNerve Q.obj Q.property) :=
  ObjectProperty.homMk (internalHomPrecomp directDGNerveToQCat Q.obj)

/-- Inner-fibrant replacement does not change the quasicategory of maps out of the coherent dg
nerve. -/
theorem directDGNerveToQCatPrecomp_isBicategoricalEquivalence
    (Q : SSet.QCat.{1}) :
    IsBicategoricalEquivalence (directDGNerveToQCatPrecompQCat Q) := by
  exact toInnerFibrantReplacement_precomp_isBicategoricalEquivalence
    directDGHomotopyCoherentNerve Q

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
