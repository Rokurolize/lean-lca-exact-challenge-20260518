/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWeakEquivalenceEdge
import LeanLCAExactChallenge.Infinity.MetrizableEquivalenceForcing
import LeanLCAExactChallenge.Infinity.InnerAnodyneMapping
import LeanLCAExactChallenge.Infinity.JoyalParameterizedExtension

/-!
# Comparing the ordinary localization with the corrected quotient

The generated corrected weak edges are extended to free-living equivalences in the corrected
quotient. The resulting maps out of the equivalence-forcing presentation and its fibrant
replacement provide the strict comparison triangle used by the localization argument.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open CategoryTheory.MorphismProperty
open Opposite
open Simplicial

/-- The internal-Hom vertex represented by an edge. -/
def internalHomVertexOfEdge {Q : SSet.{u}} {x y : Q _⦋0⦌}
    (e : SSet.Edge x y) : ((ihom (Δ[1] : SSet.{u})).obj Q) _⦋0⦌ :=
  SSet.unitHomEquiv ((ihom (Δ[1] : SSet.{u})).obj Q)
    (MonoidalClosed.curry' (SSet.yonedaEquiv.symm e.edge))

/-- The internal-Hom vertex represented by an edge evaluates back to that edge simplex. -/
theorem internalHomVertexMap_internalHomVertexOfEdge
    {Q : SSet.{u}} {x y : Q _⦋0⦌} (e : SSet.Edge x y) :
    internalHomVertexMap (Δ[1] : SSet.{u}) Q (internalHomVertexOfEdge e) =
      SSet.yonedaEquiv.symm e.edge := by
  unfold internalHomVertexOfEdge internalHomVertexMap
  rw [Equiv.symm_apply_apply]
  exact MonoidalClosed.uncurry'_curry' _

/-- An equivalence edge defines a vertex of the equivalence-edge internal Hom. -/
def equivalenceEdgeInternalHomVertexOfEdge
    {Q : SSet.{u}} {x y : Q _⦋0⦌} (e : SSet.Edge x y)
    (he : EdgeIsEquivalence e) : (equivalenceEdgeInternalHom Q) _⦋0⦌ := by
  refine ⟨internalHomVertexOfEdge e, ?_⟩
  unfold equivalenceEdgeInternalHom
  rw [mem_fullSubcomplexOnVertices_zero_iff]
  rw [internalHomVertexMap_internalHomVertexOfEdge]
  rw [Equiv.apply_symm_apply]
  let ec := SSet.Edge.castEndpoints e.src_eq e.tgt_eq e
  have hec : EdgeIsEquivalence ec := he.castEndpoints e.src_eq e.tgt_eq
  have heq : ec = SSet.Edge.mk' e.edge := by
    apply SSet.Edge.ext
    simp only [ec, SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
  simpa only [heq] using hec

/-- Every equivalence edge in a quasicategory extends to the free-living equivalence. -/
noncomputable def equivalenceIntervalExtensionOfEdgeIsEquivalence
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    {x y : Q _⦋0⦌} (e : SSet.Edge x y) (he : EdgeIsEquivalence e) :
    EquivalenceIntervalExtension e := by
  let E := equivalenceEdgeInternalHom Q
  let v : E _⦋0⦌ := equivalenceEdgeInternalHomVertexOfEdge e he
  let g : (Δ[0] : SSet.{u}) ⟶ E := SSet.yonedaEquiv.symm v
  let A : SSet.{u} := ⊥_ SSet.{u}
  let i : A ⟶ (Δ[0] : SSet.{u}) := initial.to _
  let f : A ⟶ (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q := initial.to _
  let p := equivalenceIntervalRestrictionToEquivalenceEdges Q
  let sq : CommSq f i p g := ⟨Subsingleton.elim _ _⟩
  have hp : (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}).rlp p :=
    intervalRestriction_mem_monomorphisms_rlp_of_specialLeftHornFillers Q
      (@hasAllSpecialLeftHornFillers_direct Q inferInstance)
  have hi : (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}) i := by
    change Mono i
    infer_instance
  have hLift : HasLiftingProperty i p := hp i hi
  letI : sq.HasLift := hLift.sq_hasLift sq
  let l : (Δ[0] : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q := sq.lift
  let w := SSet.yonedaEquiv l
  let F : CategoryTheory.nerve EquivalenceInterval.{u} ⟶ Q :=
    internalHomVertexMap (CategoryTheory.nerve EquivalenceInterval.{u}) Q w
  refine { map := F, restrict := ?_ }
  apply SSet.yonedaEquiv.injective
  rw [← internalHomVertexMap_precomp]
  have hfac := congrArg SSet.yonedaEquiv sq.fac_right
  change ((equivalenceIntervalRestrictionToEquivalenceEdges Q).app (op ⦋0⦌)) w = v at hfac
  have hval := congrArg Subtype.val hfac
  change (internalHomPrecomp equivalenceIntervalInclusion Q).app (op ⦋0⦌) w =
    internalHomVertexOfEdge e at hval
  rw [hval]
  rw [internalHomVertexMap_internalHomVertexOfEdge]

namespace MetrizableBoundedComplexes
namespace DrinfeldWord

local instance correctedQuotientComparison_quasicategory :
    SSet.Quasicategory correctedQuotientDGQCat.obj := correctedQuotientDGQCat.property

/-- The corrected quotient comparison inverts the complete generated marking. -/
theorem quotientComparison_invertsMarkedEdges :
    InvertsMarkedEdges (relativeNerveEdgeMarking relativeCategory)
      metrizableComplexNerveToCorrectedQuotientDG :=
  metrizableComplexNerveToCorrectedQuotientDG_invertsMarkedEdges

/-- The image of each generated weak edge has a chosen free-equivalence extension in the
corrected quotient. -/
noncomputable def quotientGeneratedWeakExtension
    (a : GeneratedWeakEquivalenceArrow) :
    EquivalenceIntervalExtension
      ((CategoryTheory.nerve.edgeMk a.hom).map
        metrizableComplexNerveToCorrectedQuotientDG) :=
  equivalenceIntervalExtensionOfEdgeIsEquivalence
    ((CategoryTheory.nerve.edgeMk a.hom).map
      metrizableComplexNerveToCorrectedQuotientDG)
    (metrizableComplexNerveToCorrectedQuotientDG_generatedIsEquivalence
      a.hom a.weak)

/-- Send every free-equivalence copy in the generated weak-arrow family to the chosen
extension in the corrected quotient. -/
noncomputable def quotientWeakEquivalenceCopiesMap :
    ∐ relativeCategory.weakEquivalenceFamily ⟶ correctedQuotientDGQCat.obj :=
  Sigma.desc fun a ↦ (quotientGeneratedWeakExtension a).map

/-- The two maps out of the generated weak-edge family agree. -/
theorem quotientWeakFamilyCompatibility :
    relativeCategory.weakIntervalsToNerve ≫
        metrizableComplexNerveToCorrectedQuotientDG =
      relativeCategory.weakIntervalsToEquivalences ≫
        quotientWeakEquivalenceCopiesMap := by
  apply Sigma.hom_ext
  intro a
  have hN : Sigma.ι relativeCategory.weakIntervalFamily a ≫
      relativeCategory.weakIntervalsToNerve =
      relativeCategory.weakArrowSimplex a :=
    Sigma.ι_desc (fun a ↦ relativeCategory.weakArrowSimplex a) a
  have hE : Sigma.ι relativeCategory.weakIntervalFamily a ≫
      relativeCategory.weakIntervalsToEquivalences =
      equivalenceIntervalInclusion ≫
        Sigma.ι relativeCategory.weakEquivalenceFamily a := by
    exact Sigma.ι_desc
      (fun a ↦ equivalenceIntervalInclusion ≫
        Sigma.ι relativeCategory.weakEquivalenceFamily a) a
  have hQ : Sigma.ι relativeCategory.weakEquivalenceFamily a ≫
      quotientWeakEquivalenceCopiesMap =
      (quotientGeneratedWeakExtension a).map :=
    Sigma.ι_desc (fun a ↦ (quotientGeneratedWeakExtension a).map) a
  have hW : relativeCategory.weakArrowSimplex a ≫
      metrizableComplexNerveToCorrectedQuotientDG =
      SSet.yonedaEquiv.symm
        ((CategoryTheory.nerve.edgeMk a.hom).map
          metrizableComplexNerveToCorrectedQuotientDG).edge := by
    apply SSet.yonedaEquiv.injective
    simp only [RelativeCategoryData.weakArrowSimplex,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, SSet.Edge.map_edge]
  calc
    Sigma.ι relativeCategory.weakIntervalFamily a ≫
        (relativeCategory.weakIntervalsToNerve ≫
          metrizableComplexNerveToCorrectedQuotientDG) =
      (Sigma.ι relativeCategory.weakIntervalFamily a ≫
        relativeCategory.weakIntervalsToNerve) ≫
          metrizableComplexNerveToCorrectedQuotientDG :=
      (Category.assoc _ _ _).symm
    _ = relativeCategory.weakArrowSimplex a ≫
        metrizableComplexNerveToCorrectedQuotientDG :=
      congrArg (fun t ↦ t ≫ metrizableComplexNerveToCorrectedQuotientDG) hN
    _ = SSet.yonedaEquiv.symm
        ((CategoryTheory.nerve.edgeMk a.hom).map
          metrizableComplexNerveToCorrectedQuotientDG).edge := hW
    _ = equivalenceIntervalInclusion ≫
        (quotientGeneratedWeakExtension a).map :=
      (quotientGeneratedWeakExtension a).restrict.symm
    _ = equivalenceIntervalInclusion ≫
        (Sigma.ι relativeCategory.weakEquivalenceFamily a ≫
          quotientWeakEquivalenceCopiesMap) :=
      congrArg (fun t ↦ equivalenceIntervalInclusion ≫ t) hQ.symm
    _ = (equivalenceIntervalInclusion ≫
          Sigma.ι relativeCategory.weakEquivalenceFamily a) ≫
        quotientWeakEquivalenceCopiesMap :=
      (Category.assoc _ _ _).symm
    _ = (Sigma.ι relativeCategory.weakIntervalFamily a ≫
          relativeCategory.weakIntervalsToEquivalences) ≫
        quotientWeakEquivalenceCopiesMap :=
      congrArg (fun t ↦ t ≫ quotientWeakEquivalenceCopiesMap) hE.symm
    _ = Sigma.ι relativeCategory.weakIntervalFamily a ≫
        (relativeCategory.weakIntervalsToEquivalences ≫
          quotientWeakEquivalenceCopiesMap) :=
      Category.assoc _ _ _

/-- The presentation-level comparison from the ordinary free-equivalence pushout to the
corrected quotient. -/
noncomputable def metrizableEquivalenceForcingPresentationToCorrectedQuotientDG :
    metrizableEquivalenceForcingPresentation ⟶ correctedQuotientDGQCat.obj :=
  pushout.desc metrizableComplexNerveToCorrectedQuotientDG
    quotientWeakEquivalenceCopiesMap quotientWeakFamilyCompatibility

/-- The presentation-level comparison forms the strict triangle with the ordinary nerve. -/
theorem metrizableEquivalenceForcingPresentationToCorrectedQuotientDG_triangle :
    relativeCategory.toEquivalenceForcingPresentation ≫
        metrizableEquivalenceForcingPresentationToCorrectedQuotientDG =
      metrizableComplexNerveToCorrectedQuotientDG := by
  exact pushout.inl_desc _ _ _

/-- Extend the presentation comparison across its inner-fibrant replacement. -/
noncomputable def metrizableEquivalenceForcingToCorrectedQuotientDG :
    metrizableEquivalenceForcingQCat.obj ⟶ correctedQuotientDGQCat.obj :=
  Classical.choose (exists_extension_of_innerAnodyne
    (relativeCategory.toEquivalenceForcingQCat_innerAnodyne)
    metrizableEquivalenceForcingPresentationToCorrectedQuotientDG)

/-- The fibrant-replacement comparison restricts to the presentation comparison. -/
theorem metrizableEquivalenceForcingToCorrectedQuotientDG_restrict :
    relativeCategory.toEquivalenceForcingQCat ≫
        metrizableEquivalenceForcingToCorrectedQuotientDG =
      metrizableEquivalenceForcingPresentationToCorrectedQuotientDG :=
  Classical.choose_spec (exists_extension_of_innerAnodyne
    (relativeCategory.toEquivalenceForcingQCat_innerAnodyne)
    metrizableEquivalenceForcingPresentationToCorrectedQuotientDG)

/-- The ordinary localization comparison to the corrected quotient has a strict source
triangle. -/
theorem metrizableEquivalenceForcingToCorrectedQuotientDG_triangle :
    metrizableEquivalenceForcingMap ≫
        metrizableEquivalenceForcingToCorrectedQuotientDG =
      metrizableComplexNerveToCorrectedQuotientDG := by
  change (relativeCategory.toEquivalenceForcingPresentation ≫
      relativeCategory.toEquivalenceForcingQCat) ≫
        metrizableEquivalenceForcingToCorrectedQuotientDG = _
  rw [Category.assoc,
    metrizableEquivalenceForcingToCorrectedQuotientDG_restrict,
    metrizableEquivalenceForcingPresentationToCorrectedQuotientDG_triangle]

/-- Bundle the comparison as a map of quasicategories. -/
def metrizableEquivalenceForcingToCorrectedQuotientDGQCatMap :
    metrizableEquivalenceForcingQCat ⟶ correctedQuotientDGQCat :=
  ObjectProperty.homMk metrizableEquivalenceForcingToCorrectedQuotientDG

end DrinfeldWord
end MetrizableBoundedComplexes
end LeanLCAExactChallenge.Infinity
