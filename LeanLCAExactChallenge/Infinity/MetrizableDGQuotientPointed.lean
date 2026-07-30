/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EnrichedMappingCylinder
import LeanLCAExactChallenge.Infinity.CoherentNerveHomotopyInverse
import LeanLCAExactChallenge.Infinity.Limits
import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceCoherentInverse
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientZeroRepresentability
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientSimplicialCategory

/-! # Pointedness of the corrected Drinfeld quotient -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite Simplicial SimplicialObject.Truncated SimplexCategory.Truncated
  QuotientDoldKanMonoidal
open scoped MonoidalCategory Bicategory ZeroObject

local instance correctedQuotientPointedHomCategory
    (X Y : SSet.QCat.{1}) : Category (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

abbrev internalHomToTerminalTruncated (Q : SSet.QCat.{1}) :
    SSet.Truncated.{1} 2 :=
  (SSet.truncation 2).obj ((ihom Q.obj).obj terminalQCat.obj)

@[implicit_reducible]
noncomputable def internalHomToTerminal_uniqueVertex (Q : SSet.QCat.{1}) :
    Unique ((internalHomToTerminalTruncated Q) _⦋0⦌₂) := by
  change Unique (((ihom Q.obj).obj terminalQCat.obj) _⦋0⦌)
  refine ⟨⟨(SSet.unitHomEquiv ((ihom Q.obj).obj terminalQCat.obj))
      (CategoryTheory.MonoidalClosed.curry' (terminal.from Q.obj))⟩, ?_⟩
  intro x
  apply EnrichedMappingCylinder.internalHomVertexMap_injective
  exact terminalIsTerminal.hom_ext _ _

@[implicit_reducible]
noncomputable def internalHomToTerminal_subsingletonEdges (Q : SSet.QCat.{1}) :
    Subsingleton ((internalHomToTerminalTruncated Q) _⦋1⦌₂) := by
  change Subsingleton (((ihom Q.obj).obj terminalQCat.obj) _⦋1⦌)
  refine ⟨fun a b ↦ ?_⟩
  apply SSet.yonedaEquiv.symm.injective
  apply CategoryTheory.MonoidalClosed.uncurry_injective
  exact terminalIsTerminal.hom_ext _ _

@[implicit_reducible]
noncomputable def qcatTwoCellToTerminal_subsingleton
    (Q : SSet.QCat.{1}) (f g : Q ⟶ terminalQCat) : Subsingleton (f ⟶ g) := by
  letI := internalHomToTerminal_uniqueVertex Q
  letI := internalHomToTerminal_subsingletonEdges Q
  refine ⟨fun a b ↦ ?_⟩
  apply CategoryTheory.CatEnrichedOrdinary.Hom.ext
  exact (SSet.Truncated.HomotopyCategory.subsingleton_hom
    (internalHomToTerminalTruncated Q) _ _).elim _ _

private theorem quotientModule_subsingleton_of_isZero
    (M : ModuleCat.{1} QuotientCoefficientRing) (hM : IsZero M) :
    Subsingleton M := by
  refine ⟨fun x y ↦ ?_⟩
  have hid : (𝟙 M) = 0 := hM.eq_of_src _ _
  have hx := ConcreteCategory.congr_hom hid x
  have hy := ConcreteCategory.congr_hom hid y
  have hx0 : x = 0 := by
    rw [ModuleCat.id_apply] at hx
    change x = (0 : M →ₗ[QuotientCoefficientRing] M) x at hx
    simpa using hx
  have hy0 : y = 0 := by
    rw [ModuleCat.id_apply] at hy
    change y = (0 : M →ₗ[QuotientCoefficientRing] M) y at hy
    simpa using hy
  exact hx0.trans hy0.symm

local instance quotientTruncLEPreservesZeroMorphisms :
    (ComplexShape.embeddingDownNat.truncLE'Functor
      (ModuleCat.{1} QuotientCoefficientRing)).PreservesZeroMorphisms where
  map_zero K L := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (HomologicalComplex.truncLE'Map (0 : K ⟶ L)
      ComplexShape.embeddingDownNat).f n = 0
    by_cases hb : ComplexShape.embeddingDownNat.BoundaryLE n
    · rw [HomologicalComplex.truncLE'Map_f_eq_cyclesMap (0 : K ⟶ L)
        ComplexShape.embeddingDownNat hb rfl, HomologicalComplex.cyclesMap_zero]
      simp
    · rw [HomologicalComplex.truncLE'Map_f_eq (0 : K ⟶ L)
        ComplexShape.embeddingDownNat hb rfl]
      simp

/-- The underlying simplicial set of a zero simplicial module is terminal. -/
noncomputable def quotientCoefficientSimplicialForget_isTerminal_of_isZero
    (M : CorrectedQuotientDGSimp) (hM : IsZero M) :
    IsTerminal (quotientCoefficientSimplicialForget.obj M) := by
  refine IsTerminal.ofUniqueHom (fun X ↦ ?_) (fun X f ↦ ?_)
  · exact
      { app := fun U ↦ ↾fun _ ↦ (0 : M.obj U)
        naturality := fun U V f ↦ by
          ext x
          let hV : IsZero (M.obj V) :=
            (((evaluation SimplexCategoryᵒᵖ
              (ModuleCat.{1} QuotientCoefficientRing)).obj V).map_isZero hM)
          exact (quotientModule_subsingleton_of_isZero _ hV).elim _ _ }
  · ext U x
    let hU : IsZero (M.obj U) :=
      (((evaluation SimplexCategoryᵒᵖ
        (ModuleCat.{1} QuotientCoefficientRing)).obj U).map_isZero hM)
    exact (quotientModule_subsingleton_of_isZero _ hU).elim _ _

/-- Mapping out of the geometric zero object is a terminal simplicial set. -/
noncomputable def correctedQuotientDGMappingSSet_fromZero_isTerminal
    (K : ComplexCategory) :
    IsTerminal (correctedQuotientDGMappingSSet (0 : ComplexCategory) K) := by
  let hcochain : IsZero
      (quotientDGEnrichedHom (Opposite.op K) quotientDGZeroObject) :=
    quotientDGEnrichedHom_toZero_isZero (Opposite.op K)
  let hchain : IsZero
      (quotientDGChainEnrichedHom (Opposite.op K) quotientDGZeroObject) :=
    (ComplexShape.embeddingDownNat.truncLE'Functor
      (ModuleCat.{1} QuotientCoefficientRing)).map_isZero hcochain
  let hsimp : IsZero
      (quotientModuleDoldKanEquivalence.inverse.obj
        (quotientDGChainEnrichedHom (Opposite.op K) quotientDGZeroObject)) :=
    quotientModuleDoldKanEquivalence.inverse.map_isZero hchain
  exact quotientCoefficientSimplicialForget_isTerminal_of_isZero _ hsimp

/-- Mapping into the geometric zero object is a terminal simplicial set. -/
noncomputable def correctedQuotientDGMappingSSet_toZero_isTerminal
    (K : ComplexCategory) :
    IsTerminal (correctedQuotientDGMappingSSet K (0 : ComplexCategory)) := by
  let hcochain : IsZero
      (quotientDGEnrichedHom quotientDGZeroObject (Opposite.op K)) :=
    quotientDGEnrichedHom_fromZero_isZero (Opposite.op K)
  let hchain : IsZero
      (quotientDGChainEnrichedHom quotientDGZeroObject (Opposite.op K)) :=
    (ComplexShape.embeddingDownNat.truncLE'Functor
      (ModuleCat.{1} QuotientCoefficientRing)).map_isZero hcochain
  let hsimp : IsZero
      (quotientModuleDoldKanEquivalence.inverse.obj
        (quotientDGChainEnrichedHom quotientDGZeroObject (Opposite.op K))) :=
    quotientModuleDoldKanEquivalence.inverse.map_isZero hchain
  exact quotientCoefficientSimplicialForget_isTerminal_of_isZero _ hsimp

/-- Every enriched Hom out of the corrected quotient zero object is terminal. -/
noncomputable def correctedQuotientDG_enrichedHom_fromZero_isTerminal
    (K : CorrectedQuotientDGSimplicialCategory) :
    IsTerminal
      (correctedQuotientDGObject (0 : ComplexCategory) ⟶[SSet] K) := by
  change IsTerminal (correctedQuotientDGMappingSSet (0 : ComplexCategory)
    (show CorrectedQuotientDGSimplicialModuleCategory from K.unop).unop)
  exact correctedQuotientDGMappingSSet_fromZero_isTerminal _

/-- Every enriched Hom into the corrected quotient zero object is terminal. -/
noncomputable def correctedQuotientDG_enrichedHom_toZero_isTerminal
    (K : CorrectedQuotientDGSimplicialCategory) :
    IsTerminal
      (K ⟶[SSet] correctedQuotientDGObject (0 : ComplexCategory)) := by
  change IsTerminal (correctedQuotientDGMappingSSet
    (show CorrectedQuotientDGSimplicialModuleCategory from K.unop).unop
    (0 : ComplexCategory))
  exact correctedQuotientDGMappingSSet_toZero_isTerminal _

/-- The constant enriched endofunctor at the corrected quotient zero object. -/
noncomputable def correctedQuotientDGConstantZeroEnrichedFunctor :
    EnrichedFunctor SSet CorrectedQuotientDGSimplicialCategory
      CorrectedQuotientDGSimplicialCategory where
  obj _ := correctedQuotientDGObject (0 : ComplexCategory)
  map X Y := (correctedQuotientDG_enrichedHom_fromZero_isTerminal
    (correctedQuotientDGObject (0 : ComplexCategory))).from (X ⟶[SSet] Y)
  map_id _ :=
    (correctedQuotientDG_enrichedHom_fromZero_isTerminal
      (correctedQuotientDGObject (0 : ComplexCategory))).hom_ext _ _
  map_comp _ _ _ :=
    (correctedQuotientDG_enrichedHom_fromZero_isTerminal
      (correctedQuotientDGObject (0 : ComplexCategory))).hom_ext _ _

/-- The unique strict enriched transformation from the constant zero functor to the identity. -/
noncomputable def correctedQuotientDGZeroToIdentityTransformation :
    SSetUnitGradedNatTrans correctedQuotientDGConstantZeroEnrichedFunctor
      (EnrichedFunctor.id SSet CorrectedQuotientDGSimplicialCategory) where
  app X := (correctedQuotientDG_enrichedHom_fromZero_isTerminal X).from
    SSetCentralUnit.1
  naturality _ Y :=
    (correctedQuotientDG_enrichedHom_fromZero_isTerminal Y).hom_ext _ _

/-- The unique strict enriched transformation from the identity to the constant zero functor. -/
noncomputable def correctedQuotientDGIdentityToZeroTransformation :
    SSetUnitGradedNatTrans
      (EnrichedFunctor.id SSet CorrectedQuotientDGSimplicialCategory)
      correctedQuotientDGConstantZeroEnrichedFunctor where
  app X := (correctedQuotientDG_enrichedHom_toZero_isTerminal X).from
    SSetCentralUnit.1
  naturality X _ :=
    (correctedQuotientDG_enrichedHom_toZero_isTerminal X).hom_ext _ _

/-- The zero object represented as a vertex of the corrected quotient coherent nerve. -/
def correctedQuotientDGZeroVertex :
    correctedQuotientDGQCat.obj _⦋0⦌ :=
  CoherentNerveHomotopyInverse.TriangleData.coherentVertex
    CorrectedQuotientDGSimplicialCategory
    (correctedQuotientDGObject (0 : ComplexCategory))

/-- The selected zero-object map from the terminal quasicategory. -/
def correctedQuotientDGZeroObjectMap :
    terminalQCat ⟶ correctedQuotientDGQCat :=
  ObjectProperty.homMk (SSet.const correctedQuotientDGZeroVertex)

/-- The coherent nerve map of the enriched identity functor is the identity. -/
theorem correctedQuotientDG_simplicialNerveMap_id :
    simplicialNerveMap
        (EnrichedFunctor.id SSet CorrectedQuotientDGSimplicialCategory) =
      𝟙 correctedQuotientDGQCat.obj := by
  ext U σ
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  simp [simplicialNerveMap]

/-- The coherent nerve map of the constant-zero enriched functor is the constant zero map. -/
theorem correctedQuotientDG_simplicialNerveMap_constantZero :
    simplicialNerveMap correctedQuotientDGConstantZeroEnrichedFunctor =
      SSet.const correctedQuotientDGZeroVertex := by
  ext U σ
  let L := EnrichedFunctor.comp SSet σ
    correctedQuotientDGConstantZeroEnrichedFunctor
  let R := (SSet.const correctedQuotientDGZeroVertex).app U σ
  change L = R
  have hobj : ∀ i, L.obj i = R.obj i := fun _ ↦ rfl
  apply EnrichedFunctor.ext SSet hobj
  intro X Y
  exact (correctedQuotientDG_enrichedHom_fromZero_isTerminal
    (correctedQuotientDGObject (0 : ComplexCategory))).hom_ext _ _

theorem correctedQuotientDG_coherentNerveQCatMap_id :
    EnrichedMappingCylinder.coherentNerveQCatMap
        correctedQuotientDGHomotopyCoherentNerve_quasicategory
        correctedQuotientDGHomotopyCoherentNerve_quasicategory
        (EnrichedFunctor.id SSet CorrectedQuotientDGSimplicialCategory) =
      𝟙 correctedQuotientDGQCat := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  exact correctedQuotientDG_simplicialNerveMap_id

theorem correctedQuotientDG_coherentNerveQCatMap_constantZero :
    EnrichedMappingCylinder.coherentNerveQCatMap
        correctedQuotientDGHomotopyCoherentNerve_quasicategory
        correctedQuotientDGHomotopyCoherentNerve_quasicategory
        correctedQuotientDGConstantZeroEnrichedFunctor =
      toTerminalQCat correctedQuotientDGQCat ≫ correctedQuotientDGZeroObjectMap := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  change simplicialNerveMap correctedQuotientDGConstantZeroEnrichedFunctor =
    terminal.from correctedQuotientDGQCat.obj ≫
      SSet.const correctedQuotientDGZeroVertex
  rw [SSet.comp_const]
  exact correctedQuotientDG_simplicialNerveMap_constantZero

theorem correctedQuotientDGZeroObjectMap_comp_toTerminal :
    correctedQuotientDGZeroObjectMap ≫
        toTerminalQCat correctedQuotientDGQCat =
      𝟙 terminalQCat := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  exact terminalIsTerminal.hom_ext _ _

/-- The counit-shaped QCat `2`-cell from the constant zero map to the identity. -/
noncomputable def correctedQuotientDGZeroToIdentityTwoCell :
    (toTerminalQCat correctedQuotientDGQCat ≫
        correctedQuotientDGZeroObjectMap) ⟶
      (𝟙 correctedQuotientDGQCat) := by
  let c := EnrichedMappingCylinder.coherentNerveTwoCell
    correctedQuotientDGConstantZeroEnrichedFunctor
    (EnrichedFunctor.id SSet CorrectedQuotientDGSimplicialCategory)
    correctedQuotientDGZeroToIdentityTransformation
    correctedQuotientDGHomotopyCoherentNerve_quasicategory
    correctedQuotientDGHomotopyCoherentNerve_quasicategory
  exact eqToHom correctedQuotientDG_coherentNerveQCatMap_constantZero.symm ≫
    c ≫ eqToHom correctedQuotientDG_coherentNerveQCatMap_id

/-- The unit-shaped QCat `2`-cell from the identity to the constant zero map. -/
noncomputable def correctedQuotientDGIdentityToZeroTwoCell :
    (𝟙 correctedQuotientDGQCat) ⟶
      (toTerminalQCat correctedQuotientDGQCat ≫
        correctedQuotientDGZeroObjectMap) := by
  let c := EnrichedMappingCylinder.coherentNerveTwoCell
    (EnrichedFunctor.id SSet CorrectedQuotientDGSimplicialCategory)
    correctedQuotientDGConstantZeroEnrichedFunctor
    correctedQuotientDGIdentityToZeroTransformation
    correctedQuotientDGHomotopyCoherentNerve_quasicategory
    correctedQuotientDGHomotopyCoherentNerve_quasicategory
  exact eqToHom correctedQuotientDG_coherentNerveQCatMap_id.symm ≫
    c ≫ eqToHom correctedQuotientDG_coherentNerveQCatMap_constantZero


/-- Every coherent edge from the corrected quotient zero vertex to itself is equal. -/
lemma correctedQuotientDGZeroEdge_obj_eq
    (e : SSet.Edge correctedQuotientDGZeroVertex correctedQuotientDGZeroVertex)
    (i : CategoryTheory.SimplicialThickening (ULift.{1, 0} (Fin 2))) :
    e.edge.obj i = correctedQuotientDGObject (0 : ComplexCategory) := by
  rcases i with ⟨⟨i⟩⟩
  fin_cases i
  · let z : CategoryTheory.SimplicialThickening (ULift.{1, 0} (Fin 1)) :=
      CategoryTheory.SimplicialThickening.mk (ULift.up 0)
    exact congrArg (fun F ↦ F.obj z) e.src_eq
  · let z : CategoryTheory.SimplicialThickening (ULift.{1, 0} (Fin 1)) :=
      CategoryTheory.SimplicialThickening.mk (ULift.up 0)
    exact congrArg (fun F ↦ F.obj z) e.tgt_eq

@[implicit_reducible]
noncomputable def correctedQuotientDGZeroEdge_subsingleton :
    Subsingleton
      (SSet.Edge correctedQuotientDGZeroVertex correctedQuotientDGZeroVertex) := by
  constructor
  intro a b
  apply SSet.Edge.ext
  let hobj : ∀ i, a.edge.obj i = b.edge.obj i := fun i ↦
    (correctedQuotientDGZeroEdge_obj_eq a i).trans
      (correctedQuotientDGZeroEdge_obj_eq b i).symm
  refine EnrichedFunctor.ext SSet hobj ?_
  intro i j
  let Z := correctedQuotientDGObject (0 : ComplexCategory)
  have hi : b.edge.obj i = Z := correctedQuotientDGZeroEdge_obj_eq b i
  have hj : b.edge.obj j = Z := correctedQuotientDGZeroEdge_obj_eq b j
  let e : (Z ⟶[SSet] Z) ≅ (b.edge.obj i ⟶[SSet] b.edge.obj j) :=
    eqToIso (congrArg₂
      (fun (X Y : CorrectedQuotientDGSimplicialCategory) ↦ X ⟶[SSet] Y)
      hi.symm hj.symm)
  exact ((correctedQuotientDG_enrichedHom_fromZero_isTerminal Z).ofIso e).hom_ext _ _

/-- The selected vertex of the terminal simplicial set. -/
def correctedQuotientDGTerminalVertex : terminalQCat.obj _⦋0⦌ :=
  SSet.unitHomEquiv terminalQCat.obj
    (terminalIsTerminal.from (𝟙_ SSet.{1}))

@[implicit_reducible]
noncomputable def correctedQuotientDGTerminalEvaluation_isIso :
    IsIso (internalHomEvaluationAtVertex terminalQCat.obj
      correctedQuotientDGQCat.obj correctedQuotientDGTerminalVertex) := by
  let p := (SSet.unitHomEquiv terminalQCat.obj).symm
    correctedQuotientDGTerminalVertex
  letI : IsIso p := isIso_of_isTerminal
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{1}))
    terminalIsTerminal p
  letI : IsIso (internalHomPrecomp p correctedQuotientDGQCat.obj) := by
    refine ⟨⟨internalHomPrecomp (inv p) correctedQuotientDGQCat.obj, ?_, ?_⟩⟩
    · rw [internalHomPrecomp_comp, IsIso.inv_hom_id]
      simp [internalHomPrecomp]
    · rw [internalHomPrecomp_comp, IsIso.hom_inv_id]
      simp [internalHomPrecomp]
  rw [show internalHomEvaluationAtVertex terminalQCat.obj correctedQuotientDGQCat.obj
      correctedQuotientDGTerminalVertex =
      internalHomPrecomp p correctedQuotientDGQCat.obj ≫
        (CategoryTheory.MonoidalClosed.unitIsoSelf
          (C := SSet.{1}) (X := correctedQuotientDGQCat.obj)).hom by
    ext U x
    rfl]
  infer_instance

/-- Evaluation of the zero-object map at the terminal vertex is the zero vertex. -/
theorem correctedQuotientDGZeroObjectMap_vertex :
    mapVertex correctedQuotientDGZeroObjectMap correctedQuotientDGTerminalVertex =
      correctedQuotientDGZeroVertex := by
  simp [mapVertex, correctedQuotientDGZeroObjectMap, SSet.const]

/-- Internal-Hom edges from the zero map to itself are unique. -/
@[implicit_reducible]
noncomputable def correctedQuotientDGZeroMapInternalHomEdge_subsingleton :
    Subsingleton
      (SSet.Edge
        (SSet.unitHomEquiv
          ((ihom terminalQCat.obj).obj correctedQuotientDGQCat.obj)
          (CategoryTheory.MonoidalClosed.curry' correctedQuotientDGZeroObjectMap.hom))
        (SSet.unitHomEquiv
          ((ihom terminalQCat.obj).obj correctedQuotientDGQCat.obj)
          (CategoryTheory.MonoidalClosed.curry' correctedQuotientDGZeroObjectMap.hom))) := by
  constructor
  intro a b
  letI := correctedQuotientDGZeroEdge_subsingleton
  letI := correctedQuotientDGTerminalEvaluation_isIso
  apply SSet.Edge.ext
  apply (ConcreteCategory.bijective_of_isIso
    ((internalHomEvaluationAtVertex terminalQCat.obj correctedQuotientDGQCat.obj
      correctedQuotientDGTerminalVertex).app (op ⦋1⦌))).1
  let ea := internalHomEdgeApp a correctedQuotientDGTerminalVertex
  let eb := internalHomEdgeApp b correctedQuotientDGTerminalVertex
  let ea0 : SSet.Edge correctedQuotientDGZeroVertex correctedQuotientDGZeroVertex :=
    SSet.Edge.castEndpoints correctedQuotientDGZeroObjectMap_vertex.symm
      correctedQuotientDGZeroObjectMap_vertex.symm ea
  let eb0 : SSet.Edge correctedQuotientDGZeroVertex correctedQuotientDGZeroVertex :=
    SSet.Edge.castEndpoints correctedQuotientDGZeroObjectMap_vertex.symm
      correctedQuotientDGZeroObjectMap_vertex.symm eb
  have h : ea0 = eb0 := Subsingleton.elim _ _
  simpa only [ea0, eb0, SSet.Edge.castEndpoints_edge, ea, eb,
    internalHomEdgeApp, SSet.Edge.map_edge] using congrArg SSet.Edge.edge h


/-- The internal-Hom vertex represented by the selected zero-object map. -/
def correctedQuotientDGZeroMapInternalHomVertex :
    ((ihom terminalQCat.obj).obj correctedQuotientDGQCat.obj) _⦋0⦌ :=
  SSet.unitHomEquiv _
    (CategoryTheory.MonoidalClosed.curry' correctedQuotientDGZeroObjectMap.hom)

lemma correctedQuotientDG_homEquiv_zeroObjectMap :
    CategoryTheory.CatEnrichedOrdinary.homEquiv correctedQuotientDGZeroObjectMap =
      homotopyObject correctedQuotientDGZeroMapInternalHomVertex := by
  rfl

@[implicit_reducible]
noncomputable def correctedQuotientDGZeroObjectTwoCell_subsingleton :
    Subsingleton
      (correctedQuotientDGZeroObjectMap ⟶ correctedQuotientDGZeroObjectMap) := by
  constructor
  intro a b
  apply CategoryTheory.CatEnrichedOrdinary.Hom.ext
  letI : SSet.Quasicategory
      ((ihom terminalQCat.obj).obj correctedQuotientDGQCat.obj) :=
    @quasicategory_ihom terminalQCat.obj correctedQuotientDGQCat.obj
      correctedQuotientDGQCat.property
  let V := (SSet.truncation 2).obj
    ((ihom terminalQCat.obj).obj correctedQuotientDGQCat.obj)
  letI : V.Quasicategory₂ := inferInstance
  let v : V _⦋0⦌₂ := correctedQuotientDGZeroMapInternalHomVertex
  let h : CategoryTheory.CatEnrichedOrdinary.homEquiv
        correctedQuotientDGZeroObjectMap =
      SSet.Truncated.HomotopyCategory.mk v :=
    correctedQuotientDG_homEquiv_zeroObjectMap
  let aa : SSet.Truncated.HomotopyCategory.mk v ⟶
      SSet.Truncated.HomotopyCategory.mk v :=
    eqToHom h.symm ≫ CategoryTheory.CatEnrichedOrdinary.Hom.base a ≫ eqToHom h
  let bb : SSet.Truncated.HomotopyCategory.mk v ⟶
      SSet.Truncated.HomotopyCategory.mk v :=
    eqToHom h.symm ≫ CategoryTheory.CatEnrichedOrdinary.Hom.base b ≫ eqToHom h
  obtain ⟨ea, hea⟩ := homotopyCategory_homMk_surjective_of_quasicategory
    (V := V) (x := v) (y := v) aa
  obtain ⟨eb, heb⟩ := homotopyCategory_homMk_surjective_of_quasicategory
    (V := V) (x := v) (y := v) bb
  have hab : aa = bb := by
    rw [← hea, ← heb]
    congr 1
    exact (correctedQuotientDGZeroMapInternalHomEdge_subsingleton).elim ea eb
  apply (cancel_epi (eqToHom h.symm)).1
  apply (cancel_mono (eqToHom h)).1
  simpa only [Category.assoc, aa, bb] using hab


/-- The selected zero object is left adjoint to the unique map to the terminal quasicategory. -/
noncomputable def correctedQuotientDGInitialAdjunction :
    Bicategory.Adjunction correctedQuotientDGZeroObjectMap
      (toTerminalQCat correctedQuotientDGQCat) where
  unit := eqToHom correctedQuotientDGZeroObjectMap_comp_toTerminal.symm
  counit := correctedQuotientDGZeroToIdentityTwoCell
  left_triangle := by
    exact correctedQuotientDGZeroObjectTwoCell_subsingleton.elim _ _
  right_triangle := by
    exact (qcatTwoCellToTerminal_subsingleton correctedQuotientDGQCat _ _).elim _ _

/-- The unique map to the terminal quasicategory is left adjoint to the selected zero object. -/
noncomputable def correctedQuotientDGTerminalAdjunction :
    Bicategory.Adjunction (toTerminalQCat correctedQuotientDGQCat)
      correctedQuotientDGZeroObjectMap where
  unit := correctedQuotientDGIdentityToZeroTwoCell
  counit := eqToHom correctedQuotientDGZeroObjectMap_comp_toTerminal
  left_triangle := by
    exact (qcatTwoCellToTerminal_subsingleton correctedQuotientDGQCat _ _).elim _ _
  right_triangle := by
    exact correctedQuotientDGZeroObjectTwoCell_subsingleton.elim _ _

/-- The corrected Drinfeld quotient coherent nerve has a chosen zero object. -/
noncomputable def correctedQuotientDGPointedStructure :
    PointedStructure correctedQuotientDGQCat where
  zeroObject := correctedQuotientDGZeroObjectMap
  initialAdjunction := correctedQuotientDGInitialAdjunction
  terminalAdjunction := correctedQuotientDGTerminalAdjunction

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes.DrinfeldWord
