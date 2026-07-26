/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.ScratchCoherentNerveHomotopyInverse

/-!
# Corrected weak equivalences in the corrected quotient coherent nerve

The explicit quotient homotopy inverse is transported through smart truncation and Dold--Kan,
then recognized by the generic coherent-nerve homotopy-inverse criterion.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial
open QuotientDoldKanMonoidal
open CoherentNerveHomotopyInverse

/-- The sum of two closed quotient elements is closed. -/
theorem quotientAdd_closed (K L : ComplexCategory)
    (x y : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential K L 0).hom y = 0) :
    (quotientTotalDifferential K L 0).hom (x + y) = 0 := by
  rw [map_add, hx, hy, add_zero]

/-- Smart truncation preserves addition of closed degree-zero quotient elements. -/
theorem quotientDGChainZeroOfClosed_add (K L : ComplexCategory)
    (x y : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential K L 0).hom y = 0) :
    quotientDGChainZeroOfClosed K L x hx +
        quotientDGChainZeroOfClosed K L y hy =
      quotientDGChainZeroOfClosed K L (x + y)
        (quotientAdd_closed K L x y hx hy) := by
  let H := quotientCoefficientCochainComplex K L
  let r := H.truncLE'ToRestriction ComplexShape.embeddingDownNat
  have hmono : Mono (r.f 0) := by
    have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
      simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
        (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
    rw [quotientTruncLEToRestriction_f_zero H hb]
    infer_instance
  apply (ModuleCat.mono_iff_injective (r.f 0)).mp hmono
  rw [map_add]
  rw [quotientDGChainZeroOfClosed_toRestriction,
    quotientDGChainZeroOfClosed_toRestriction,
    quotientDGChainZeroOfClosed_toRestriction]
  rfl

/-- The boundary of a degree-minus-one quotient element, displayed in degree zero. -/
def quotientDGHomotopyBoundary (K L : ComplexCategory)
    (h : quotientGradedModule K L (-1)) : quotientGradedModule K L 0 :=
  (quotientTotalDifferential K L (-1)).hom h

/-- The displayed homotopy boundary is closed. -/
theorem quotientDGHomotopyBoundary_closed (K L : ComplexCategory)
    (h : quotientGradedModule K L (-1)) :
    (quotientTotalDifferential K L 0).hom
      (quotientDGHomotopyBoundary K L h) = 0 := by
  change (quotientTotalDifferential K L 0).hom
      ((quotientTotalDifferential K L (-1)).hom h) = 0
  exact quotientDGChainOneBoundary_closed K L h

/-- The natural target of a degree-minus-one quotient homotopy is closed. -/
theorem quotientDGHomotopyTarget_closed (K L : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (h : quotientGradedModule K L (-1)) :
    (quotientTotalDifferential K L 0).hom
      (x + quotientDGHomotopyBoundary K L h) = 0 :=
  quotientAdd_closed K L x _ hx (quotientDGHomotopyBoundary_closed K L h)

/-- The explicit Dold--Kan edge associated to a quotient homotopy. -/
def quotientDGHomotopyEdge (K L : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (h : quotientGradedModule K L (-1)) :
    SSet.Edge
      (correctedQuotientDGMappingVertexOfClosed K L x hx)
      (correctedQuotientDGMappingVertexOfClosed K L
        (x + quotientDGHomotopyBoundary K L h)
        (quotientDGHomotopyTarget_closed K L x hx h)) :=
  SSet.Edge.mk
    (quotientDoldKanGammaOneSimplex
      (quotientDGMappingChain K L)
      (quotientDGChainZeroOfClosed K L x hx)
      (quotientDGChainOneOfDegreeNegOne K L h))
    (by
      change ((quotientModuleDoldKanEquivalence.inverse.obj
        (quotientDGMappingChain K L)).δ 1).hom
          (quotientDoldKanGammaOneSimplex
            (quotientDGMappingChain K L)
            (quotientDGChainZeroOfClosed K L x hx)
            (quotientDGChainOneOfDegreeNegOne K L h)) =
        (quotientModuleDoldKanInverseZeroIso
          (quotientDGMappingChain K L)).hom.hom
            (quotientDGChainZeroOfClosed K L x hx)
      rw [quotientDoldKanGammaOneSimplex_delta_one]
      rfl)
    (by
      change ((quotientModuleDoldKanEquivalence.inverse.obj
        (quotientDGMappingChain K L)).δ 0).hom
          (quotientDoldKanGammaOneSimplex
            (quotientDGMappingChain K L)
            (quotientDGChainZeroOfClosed K L x hx)
            (quotientDGChainOneOfDegreeNegOne K L h)) =
        (quotientModuleDoldKanInverseZeroIso
          (quotientDGMappingChain K L)).hom.hom
            (quotientDGChainZeroOfClosed K L
              (x + quotientDGHomotopyBoundary K L h)
              (quotientDGHomotopyTarget_closed K L x hx h))
      rw [quotientDoldKanGammaOneSimplex_delta_zero]
      rw [quotientDGChainOneOfDegreeNegOne_boundary]
      rw [quotientDGChainZeroOfClosed_add]
      rfl)

/-- Reindex the natural homotopy edge along an explicitly identified target. -/
def quotientDGHomotopyEdgeTo (K L : ComplexCategory)
    (x y : quotientGradedModule K L 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential K L 0).hom y = 0)
    (h : quotientGradedModule K L (-1))
    (htarget : x + quotientDGHomotopyBoundary K L h = y) :
    SSet.Edge
      (correctedQuotientDGMappingVertexOfClosed K L x hx)
      (correctedQuotientDGMappingVertexOfClosed K L y hy) := by
  let e := quotientDGHomotopyEdge K L x hx h
  have htgt : correctedQuotientDGMappingVertexOfClosed K L y hy =
      correctedQuotientDGMappingVertexOfClosed K L
        (x + quotientDGHomotopyBoundary K L h)
        (quotientDGHomotopyTarget_closed K L x hx h) := by
    subst y
    rfl
  exact SSet.Edge.castEndpoints rfl htgt e

/-- The zero-word image of an ordinary bounded morphism is closed. -/
theorem quotientOriginalMorphismElement_closed {K L : ComplexCategory} (f : K ⟶ L) :
    (quotientTotalDifferential K L 0).hom
      (quotientOriginalMorphismElement f) = 0 := by
  change (quotientTotalDifferential K L 0).hom
    (quotientOriginalCochainElement
      (CochainComplex.HomComplex.Cochain.ofHom f.hom)) = 0
  rw [quotientOriginalCochainElement_d]
  change quotientOriginalCochainElement
      (CochainComplex.HomComplex.δ 0 1
        (CochainComplex.HomComplex.Cochain.ofHom f.hom)) = 0
  rw [CochainComplex.HomComplex.δ_ofHom]
  exact quotientOriginalCochainElement_zero K L 1

/-- The left homotopy starts at the identity and ends at `f ≫ g`. -/
theorem correctedWeakEquivalenceLeftHomotopy_target
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    quotientIdentityElement K +
        quotientDGHomotopyBoundary K K
          (correctedWeakEquivalenceLeftHomotopyElement f hf) =
      quotientCompose (quotientOriginalMorphismElement f)
        (correctedWeakEquivalenceInverseElement f hf) := by
  unfold quotientDGHomotopyBoundary
  rw [correctedWeakEquivalenceLeftHomotopyElement_d]
  have hcast := quotientGradedModule_cast_eq K K
    (show (0 : ℤ) + 0 = 0 by omega) rfl
    (quotientCompose (quotientOriginalMorphismElement f)
      (correctedWeakEquivalenceInverseElement f hf))
  rw [hcast]
  simp only [eqToHom_refl]
  abel

/-- The right homotopy starts at the identity and ends at `g ≫ f`. -/
theorem correctedWeakEquivalenceRightHomotopy_target
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    quotientIdentityElement L +
        quotientDGHomotopyBoundary L L
          (correctedWeakEquivalenceRightHomotopyElement f hf) =
      quotientCompose (correctedWeakEquivalenceInverseElement f hf)
        (quotientOriginalMorphismElement f) := by
  unfold quotientDGHomotopyBoundary
  rw [correctedWeakEquivalenceRightHomotopyElement_d]
  have hcast := quotientGradedModule_cast_eq L L
    (show (0 : ℤ) + 0 = 0 by omega) rfl
    (quotientCompose (correctedWeakEquivalenceInverseElement f hf)
      (quotientOriginalMorphismElement f))
  rw [hcast]
  simp only [eqToHom_refl]
  abel

/-- The Dold--Kan path from the source identity to `f ≫ g`. -/
def correctedWeakEquivalenceLeftMappingPath
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    SSet.Edge
      (correctedQuotientDGMappingVertexOfClosed K K
        (quotientIdentityElement K) (quotientIdentityElement_closed K))
      (correctedQuotientDGMappingVertexOfClosed K K
        (quotientCompose (quotientOriginalMorphismElement f)
          (correctedWeakEquivalenceInverseElement f hf))
        (quotientCompose_closed K L K
          (quotientOriginalMorphismElement f)
          (correctedWeakEquivalenceInverseElement f hf)
          (quotientOriginalMorphismElement_closed f)
          (correctedWeakEquivalenceInverseElement_d f hf))) :=
  quotientDGHomotopyEdgeTo K K
    (quotientIdentityElement K)
    (quotientCompose (quotientOriginalMorphismElement f)
      (correctedWeakEquivalenceInverseElement f hf))
    (quotientIdentityElement_closed K)
    (quotientCompose_closed K L K
      (quotientOriginalMorphismElement f)
      (correctedWeakEquivalenceInverseElement f hf)
      (quotientOriginalMorphismElement_closed f)
      (correctedWeakEquivalenceInverseElement_d f hf))
    (correctedWeakEquivalenceLeftHomotopyElement f hf)
    (correctedWeakEquivalenceLeftHomotopy_target f hf)

/-- The Dold--Kan path from the target identity to `g ≫ f`. -/
def correctedWeakEquivalenceRightMappingPath
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    SSet.Edge
      (correctedQuotientDGMappingVertexOfClosed L L
        (quotientIdentityElement L) (quotientIdentityElement_closed L))
      (correctedQuotientDGMappingVertexOfClosed L L
        (quotientCompose (correctedWeakEquivalenceInverseElement f hf)
          (quotientOriginalMorphismElement f))
        (quotientCompose_closed L K L
          (correctedWeakEquivalenceInverseElement f hf)
          (quotientOriginalMorphismElement f)
          (correctedWeakEquivalenceInverseElement_d f hf)
          (quotientOriginalMorphismElement_closed f))) :=
  quotientDGHomotopyEdgeTo L L
    (quotientIdentityElement L)
    (quotientCompose (correctedWeakEquivalenceInverseElement f hf)
      (quotientOriginalMorphismElement f))
    (quotientIdentityElement_closed L)
    (quotientCompose_closed L K L
      (correctedWeakEquivalenceInverseElement f hf)
      (quotientOriginalMorphismElement f)
      (correctedWeakEquivalenceInverseElement_d f hf)
      (quotientOriginalMorphismElement_closed f))
    (correctedWeakEquivalenceRightHomotopyElement f hf)
    (correctedWeakEquivalenceRightHomotopy_target f hf)

@[simp]
theorem originalCoefficientDGMorphism_homEquiv
    {K L : ComplexCategory} (f : K ⟶ L) :
    SimplicialCategory.homEquiv' _ _ (originalCoefficientDGMorphism f) =
      originalCoefficientDGMappingVertex f :=
  Equiv.apply_symm_apply _ _

/-- The ordinary source functor sends a bounded morphism to its explicit mapping vertex. -/
theorem originalCoefficientDGOrdinaryFunctor_map_homEquiv
    {K L : ComplexCategory} (f : K ⟶ L) :
    SimplicialCategory.homEquiv'
        (originalCoefficientDGOrdinaryFunctor.obj K)
        (originalCoefficientDGOrdinaryFunctor.obj L)
        (originalCoefficientDGOrdinaryFunctor.map f) =
      originalCoefficientDGMappingVertex f := by
  unfold originalCoefficientDGOrdinaryFunctor
  rw [Functor.comp_map]
  change SSet.unitHomEquiv (originalCoefficientDGMappingSSet K L)
      (Functor.LaxMonoidal.ε quotientCoefficientSimplicialForget ≫
        quotientCoefficientSimplicialForget.map
          (quotientDoldKanInverseUnitHomEquiv
            (originalCoefficientDGChainEnrichedHom (Opposite.op L) (Opposite.op K))
            (originalCoefficientDGChainMorphismMap (Opposite.op f)))) =
    originalCoefficientDGMappingVertex f
  rw [quotientCoefficientSimplicialForget_unitHom_vertex]
  change (((quotientDoldKanInverseUnitHomEquiv
      (originalCoefficientDGChainEnrichedHom (Opposite.op L) (Opposite.op K))
      (originalCoefficientDGChainMorphismMap (Opposite.op f))).app (op ⦋0⦌)).hom
        (show (𝟙_ QuotientChain).X 0 from (1 : QuotientCoefficientRing))) = _
  rw [quotientDoldKanInverseUnitHomEquiv_vertex]
  rw [originalCoefficientDGChainMorphismMap_f_zero]
  rfl

/-- The degree-zero bounded-morphism span maps to the zero-word quotient span. -/
theorem originalCoefficientDGMorphismSpan_map_toQuotient
    {K L : ComplexCategory} (f : K ⟶ L) :
    originalCoefficientDGMorphismSpan f ≫
        (OriginalCoefficientHomToQuotient K L).f 0 =
      quotientDGElementSpan K L (quotientOriginalMorphismElement f) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change QuotientCoefficientRing at r
  simp only [ModuleCat.comp_apply]
  rw [show (originalCoefficientDGMorphismSpan f).hom r =
      r • (ULift.up (ULift.up (CochainComplex.HomComplex.Cochain.ofHom f.hom))) by
    exact LinearMap.toSpanSingleton_apply _ _ _ _]
  rw [map_smul, OriginalCoefficientHomToQuotient_apply_up]
  change r • ULift.up (quotientOriginalMorphismElement f) =
    (quotientDGElementSpan K L (quotientOriginalMorphismElement f)).hom r
  exact (LinearMap.toSpanSingleton_apply _ _ _ _).symm

/-- Smart truncation carries the bounded-morphism degree-zero map to its zero-word quotient map. -/
theorem originalCoefficientDGChainMorphismDegreeZero_map_toQuotient
    {K L : ComplexCategory} (f : K ⟶ L) :
    originalCoefficientDGChainMorphismDegreeZero f ≫
        (originalCoefficientDGChainHomToQuotient
          (show OriginalCoefficientDGCategory from Opposite.op L)
          (show OriginalCoefficientDGCategory from Opposite.op K)).f 0 =
      quotientDGChainZeroMapOfClosed K L
        (quotientOriginalMorphismElement f)
        (quotientOriginalMorphismElement_closed f) := by
  let r := (quotientCoefficientCochainComplex K L).truncLE'ToRestriction
    ComplexShape.embeddingDownNat
  have hmono : Mono (r.f 0) := by
    have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
      simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
        (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
    rw [quotientTruncLEToRestriction_f_zero _ hb]
    infer_instance
  apply (cancel_mono (r.f 0)).1
  simp only [Category.assoc]
  have hnat := originalCoefficientDGChainHomToQuotient_toRestriction
    (show OriginalCoefficientDGCategory from Opposite.op L)
    (show OriginalCoefficientDGCategory from Opposite.op K) 0
  change (originalCoefficientDGChainHomToQuotient
      (show OriginalCoefficientDGCategory from Opposite.op L)
      (show OriginalCoefficientDGCategory from Opposite.op K)).f 0 ≫ r.f 0 =
    ((OriginalCoefficientCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0 ≫
      (OriginalCoefficientHomToQuotient K L).f 0 at hnat
  rw [hnat]
  rw [← Category.assoc]
  rw [originalCoefficientDGChainMorphismDegreeZero_toRestriction]
  rw [quotientDGChainZeroMapOfClosed_toRestriction]
  exact originalCoefficientDGMorphismSpan_map_toQuotient f

/-- The zero-word enriched functor sends the original bounded-morphism vertex to the
corresponding corrected-quotient vertex. -/
theorem originalToCorrectedQuotient_map_mappingVertex
    {K L : ComplexCategory} (f : K ⟶ L) :
    (originalToCorrectedQuotientDGSimplicialCategory.map
      (originalCoefficientDGOrdinaryFunctor.obj K)
      (originalCoefficientDGOrdinaryFunctor.obj L)).app (op ⦋0⦌)
        (originalCoefficientDGMappingVertex f) =
      correctedQuotientDGMappingVertexOfClosed K L
        (quotientOriginalMorphismElement f)
        (quotientOriginalMorphismElement_closed f) := by
  change ((quotientModuleDoldKanEquivalence.inverse.map
      (originalCoefficientDGChainHomToQuotient
        (show OriginalCoefficientDGCategory from Opposite.op L)
        (show OriginalCoefficientDGCategory from Opposite.op K))).app
          (op ⦋0⦌)).hom
      ((quotientModuleDoldKanInverseZeroIso
        (originalCoefficientDGChainEnrichedHom (Opposite.op L) (Opposite.op K))).hom.hom
          ((originalCoefficientDGChainMorphismDegreeZero f).hom 1)) =
    (quotientModuleDoldKanInverseZeroIso (quotientDGMappingChain K L)).hom.hom
      (quotientDGChainZeroOfClosed K L
        (quotientOriginalMorphismElement f)
        (quotientOriginalMorphismElement_closed f))
  have hnat := ConcreteCategory.congr_hom
    (quotientModuleDoldKanInverseZeroIso_hom_naturality
      (originalCoefficientDGChainHomToQuotient
        (show OriginalCoefficientDGCategory from Opposite.op L)
        (show OriginalCoefficientDGCategory from Opposite.op K)))
    ((originalCoefficientDGChainMorphismDegreeZero f).hom 1)
  simp only [ModuleCat.comp_apply] at hnat
  rw [hnat]
  have hchain := ConcreteCategory.congr_hom
    (originalCoefficientDGChainMorphismDegreeZero_map_toQuotient f)
    (1 : QuotientCoefficientRing)
  change ((originalCoefficientDGChainHomToQuotient
      (show OriginalCoefficientDGCategory from Opposite.op L)
      (show OriginalCoefficientDGCategory from Opposite.op K)).f 0).hom
        ((originalCoefficientDGChainMorphismDegreeZero f).hom 1) =
      quotientDGChainZeroOfClosed K L
        (quotientOriginalMorphismElement f)
        (quotientOriginalMorphismElement_closed f) at hchain
  exact congrArg
    (quotientModuleDoldKanInverseZeroIso (quotientDGMappingChain K L)).hom.hom hchain

/-- The actual corrected-quotient morphism represented by a bounded morphism. -/
def correctedWeakEquivalenceMorphism {K L : ComplexCategory} (f : K ⟶ L) :
    correctedQuotientDGObject K ⟶ correctedQuotientDGObject L :=
  correctedQuotientDGMorphismOfClosed (quotientOriginalMorphismElement f)
    (quotientOriginalMorphismElement_closed f)

/-- The ordinary morphism induced by the zero-word enriched functor is the explicit
corrected-quotient morphism. -/
theorem originalToCorrectedQuotient_mapOrdinary_eq
    {K L : ComplexCategory} (f : K ⟶ L) :
    CoherentNerveHomotopyInverse.TriangleData.mapOrdinary
        OriginalCoefficientDGSimplicialCategory
        originalToCorrectedQuotientDGSimplicialCategory
        (originalCoefficientDGOrdinaryFunctor.map f) =
      correctedWeakEquivalenceMorphism f := by
  apply (CategoryTheory.eHomEquiv SSet).injective
  rw [CoherentNerveHomotopyInverse.TriangleData.eHomEquiv_mapOrdinary]
  apply (SSet.unitHomEquiv
    (correctedQuotientDGObject K ⟶[SSet] correctedQuotientDGObject L)).injective
  change (originalToCorrectedQuotientDGSimplicialCategory.map
      (originalCoefficientDGOrdinaryFunctor.obj K)
      (originalCoefficientDGOrdinaryFunctor.obj L)).app (op ⦋0⦌)
        (SimplicialCategory.homEquiv'
          (originalCoefficientDGOrdinaryFunctor.obj K)
          (originalCoefficientDGOrdinaryFunctor.obj L)
          (originalCoefficientDGOrdinaryFunctor.map f)) =
    SimplicialCategory.homEquiv'
      (correctedQuotientDGObject K) (correctedQuotientDGObject L)
      (correctedWeakEquivalenceMorphism f)
  rw [originalCoefficientDGOrdinaryFunctor_map_homEquiv]
  rw [originalToCorrectedQuotient_map_mappingVertex]
  exact (correctedQuotientDGMorphismOfClosed_homEquiv K L
    (quotientOriginalMorphismElement f) (quotientOriginalMorphismElement_closed f)).symm

/-- The actual inverse morphism represented by the explicit quotient inverse element. -/
def correctedWeakEquivalenceInverseMorphism
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    correctedQuotientDGObject L ⟶ correctedQuotientDGObject K :=
  correctedQuotientDGMorphismOfClosed
    (correctedWeakEquivalenceInverseElement f hf)
    (correctedWeakEquivalenceInverseElement_d f hf)

/-- The enriched identity vertex is the mapping vertex of the quotient identity element. -/
theorem correctedQuotientDG_homEquiv_identity (K : ComplexCategory) :
    SimplicialCategory.homEquiv'
        (correctedQuotientDGObject K) (correctedQuotientDGObject K) (𝟙 _) =
      correctedQuotientDGMappingVertexOfClosed K K
        (quotientIdentityElement K) (quotientIdentityElement_closed K) := by
  rw [← correctedQuotientDGMorphismOfClosed_identity K]
  exact correctedQuotientDGMorphismOfClosed_homEquiv K K
    (quotientIdentityElement K) (quotientIdentityElement_closed K)

set_option maxRecDepth 10000 in
/-- The enriched composite vertex agrees with the raw quotient composite element. -/
theorem correctedQuotientDG_homEquiv_comp
    (K L M : ComplexCategory)
    (x : quotientGradedModule K L 0)
    (y : quotientGradedModule L M 0)
    (hx : (quotientTotalDifferential K L 0).hom x = 0)
    (hy : (quotientTotalDifferential L M 0).hom y = 0) :
    (SimplicialCategory.sHomComp
      (correctedQuotientDGObject K)
      (correctedQuotientDGObject L)
      (correctedQuotientDGObject M)).app (op ⦋0⦌)
        (SimplicialCategory.homEquiv'
          (correctedQuotientDGObject K) (correctedQuotientDGObject L)
          (correctedQuotientDGMorphismOfClosed x hx),
        SimplicialCategory.homEquiv'
          (correctedQuotientDGObject L) (correctedQuotientDGObject M)
          (correctedQuotientDGMorphismOfClosed y hy)) =
      correctedQuotientDGMappingVertexOfClosed K M (quotientCompose x y)
        (quotientCompose_closed K L M x y hx hy) := by
  calc
    _ = SimplicialCategory.homEquiv'
        (correctedQuotientDGObject K) (correctedQuotientDGObject M)
        (correctedQuotientDGMorphismOfClosed x hx ≫
          correctedQuotientDGMorphismOfClosed y hy) := rfl
    _ = SimplicialCategory.homEquiv'
        (correctedQuotientDGObject K) (correctedQuotientDGObject M)
        (correctedQuotientDGMorphismOfClosed (quotientCompose x y)
          (quotientCompose_closed K L M x y hx hy)) := by
      rw [correctedQuotientDGMorphismOfClosed_comp]
    _ = _ := correctedQuotientDGMorphismOfClosed_homEquiv K M
      (quotientCompose x y) (quotientCompose_closed K L M x y hx hy)

/-- The explicit quotient inverse data in the actual corrected simplicial category. -/
def correctedWeakEquivalenceHomotopyInverseData
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    CoherentNerveHomotopyInverse.HomotopyInverseData
      CorrectedQuotientDGSimplicialCategory
      (correctedWeakEquivalenceMorphism f) where
  inverse := correctedWeakEquivalenceInverseMorphism f hf
  rightPath := by
    let e := correctedWeakEquivalenceLeftMappingPath f hf
    have hsrc : SimplicialCategory.homEquiv'
          (correctedQuotientDGObject K) (correctedQuotientDGObject K) (𝟙 _) =
        correctedQuotientDGMappingVertexOfClosed K K
          (quotientIdentityElement K) (quotientIdentityElement_closed K) :=
      correctedQuotientDG_homEquiv_identity K
    have htgt :
        (SimplicialCategory.sHomComp
          (correctedQuotientDGObject K)
          (correctedQuotientDGObject L)
          (correctedQuotientDGObject K)).app (op ⦋0⦌)
            (SimplicialCategory.homEquiv'
              (correctedQuotientDGObject K) (correctedQuotientDGObject L)
              (correctedWeakEquivalenceMorphism f),
            SimplicialCategory.homEquiv'
              (correctedQuotientDGObject L) (correctedQuotientDGObject K)
              (correctedWeakEquivalenceInverseMorphism f hf)) =
          correctedQuotientDGMappingVertexOfClosed K K
            (quotientCompose (quotientOriginalMorphismElement f)
              (correctedWeakEquivalenceInverseElement f hf))
            (quotientCompose_closed K L K
              (quotientOriginalMorphismElement f)
              (correctedWeakEquivalenceInverseElement f hf)
              (quotientOriginalMorphismElement_closed f)
              (correctedWeakEquivalenceInverseElement_d f hf)) := by
      exact correctedQuotientDG_homEquiv_comp K L K
        (quotientOriginalMorphismElement f)
        (correctedWeakEquivalenceInverseElement f hf)
        (quotientOriginalMorphismElement_closed f)
        (correctedWeakEquivalenceInverseElement_d f hf)
    exact SSet.Edge.castEndpoints hsrc htgt e
  leftPath := by
    let e := correctedWeakEquivalenceRightMappingPath f hf
    have hsrc : SimplicialCategory.homEquiv'
          (correctedQuotientDGObject L) (correctedQuotientDGObject L) (𝟙 _) =
        correctedQuotientDGMappingVertexOfClosed L L
          (quotientIdentityElement L) (quotientIdentityElement_closed L) :=
      correctedQuotientDG_homEquiv_identity L
    have htgt :
        (SimplicialCategory.sHomComp
          (correctedQuotientDGObject L)
          (correctedQuotientDGObject K)
          (correctedQuotientDGObject L)).app (op ⦋0⦌)
            (SimplicialCategory.homEquiv'
              (correctedQuotientDGObject L) (correctedQuotientDGObject K)
              (correctedWeakEquivalenceInverseMorphism f hf),
            SimplicialCategory.homEquiv'
              (correctedQuotientDGObject K) (correctedQuotientDGObject L)
              (correctedWeakEquivalenceMorphism f)) =
          correctedQuotientDGMappingVertexOfClosed L L
            (quotientCompose (correctedWeakEquivalenceInverseElement f hf)
              (quotientOriginalMorphismElement f))
            (quotientCompose_closed L K L
              (correctedWeakEquivalenceInverseElement f hf)
              (quotientOriginalMorphismElement f)
              (correctedWeakEquivalenceInverseElement_d f hf)
              (quotientOriginalMorphismElement_closed f)) := by
      exact correctedQuotientDG_homEquiv_comp L K L
        (correctedWeakEquivalenceInverseElement f hf)
        (quotientOriginalMorphismElement f)
        (correctedWeakEquivalenceInverseElement_d f hf)
        (quotientOriginalMorphismElement_closed f)
    exact SSet.Edge.castEndpoints hsrc htgt e

/-- The ordinary-to-original-DG comparison sends a bounded arrow to its coherent edge. -/
theorem metrizableComplexNerveToOriginalCoefficientDG_edge
    {K L : ComplexCategory} (f : K ⟶ L) :
    (CategoryTheory.nerve.edgeMk f).map
        metrizableComplexNerveToOriginalCoefficientDGHomotopyCoherentNerve =
      CoherentNerveHomotopyInverse.TriangleData.coherentEdge
        OriginalCoefficientDGSimplicialCategory
        (originalCoefficientDGOrdinaryFunctor.map f) := by
  apply SSet.Edge.ext
  simp only [SSet.Edge.map_edge,
    CoherentNerveHomotopyInverse.TriangleData.coherentEdge_edge]
  change OrdinaryToSimplicialNerve.coherentSimplexOfChain
      OriginalCoefficientDGSimplicialCategory
        ((originalCoefficientDGOrdinaryFunctor.mapComposableArrows 1).obj
          (CategoryTheory.ComposableArrows.mk₁ f)) =
    OrdinaryToSimplicialNerve.coherentSimplexOfChain
      OriginalCoefficientDGSimplicialCategory
      (CoherentNerveHomotopyInverse.TriangleData.edgeChain
        OriginalCoefficientDGSimplicialCategory
        (originalCoefficientDGOrdinaryFunctor.map f))
  apply congrArg
  calc
    (originalCoefficientDGOrdinaryFunctor.mapComposableArrows 1).obj
        (CategoryTheory.ComposableArrows.mk₁ f) =
      CategoryTheory.ComposableArrows.mk₁
        ((originalCoefficientDGOrdinaryFunctor.mapComposableArrows 1).obj
          (CategoryTheory.ComposableArrows.mk₁ f)).hom :=
      (CategoryTheory.ComposableArrows.mk₁_hom _).symm
    _ = CoherentNerveHomotopyInverse.TriangleData.edgeChain
        OriginalCoefficientDGSimplicialCategory
        (originalCoefficientDGOrdinaryFunctor.map f) := by
      congr 1

/-- The ordinary-to-original-DG comparison sends an object to its coherent vertex. -/
theorem metrizableComplexNerveToOriginalCoefficientDG_vertex (K : ComplexCategory) :
    metrizableComplexNerveToOriginalCoefficientDGHomotopyCoherentNerve.app (op ⦋0⦌)
        (CategoryTheory.ComposableArrows.mk₀ K) =
      CoherentNerveHomotopyInverse.TriangleData.coherentVertex
        OriginalCoefficientDGSimplicialCategory
        (originalCoefficientDGOrdinaryFunctor.obj K) := by
  change OrdinaryToSimplicialNerve.coherentSimplexOfChain
      OriginalCoefficientDGSimplicialCategory
        ((originalCoefficientDGOrdinaryFunctor.mapComposableArrows 0).obj
          (CategoryTheory.ComposableArrows.mk₀ K)) =
    OrdinaryToSimplicialNerve.coherentSimplexOfChain
      OriginalCoefficientDGSimplicialCategory
      (CategoryTheory.ComposableArrows.mk₀
        (CategoryTheory.ForgetEnrichment.of SSet
          (originalCoefficientDGOrdinaryFunctor.obj K)))
  apply congrArg
  exact CategoryTheory.ComposableArrows.ext
    (h := fun i ↦ by
      fin_cases i
      rfl)
    (w := fun i hi ↦ by omega)

/-- The ordinary-to-quotient comparison sends an object to its corrected coherent vertex. -/
theorem metrizableComplexNerveToCorrectedQuotientDG_vertex (K : ComplexCategory) :
    metrizableComplexNerveToCorrectedQuotientDG.app (op ⦋0⦌)
        (CategoryTheory.ComposableArrows.mk₀ K) =
      CoherentNerveHomotopyInverse.TriangleData.coherentVertex
        CorrectedQuotientDGSimplicialCategory
        (correctedQuotientDGObject K) := by
  change originalToCorrectedQuotientDGHomotopyCoherentNerve.app (op ⦋0⦌)
      (metrizableComplexNerveToOriginalCoefficientDGHomotopyCoherentNerve.app
        (op ⦋0⦌) (CategoryTheory.ComposableArrows.mk₀ K)) = _
  rw [metrizableComplexNerveToOriginalCoefficientDG_vertex]
  exact CoherentNerveHomotopyInverse.TriangleData.coherentNerveMap_vertex
    OriginalCoefficientDGSimplicialCategory
    originalToCorrectedQuotientDGSimplicialCategory
    (originalCoefficientDGOrdinaryFunctor.obj K)

/-- The ordinary-to-quotient comparison sends a bounded arrow to the coherent edge of its
zero-word quotient morphism. -/
theorem metrizableComplexNerveToCorrectedQuotientDG_edge
    {K L : ComplexCategory} (f : K ⟶ L) :
    (CategoryTheory.nerve.edgeMk f).map metrizableComplexNerveToCorrectedQuotientDG =
      SSet.Edge.castEndpoints
        (metrizableComplexNerveToCorrectedQuotientDG_vertex K)
        (metrizableComplexNerveToCorrectedQuotientDG_vertex L)
        (CoherentNerveHomotopyInverse.TriangleData.coherentEdge
          CorrectedQuotientDGSimplicialCategory
          (correctedWeakEquivalenceMorphism f)) := by
  apply SSet.Edge.ext
  simp only [SSet.Edge.castEndpoints_edge]
  calc
    ((CategoryTheory.nerve.edgeMk f).map
        metrizableComplexNerveToCorrectedQuotientDG).edge =
      (((CategoryTheory.nerve.edgeMk f).map
          metrizableComplexNerveToOriginalCoefficientDGHomotopyCoherentNerve).map
        originalToCorrectedQuotientDGHomotopyCoherentNerve).edge := rfl
    _ = ((CoherentNerveHomotopyInverse.TriangleData.coherentEdge
          OriginalCoefficientDGSimplicialCategory
          (originalCoefficientDGOrdinaryFunctor.map f)).map
        originalToCorrectedQuotientDGHomotopyCoherentNerve).edge := by
      rw [metrizableComplexNerveToOriginalCoefficientDG_edge]
    _ = (SSet.Edge.castEndpoints
          (CoherentNerveHomotopyInverse.TriangleData.coherentNerveMap_vertex
            OriginalCoefficientDGSimplicialCategory
            originalToCorrectedQuotientDGSimplicialCategory
            (originalCoefficientDGOrdinaryFunctor.obj K))
          (CoherentNerveHomotopyInverse.TriangleData.coherentNerveMap_vertex
            OriginalCoefficientDGSimplicialCategory
            originalToCorrectedQuotientDGSimplicialCategory
            (originalCoefficientDGOrdinaryFunctor.obj L))
          (CoherentNerveHomotopyInverse.TriangleData.coherentEdge
            CorrectedQuotientDGSimplicialCategory
            (CoherentNerveHomotopyInverse.TriangleData.mapOrdinary
              OriginalCoefficientDGSimplicialCategory
              originalToCorrectedQuotientDGSimplicialCategory
              (originalCoefficientDGOrdinaryFunctor.map f)))).edge := by
      exact congrArg SSet.Edge.edge
        (CoherentNerveHomotopyInverse.TriangleData.coherentEdge_map
          OriginalCoefficientDGSimplicialCategory
          originalToCorrectedQuotientDGSimplicialCategory
          (originalCoefficientDGOrdinaryFunctor.map f))
    _ = (CoherentNerveHomotopyInverse.TriangleData.coherentEdge
          CorrectedQuotientDGSimplicialCategory
          (correctedWeakEquivalenceMorphism f)).edge := by
      rw [SSet.Edge.castEndpoints_edge,
        originalToCorrectedQuotient_mapOrdinary_eq]

/-- A raw corrected weak equivalence becomes an equivalence edge in the corrected quotient
coherent nerve. -/
theorem correctedWeakEquivalenceMorphism_edgeIsEquivalence
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    EdgeIsEquivalence
      (CoherentNerveHomotopyInverse.TriangleData.coherentEdge
        CorrectedQuotientDGSimplicialCategory
        (correctedWeakEquivalenceMorphism f)) :=
  CoherentNerveHomotopyInverse.coherentEdge_isEquivalence_of_homotopyInverse
    CorrectedQuotientDGSimplicialCategory
    (correctedWeakEquivalenceMorphism f)
    (correctedWeakEquivalenceHomotopyInverseData f hf)

/-- The ordinary-to-quotient comparison inverts every raw corrected weak equivalence. -/
theorem metrizableComplexNerveToCorrectedQuotientDG_rawIsEquivalence
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    EdgeIsEquivalence
      ((CategoryTheory.nerve.edgeMk f).map metrizableComplexNerveToCorrectedQuotientDG) := by
  rw [metrizableComplexNerveToCorrectedQuotientDG_edge]
  exact (correctedWeakEquivalenceMorphism_edgeIsEquivalence f hf).castEndpoints
    (metrizableComplexNerveToCorrectedQuotientDG_vertex K)
    (metrizableComplexNerveToCorrectedQuotientDG_vertex L)

/-- The ordinary-to-quotient comparison inverts the multiplicative closure of the corrected
weak equivalences. -/
theorem metrizableComplexNerveToCorrectedQuotientDG_generatedIsEquivalence
    {K L : ComplexCategory} (f : K ⟶ L) (hf : GeneratedWeakEquivalence f) :
    EdgeIsEquivalence
      ((CategoryTheory.nerve.edgeMk f).map metrizableComplexNerveToCorrectedQuotientDG) := by
  induction hf with
  | of f hf =>
      exact metrizableComplexNerveToCorrectedQuotientDG_rawIsEquivalence f hf
  | id K =>
      rw [CategoryTheory.nerve.edgeMk_id]
      exact (edgeIsEquivalence_id _).map metrizableComplexNerveToCorrectedQuotientDG
  | comp_of f g hf hg ih =>
      obtain ⟨s⟩ := (CategoryTheory.nerve.nonempty_compStruct_iff f g (f ≫ g)).2 rfl
      exact EdgeIsEquivalence.comp
        (s.map metrizableComplexNerveToCorrectedQuotientDG)
        ih
        (metrizableComplexNerveToCorrectedQuotientDG_rawIsEquivalence g hg)

/-- The ordinary-to-quotient comparison inverts the complete generated marking. -/
theorem metrizableComplexNerveToCorrectedQuotientDG_invertsMarkedEdges :
    InvertsMarkedEdges (relativeNerveEdgeMarking relativeCategory)
      metrizableComplexNerveToCorrectedQuotientDG := by
  exact relativeCategory.invertsMarkedEdges_of_weakEquivalence
    metrizableComplexNerveToCorrectedQuotientDG
    (fun a ↦ metrizableComplexNerveToCorrectedQuotientDG_generatedIsEquivalence
      a.hom a.weak)

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
