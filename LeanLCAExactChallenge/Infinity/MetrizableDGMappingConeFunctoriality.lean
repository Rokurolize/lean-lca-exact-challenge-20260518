/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGMappingConeFunctor
import LeanLCAExactChallenge.Infinity.MetrizableDGMappingConeCoherentSimplex

/-!
# Functoriality of bounded DG mapping-cone triangles

A commutative square of bounded complexes carries the degree-minus-one cone coherence to the
corresponding coherence of the target cone. The same square therefore defines a natural
transformation between the two ordinary composable cone triangles.

These statements are the chain-level functorial input for assembling coherent mapping-cone
two-simplices into a functorial corner extension.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open CategoryTheory

/-- The degree-minus-one cone inclusion is natural with respect to a commutative square of
arrows. -/
theorem dgMappingConeInl_naturality {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    (dgMappingConeInl f.hom).comp
        (CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeMap sq)))
        (add_zero (-1)) =
      (CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map sq.left)).comp
        (dgMappingConeInl g.hom) (zero_add (-1)) := by
  unfold dgMappingConeInl
  rw [boundedInclusion_map_dgMappingConeMap]
  apply CochainComplex.HomComplex.Cochain.ext
  intro p q hpq
  rw [CochainComplex.HomComplex.Cochain.comp_zero_cochain_v,
    CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
  rw [CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]
  unfold CochainComplex.mappingCone.map
  rw [CochainComplex.mappingCone.inl_v_desc_f]
  rw [CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
    CochainComplex.HomComplex.Cochain.ofHom_v]

/-- Postcomposition by a bounded chain map on untruncated DG Hom complexes. -/
def dgHomZModulePostcomposition (K : ComplexCategory)
    {L M : ComplexCategory} (g : L ⟶ M) :
    dgHomZModuleCochainComplex K L ⟶ dgHomZModuleCochainComplex K M where
  f n := ModuleCat.ofHom
    { toFun := fun γ ↦ γ.comp
        (CochainComplex.HomComplex.Cochain.ofHom g.hom) (add_zero n)
      map_add' := fun γ γ' ↦
        CochainComplex.HomComplex.Cochain.add_comp γ γ' _ (add_zero n)
      map_smul' := fun r γ ↦
        CochainComplex.HomComplex.Cochain.smul_comp r γ _ (add_zero n) }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro γ
    simp [dgHomZModuleCochainComplex,
      CochainComplex.HomComplex.δ_comp_ofHom]

/-- Postcomposition on the smart-truncated direct mapping chain complexes. -/
def dgMappingDirectZModulePostcomposition (K : ComplexCategory)
    {L M : ComplexCategory} (g : L ⟶ M) :
    dgMappingDirectZModuleChainComplex K L ⟶
      dgMappingDirectZModuleChainComplex K M :=
  HomologicalComplex.truncLE'Map (dgHomZModulePostcomposition K g)
    ComplexShape.embeddingDownNat

/-- Precomposition on the smart-truncated direct mapping chain complexes. -/
def dgMappingDirectZModulePrecomposition (M : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleChainComplex L M ⟶
      dgMappingDirectZModuleChainComplex K M :=
  HomologicalComplex.truncLE'Map (dgHomZModulePrecomposition M f)
    ComplexShape.embeddingDownNat

/-- The degree-one mapping-cone coherence is natural under simultaneous precomposition at
the source and postcomposition at the cone. -/
theorem dgMappingConeCoherenceChainOne_naturality
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    ((dgMappingDirectZModulePostcomposition f.left (dgMappingConeMap sq)).f 1).hom
        (MappingConeTriangle.dgMappingConeCoherenceChainOne f.hom) =
      ((dgMappingDirectZModulePrecomposition (dgMappingConeObject g.hom) sq.left).f 1).hom
        (MappingConeTriangle.dgMappingConeCoherenceChainOne g.hom) := by
  apply (ModuleCat.mono_iff_injective
    (((dgHomZModuleCochainComplex f.left (dgMappingConeObject g.hom)).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 1)).1 inferInstance
  have hpost := HomologicalComplex.truncLE'ToRestriction_naturality
    (dgHomZModulePostcomposition f.left (dgMappingConeMap sq))
    ComplexShape.embeddingDownNat
  have hpre := HomologicalComplex.truncLE'ToRestriction_naturality
    (dgHomZModulePrecomposition (dgMappingConeObject g.hom) sq.left)
    ComplexShape.embeddingDownNat
  have hpost1 := HomologicalComplex.congr_hom hpost 1
  have hpre1 := HomologicalComplex.congr_hom hpre 1
  have hpostapp := ConcreteCategory.congr_hom hpost1
    (MappingConeTriangle.dgMappingConeCoherenceChainOne f.hom)
  have hpreapp := ConcreteCategory.congr_hom hpre1
    (MappingConeTriangle.dgMappingConeCoherenceChainOne g.hom)
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at hpostapp hpreapp
  calc
    _ = (ConcreteCategory.hom
          ((HomologicalComplex.restrictionMap
            (dgHomZModulePostcomposition f.left (dgMappingConeMap sq))
            ComplexShape.embeddingDownNat).f 1))
        ((ConcreteCategory.hom
          (((dgHomZModuleCochainComplex f.left
            (dgMappingConeObject f.hom)).truncLE'ToRestriction
              ComplexShape.embeddingDownNat).f 1))
          (MappingConeTriangle.dgMappingConeCoherenceChainOne f.hom)) := hpostapp
    _ = (dgMappingConeInl f.hom).comp
          (CochainComplex.HomComplex.Cochain.ofHom
            ((boundedCochainComplex MetrizableLCA.{0}).ι.map
              (dgMappingConeMap sq))) (add_zero (-1)) := by
      rw [MappingConeTriangle.dgMappingConeCoherenceChainOne_toRestriction]
      rfl
    _ = (CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map sq.left)).comp
        (dgMappingConeInl g.hom) (zero_add (-1)) :=
      dgMappingConeInl_naturality sq
    _ = (ConcreteCategory.hom
          ((HomologicalComplex.restrictionMap
            (dgHomZModulePrecomposition (dgMappingConeObject g.hom) sq.left)
            ComplexShape.embeddingDownNat).f 1))
        ((ConcreteCategory.hom
          (((dgHomZModuleCochainComplex g.left
            (dgMappingConeObject g.hom)).truncLE'ToRestriction
              ComplexShape.embeddingDownNat).f 1))
          (MappingConeTriangle.dgMappingConeCoherenceChainOne g.hom)) := by
      rw [MappingConeTriangle.dgMappingConeCoherenceChainOne_toRestriction]
      rfl
    _ = _ := hpreapp.symm

/-- The explicit Dold--Kan one-simplex of the mapping-cone coherence is natural under a
commutative square. -/
theorem dgMappingConeCoherenceGammaOneSimplex_naturality
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    ((DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingDirectZModulePostcomposition f.left (dgMappingConeMap sq))).app
        (Opposite.op (SimplexCategory.mk 1))).hom
      (MappingConeTriangle.dgMappingConeCoherenceGammaOneSimplex f.hom) =
    ((DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingDirectZModulePrecomposition (dgMappingConeObject g.hom) sq.left)).app
        (Opposite.op (SimplexCategory.mk 1))).hom
      (MappingConeTriangle.dgMappingConeCoherenceGammaOneSimplex g.hom) := by
  change ((AlgebraicTopology.DoldKan.Γ₀.map
      (dgMappingDirectZModulePostcomposition f.left (dgMappingConeMap sq))).app
        (Opposite.op (SimplexCategory.mk 1))).hom
      (doldKanGammaOneSimplex
        (dgMappingDirectZModuleChainComplex f.left (dgMappingConeObject f.hom)) 0
        (MappingConeTriangle.dgMappingConeCoherenceChainOne f.hom)) =
    ((AlgebraicTopology.DoldKan.Γ₀.map
      (dgMappingDirectZModulePrecomposition (dgMappingConeObject g.hom) sq.left)).app
        (Opposite.op (SimplexCategory.mk 1))).hom
      (doldKanGammaOneSimplex
        (dgMappingDirectZModuleChainComplex g.left (dgMappingConeObject g.hom)) 0
        (MappingConeTriangle.dgMappingConeCoherenceChainOne g.hom))
  rw [doldKanGammaOneSimplex_map, doldKanGammaOneSimplex_map]
  simp only [map_zero]
  rw [dgMappingConeCoherenceChainOne_naturality]

/-- Dold--Kan realization of smart-truncated postcomposition. -/
def dgMappingDirectZModulePostcompositionSSet (K : ComplexCategory)
    {L M : ComplexCategory} (g : L ⟶ M) :
    dgMappingDirectZModuleSSet K L ⟶ dgMappingDirectZModuleSSet K M :=
  zModuleSimplicialForget.map
    (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingDirectZModulePostcomposition K g))

/-- Dold--Kan realization of smart-truncated precomposition. -/
def dgMappingDirectZModulePrecompositionSSet (M : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleSSet L M ⟶ dgMappingDirectZModuleSSet K M :=
  zModuleSimplicialForget.map
    (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingDirectZModulePrecomposition M f))

/-- The explicit Dold--Kan coherence edge is natural after realizing the two chain-level
whiskering maps. -/
theorem dgMappingConeCoherenceEdgeMap_naturality
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    MappingConeTriangle.dgMappingConeCoherenceEdgeMap f.hom ≫
        dgMappingDirectZModulePostcompositionSSet f.left (dgMappingConeMap sq) =
      MappingConeTriangle.dgMappingConeCoherenceEdgeMap g.hom ≫
        dgMappingDirectZModulePrecompositionSSet (dgMappingConeObject g.hom) sq.left := by
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp,
    MappingConeTriangle.dgMappingConeCoherenceEdgeMap,
    Equiv.apply_symm_apply, dgMappingDirectZModulePostcompositionSSet,
    dgMappingDirectZModulePrecompositionSSet]
  exact dgMappingConeCoherenceGammaOneSimplex_naturality sq

/-- The long thickening-path map in the coherent cone triangle is natural under a
commutative square. -/
theorem trianglePathCoherenceMap_naturality
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    MappingConeTriangle.trianglePathCoherenceMap f.hom ≫
        dgMappingDirectZModulePostcompositionSSet f.left (dgMappingConeMap sq) =
      MappingConeTriangle.trianglePathCoherenceMap g.hom ≫
        dgMappingDirectZModulePrecompositionSSet (dgMappingConeObject g.hom) sq.left := by
  unfold MappingConeTriangle.trianglePathCoherenceMap
  simp only [Category.assoc]
  rw [dgMappingConeCoherenceEdgeMap_naturality]

namespace MappingConeTriangle

set_option maxHeartbeats 1000000 in
-- Normalizing the two dependent composable-arrow naturality conditions needs extra budget.
/-- A commutative square of arrows defines a natural transformation between the corresponding
ordinary cone triangles. -/
noncomputable def mappingConeOrdinaryChainNatTrans
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    mappingConeOrdinaryChain f.hom ⟶ mappingConeOrdinaryChain g.hom :=
  CategoryTheory.ComposableArrows.homMk₂
    (directDGMorphism sq.left)
    (directDGMorphism sq.right)
    (directDGMorphism (dgMappingConeMap sq))
    (by
      rw [show (mappingConeOrdinaryChain f.hom).map' 0 1 =
          directDGMorphism f.hom by rfl,
        show (mappingConeOrdinaryChain g.hom).map' 0 1 =
          directDGMorphism g.hom by rfl]
      apply directDGToComplexFunctor.map_injective
      rw [Functor.map_comp, Functor.map_comp]
      simpa only [directDGToComplexFunctor_map_directDGMorphism] using
        (Arrow.w sq).symm)
    (by
      rw [show (mappingConeOrdinaryChain f.hom).map' 1 2 =
          directDGMorphism (dgMappingConeInr f.hom) by rfl,
        show (mappingConeOrdinaryChain g.hom).map' 1 2 =
          directDGMorphism (dgMappingConeInr g.hom) by rfl]
      apply directDGToComplexFunctor.map_injective
      rw [Functor.map_comp, Functor.map_comp]
      rw [directDGToComplexFunctor_map_directDGMorphism,
        directDGToComplexFunctor_map_directDGMorphism,
        directDGToComplexFunctor_map_directDGMorphism,
        directDGToComplexFunctor_map_directDGMorphism]
      apply (boundedCochainComplex MetrizableLCA.{0}).ι.map_injective
      rw [Functor.map_comp, Functor.map_comp,
        boundedInclusion_map_dgMappingConeInr,
        boundedInclusion_map_dgMappingConeMap,
        boundedInclusion_map_dgMappingConeInr]
      rw [CochainComplex.mappingCone.map_eq_mapOfHomotopy,
        CochainComplex.mappingCone.triangleMapOfHomotopy_comm₂])

@[simp]
theorem mappingConeOrdinaryChainNatTrans_app_zero
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    (mappingConeOrdinaryChainNatTrans sq).app 0 = directDGMorphism sq.left :=
  rfl

@[simp]
theorem mappingConeOrdinaryChainNatTrans_app_one
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    (mappingConeOrdinaryChainNatTrans sq).app 1 = directDGMorphism sq.right :=
  rfl

@[simp]
theorem mappingConeOrdinaryChainNatTrans_app_two
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    (mappingConeOrdinaryChainNatTrans sq).app 2 =
      directDGMorphism (dgMappingConeMap sq) :=
  rfl

end MappingConeTriangle

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
