/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGMappingConeFunctor
import LeanLCAExactChallenge.Infinity.MetrizableDGMappingConeCoherentSimplex
import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialWhiskering
import LeanLCAExactChallenge.Infinity.CoherentNerveChainNaturality

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

@[simp]
theorem mappingConeOrdinaryChainNatTrans_id (f : Arrow ComplexCategory) :
    mappingConeOrdinaryChainNatTrans (𝟙 f) =
      𝟙 (mappingConeOrdinaryChain f.hom) := by
  apply CategoryTheory.ComposableArrows.hom_ext₂
  · change (mappingConeOrdinaryChainNatTrans (𝟙 f)).app (0 : Fin 3) = _
    rw [mappingConeOrdinaryChainNatTrans_app_zero, Arrow.id_left,
      directDGMorphism_id]
    rfl
  · change (mappingConeOrdinaryChainNatTrans (𝟙 f)).app (1 : Fin 3) = _
    rw [mappingConeOrdinaryChainNatTrans_app_one, Arrow.id_right,
      directDGMorphism_id]
    rfl
  · change (mappingConeOrdinaryChainNatTrans (𝟙 f)).app (2 : Fin 3) = _
    rw [mappingConeOrdinaryChainNatTrans_app_two]
    rw [show dgMappingConeMap (𝟙 f) = 𝟙 (dgMappingConeObject f.hom) by
      exact dgMappingConeFunctor.map_id f]
    rw [directDGMorphism_id]
    rfl

@[simp]
theorem mappingConeOrdinaryChainNatTrans_comp
    {f g h : Arrow ComplexCategory} (sq : f ⟶ g) (sq' : g ⟶ h) :
    mappingConeOrdinaryChainNatTrans (sq ≫ sq') =
      mappingConeOrdinaryChainNatTrans sq ≫
        mappingConeOrdinaryChainNatTrans sq' := by
  apply CategoryTheory.ComposableArrows.hom_ext₂
  · change (mappingConeOrdinaryChainNatTrans (sq ≫ sq')).app (0 : Fin 3) =
      (mappingConeOrdinaryChainNatTrans sq ≫
        mappingConeOrdinaryChainNatTrans sq').app (0 : Fin 3)
    rw [mappingConeOrdinaryChainNatTrans_app_zero,
      CategoryTheory.NatTrans.comp_app,
      mappingConeOrdinaryChainNatTrans_app_zero,
      mappingConeOrdinaryChainNatTrans_app_zero,
      Arrow.comp_left, directDGMorphism_comp]
  · change (mappingConeOrdinaryChainNatTrans (sq ≫ sq')).app (1 : Fin 3) =
      (mappingConeOrdinaryChainNatTrans sq ≫
        mappingConeOrdinaryChainNatTrans sq').app (1 : Fin 3)
    rw [mappingConeOrdinaryChainNatTrans_app_one,
      CategoryTheory.NatTrans.comp_app,
      mappingConeOrdinaryChainNatTrans_app_one,
      mappingConeOrdinaryChainNatTrans_app_one,
      Arrow.comp_right, directDGMorphism_comp]
  · change (mappingConeOrdinaryChainNatTrans (sq ≫ sq')).app (2 : Fin 3) =
      (mappingConeOrdinaryChainNatTrans sq ≫
        mappingConeOrdinaryChainNatTrans sq').app (2 : Fin 3)
    rw [mappingConeOrdinaryChainNatTrans_app_two,
      CategoryTheory.NatTrans.comp_app,
      mappingConeOrdinaryChainNatTrans_app_two,
      mappingConeOrdinaryChainNatTrans_app_two,
      show dgMappingConeMap (sq ≫ sq') =
          dgMappingConeMap sq ≫ dgMappingConeMap sq' by
        exact dgMappingConeFunctor.map_comp sq sq',
      directDGMorphism_comp]

/-- The ordinary component of a commutative square at one coherent-triangle vertex. -/
noncomputable def mappingConeCoherentSimplexComponent
    {f g : Arrow ComplexCategory} (sq : f ⟶ g)
    (i : CategoryTheory.SimplicialThickening (ULift (Fin 3))) :
    (mappingConeCoherentSimplex f.hom).obj i ⟶
      (mappingConeCoherentSimplex g.hom).obj i :=
  (OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans
    DirectDGSimplicialCategory (mappingConeOrdinaryChainNatTrans sq)).componentHom i

@[simp]
theorem mappingConeCoherentSimplexComponent_zero
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    mappingConeCoherentSimplexComponent sq triangleZero = directDGMorphism sq.left := by
  simp only [mappingConeCoherentSimplexComponent,
    OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    mappingConeOrdinaryChainNatTrans_app_zero]
  change (eHomEquiv SSet).symm
      (CategoryTheory.ForgetEnrichment.homTo SSet
        (show (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.left) :
            CategoryTheory.ForgetEnrichment SSet DirectDGSimplicialCategory) ⟶
          CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.left) from
            directDGMorphism sq.left)) = directDGMorphism sq.left
  rw [show CategoryTheory.ForgetEnrichment.homTo SSet
      (show (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.left) :
          CategoryTheory.ForgetEnrichment SSet DirectDGSimplicialCategory) ⟶
        CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.left) from
          directDGMorphism sq.left) =
      @eHomEquiv SSet _ _ DirectDGSimplicialCategory _ _
        (CategoryTheory.ForgetEnrichment.to SSet
          (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.left)))
        (CategoryTheory.ForgetEnrichment.to SSet
          (CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.left)))
        (show CategoryTheory.ForgetEnrichment.to SSet
              (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.left)) ⟶
            CategoryTheory.ForgetEnrichment.to SSet
              (CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.left)) from
          directDGMorphism sq.left) by rfl]
  exact Equiv.symm_apply_apply _ _

@[simp]
theorem mappingConeCoherentSimplexComponent_one
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    mappingConeCoherentSimplexComponent sq triangleOne = directDGMorphism sq.right := by
  simp only [mappingConeCoherentSimplexComponent,
    OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    mappingConeOrdinaryChainNatTrans_app_one]
  change (eHomEquiv SSet).symm
      (CategoryTheory.ForgetEnrichment.homTo SSet
        (show (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.right) :
            CategoryTheory.ForgetEnrichment SSet DirectDGSimplicialCategory) ⟶
          CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.right) from
            directDGMorphism sq.right)) = directDGMorphism sq.right
  rw [show CategoryTheory.ForgetEnrichment.homTo SSet
      (show (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.right) :
          CategoryTheory.ForgetEnrichment SSet DirectDGSimplicialCategory) ⟶
        CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.right) from
          directDGMorphism sq.right) =
      @eHomEquiv SSet _ _ DirectDGSimplicialCategory _ _
        (CategoryTheory.ForgetEnrichment.to SSet
          (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.right)))
        (CategoryTheory.ForgetEnrichment.to SSet
          (CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.right)))
        (show CategoryTheory.ForgetEnrichment.to SSet
              (CategoryTheory.ForgetEnrichment.of SSet (directDGObject f.right)) ⟶
            CategoryTheory.ForgetEnrichment.to SSet
              (CategoryTheory.ForgetEnrichment.of SSet (directDGObject g.right)) from
          directDGMorphism sq.right) by rfl]
  exact Equiv.symm_apply_apply _ _

@[simp]
theorem mappingConeCoherentSimplexComponent_two
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    mappingConeCoherentSimplexComponent sq triangleTwo =
      directDGMorphism (dgMappingConeMap sq) := by
  simp only [mappingConeCoherentSimplexComponent,
    OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    mappingConeOrdinaryChainNatTrans_app_two]
  change (eHomEquiv SSet).symm
      (CategoryTheory.ForgetEnrichment.homTo SSet
        (show (CategoryTheory.ForgetEnrichment.of SSet
              (directDGObject (dgMappingConeObject f.hom)) :
            CategoryTheory.ForgetEnrichment SSet DirectDGSimplicialCategory) ⟶
          CategoryTheory.ForgetEnrichment.of SSet
            (directDGObject (dgMappingConeObject g.hom)) from
              directDGMorphism (dgMappingConeMap sq))) =
        directDGMorphism (dgMappingConeMap sq)
  rw [show CategoryTheory.ForgetEnrichment.homTo SSet
      (show (CategoryTheory.ForgetEnrichment.of SSet
            (directDGObject (dgMappingConeObject f.hom)) :
          CategoryTheory.ForgetEnrichment SSet DirectDGSimplicialCategory) ⟶
        CategoryTheory.ForgetEnrichment.of SSet
          (directDGObject (dgMappingConeObject g.hom)) from
            directDGMorphism (dgMappingConeMap sq)) =
      @eHomEquiv SSet _ _ DirectDGSimplicialCategory _ _
        (CategoryTheory.ForgetEnrichment.to SSet
          (CategoryTheory.ForgetEnrichment.of SSet
            (directDGObject (dgMappingConeObject f.hom))))
        (CategoryTheory.ForgetEnrichment.to SSet
          (CategoryTheory.ForgetEnrichment.of SSet
            (directDGObject (dgMappingConeObject g.hom))))
        (show CategoryTheory.ForgetEnrichment.to SSet
              (CategoryTheory.ForgetEnrichment.of SSet
                (directDGObject (dgMappingConeObject f.hom))) ⟶
            CategoryTheory.ForgetEnrichment.to SSet
              (CategoryTheory.ForgetEnrichment.of SSet
                (directDGObject (dgMappingConeObject g.hom))) from
          directDGMorphism (dgMappingConeMap sq)) by rfl]
  exact Equiv.symm_apply_apply _ _

/-- Away from the long edge, coherent cone naturality is the locally constant chain
naturality. -/
theorem mappingConeCoherentSimplexComponent_naturality_of_not_special
    {f g : Arrow ComplexCategory} (sq : f ⟶ g)
    (i j : CategoryTheory.SimplicialThickening (ULift (Fin 3)))
    (hspecial : ¬ (i = triangleZero ∧ j = triangleTwo)) :
    (mappingConeCoherentSimplex f.hom).map i j ≫
        eHomWhiskerLeft SSet ((mappingConeCoherentSimplex f.hom).obj i)
          (mappingConeCoherentSimplexComponent sq j) =
      (mappingConeCoherentSimplex g.hom).map i j ≫
        eHomWhiskerRight SSet (mappingConeCoherentSimplexComponent sq i)
          ((mappingConeCoherentSimplex g.hom).obj j) := by
  let α := OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans
    DirectDGSimplicialCategory (mappingConeOrdinaryChainNatTrans sq)
  change mappingConeTriangleMap f.hom i j ≫
        eHomWhiskerLeft SSet
          ((mappingConeLocallyConstantSimplex f.hom).obj i) (α.componentHom j) =
      mappingConeTriangleMap g.hom i j ≫
        eHomWhiskerRight SSet (α.componentHom i)
          ((mappingConeLocallyConstantSimplex g.hom).obj j)
  simp only [mappingConeTriangleMap, dif_neg hspecial]
  exact α.map_eHomWhiskerLeft_eq_map_eHomWhiskerRight i j

set_option maxHeartbeats 1000000 in
-- The long edge unfolds both transported enrichments after the concrete endpoints are fixed.
/-- Naturality of the distinguished long edge in the coherent mapping-cone simplex. -/
theorem mappingConeCoherentSimplexComponent_naturality_special
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    (mappingConeCoherentSimplex f.hom).map triangleZero triangleTwo ≫
        eHomWhiskerLeft SSet
          ((mappingConeCoherentSimplex f.hom).obj triangleZero)
          (mappingConeCoherentSimplexComponent sq triangleTwo) =
      (mappingConeCoherentSimplex g.hom).map triangleZero triangleTwo ≫
        eHomWhiskerRight SSet
          (mappingConeCoherentSimplexComponent sq triangleZero)
          ((mappingConeCoherentSimplex g.hom).obj triangleTwo) := by
  rw [mappingConeCoherentSimplexComponent_two,
    mappingConeCoherentSimplexComponent_zero]
  change mappingConeTriangleMap f.hom triangleZero triangleTwo ≫
        eHomWhiskerLeft SSet (directDGObject f.left)
          (directDGMorphism (dgMappingConeMap sq)) =
      mappingConeTriangleMap g.hom triangleZero triangleTwo ≫
        eHomWhiskerRight SSet (directDGMorphism sq.left)
          (directDGObject (dgMappingConeObject g.hom))
  rw [mappingConeTriangleMap_zero_two, mappingConeTriangleMap_zero_two]
  rw [directDG_eHomWhiskerLeft_eq_postcomposition,
    directDG_eHomWhiskerRight_eq_precomposition]
  exact trianglePathCoherenceMap_naturality sq

theorem mappingConeCoherentSimplexComponent_naturality
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    ∀ i j : CategoryTheory.SimplicialThickening (ULift (Fin 3)),
      (mappingConeCoherentSimplex f.hom).map i j ≫
          eHomWhiskerLeft SSet ((mappingConeCoherentSimplex f.hom).obj i)
            (mappingConeCoherentSimplexComponent sq j) =
        (mappingConeCoherentSimplex g.hom).map i j ≫
          eHomWhiskerRight SSet (mappingConeCoherentSimplexComponent sq i)
            ((mappingConeCoherentSimplex g.hom).obj j) := by
  intro i j
  by_cases hspecial : i = triangleZero ∧ j = triangleTwo
  · rcases hspecial with ⟨rfl, rfl⟩
    exact mappingConeCoherentSimplexComponent_naturality_special sq
  · exact mappingConeCoherentSimplexComponent_naturality_of_not_special
      sq i j hspecial

/-- A commutative square acts functorially on the full coherent mapping-cone two-simplex. -/
noncomputable def mappingConeCoherentSimplexNatTrans
    {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    SSetUnitGradedNatTrans
      (mappingConeCoherentSimplex f.hom) (mappingConeCoherentSimplex g.hom) :=
  SSetUnitGradedNatTrans.ofComponentHom
    (mappingConeCoherentSimplexComponent sq)
    (mappingConeCoherentSimplexComponent_naturality sq)

@[simp]
theorem mappingConeCoherentSimplexNatTrans_id (f : Arrow ComplexCategory) :
    mappingConeCoherentSimplexNatTrans (𝟙 f) =
      SSetUnitGradedNatTrans.id (mappingConeCoherentSimplex f.hom) := by
  apply GradedNatTrans.ext
  funext i
  apply (eHomEquiv SSet).symm.injective
  change mappingConeCoherentSimplexComponent (𝟙 f) i =
    (SSetUnitGradedNatTrans.id
      (mappingConeCoherentSimplex f.hom)).componentHom i
  unfold mappingConeCoherentSimplexComponent
  rw [mappingConeOrdinaryChainNatTrans_id,
    OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    SSetUnitGradedNatTrans.componentHom_id]
  change (CategoryTheory.ForgetEnrichment.equivFunctor SSet
      DirectDGSimplicialCategory).map
        (𝟙 ((mappingConeOrdinaryChain f.hom).obj i.as.down)) =
    𝟙 ((CategoryTheory.ForgetEnrichment.equivFunctor SSet
      DirectDGSimplicialCategory).obj
        ((mappingConeOrdinaryChain f.hom).obj i.as.down))
  exact (CategoryTheory.ForgetEnrichment.equivFunctor SSet
    DirectDGSimplicialCategory).map_id _

@[simp]
theorem mappingConeCoherentSimplexNatTrans_comp
    {f g h : Arrow ComplexCategory} (sq : f ⟶ g) (sq' : g ⟶ h) :
    mappingConeCoherentSimplexNatTrans (sq ≫ sq') =
      SSetUnitGradedNatTrans.comp
        (mappingConeCoherentSimplexNatTrans sq)
        (mappingConeCoherentSimplexNatTrans sq') := by
  apply GradedNatTrans.ext
  funext i
  apply (eHomEquiv SSet).symm.injective
  change mappingConeCoherentSimplexComponent (sq ≫ sq') i =
    (SSetUnitGradedNatTrans.comp
      (mappingConeCoherentSimplexNatTrans sq)
      (mappingConeCoherentSimplexNatTrans sq')).componentHom i
  unfold mappingConeCoherentSimplexComponent
  rw [mappingConeOrdinaryChainNatTrans_comp,
    OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    SSetUnitGradedNatTrans.componentHom_comp]
  unfold mappingConeCoherentSimplexNatTrans
  rw [SSetUnitGradedNatTrans.componentHom_ofComponentHom,
    SSetUnitGradedNatTrans.componentHom_ofComponentHom]
  unfold mappingConeCoherentSimplexComponent
  rw [OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans_componentHom,
    OrdinaryToSimplicialNerve.coherentSimplexOfChainUnitGradedNatTrans_componentHom]
  exact (CategoryTheory.ForgetEnrichment.equivFunctor SSet
    DirectDGSimplicialCategory).map_comp _ _

/-- The coherent mapping-cone two-simplex varies functorially with its input arrow. -/
noncomputable def mappingConeCoherentSimplexFunctor :
    Arrow ComplexCategory ⥤
      SSetGradedEnrichedFunctorCategory
        (CategoryTheory.SimplicialThickening (ULift (Fin 3)))
        DirectDGSimplicialCategory where
  obj f := mappingConeCoherentSimplex f.hom
  map sq := mappingConeCoherentSimplexNatTrans sq
  map_id f := mappingConeCoherentSimplexNatTrans_id f
  map_comp sq sq' := mappingConeCoherentSimplexNatTrans_comp sq sq'

end MappingConeTriangle

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
