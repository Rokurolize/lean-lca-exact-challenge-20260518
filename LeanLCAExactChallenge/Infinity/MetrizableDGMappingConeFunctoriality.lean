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
