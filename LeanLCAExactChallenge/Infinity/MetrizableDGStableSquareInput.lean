/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGMappingConeCoherentSimplex

/-!
# Dold--Kan input for stable square recognition

This file records the coherent one-simplex and boundary identities used by the stable-square
construction for the direct DG mapping-cone carrier.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace RawDirectDGCoherentNerveSquare

open CategoryTheory
open Opposite
open Simplicial
open scoped Simplicial

def coherenceChainOne (sq : RawDirectDGCoherentNerveSquare) :
    (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11).X 1 :=
  ((dgHomZModuleCochainComplex sq.obj00 sq.obj11).truncLE'XIso
    ComplexShape.embeddingDownNat rfl (by
      rw [show ComplexShape.embeddingDownNat.BoundaryLE 1 ↔ (1 : ℕ) = 0 by
        simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
          ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 1]
      omega)).inv sq.coherenceCochain

theorem coherenceChainOne_toRestriction (sq : RawDirectDGCoherentNerveSquare) :
    (((dgHomZModuleCochainComplex sq.obj00 sq.obj11).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 1).hom (coherenceChainOne sq) =
        sq.coherenceCochain := by
  let H := dgHomZModuleCochainComplex sq.obj00 sq.obj11
  have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE 1 := by
    rw [show ComplexShape.embeddingDownNat.BoundaryLE 1 ↔ (1 : ℕ) = 0 by
      simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
        ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 1]
    omega
  have hn' : ¬ ComplexShape.embeddingDownNat.op.BoundaryGE 1 := by
    simpa using hn
  change ((H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 1).hom
      ((H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).inv.hom
        sq.coherenceCochain) = sq.coherenceCochain
  rw [show (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 1 =
      (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).hom by
    dsimp [HomologicalComplex.truncLE'ToRestriction]
    rw [(H.op).restrictionToTruncGE'_f_eq_iso_hom_iso_inv
      ComplexShape.embeddingDownNat.op rfl hn']
    dsimp [HomologicalComplex.restrictionXIso,
      HomologicalComplex.truncLE'XIso]
    simp]
  exact ConcreteCategory.congr_hom
    (Iso.inv_hom_id_assoc (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn) (𝟙 _))
    sq.coherenceCochain

theorem coherenceChainOne_boundary_toRestriction
    (sq : RawDirectDGCoherentNerveSquare) :
    (((dgHomZModuleCochainComplex sq.obj00 sq.obj11).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0).hom
        (((dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11).d 1 0).hom
          (coherenceChainOne sq)) =
      CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (sq.top ≫ sq.right)) -
        CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (sq.left ≫ sq.bottom)) := by
  let H := dgHomZModuleCochainComplex sq.obj00 sq.obj11
  have hcomm := (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).comm 1 0
  have happ := ConcreteCategory.congr_hom hcomm (coherenceChainOne sq)
  change ((H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0).hom
      (((H.truncLE' ComplexShape.embeddingDownNat).d 1 0).hom
        (coherenceChainOne sq)) = _
  calc
    _ = ((H.restriction ComplexShape.embeddingDownNat).d 1 0).hom
        (((H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 1).hom
          (coherenceChainOne sq)) := by
      simpa only [ConcreteCategory.comp_apply] using happ.symm
    _ = CochainComplex.HomComplex.δ (-1) 0 sq.coherenceCochain := by
      rw [coherenceChainOne_toRestriction]
      rfl
    _ = _ := by
      rw [eq_sub_iff_add_eq]
      convert sq.coherence_delta.symm using 1 <;>
        simp only [Functor.map_comp] <;> rfl

def coherenceGammaOneSimplex (sq : RawDirectDGCoherentNerveSquare) :
    (dgMappingDirectZModuleSimplicialModule sq.obj00 sq.obj11).obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  doldKanGammaOneSimplex
    (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11) 0
    (coherenceChainOne sq)

def coherenceEdgeMap (sq : RawDirectDGCoherentNerveSquare) :
    (Δ[1] : SSet.{0}) ⟶ dgMappingDirectZModuleSSet sq.obj00 sq.obj11 :=
  SSet.yonedaEquiv.symm (coherenceGammaOneSimplex sq)

theorem coherenceGammaOneSimplex_delta_one
    (sq : RawDirectDGCoherentNerveSquare) :
    ((dgMappingDirectZModuleSimplicialModule sq.obj00 sq.obj11).δ 1).hom
        (coherenceGammaOneSimplex sq) = 0 := by
  change ((AlgebraicTopology.DoldKan.Γ₀.obj
    (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11)).δ 1).hom
      (doldKanGammaOneSimplex
        (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11) 0
        (coherenceChainOne sq)) = 0
  rw [doldKanGammaOneSimplex_delta_one]
  exact map_zero _

theorem coherenceGammaOneSimplex_delta_zero
    (sq : RawDirectDGCoherentNerveSquare) :
    ((dgMappingDirectZModuleSimplicialModule sq.obj00 sq.obj11).δ 0).hom
        (coherenceGammaOneSimplex sq) =
      ((AlgebraicTopology.DoldKan.Γ₀.splitting
        (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11)).ι 0).hom
          ((0 : (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11).X 0) +
            ((dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11).d 1 0).hom
              (coherenceChainOne sq)) := by
  change ((AlgebraicTopology.DoldKan.Γ₀.obj
    (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11)).δ 0).hom
      (doldKanGammaOneSimplex
        (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11) 0
        (coherenceChainOne sq)) = _
  exact doldKanGammaOneSimplex_delta_zero
    (dgMappingDirectZModuleChainComplex sq.obj00 sq.obj11) 0
    (coherenceChainOne sq)

theorem coherenceGammaOneSimplex_delta_zero_vertex
    (sq : RawDirectDGCoherentNerveSquare) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms sq.obj00 sq.obj11
        (((dgMappingDirectZModuleSimplicialModule sq.obj00 sq.obj11).δ 0).hom
          (coherenceGammaOneSimplex sq)) =
      sq.top ≫ sq.right - sq.left ≫ sq.bottom := by
  rw [coherenceGammaOneSimplex_delta_zero]
  rw [zero_add]
  rw [dgMappingDirectZModuleVerticesEquivBoundedMorphisms_splitting_zero]
  apply dgMappingDirectZModuleChainComplexZeroEquivBoundedHom_eq_of_toRestriction_eq
  simpa only [Functor.map_sub, CochainComplex.HomComplex.Cochain.ofHom_sub] using
    coherenceChainOne_boundary_toRestriction sq

theorem mappingConeRawCoherentSquare_coherenceGammaOneSimplex_delta_zero_vertex
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K (dgMappingConeObject f)
        (((dgMappingDirectZModuleSimplicialModule K (dgMappingConeObject f)).δ 0).hom
          (coherenceGammaOneSimplex
            (directDGMappingConeRawCoherentSquare f))) =
      f ≫ dgMappingConeInr f := by
  simpa [directDGMappingConeRawCoherentSquare] using
    coherenceGammaOneSimplex_delta_zero_vertex
      (directDGMappingConeRawCoherentSquare f)

end RawDirectDGCoherentNerveSquare
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
