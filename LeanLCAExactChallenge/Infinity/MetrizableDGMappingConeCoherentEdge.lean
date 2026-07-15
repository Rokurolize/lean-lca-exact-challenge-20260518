/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
import LeanLCAExactChallenge.Infinity.MetrizableDGDoldKanEdge
import LeanLCAExactChallenge.Infinity.MetrizableDGStableConstructions
import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence

/-!
# The coherent Dold--Kan edge of a mapping-cone triangle

The long mapping object in the thickened triangle is `Δ[1]`.

Its edge is induced by the degree-minus-one mapping-cone cochain.

Both faces and the truncated boundary are computed explicitly.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory
open Opposite
open Simplicial
open scoped Simplicial

/-- Restriction determines a direct degree-zero element as a bounded morphism. -/
theorem dgMappingDirectZModuleChainComplexZeroEquivBoundedHom_eq_of_toRestriction_eq
    (K L : ComplexCategory) (x : (dgMappingDirectZModuleChainComplex K L).X 0)
    (g : K ⟶ L)
    (h : (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0).hom x =
        CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map g)) :
    dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L x = g := by
  let x' := (dgMappingZModuleChainComplexIsoDirect K L).inv.f 0 x
  have hx' : (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0 x' = x := by
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom
        (dgMappingZModuleChainComplexIsoDirect K L).inv_hom_id 0) x
  have hz := dgMappingZModuleZeroCochain_f_eq_boundedHom K L x'
  change dgMappingZModuleChainComplexZeroEquivBoundedHom K L x' = g
  apply (boundedCochainComplex MetrizableLCA.{0}).ι.map_injective
  apply HomologicalComplex.Hom.ext
  funext i
  rw [← hz i]
  change (dgMappingZModuleZeroCochain K L x').v i i (add_zero i) = _
  rw [dgMappingZModuleZeroCochain, hx']
  exact CochainComplex.HomComplex.Cochain.congr_v h i i (add_zero i)

/-- The degree-zero Dold--Kan summand has the expected bounded vertex. -/
theorem dgMappingDirectZModuleVerticesEquivBoundedMorphisms_splitting_zero
    (K L : ComplexCategory) (x : (dgMappingDirectZModuleChainComplex K L).X 0) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K L
        (((AlgebraicTopology.DoldKan.Γ₀.splitting
          (dgMappingDirectZModuleChainComplex K L)).ι 0).hom x) =
      dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L x := by
  change dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L
    ((zModuleDoldKanInverseZeroIso
      (dgMappingDirectZModuleChainComplex K L)).inv.hom
        (((AlgebraicTopology.DoldKan.Γ₀.splitting
          (dgMappingDirectZModuleChainComplex K L)).ι 0).hom x)) = _
  apply congrArg (dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L)
  let T := dgMappingDirectZModuleChainComplex K L
  have h := ConcreteCategory.congr_hom
    (zModuleDoldKanInverseZeroIso_inv_on_identity_summand T) x
  rw [← (AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan_inj_id 0]
  change ((zModuleDoldKanInverseZeroIso T).inv.hom
    (((AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan
      (op (SimplexCategory.mk 0))).inj
        (SimplicialObject.Splitting.IndexSet.id
          (op (SimplexCategory.mk 0))) x)) = x
  calc
    _ = (ConcreteCategory.hom (𝟙 (T.X 0))) x := h
    _ = x := rfl

namespace MappingConeTriangle

/-- The path category from vertex `0` to vertex `2` in the thickening of `Fin 3`. -/
abbrev TrianglePath : Type :=
  CategoryTheory.SimplicialThickening.Path
    (ULift.up (0 : Fin 3)) (ULift.up (2 : Fin 3))

/-- The unique possible interior vertex of a path from `0` to `2`. -/
abbrev TriangleInterior : Type :=
  Set.Ioo (ULift.up (0 : Fin 3)) (ULift.up (2 : Fin 3))

/-- The middle vertex as an element of the open interval from `0` to `2`. -/
def triangleInteriorOne : TriangleInterior := ⟨ULift.up 1, by decide⟩

instance triangleInteriorSubsingleton : Subsingleton TriangleInterior :=
  ⟨by
    intro x y
    apply Subtype.ext
    apply ULift.ext
    apply Fin.ext
    have hx := x.property
    have hy := y.property
    change 0 < x.val.down.val ∧ x.val.down.val < 2 at hx
    change 0 < y.val.down.val ∧ y.val.down.val < 2 at hy
    omega⟩

/-- Evaluation at the unique interior vertex identifies its bitvectors with `Fin 2`. -/
def triangleInteriorEvaluationOrderIso :
    (TriangleInterior → Fin 2) ≃o Fin 2 where
  toFun b := b triangleInteriorOne
  invFun n := fun _ ↦ n
  left_inv b := by
    funext x
    exact congrArg b (Subsingleton.elim triangleInteriorOne x)
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    constructor
    · intro h x
      cases Subsingleton.elim x triangleInteriorOne
      exact h
    · intro h
      exact h triangleInteriorOne

/-- A path from `0` to `2` is determined by whether it contains vertex `1`. -/
def trianglePathOrderIso : TrianglePath ≃o Fin 2 :=
  (CoherentNervePathFiltration.Path.thickPathBitvectorOrderIso
    (i := ULift.up (0 : Fin 3)) (j := ULift.up (2 : Fin 3)) (by decide)).trans
      triangleInteriorEvaluationOrderIso

/-- The categorical forward map from thick paths to the lifted ordered interval. -/
def trianglePathToFinFunctor : CategoryTheory.Functor TrianglePath (ULift (Fin 2)) where
  obj P := ULift.up (trianglePathOrderIso P)
  map {_ _} f := homOfLE (trianglePathOrderIso.monotone f.1.1.1)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The categorical inverse map from the lifted ordered interval to thick paths. -/
def finToTrianglePathFunctor : CategoryTheory.Functor (ULift (Fin 2)) TrianglePath where
  obj n := trianglePathOrderIso.symm n.down
  map {_ _} f := ⟨⟨⟨trianglePathOrderIso.symm.monotone (leOfHom f)⟩⟩⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The two path/interval functors compose to the identity on paths. -/
theorem trianglePathFunctors_comp :
    trianglePathToFinFunctor ⋙ finToTrianglePathFunctor =
      CategoryTheory.Functor.id TrianglePath := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun P ↦ trianglePathOrderIso.left_inv P)
    (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The two path/interval functors compose to the identity on the lifted interval. -/
theorem finTrianglePathFunctors_comp :
    finToTrianglePathFunctor ⋙ trianglePathToFinFunctor =
      CategoryTheory.Functor.id (ULift (Fin 2)) := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun n ↦ congrArg ULift.up (trianglePathOrderIso.right_inv n.down))
    (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The nerve of the `0`-to-`2` path category is the nerve of the lifted ordered interval. -/
def trianglePathNerveFinIso :
    CategoryTheory.nerve TrianglePath ≅ CategoryTheory.nerve (ULift (Fin 2)) where
  hom := CategoryTheory.nerveMap trianglePathToFinFunctor
  inv := CategoryTheory.nerveMap finToTrianglePathFunctor
  hom_inv_id := by
    change CategoryTheory.nerveFunctor.map trianglePathToFinFunctor.toCatHom ≫
      CategoryTheory.nerveFunctor.map finToTrianglePathFunctor.toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have h : trianglePathToFinFunctor.toCatHom ≫ finToTrianglePathFunctor.toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact trianglePathFunctors_comp
    rw [h, CategoryTheory.Functor.map_id]
    rfl
  inv_hom_id := by
    change CategoryTheory.nerveFunctor.map finToTrianglePathFunctor.toCatHom ≫
      CategoryTheory.nerveFunctor.map trianglePathToFinFunctor.toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have h : finToTrianglePathFunctor.toCatHom ≫ trianglePathToFinFunctor.toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact finTrianglePathFunctors_comp
    rw [h, CategoryTheory.Functor.map_id]
    rfl

/-- The `0`-to-`2` mapping object in the thickening of `Fin 3` is `Δ[1]`. -/
def trianglePathNerveIso :
    (Δ[1] : SSet.{0}) ≅ CategoryTheory.nerve TrianglePath :=
  (SSet.stdSimplex.isoNerve 1).trans trianglePathNerveFinIso.symm

/-- The degree-minus-one cone inclusion transported into degree one of the truncated direct Hom. -/
def dgMappingConeCoherenceChainOne {K L : ComplexCategory} (f : K ⟶ L) :
    (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)).X 1 :=
  ((dgHomZModuleCochainComplex K (dgMappingConeObject f)).truncLE'XIso
    ComplexShape.embeddingDownNat rfl (by
      rw [show ComplexShape.embeddingDownNat.BoundaryLE 1 ↔ (1 : ℕ) = 0 by
        simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
          ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 1]
      omega)).inv (dgMappingConeInl f)

/-- Restricting the transported degree-one class recovers the cone inclusion. -/
theorem dgMappingConeCoherenceChainOne_toRestriction
    {K L : ComplexCategory} (f : K ⟶ L) :
    (((dgHomZModuleCochainComplex K (dgMappingConeObject f)).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 1).hom (dgMappingConeCoherenceChainOne f) =
        dgMappingConeInl f := by
  let H := dgHomZModuleCochainComplex K (dgMappingConeObject f)
  have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE 1 := by
    rw [show ComplexShape.embeddingDownNat.BoundaryLE 1 ↔ (1 : ℕ) = 0 by
      simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
        ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 1]
    omega
  have hn' : ¬ ComplexShape.embeddingDownNat.op.BoundaryGE 1 := by
    simpa using hn
  change ((H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 1).hom
      ((H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).inv.hom
        (dgMappingConeInl f)) = dgMappingConeInl f
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
    (dgMappingConeInl f)

/-- The boundary of the transported class restricts to the cone-triangle composite. -/
theorem dgMappingConeCoherenceChainOne_boundary_toRestriction
    {K L : ComplexCategory} (f : K ⟶ L) :
    (((dgHomZModuleCochainComplex K (dgMappingConeObject f)).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0).hom
        (((dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)).d 1 0).hom
          (dgMappingConeCoherenceChainOne f)) =
      CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map
          (f ≫ dgMappingConeInr f)) := by
  let H := dgHomZModuleCochainComplex K (dgMappingConeObject f)
  have hcomm := (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).comm 1 0
  have happ := ConcreteCategory.congr_hom hcomm (dgMappingConeCoherenceChainOne f)
  change ((H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0).hom
      (((H.truncLE' ComplexShape.embeddingDownNat).d 1 0).hom
        (dgMappingConeCoherenceChainOne f)) = _
  calc
    _ = ((H.restriction ComplexShape.embeddingDownNat).d 1 0).hom
        (((H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 1).hom
          (dgMappingConeCoherenceChainOne f)) := by
      simpa only [ConcreteCategory.comp_apply] using happ.symm
    _ = CochainComplex.HomComplex.δ (-1) 0 (dgMappingConeInl f) := by
      rw [dgMappingConeCoherenceChainOne_toRestriction]
      rfl
    _ = _ := dgMappingConeInl_delta f

/-- The explicit Dold--Kan one-simplex induced by the mapping-cone nullhomotopy. -/
def dgMappingConeCoherenceGammaOneSimplex {K L : ComplexCategory} (f : K ⟶ L) :
    (dgMappingDirectZModuleSimplicialModule K (dgMappingConeObject f)).obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  doldKanGammaOneSimplex
    (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)) 0
    (dgMappingConeCoherenceChainOne f)

/-- The standard one-simplex mapped to the explicit mapping-cone Dold--Kan edge. -/
def dgMappingConeCoherenceEdgeMap {K L : ComplexCategory} (f : K ⟶ L) :
    (Δ[1] : SSet.{0}) ⟶ dgMappingDirectZModuleSSet K (dgMappingConeObject f) :=
  SSet.yonedaEquiv.symm (dgMappingConeCoherenceGammaOneSimplex f)

/-- The `0`-to-`2` thickening mapping object mapped to the cone coherence edge. -/
def trianglePathCoherenceMap {K L : ComplexCategory} (f : K ⟶ L) :
    CategoryTheory.nerve TrianglePath ⟶
      dgMappingDirectZModuleSSet K (dgMappingConeObject f) :=
  trianglePathNerveIso.inv ≫ dgMappingConeCoherenceEdgeMap f

/-- The initial face of the cone coherence edge is the zero vertex. -/
theorem dgMappingConeCoherenceGammaOneSimplex_delta_one
    {K L : ComplexCategory} (f : K ⟶ L) :
    ((dgMappingDirectZModuleSimplicialModule K (dgMappingConeObject f)).δ 1).hom
        (dgMappingConeCoherenceGammaOneSimplex f) = 0 := by
  change ((AlgebraicTopology.DoldKan.Γ₀.obj
    (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f))).δ 1).hom
      (doldKanGammaOneSimplex
        (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)) 0
        (dgMappingConeCoherenceChainOne f)) = 0
  rw [doldKanGammaOneSimplex_delta_one]
  exact map_zero _

/-- The final face of the cone coherence edge is the Dold--Kan image of its chain boundary. -/
theorem dgMappingConeCoherenceGammaOneSimplex_delta_zero
    {K L : ComplexCategory} (f : K ⟶ L) :
    ((dgMappingDirectZModuleSimplicialModule K (dgMappingConeObject f)).δ 0).hom
        (dgMappingConeCoherenceGammaOneSimplex f) =
      ((AlgebraicTopology.DoldKan.Γ₀.splitting
        (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f))).ι 0).hom
          ((0 : (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)).X 0) +
            ((dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)).d 1 0).hom
              (dgMappingConeCoherenceChainOne f)) := by
  change ((AlgebraicTopology.DoldKan.Γ₀.obj
    (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f))).δ 0).hom
      (doldKanGammaOneSimplex
        (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)) 0
        (dgMappingConeCoherenceChainOne f)) = _
  exact doldKanGammaOneSimplex_delta_zero
    (dgMappingDirectZModuleChainComplex K (dgMappingConeObject f)) 0
    (dgMappingConeCoherenceChainOne f)

/-- The final face represents the composite into the cone. -/
theorem dgMappingConeCoherenceGammaOneSimplex_delta_zero_vertex
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K (dgMappingConeObject f)
        (((dgMappingDirectZModuleSimplicialModule K (dgMappingConeObject f)).δ 0).hom
          (dgMappingConeCoherenceGammaOneSimplex f)) =
      f ≫ dgMappingConeInr f := by
  rw [dgMappingConeCoherenceGammaOneSimplex_delta_zero]
  simp only [zero_add]
  rw [dgMappingDirectZModuleVerticesEquivBoundedMorphisms_splitting_zero]
  apply dgMappingDirectZModuleChainComplexZeroEquivBoundedHom_eq_of_toRestriction_eq
  exact dgMappingConeCoherenceChainOne_boundary_toRestriction f

end MappingConeTriangle

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
