/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGStableConstructions
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Functorial mapping cones in the bounded DG carrier

The mapping cone construction is promoted from its objectwise form to a functor on the
ordinary arrow category of bounded complexes. The canonical inclusion of the target into the
mapping cone is recorded as a natural transformation.

This is the ordinary functorial input required before the cone construction can be promoted to
an enriched corner extension.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open CategoryTheory

/-- A commutative square of bounded complexes induces the corresponding morphism of mapping
cones. -/
noncomputable def dgMappingConeMap {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    dgMappingConeObject f.hom ⟶ dgMappingConeObject g.hom :=
  (boundedCochainComplex MetrizableLCA.{0}).ι.preimage
    (CochainComplex.mappingCone.map
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f.hom)
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map g.hom)
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map sq.left)
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map sq.right)
      (by
        simpa only [Functor.map_comp] using
          congrArg ((boundedCochainComplex MetrizableLCA.{0}).ι.map) (Arrow.w sq).symm))

/-- The bounded inclusion sends the functorial cone map to the standard map of mapping cones. -/
@[simp]
theorem boundedInclusion_map_dgMappingConeMap {f g : Arrow ComplexCategory}
    (sq : f ⟶ g) :
    (boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeMap sq) =
      CochainComplex.mappingCone.map
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f.hom)
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map g.hom)
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map sq.left)
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map sq.right)
        (by
          simpa only [Functor.map_comp] using
            congrArg ((boundedCochainComplex MetrizableLCA.{0}).ι.map) (Arrow.w sq).symm) :=
  Functor.map_preimage _ _

set_option maxHeartbeats 1000000 in
-- Eliminating the dependent commutativity proofs in the two functor laws needs extra budget.
/-- Mapping cones form a functor on the ordinary arrow category of bounded complexes. -/
noncomputable def dgMappingConeFunctor : Arrow ComplexCategory ⥤ ComplexCategory where
  obj f := dgMappingConeObject f.hom
  map sq := dgMappingConeMap sq
  map_id f := by
    apply (boundedCochainComplex MetrizableLCA.{0}).ι.map_injective
    calc
      (boundedCochainComplex MetrizableLCA.{0}).ι.map
          (dgMappingConeMap (𝟙 f)) =
        CochainComplex.mappingCone.map
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f.hom)
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f.hom)
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (Arrow.Hom.left (𝟙 f)))
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (Arrow.Hom.right (𝟙 f))) _ :=
        boundedInclusion_map_dgMappingConeMap (𝟙 f)
      _ = 𝟙 ((boundedCochainComplex MetrizableLCA.{0}).ι.obj
          (dgMappingConeObject f.hom)) := by
        have hl := (boundedCochainComplex MetrizableLCA.{0}).ι.map_id f.left
        have hr := (boundedCochainComplex MetrizableLCA.{0}).ι.map_id f.right
        cases hl
        cases hr
        exact CochainComplex.mappingCone.map_id _
      _ = (boundedCochainComplex MetrizableLCA.{0}).ι.map
          (𝟙 (dgMappingConeObject f.hom)) :=
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map_id _).symm
  map_comp {X Y Z} sq sq' := by
    apply (boundedCochainComplex MetrizableLCA.{0}).ι.map_injective
    let φ₁ := (boundedCochainComplex MetrizableLCA.{0}).ι.map X.hom
    let φ₂ := (boundedCochainComplex MetrizableLCA.{0}).ι.map Y.hom
    let φ₃ := (boundedCochainComplex MetrizableLCA.{0}).ι.map Z.hom
    let a := (boundedCochainComplex MetrizableLCA.{0}).ι.map sq.left
    let b := (boundedCochainComplex MetrizableLCA.{0}).ι.map sq.right
    let a' := (boundedCochainComplex MetrizableLCA.{0}).ι.map sq'.left
    let b' := (boundedCochainComplex MetrizableLCA.{0}).ι.map sq'.right
    let comm : φ₁ ≫ b = a ≫ φ₂ := by
      simpa only [φ₁, φ₂, a, b, Functor.map_comp] using
        congrArg ((boundedCochainComplex MetrizableLCA.{0}).ι.map) (Arrow.w sq).symm
    let comm' : φ₂ ≫ b' = a' ≫ φ₃ := by
      simpa only [φ₂, φ₃, a', b', Functor.map_comp] using
        congrArg ((boundedCochainComplex MetrizableLCA.{0}).ι.map) (Arrow.w sq').symm
    calc
      (boundedCochainComplex MetrizableLCA.{0}).ι.map
          (dgMappingConeMap (sq ≫ sq')) =
        CochainComplex.mappingCone.map
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map X.hom)
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map Z.hom)
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (Arrow.Hom.left (sq ≫ sq')))
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (Arrow.Hom.right (sq ≫ sq'))) _ :=
        boundedInclusion_map_dgMappingConeMap (sq ≫ sq')
      _ = CochainComplex.mappingCone.map φ₁ φ₂ a b comm ≫
          CochainComplex.mappingCone.map φ₂ φ₃ a' b' comm' := by
        have hl : (boundedCochainComplex MetrizableLCA.{0}).ι.map
            (Arrow.Hom.left (sq ≫ sq')) = a ≫ a' := by
          rw [Arrow.comp_left, Functor.map_comp]
        have hr : (boundedCochainComplex MetrizableLCA.{0}).ι.map
            (Arrow.Hom.right (sq ≫ sq')) = b ≫ b' := by
          rw [Arrow.comp_right, Functor.map_comp]
        cases hl
        cases hr
        exact CochainComplex.mappingCone.map_comp φ₁ φ₂ φ₃ a b comm a' b' comm'
      _ = (boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeMap sq) ≫
          (boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeMap sq') := by
        rw [boundedInclusion_map_dgMappingConeMap,
          boundedInclusion_map_dgMappingConeMap]
      _ = (boundedCochainComplex MetrizableLCA.{0}).ι.map
          (dgMappingConeMap sq ≫ dgMappingConeMap sq') :=
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map_comp _ _).symm

@[simp]
theorem dgMappingConeFunctor_obj (f : Arrow ComplexCategory) :
    dgMappingConeFunctor.obj f = dgMappingConeObject f.hom :=
  rfl

@[simp]
theorem dgMappingConeFunctor_map {f g : Arrow ComplexCategory} (sq : f ⟶ g) :
    dgMappingConeFunctor.map sq = dgMappingConeMap sq :=
  rfl

/-- The canonical target inclusion is natural in a commutative square of arrows. -/
noncomputable def dgMappingConeInrNatTrans :
    (Arrow.rightFunc : Arrow ComplexCategory ⥤ ComplexCategory) ⟶
      dgMappingConeFunctor where
  app f := dgMappingConeInr f.hom
  naturality {f g} sq := by
    change sq.right ≫ dgMappingConeInr g.hom =
      dgMappingConeInr f.hom ≫ dgMappingConeMap sq
    symm
    apply (boundedCochainComplex MetrizableLCA.{0}).ι.map_injective
    rw [Functor.map_comp, Functor.map_comp,
      boundedInclusion_map_dgMappingConeInr,
      boundedInclusion_map_dgMappingConeMap,
      boundedInclusion_map_dgMappingConeInr]
    rw [CochainComplex.mappingCone.map_eq_mapOfHomotopy,
      CochainComplex.mappingCone.triangleMapOfHomotopy_comm₂]

@[simp]
theorem dgMappingConeInrNatTrans_app (f : Arrow ComplexCategory) :
    dgMappingConeInrNatTrans.app f = dgMappingConeInr f.hom :=
  rfl

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
