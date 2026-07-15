/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.LCA.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Metrizable.Basic

/-!
Closed-subgroup quotients in the local `MetrizableLCA` category.

The quotient topology on an additive quotient group is already available in
mathlib.  The local point supplied here is the metrizable instance: the quotient
of a metrizable topological abelian group by a closed subgroup is first
countable and T₀, hence metrizable via the right uniformity of the quotient
topological group.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open Filter
open Topology
open Uniformity

namespace MetrizableLCA

variable (X : MetrizableLCA.{u}) (N : AddSubgroup X)

lemma quotient_metrizableSpace (hN : IsClosed (N : Set X)) :
    TopologicalSpace.MetrizableSpace (X ⧸ N) := by
  letI : UniformSpace (X ⧸ N) := IsTopologicalAddGroup.rightUniformSpace (X ⧸ N)
  haveI : IsUniformAddGroup (X ⧸ N) := isUniformAddGroup_of_addCommGroup
  haveI : (uniformity (X ⧸ N)).IsCountablyGenerated := by
    exact IsUniformAddGroup.uniformity_countably_generated
  infer_instance

/-- The quotient of a metrizable LCA group by a closed additive subgroup. -/
noncomputable def quotientObj (hN : IsClosed (N : Set X)) : MetrizableLCA.{u} where
  carrier := X ⧸ N
  locallyCompactSpace := by infer_instance
  metrizableSpace := quotient_metrizableSpace X N hN

/-- The canonical quotient morphism in `MetrizableLCA`. -/
noncomputable def quotientMap (hN : IsClosed (N : Set X)) :
    X ⟶ quotientObj X N hN where
  hom' :=
    { QuotientAddGroup.mk' N with
      continuous_toFun := QuotientAddGroup.continuous_mk }

@[simp]
lemma quotientMap_apply (hN : IsClosed (N : Set X)) (x : X) :
    quotientMap X N hN x = (x : X ⧸ N) :=
  rfl

lemma quotientMap_surjective (hN : IsClosed (N : Set X)) :
    Function.Surjective (quotientMap X N hN : X → quotientObj X N hN) :=
  QuotientAddGroup.mk'_surjective N

lemma quotientMap_openMap (hN : IsClosed (N : Set X)) :
    IsOpenMap (quotientMap X N hN : X → quotientObj X N hN) :=
  QuotientAddGroup.isOpenMap_coe

/-- A continuous additive homomorphism that vanishes on `N` descends to the quotient. -/
noncomputable def quotientLift {Y : MetrizableLCA.{u}} (hN : IsClosed (N : Set X))
    (φ : X ⟶ Y) (hφ : N ≤ φ.hom.toAddMonoidHom.ker) :
    quotientObj X N hN ⟶ Y where
  hom' :=
    { QuotientAddGroup.lift N φ.hom.toAddMonoidHom hφ with
      continuous_toFun := by
        change Continuous (QuotientAddGroup.lift N φ.hom.toAddMonoidHom hφ : X ⧸ N → Y)
        rw [← QuotientAddGroup.isOpenQuotientMap_mk.continuous_comp_iff]
        exact φ.hom.continuous }

@[simp]
lemma quotientLift_quotientMap {Y : MetrizableLCA.{u}} (hN : IsClosed (N : Set X))
    (φ : X ⟶ Y) (hφ : N ≤ φ.hom.toAddMonoidHom.ker) :
    quotientMap X N hN ≫ quotientLift X N hN φ hφ = φ := by
  ext x
  rfl

@[simp]
lemma quotientLift_apply_mk {Y : MetrizableLCA.{u}} (hN : IsClosed (N : Set X))
    (φ : X ⟶ Y) (hφ : N ≤ φ.hom.toAddMonoidHom.ker) (x : X) :
    quotientLift X N hN φ hφ (x : X ⧸ N) = φ x :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
