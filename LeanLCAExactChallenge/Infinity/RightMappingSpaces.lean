/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaces
import LeanLCAExactChallenge.Infinity.JoyalSlices
import LeanLCAExactChallenge.Infinity.QuasicategoryAllEdgesKan

/-! # Right mapping spaces of quasicategories

The right mapping space from `x` to `y` is the fiber over `x` of the over-slice projection at
`y`. Its projection to the point is a right fibration, so the fiber is a quasicategory. Every
edge maps to an identity edge in the point and is therefore an equivalence, which upgrades the
fiber to a Kan complex.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-- The left mapping space from `x` to `y`, modeled as the fiber of the under-slice
projection over `y`. -/
abbrev leftMappingSpace (Q : SSet.{u}) (x y : Q _⦋0⦌) : SSet.{u} :=
  pullback (underSliceProjection Q x) (endpointVertex Q y)

/-- The left mapping space includes in the under-slice at its source. -/
def leftMappingSpaceToUnderSlice (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    leftMappingSpace Q x y ⟶ underSlice Q x :=
  pullback.fst (underSliceProjection Q x) (endpointVertex Q y)

/-- The left mapping space projects to the terminal parameter simplex. -/
def leftMappingSpaceToPoint (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    leftMappingSpace Q x y ⟶ (Δ[0] : SSet.{u}) :=
  pullback.snd (underSliceProjection Q x) (endpointVertex Q y)

@[reassoc]
theorem leftMappingSpace_condition (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    leftMappingSpaceToUnderSlice Q x y ≫ underSliceProjection Q x =
      leftMappingSpaceToPoint Q x y ≫ endpointVertex Q y :=
  pullback.condition

noncomputable instance leftMappingSpaceToPoint_leftFibration
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌) :
    LeftFibration (leftMappingSpaceToPoint Q x y) := by
  dsimp only [leftMappingSpaceToPoint]
  infer_instance

/-- The right mapping space from `x` to `y`, modeled as the fiber of the over-slice
projection over `x`. -/
abbrev rightMappingSpace (Q : SSet.{u}) (x y : Q _⦋0⦌) : SSet.{u} :=
  pullback (overSliceProjection Q y) (endpointVertex Q x)

/-- The right mapping space includes in the over-slice at its target. -/
def rightMappingSpaceToOverSlice (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    rightMappingSpace Q x y ⟶ overSlice Q y :=
  pullback.fst (overSliceProjection Q y) (endpointVertex Q x)

/-- The right mapping space projects to the terminal parameter simplex. -/
def rightMappingSpaceToPoint (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    rightMappingSpace Q x y ⟶ (Δ[0] : SSet.{u}) :=
  pullback.snd (overSliceProjection Q y) (endpointVertex Q x)

@[reassoc]
theorem rightMappingSpace_condition (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    rightMappingSpaceToOverSlice Q x y ≫ overSliceProjection Q y =
      rightMappingSpaceToPoint Q x y ≫ endpointVertex Q x :=
  pullback.condition

noncomputable instance rightMappingSpaceToPoint_rightFibration
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌) :
    RightFibration (rightMappingSpaceToPoint Q x y) := by
  dsimp only [rightMappingSpaceToPoint]
  infer_instance

private instance rightMappingDeltaZeroObjSubsingleton (U : SimplexCategoryᵒᵖ) :
    Subsingleton ((Δ[0] : SSet.{u}).obj U) where
  allEq a b := by
    apply SSet.stdSimplex.ext
    intro i
    exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

private instance deltaZero_quasicategory : SSet.Quasicategory (Δ[0] : SSet.{u}) := by
  apply SSet.quasicategory_of_filler
  intro n i σ h0 hn
  exact ⟨SSet.stdSimplex.objMk (OrderHom.const _ 0),
    fun j hj ↦ Subsingleton.elim _ _⟩

noncomputable instance leftMappingSpace_quasicategory
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌) :
    SSet.Quasicategory (leftMappingSpace Q x y) :=
  SSet.quasicategory_of_innerFibration (leftMappingSpaceToPoint Q x y)

/-- Every edge in a left mapping space is an equivalence, since its image in the point is
an identity and the left-fibration projection reflects equivalences. -/
theorem leftMappingSpace_edges_are_equivalences
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌)
    (s : (leftMappingSpace Q x y) _⦋1⦌) :
    EdgeIsEquivalence (SSet.Edge.mk' s) := by
  let p := leftMappingSpaceToPoint Q x y
  let source := (leftMappingSpace Q x y).map
    (SimplexCategory.δ (1 : Fin 2)).op s
  let target := (leftMappingSpace Q x y).map
    (SimplexCategory.δ (0 : Fin 2)).op s
  let e : SSet.Edge source target := SSet.Edge.mk' s
  apply LeftFibration.edgeIsEquivalence_of_map p e
  let eid := SSet.Edge.id (p.app (op ⦋0⦌) source)
  have hxy : p.app (op ⦋0⦌) source = p.app (op ⦋0⦌) target :=
    Subsingleton.elim _ _
  let eid' : SSet.Edge (p.app (op ⦋0⦌) source)
      (p.app (op ⦋0⦌) target) :=
    SSet.Edge.castEndpoints rfl hxy.symm eid
  have heq : e.map p = eid' := by
    apply SSet.Edge.ext
    exact Subsingleton.elim _ _
  rw [heq]
  exact (edgeIsEquivalence_id _).castEndpoints rfl hxy.symm

/-- Left mapping spaces of quasicategories are Kan complexes. -/
noncomputable instance leftMappingSpace_kanComplex
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌) :
    SSet.KanComplex (leftMappingSpace Q x y) :=
  quasicategory_all_edges_equivalences_kan _
    (leftMappingSpace_edges_are_equivalences Q x y)

noncomputable instance rightMappingSpace_quasicategory
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌) :
    SSet.Quasicategory (rightMappingSpace Q x y) :=
  SSet.quasicategory_of_innerFibration (rightMappingSpaceToPoint Q x y)

/-- Every edge in a right mapping space is an equivalence, since its image in the point is
an identity and the right-fibration projection reflects equivalences. -/
theorem rightMappingSpace_edges_are_equivalences
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌)
    (s : (rightMappingSpace Q x y) _⦋1⦌) :
    EdgeIsEquivalence (SSet.Edge.mk' s) := by
  let p := rightMappingSpaceToPoint Q x y
  let source := (rightMappingSpace Q x y).map
    (SimplexCategory.δ (1 : Fin 2)).op s
  let target := (rightMappingSpace Q x y).map
    (SimplexCategory.δ (0 : Fin 2)).op s
  let e : SSet.Edge source target := SSet.Edge.mk' s
  apply RightFibration.edgeIsEquivalence_of_map p e
  let eid := SSet.Edge.id (p.app (op ⦋0⦌) source)
  have hxy : p.app (op ⦋0⦌) source = p.app (op ⦋0⦌) target :=
    Subsingleton.elim _ _
  let eid' : SSet.Edge (p.app (op ⦋0⦌) source)
      (p.app (op ⦋0⦌) target) :=
    SSet.Edge.castEndpoints rfl hxy.symm eid
  have heq : e.map p = eid' := by
    apply SSet.Edge.ext
    exact Subsingleton.elim _ _
  rw [heq]
  exact (edgeIsEquivalence_id _).castEndpoints rfl hxy.symm

/-- Right mapping spaces of quasicategories are Kan complexes. -/
noncomputable instance rightMappingSpace_kanComplex
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌) :
    SSet.KanComplex (rightMappingSpace Q x y) :=
  quasicategory_all_edges_equivalences_kan _
    (rightMappingSpace_edges_are_equivalences Q x y)

end LeanLCAExactChallenge.Infinity
