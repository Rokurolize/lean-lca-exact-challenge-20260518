/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.BicategoricalEquivalenceInternalHom
import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceEdges
import LeanLCAExactChallenge.Infinity.QuasicategoryAllEdgesKan
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-! # Internal Homs out of categorical deformation retracts

An ordinary categorical retraction with a natural transformation from the identity to the
associated closure operator induces an adjoint equivalence on functor quasicategories with a
Kan target.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalClosed Opposite Simplicial
open scoped Bicategory MonoidalCategory MonoidalClosed

local instance nerveRetractQCatHomCategory (X Y : SSet.QCat.{u}) : Category (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- A natural transformation gives an edge between the corresponding vertices of the
categorical-nerve internal Hom. -/
noncomputable def nerveNatTransInternalHomEdge
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {F G : C ⥤ D} (α : F ⟶ G) :
    SSet.Edge
      (SSet.unitHomEquiv
        ((ihom (CategoryTheory.nerve C)).obj (CategoryTheory.nerve D))
        (MonoidalClosed.curry' (CategoryTheory.nerveMap F)))
      (SSet.unitHomEquiv
        ((ihom (CategoryTheory.nerve C)).obj (CategoryTheory.nerve D))
        (MonoidalClosed.curry' (CategoryTheory.nerveMap G))) := by
  let e := (CategoryTheory.nerve.edgeMk α).map
    (nerveInternalHomIso (Cat.of C) (Cat.of D)).hom
  have desiredVertexMap (H : C ⥤ D) :
      internalHomVertexMap (CategoryTheory.nerve C) (CategoryTheory.nerve D)
        (SSet.unitHomEquiv
          ((ihom (CategoryTheory.nerve C)).obj (CategoryTheory.nerve D))
          (MonoidalClosed.curry' (CategoryTheory.nerveMap H))) =
        CategoryTheory.nerveMap H := by
    unfold internalHomVertexMap
    change MonoidalClosed.uncurry'
      ((SSet.unitHomEquiv
        ((ihom (CategoryTheory.nerve C)).obj (CategoryTheory.nerve D))).symm
          (SSet.unitHomEquiv
            ((ihom (CategoryTheory.nerve C)).obj (CategoryTheory.nerve D))
            (MonoidalClosed.curry' (CategoryTheory.nerveMap H)))) = _
    rw [Equiv.symm_apply_apply]
    exact MonoidalClosed.uncurry'_curry' _
  have hF :
      (nerveInternalHomIso (Cat.of C) (Cat.of D)).hom.app (op ⦋0⦌)
          (CategoryTheory.nerveEquiv.symm F) =
        SSet.unitHomEquiv
          ((ihom (CategoryTheory.nerve C)).obj (CategoryTheory.nerve D))
          (MonoidalClosed.curry' (CategoryTheory.nerveMap F)) := by
    apply internalHomVertexMap_injective
    exact (nerveInternalHomIso_vertex_map (Cat.of C) (Cat.of D) F).trans
      (desiredVertexMap F).symm
  have hG :
      (nerveInternalHomIso (Cat.of C) (Cat.of D)).hom.app (op ⦋0⦌)
          (CategoryTheory.nerveEquiv.symm G) =
        SSet.unitHomEquiv
          ((ihom (CategoryTheory.nerve C)).obj (CategoryTheory.nerve D))
          (MonoidalClosed.curry' (CategoryTheory.nerveMap G)) := by
    apply internalHomVertexMap_injective
    exact (nerveInternalHomIso_vertex_map (Cat.of C) (Cat.of D) G).trans
      (desiredVertexMap G).symm
  exact SSet.Edge.castEndpoints hF.symm hG.symm e

set_option maxHeartbeats 800000 in
-- Normalizing the two nested internal-Hom transposes exceeds the default elaboration budget.
/-- Apply precomposition to the internal-Hom edge represented by an ordinary natural
transformation. -/
noncomputable def internalHomPrecompEdgeOfNerveNatTrans
    {C : Type u} [Category.{u} C] {F G : C ⥤ C} (α : F ⟶ G)
    (Q : SSet.{u}) :
    SSet.Edge
      (SSet.unitHomEquiv
        ((ihom ((ihom (CategoryTheory.nerve C)).obj Q)).obj
          ((ihom (CategoryTheory.nerve C)).obj Q))
        (MonoidalClosed.curry'
          (internalHomPrecomp (CategoryTheory.nerveMap F) Q)))
      (SSet.unitHomEquiv
        ((ihom ((ihom (CategoryTheory.nerve C)).obj Q)).obj
          ((ihom (CategoryTheory.nerve C)).obj Q))
        (MonoidalClosed.curry'
          (internalHomPrecomp (CategoryTheory.nerveMap G) Q))) :=
  SSet.Edge.castEndpoints
    (internalHomPrecompositionAction_vertex
      (CategoryTheory.nerve C) Q (CategoryTheory.nerveMap F)).symm
    (internalHomPrecompositionAction_vertex
      (CategoryTheory.nerve C) Q (CategoryTheory.nerveMap G)).symm
    ((nerveNatTransInternalHomEdge α).map
      (internalHomPrecompositionAction (CategoryTheory.nerve C) Q))

/-- With a Kan target, precomposition sends every ordinary natural transformation to an
equivalence edge. -/
theorem internalHomPrecompEdgeOfNerveNatTrans_isEquivalence
    {C : Type u} [Category.{u} C] {F G : C ⥤ C} (α : F ⟶ G)
    (Q : SSet.{u}) [SSet.KanComplex Q] :
    EdgeIsEquivalence (internalHomPrecompEdgeOfNerveNatTrans α Q) := by
  apply edgeIsEquivalence_of_kan
    ((ihom ((ihom (CategoryTheory.nerve C)).obj Q)).obj
      ((ihom (CategoryTheory.nerve C)).obj Q))

set_option maxHeartbeats 800000 in
-- Elaborating the endpoint transports in the induced QCat `2`-cell exceeds the default budget.
/-- A natural transformation between endofunctors yields an invertible `2`-cell between the
induced precomposition maps whenever the target is Kan. -/
noncomputable def internalHomPrecompTwoIsoOfNerveNatTrans
    {C : Type u} [Category.{u} C] {F G : C ⥤ C} (α : F ⟶ G)
    (Q : SSet.{u}) [SSet.KanComplex Q] :
    (ObjectProperty.homMk
      (internalHomPrecomp (CategoryTheory.nerveMap F) Q) :
        internalHomQCat (CategoryTheory.nerve C) Q inferInstance ⟶
          internalHomQCat (CategoryTheory.nerve C) Q inferInstance) ≅
      ObjectProperty.homMk
        (internalHomPrecomp (CategoryTheory.nerveMap G) Q) :=
  twoIsoOfInternalHomEquivalenceEdge
    (internalHomPrecompEdgeOfNerveNatTrans α Q)
    (internalHomPrecompEdgeOfNerveNatTrans_isEquivalence α Q)

set_option maxHeartbeats 1200000 in
-- The assembled bicategorical unit and counit require a larger definitional-equality budget.
/-- Precomposition along an ordinary categorical deformation retract is an adjoint
equivalence of functor quasicategories with Kan target. -/
noncomputable def internalHomPrecompBicategoricalEquivalenceOfRetractNatTrans
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (i : C ⥤ D) (r : D ⥤ C) (hir : i ⋙ r = 𝟭 C)
    (η : 𝟭 D ⟶ r ⋙ i) (Q : SSet.{u}) [SSet.KanComplex Q] :
    Bicategory.Equivalence
      (internalHomQCat (CategoryTheory.nerve D) Q inferInstance)
      (internalHomQCat (CategoryTheory.nerve C) Q inferInstance) := by
  let HD := internalHomQCat (CategoryTheory.nerve D) Q inferInstance
  let HC := internalHomQCat (CategoryTheory.nerve C) Q inferInstance
  let p : HD ⟶ HC := ObjectProperty.homMk
    (internalHomPrecomp (CategoryTheory.nerveMap i) Q)
  let s : HC ⟶ HD := ObjectProperty.homMk
    (internalHomPrecomp (CategoryTheory.nerveMap r) Q)
  let preDId : HD ⟶ HD := ObjectProperty.homMk
    (internalHomPrecomp (CategoryTheory.nerveMap (𝟭 D)) Q)
  let preDComp : HD ⟶ HD := ObjectProperty.homMk
    (internalHomPrecomp (CategoryTheory.nerveMap (r ⋙ i)) Q)
  let preCId : HC ⟶ HC := ObjectProperty.homMk
    (internalHomPrecomp (CategoryTheory.nerveMap (𝟭 C)) Q)
  let preCComp : HC ⟶ HC := ObjectProperty.homMk
    (internalHomPrecomp (CategoryTheory.nerveMap (i ⋙ r)) Q)
  have hp_comp_s : p ≫ s = preDComp := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    change internalHomPrecomp (CategoryTheory.nerveMap i) Q ≫
        internalHomPrecomp (CategoryTheory.nerveMap r) Q =
      internalHomPrecomp (CategoryTheory.nerveMap (r ⋙ i)) Q
    rw [internalHomPrecomp_comp]
    rfl
  have hs_comp_p : s ≫ p = preCComp := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    change internalHomPrecomp (CategoryTheory.nerveMap r) Q ≫
        internalHomPrecomp (CategoryTheory.nerveMap i) Q =
      internalHomPrecomp (CategoryTheory.nerveMap (i ⋙ r)) Q
    rw [internalHomPrecomp_comp]
    rfl
  have hpreDId : preDId = 𝟙 HD := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    change internalHomPrecomp (CategoryTheory.nerveMap (𝟭 D)) Q = 𝟙 _
    have hnerve : CategoryTheory.nerveMap (𝟭 D) = 𝟙 (CategoryTheory.nerve D) := by
      ext U x
      rfl
    rw [hnerve]
    exact congrArg (fun F ↦ F.app Q) (MonoidalClosed.pre_id (CategoryTheory.nerve D))
  have hpreCId : preCId = 𝟙 HC := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    change internalHomPrecomp (CategoryTheory.nerveMap (𝟭 C)) Q = 𝟙 _
    have hnerve : CategoryTheory.nerveMap (𝟭 C) = 𝟙 (CategoryTheory.nerve C) := by
      ext U x
      rfl
    rw [hnerve]
    exact congrArg (fun F ↦ F.app Q) (MonoidalClosed.pre_id (CategoryTheory.nerve C))
  have hpreCComp : preCComp = preCId := by
    dsimp only [preCComp, preCId]
    rw [hir]
  let unitPreIso : preDId ≅ preDComp :=
    internalHomPrecompTwoIsoOfNerveNatTrans η Q
  let unit : 𝟙 HD ≅ p ≫ s :=
    (eqToIso hpreDId.symm).trans
      (unitPreIso.trans (eqToIso hp_comp_s.symm))
  let counit : s ≫ p ≅ 𝟙 HC :=
    (eqToIso hs_comp_p).trans
      ((eqToIso hpreCComp).trans (eqToIso hpreCId))
  exact Bicategory.Equivalence.mkOfAdjointifyCounit unit counit

end LeanLCAExactChallenge.Infinity
