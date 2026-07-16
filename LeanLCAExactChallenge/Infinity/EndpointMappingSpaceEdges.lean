/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaces
import LeanLCAExactChallenge.Infinity.QuasicategoryAllEdgesKan
import LeanLCAExactChallenge.Infinity.JoyalSpecialOuterHornDuality
import LeanLCAExactChallenge.Infinity.JoyalParameterizedExtension
import LeanLCAExactChallenge.Infinity.InnerAnodyneMapping

/-! # Equivalence edges in strict endpoint mapping spaces -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.MorphismProperty Opposite Simplicial
open scoped MonoidalCategory MonoidalClosed

def transposeInternalHom {A B Q : SSet.{u}}
    (f : A ⟶ (ihom B).obj Q) : B ⟶ (ihom A).obj Q :=
  MonoidalClosed.curry ((β_ A B).hom ≫ MonoidalClosed.uncurry f)

lemma transposeInternalHom_pre {A B C Q : SSet.{u}}
    (i : C ⟶ B) (f : A ⟶ (ihom B).obj Q) :
    i ≫ transposeInternalHom f =
      transposeInternalHom (f ≫ (MonoidalClosed.pre i).app Q) := by
  apply MonoidalClosed.uncurry_injective
  unfold transposeInternalHom
  rw [MonoidalClosed.uncurry_natural_left]
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_pre_app]
  simp

lemma transposeInternalHom_comp {A B C Q : SSet.{u}}
    (i : C ⟶ A) (f : A ⟶ (ihom B).obj Q) :
    transposeInternalHom (i ≫ f) =
      transposeInternalHom f ≫ (MonoidalClosed.pre i).app Q := by
  apply MonoidalClosed.uncurry_injective
  unfold transposeInternalHom
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_pre_app]
  rw [MonoidalClosed.uncurry_natural_left]
  simp

lemma transposeInternalHom_transpose {A B Q : SSet.{u}}
    (f : A ⟶ (ihom B).obj Q) :
    transposeInternalHom (transposeInternalHom f) = f := by
  apply MonoidalClosed.uncurry_injective
  unfold transposeInternalHom
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  simp

lemma transposeInternalHom_injective {A B Q : SSet.{u}} :
    Function.Injective
      (transposeInternalHom :
        (A ⟶ (ihom B).obj Q) → (B ⟶ (ihom A).obj Q)) := by
  intro f g h
  have hT := congrArg transposeInternalHom h
  simpa only [transposeInternalHom_transpose] using hT

lemma internalHomVertexMap_injective {A Q : SSet.{u}} :
    Function.Injective (internalHomVertexMap A Q) := by
  intro v w h
  unfold internalHomVertexMap at h
  apply (SSet.unitHomEquiv ((ihom A).obj Q)).symm.injective
  exact MonoidalClosed.uncurry'_injective h

lemma internalHomVertexMap_constant {A Q : SSet.{u}}
    (z : Q _⦋0⦌) (v : A _⦋0⦌) :
    internalHomVertexMap (Δ[0] : SSet.{u}) Q
        ((CartesianMonoidalCategory.toUnit A ≫
          MonoidalClosed.curry' (endpointVertex Q z)).app (op ⦋0⦌) v) =
      endpointVertex Q z := by
  unfold internalHomVertexMap
  rw [parameterizedUnitHomEquiv_symm_natural]
  have hunit :
      (SSet.unitHomEquiv A).symm v ≫ CartesianMonoidalCategory.toUnit A =
        𝟙 (𝟙_ SSet.{u}) := Subsingleton.elim _ _
  rw [← Category.assoc, hunit, Category.id_comp,
    MonoidalClosed.uncurry'_curry']

def constantInternalHomFamily {A B Q : SSet.{u}} (f : B ⟶ Q) :
    B ⟶ (ihom A).obj Q :=
  MonoidalClosed.curry (CartesianMonoidalCategory.snd A B ≫ f)

lemma transposeInternalHom_constant_row {B D Q : SSet.{u}}
    (q : D ⟶ Q) (i : (Δ[0] : SSet.{u}) ⟶ D) (z : Q _⦋0⦌)
    (hi : i ≫ q = endpointVertex Q z) :
    transposeInternalHom
        (i ≫ constantInternalHomFamily (A := B) q) =
      CartesianMonoidalCategory.toUnit B ≫
        MonoidalClosed.curry' (endpointVertex Q z) := by
  apply MonoidalClosed.uncurry_injective
  unfold transposeInternalHom constantInternalHomFamily
  rw [MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  rw [MonoidalClosed.uncurry_natural_left]
  unfold MonoidalClosed.curry'
  rw [MonoidalClosed.uncurry_curry]
  ext U t
  exact congrFun (congrArg (fun f ↦ f.app U) hi) t.1

def evaluateZeroFamily {B Q : SSet.{u}}
    (f : B ⟶ (ihom (Δ[0] : SSet.{u})).obj Q) : B ⟶ Q :=
  (λ_ B).inv ≫ (parameterVertexMap 0 (0 : Fin 1) ▷ B) ≫
    MonoidalClosed.uncurry f

lemma evaluateZeroFamily_constant {B Q : SSet.{u}} (z : Q _⦋0⦌) :
    evaluateZeroFamily
        (CartesianMonoidalCategory.toUnit B ≫
          MonoidalClosed.curry' (endpointVertex Q z)) =
      SSet.const z := by
  unfold evaluateZeroFamily
  rw [MonoidalClosed.uncurry_natural_left]
  exact rfl

lemma yonedaEquiv_const_one {Q : SSet.{u}} (z : Q _⦋0⦌) :
    SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ Q) =
      (SSet.Edge.id z).edge := by
  change Q.map (⦋1⦌.const ⦋0⦌ 0).op z = Q.map (SimplexCategory.σ 0).op z
  have h : ⦋1⦌.const ⦋0⦌ 0 = SimplexCategory.σ 0 := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    fin_cases i <;> rfl
  rw [h]

lemma edgeAtParameterVertex_zero_braiding :
    edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) 1 (0 : Fin 2) ≫
      (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom =
        (λ_ (Δ[1] : SSet.{u})).inv ≫
        (parameterVertexMap.{u} 1 (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
  rw [edgeAtParameterVertex_id_factor]
  simp

lemma edgeAtParameterVertex_one_braiding :
    edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) 1 (1 : Fin 2) ≫
      (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom =
        (λ_ (Δ[1] : SSet.{u})).inv ≫
        (parameterVertexMap.{u} 1 (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) := by
  rw [edgeAtParameterVertex_id_factor]
  simp

set_option linter.flexible false in
lemma parameterVertexMap_zero_factor :
    parameterVertexMap.{u} 1 (0 : Fin 2) =
      parameterVertexMap.{u} 0 (0 : Fin 1) ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  apply (SSet.unitHomEquiv (Δ[1] : SSet.{u})).injective
  simp [parameterVertexMap, SSet.unitHomEquiv]
  apply SSet.stdSimplex.obj₀Equiv.injective
  rfl

set_option linter.flexible false in
lemma parameterVertexMap_one_factor :
    parameterVertexMap.{u} 1 (1 : Fin 2) =
      parameterVertexMap.{u} 0 (0 : Fin 1) ≫ SSet.stdSimplex.δ (0 : Fin 2) := by
  apply (SSet.unitHomEquiv (Δ[1] : SSet.{u})).injective
  simp [parameterVertexMap, SSet.unitHomEquiv]
  apply SSet.stdSimplex.obj₀Equiv.injective
  rfl

lemma transposeRowZero {Q : SSet.{u}}
    (a : (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj Q) :
    edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) 1 (0 : Fin 2) ≫
        (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry a =
      evaluateZeroFamily
        (a ≫ (MonoidalClosed.pre (SSet.stdSimplex.δ (1 : Fin 2))).app Q) := by
  unfold evaluateZeroFamily
  rw [← Category.assoc, edgeAtParameterVertex_zero_braiding]
  rw [parameterVertexMap_zero_factor]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [MonoidalClosed.uncurry_pre_app]

lemma transposeRowOne {Q : SSet.{u}}
    (a : (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj Q) :
    edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) 1 (1 : Fin 2) ≫
        (β_ (Δ[1] : SSet.{u}) (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry a =
      evaluateZeroFamily
        (a ≫ (MonoidalClosed.pre (SSet.stdSimplex.δ (0 : Fin 2))).app Q) := by
  unfold evaluateZeroFamily
  rw [← Category.assoc, edgeAtParameterVertex_one_braiding]
  rw [parameterVertexMap_one_factor]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [MonoidalClosed.uncurry_pre_app]

theorem endpointFiber_edges_are_equivalences
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌)
    (s : (endpointFiber Q x y) _⦋1⦌) :
    EdgeIsEquivalence (SSet.Edge.mk' s) := by
  let e : (Δ[1] : SSet.{u}) ⟶ endpointFiber Q x y := SSet.yonedaEquiv.symm s
  let a : (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj Q :=
    e ≫ pullback.snd (endpointPoint Q x y) (endpointEvaluation Q)
  let aT : (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj Q :=
    transposeInternalHom a
  have ha : a ≫ endpointEvaluation Q =
      CartesianMonoidalCategory.toUnit (Δ[1] : SSet.{u}) ≫ endpointPoint Q x y := by
    dsimp only [a]
    rw [Category.assoc, ← pullback.condition]
    rw [← Category.assoc]
    congr 1
  have hx := congrArg
    (fun f ↦ f ≫ CartesianMonoidalCategory.fst
      ((ihom (Δ[0] : SSet.{u})).obj Q) ((ihom (Δ[0] : SSet.{u})).obj Q)) ha
  have hy := congrArg
    (fun f ↦ f ≫ CartesianMonoidalCategory.snd
      ((ihom (Δ[0] : SSet.{u})).obj Q) ((ihom (Δ[0] : SSet.{u})).obj Q)) ha
  have hx' : a ≫ (MonoidalClosed.pre (SSet.stdSimplex.δ (1 : Fin 2))).app Q =
      CartesianMonoidalCategory.toUnit (Δ[1] : SSet.{u}) ≫
        MonoidalClosed.curry' (endpointVertex Q x) := by
    simpa [endpointEvaluation, endpointPoint] using hx
  have hy' : a ≫ (MonoidalClosed.pre (SSet.stdSimplex.δ (0 : Fin 2))).app Q =
      CartesianMonoidalCategory.toUnit (Δ[1] : SSet.{u}) ≫
        MonoidalClosed.curry' (endpointVertex Q y) := by
    simpa [endpointEvaluation, endpointPoint] using hy
  let parameterZero : (Δ[1] : SSet.{u}) _⦋0⦌ :=
    SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)
  let q : (Δ[1] : SSet.{u}) ⟶ Q :=
    internalHomVertexMap (Δ[1] : SSet.{u}) Q
      (a.app (op ⦋0⦌) parameterZero)
  have hqx : SSet.stdSimplex.δ (1 : Fin 2) ≫ q = endpointVertex Q x := by
    dsimp only [q]
    rw [← internalHomVertexMap_precomp]
    change internalHomVertexMap (Δ[0] : SSet.{u}) Q
      ((a ≫ (MonoidalClosed.pre (SSet.stdSimplex.δ (1 : Fin 2))).app Q).app
        (op ⦋0⦌) parameterZero) = endpointVertex Q x
    rw [hx']
    exact internalHomVertexMap_constant x parameterZero
  have hqy : SSet.stdSimplex.δ (0 : Fin 2) ≫ q = endpointVertex Q y := by
    dsimp only [q]
    rw [← internalHomVertexMap_precomp]
    change internalHomVertexMap (Δ[0] : SSet.{u}) Q
      ((a ≫ (MonoidalClosed.pre (SSet.stdSimplex.δ (0 : Fin 2))).app Q).app
        (op ⦋0⦌) parameterZero) = endpointVertex Q y
    rw [hy']
    exact internalHomVertexMap_constant y parameterZero
  have haT : ∀ v : Fin 2,
      EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
        (internalHomVertexMap (Δ[1] : SSet.{u}) Q
          (aT.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm v))))) := by
    intro v
    fin_cases v
    · have hmap : internalHomVertexMap (Δ[1] : SSet.{u}) Q
          (aT.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
          SSet.const x := by
        rw [internalHomVertexMap_parameter]
        dsimp only [aT, transposeInternalHom]
        rw [MonoidalClosed.uncurry_curry]
        rw [transposeRowZero, hx']
        exact evaluateZeroFamily_constant x
      change EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
        (internalHomVertexMap (Δ[1] : SSet.{u}) Q
          (aT.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))))))
      rw [hmap, yonedaEquiv_const_one]
      let ex := SSet.Edge.id x
      let ex' := SSet.Edge.castEndpoints ex.src_eq ex.tgt_eq ex
      have hex' : EdgeIsEquivalence ex' :=
        (edgeIsEquivalence_id x).castEndpoints ex.src_eq ex.tgt_eq
      have heq : ex' = SSet.Edge.mk' ex.edge := by
        apply SSet.Edge.ext
        simp only [ex', SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
      simpa only [ex, heq] using hex'
    · have hmap : internalHomVertexMap (Δ[1] : SSet.{u}) Q
          (aT.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
          SSet.const y := by
        rw [internalHomVertexMap_parameter]
        dsimp only [aT, transposeInternalHom]
        rw [MonoidalClosed.uncurry_curry]
        rw [transposeRowOne, hy']
        exact evaluateZeroFamily_constant y
      change EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
        (internalHomVertexMap (Δ[1] : SSet.{u}) Q
          (aT.app (op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))))))
      rw [hmap, yonedaEquiv_const_one]
      let ey := SSet.Edge.id y
      let ey' := SSet.Edge.castEndpoints ey.src_eq ey.tgt_eq ey
      have hey' : EdgeIsEquivalence ey' :=
        (edgeIsEquivalence_id y).castEndpoints ey.src_eq ey.tgt_eq
      have heq : ey' = SSet.Edge.mk' ey.edge := by
        apply SSet.Edge.ext
        simp only [ey', SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
      simpa only [ey, heq] using hey'
  let g : (Δ[1] : SSet.{u}) ⟶ (equivalenceEdgeInternalHom Q : SSet.{u}) :=
    SSet.Subcomplex.lift aT (by
      rintro U _ ⟨t, rfl⟩ i
      rw [← NatTrans.naturality_apply aT
        (SimplexCategory.const ⦋0⦌ U.unop i).op t]
      let w :=
        ((Δ[1] : SSet.{u}).map
          (SimplexCategory.const ⦋0⦌ U.unop i).op t)
      let v := SSet.stdSimplex.obj₀Equiv w
      have hw : SSet.stdSimplex.obj₀Equiv.symm v = w := by
        exact Equiv.symm_apply_apply SSet.stdSimplex.obj₀Equiv w
      have hv := haT v
      rw [hw] at hv
      simpa only [w] using hv)
  let b : (Δ[1] : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q :=
    constantInternalHomFamily q
  let f : (SSet.boundary 1 : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q :=
    (SSet.boundary 1).ι ≫ b
  let p := equivalenceIntervalRestrictionToEquivalenceEdges Q
  have hsquare : CommSq f (SSet.boundary 1).ι p g := by
    apply CommSq.mk
    apply (cancel_mono (equivalenceEdgeInternalHom Q).ι).1
    dsimp only [p]
    simp only [Category.assoc,
      equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion]
    dsimp only [g]
    rw [SSet.Subcomplex.lift_ι]
    dsimp only [f]
    rw [Category.assoc]
    apply SSet.boundary.hom_ext
    intro i
    fin_cases i
    · simp only [← Category.assoc, SSet.boundary.ι_ι]
      apply transposeInternalHom_injective
      change transposeInternalHom
          ((SSet.stdSimplex.δ (0 : Fin 2) ≫ b) ≫
            (MonoidalClosed.pre equivalenceIntervalInclusion).app Q) =
        transposeInternalHom (SSet.stdSimplex.δ (0 : Fin 2) ≫ aT)
      calc
        _ = equivalenceIntervalInclusion ≫ transposeInternalHom
            (SSet.stdSimplex.δ (0 : Fin 2) ≫ b) :=
          (transposeInternalHom_pre equivalenceIntervalInclusion
            (SSet.stdSimplex.δ (0 : Fin 2) ≫ b)).symm
        _ = equivalenceIntervalInclusion ≫
            CartesianMonoidalCategory.toUnit
              (CategoryTheory.nerve EquivalenceInterval.{u}) ≫
              MonoidalClosed.curry' (endpointVertex Q y) := by
          rw [transposeInternalHom_constant_row q
            (SSet.stdSimplex.δ (0 : Fin 2)) y hqy]
        _ = CartesianMonoidalCategory.toUnit (Δ[1] : SSet.{u}) ≫
            MonoidalClosed.curry' (endpointVertex Q y) := by
          rw [← Category.assoc]
          have hunit : equivalenceIntervalInclusion ≫
              CartesianMonoidalCategory.toUnit
                (CategoryTheory.nerve EquivalenceInterval.{u}) =
              CartesianMonoidalCategory.toUnit (Δ[1] : SSet.{u}) :=
            Subsingleton.elim _ _
          rw [hunit]
        _ = a ≫ (MonoidalClosed.pre
            (SSet.stdSimplex.δ (0 : Fin 2))).app Q := hy'.symm
        _ = transposeInternalHom aT ≫ (MonoidalClosed.pre
            (SSet.stdSimplex.δ (0 : Fin 2))).app Q := by
          dsimp only [aT]
          rw [transposeInternalHom_transpose]
        _ = _ := (transposeInternalHom_comp
          (SSet.stdSimplex.δ (0 : Fin 2)) aT).symm
    · simp only [← Category.assoc, SSet.boundary.ι_ι]
      apply transposeInternalHom_injective
      change transposeInternalHom
          ((SSet.stdSimplex.δ (1 : Fin 2) ≫ b) ≫
            (MonoidalClosed.pre equivalenceIntervalInclusion).app Q) =
        transposeInternalHom (SSet.stdSimplex.δ (1 : Fin 2) ≫ aT)
      calc
        _ = equivalenceIntervalInclusion ≫ transposeInternalHom
            (SSet.stdSimplex.δ (1 : Fin 2) ≫ b) :=
          (transposeInternalHom_pre equivalenceIntervalInclusion
            (SSet.stdSimplex.δ (1 : Fin 2) ≫ b)).symm
        _ = equivalenceIntervalInclusion ≫
            CartesianMonoidalCategory.toUnit
              (CategoryTheory.nerve EquivalenceInterval.{u}) ≫
              MonoidalClosed.curry' (endpointVertex Q x) := by
          rw [transposeInternalHom_constant_row q
            (SSet.stdSimplex.δ (1 : Fin 2)) x hqx]
        _ = CartesianMonoidalCategory.toUnit (Δ[1] : SSet.{u}) ≫
            MonoidalClosed.curry' (endpointVertex Q x) := by
          rw [← Category.assoc]
          have hunit : equivalenceIntervalInclusion ≫
              CartesianMonoidalCategory.toUnit
                (CategoryTheory.nerve EquivalenceInterval.{u}) =
              CartesianMonoidalCategory.toUnit (Δ[1] : SSet.{u}) :=
            Subsingleton.elim _ _
          rw [hunit]
        _ = a ≫ (MonoidalClosed.pre
            (SSet.stdSimplex.δ (1 : Fin 2))).app Q := hx'.symm
        _ = transposeInternalHom aT ≫ (MonoidalClosed.pre
            (SSet.stdSimplex.δ (1 : Fin 2))).app Q := by
          dsimp only [aT]
          rw [transposeInternalHom_transpose]
        _ = _ := (transposeInternalHom_comp
          (SSet.stdSimplex.δ (1 : Fin 2)) aT).symm
  have hp := intervalRestriction_mem_monomorphisms_rlp_of_specialLeftHornFillers
    Q (hasAllSpecialLeftHornFillers_direct Q)
  have hlift : HasLiftingProperty (SSet.boundary 1).ι p :=
    hp (SSet.boundary 1).ι (by infer_instance)
  letI : HasLiftingProperty (SSet.boundary 1).ι p := hlift
  let F : (Δ[1] : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q :=
    hsquare.lift
  have hFpre : F ≫ internalHomPrecomp equivalenceIntervalInclusion Q = aT := by
    have h := congrArg (fun k ↦ k ≫ (equivalenceEdgeInternalHom Q).ι)
      hsquare.fac_right
    dsimp only [F, p] at h
    rw [Category.assoc,
      equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion] at h
    dsimp only [g] at h
    rw [SSet.Subcomplex.lift_ι] at h
    exact h
  let FT : CategoryTheory.nerve EquivalenceInterval.{u} ⟶
      (ihom (Δ[1] : SSet.{u})).obj Q :=
    transposeInternalHom F
  have hFTrestrict : equivalenceIntervalInclusion ≫ FT = a := by
    dsimp only [FT]
    rw [transposeInternalHom_pre]
    change transposeInternalHom
      (F ≫ internalHomPrecomp equivalenceIntervalInclusion Q) = a
    rw [hFpre]
    exact transposeInternalHom_transpose a
  have hFzero : SSet.stdSimplex.δ (0 : Fin 2) ≫ F =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ b := by
    calc
      _ = SSet.boundary.ι (0 : Fin 2) ≫ (SSet.boundary 1).ι ≫ F := by
        rw [← Category.assoc, SSet.boundary.ι_ι]
      _ = SSet.boundary.ι (0 : Fin 2) ≫ f := by
        rw [hsquare.fac_left]
      _ = _ := by
        dsimp only [f]
        rw [← Category.assoc, SSet.boundary.ι_ι]
  have hFone : SSet.stdSimplex.δ (1 : Fin 2) ≫ F =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ b := by
    calc
      _ = SSet.boundary.ι (1 : Fin 2) ≫ (SSet.boundary 1).ι ≫ F := by
        rw [← Category.assoc, SSet.boundary.ι_ι]
      _ = SSet.boundary.ι (1 : Fin 2) ≫ f := by
        rw [hsquare.fac_left]
      _ = _ := by
        dsimp only [f]
        rw [← Category.assoc, SSet.boundary.ι_ι]
  have hFTx : FT ≫ (MonoidalClosed.pre
      (SSet.stdSimplex.δ (1 : Fin 2))).app Q =
      CartesianMonoidalCategory.toUnit
        (CategoryTheory.nerve EquivalenceInterval.{u}) ≫
        MonoidalClosed.curry' (endpointVertex Q x) := by
    calc
      _ = transposeInternalHom
          (SSet.stdSimplex.δ (1 : Fin 2) ≫ F) :=
        (transposeInternalHom_comp (SSet.stdSimplex.δ (1 : Fin 2)) F).symm
      _ = transposeInternalHom
          (SSet.stdSimplex.δ (1 : Fin 2) ≫ b) :=
        congrArg transposeInternalHom hFone
      _ = _ := by
        dsimp only [b]
        exact transposeInternalHom_constant_row q
          (SSet.stdSimplex.δ (1 : Fin 2)) x hqx
  have hFTy : FT ≫ (MonoidalClosed.pre
      (SSet.stdSimplex.δ (0 : Fin 2))).app Q =
      CartesianMonoidalCategory.toUnit
        (CategoryTheory.nerve EquivalenceInterval.{u}) ≫
        MonoidalClosed.curry' (endpointVertex Q y) := by
    calc
      _ = transposeInternalHom
          (SSet.stdSimplex.δ (0 : Fin 2) ≫ F) :=
        (transposeInternalHom_comp (SSet.stdSimplex.δ (0 : Fin 2)) F).symm
      _ = transposeInternalHom
          (SSet.stdSimplex.δ (0 : Fin 2) ≫ b) :=
        congrArg transposeInternalHom hFzero
      _ = _ := by
        dsimp only [b]
        exact transposeInternalHom_constant_row q
          (SSet.stdSimplex.δ (0 : Fin 2)) y hqy
  have hFTendpoint :
      CartesianMonoidalCategory.toUnit
          (CategoryTheory.nerve EquivalenceInterval.{u}) ≫
          endpointPoint Q x y =
        FT ≫ endpointEvaluation Q := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa [endpointEvaluation, endpointPoint] using hFTx.symm
    · simpa [endpointEvaluation, endpointPoint] using hFTy.symm
  let H : CategoryTheory.nerve EquivalenceInterval.{u} ⟶
      endpointFiber Q x y :=
    pullback.lift
      (CartesianMonoidalCategory.toUnit
        (CategoryTheory.nerve EquivalenceInterval.{u})) FT hFTendpoint
  have hHrestrict : equivalenceIntervalInclusion ≫ H = e := by
    apply pullback.hom_ext
    · apply Subsingleton.elim
    · dsimp only [H]
      rw [Category.assoc, pullback.lift_snd, hFTrestrict]
  apply EquivalenceIntervalExtension.edgeIsEquivalence
  refine { map := H, restrict := ?_ }
  simpa only [e, SSet.Edge.mk'_edge] using hHrestrict

end Infinity
end LeanLCAExactChallenge
