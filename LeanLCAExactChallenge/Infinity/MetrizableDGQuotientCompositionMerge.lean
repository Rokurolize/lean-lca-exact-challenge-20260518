/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientCompositionInfrastructure
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-! # Settled composition in the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

def compositionBoundaryRightDifferentialPath
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom
      (factorModule d (Fin.last w.length) ⊗ factorModule e 0)
      ((dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
        ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)) :=
  (𝟙 _ ⊗ₘ factorDifferential e 0 0) ≫ compositionBoundaryMap d (e.raise 0) ≫
    eqToHom (show compositionBoundaryModule d (e.raise 0) = _ from by
      let hdeg : d.arrowDegree (Fin.last w.length) +
          (e.raise 0).arrowDegree 0 =
          (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 := by
        simp [DegreeProfile.raise]
        omega
      exact congrArg (fun t ↦
        (dgHomZModuleCochainComplex
          (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X t) hdeg)

def compositionBoundaryLeftDifferentialPath
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom
      (factorModule d (Fin.last w.length) ⊗ factorModule e 0)
      ((dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
        ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)) :=
  (factorDifferential d (Fin.last w.length) (Fin.last w.length) ⊗ₘ 𝟙 _) ≫
    compositionBoundaryMap (d.raise (Fin.last w.length)) e ≫
      eqToHom (show compositionBoundaryModule (d.raise (Fin.last w.length)) e = _ from by
        let hdeg : (d.raise (Fin.last w.length)).arrowDegree (Fin.last w.length) +
            e.arrowDegree 0 =
            (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 := by
          simp [DegreeProfile.raise]
          omega
        exact congrArg (fun t ↦
          (dgHomZModuleCochainComplex
          (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X t) hdeg)

theorem compositionBoundaryMap_raise_right_transport
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionBoundaryMap d (e.raise 0) ≫
        eqToHom (show compositionBoundaryModule d (e.raise 0) = _ from by
          let hdeg : d.arrowDegree (Fin.last w.length) +
              (e.raise 0).arrowDegree 0 =
              (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 := by
            simp [DegreeProfile.raise]
            omega
          exact congrArg (fun t ↦
            (dgHomZModuleCochainComplex
              (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X t) hdeg) =
      dgCochainCompTensorOfEq
        (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))
        (v.arrowSource 0) (v.arrowTarget 0)
        (by
          change w.vertex (Fin.last w.length).succ =
            v.vertex (0 : Fin (v.length + 1)).castSucc
          rw [show (Fin.last w.length).succ = Fin.last (w.length + 1) by ext; rfl]
          rw [vertex_last]
          rfl)
        (show d.arrowDegree (Fin.last w.length) +
            (e.arrowDegree 0 + 1) =
            (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 by omega) := by
  unfold compositionBoundaryMap
  apply dgCochainCompTensorOfEq_comp_degree_eqToHom
  simp [DegreeProfile.raise]
  omega

theorem compositionBoundaryMap_raise_left_transport
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionBoundaryMap (d.raise (Fin.last w.length)) e ≫
        eqToHom (show compositionBoundaryModule (d.raise (Fin.last w.length)) e = _ from by
          let hdeg : (d.raise (Fin.last w.length)).arrowDegree (Fin.last w.length) +
              e.arrowDegree 0 =
              (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 := by
            simp [DegreeProfile.raise]
            omega
          exact congrArg (fun t ↦
            (dgHomZModuleCochainComplex
              (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X t) hdeg) =
      dgCochainCompTensorOfEq
        (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))
        (v.arrowSource 0) (v.arrowTarget 0)
        (by
          change w.vertex (Fin.last w.length).succ =
            v.vertex (0 : Fin (v.length + 1)).castSucc
          rw [show (Fin.last w.length).succ = Fin.last (w.length + 1) by ext; rfl]
          rw [vertex_last]
          rfl)
        (show (d.raise (Fin.last w.length)).arrowDegree (Fin.last w.length) +
            e.arrowDegree 0 =
            (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 by
          simp [DegreeProfile.raise]
          omega) := by
  unfold compositionBoundaryMap
  apply dgCochainCompTensorOfEq_comp_degree_eqToHom
  simp [DegreeProfile.raise]
  omega

def compositionBoundaryRawRightDifferentialPath
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom
      (factorModule d (Fin.last w.length) ⊗ factorModule e 0)
      ((dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
        ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)) := by
  simp only [factorModule]
  exact
    ((𝟙 _ ⊗ₘ (dgHomZModuleCochainComplex
      (v.arrowSource 0) (v.arrowTarget 0)).d
        (e.arrowDegree 0) (e.arrowDegree 0 + 1)) ≫
      dgCochainCompTensorOfEq
        (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))
        (v.arrowSource 0) (v.arrowTarget 0)
        (by
          change w.vertex (Fin.last w.length).succ =
            v.vertex (0 : Fin (v.length + 1)).castSucc
          rw [show (Fin.last w.length).succ = Fin.last (w.length + 1) by ext; rfl]
          rw [vertex_last]
          rfl)
        (show d.arrowDegree (Fin.last w.length) + (e.arrowDegree 0 + 1) =
            (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 by omega))

def compositionBoundaryRawLeftDifferentialPath
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom
      (factorModule d (Fin.last w.length) ⊗ factorModule e 0)
      ((dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
        ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)) := by
  simp only [factorModule]
  exact
    (((dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))).d
      (d.arrowDegree (Fin.last w.length))
      (d.arrowDegree (Fin.last w.length) + 1) ⊗ₘ 𝟙 _) ≫
      dgCochainCompTensorOfEq
        (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))
        (v.arrowSource 0) (v.arrowTarget 0)
        (by
          change w.vertex (Fin.last w.length).succ =
            v.vertex (0 : Fin (v.length + 1)).castSucc
          rw [show (Fin.last w.length).succ = Fin.last (w.length + 1) by ext; rfl]
          rw [vertex_last]
          rfl)
        (show (d.arrowDegree (Fin.last w.length) + 1) + e.arrowDegree 0 =
            (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 by omega))

theorem compositionBoundaryRightDifferentialPath_eq_raw
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionBoundaryRightDifferentialPath d e =
      compositionBoundaryRawRightDifferentialPath d e := by
  unfold compositionBoundaryRightDifferentialPath
  rw [compositionBoundaryMap_raise_right_transport]
  rfl

theorem compositionBoundaryLeftDifferentialPath_eq_raw
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionBoundaryLeftDifferentialPath d e =
      compositionBoundaryRawLeftDifferentialPath d e := by
  unfold compositionBoundaryLeftDifferentialPath
  rw [compositionBoundaryMap_raise_left_transport]
  unfold compositionBoundaryRawLeftDifferentialPath
  apply eq_of_heq
  have hfd : HEq (factorDifferential d (Fin.last w.length) (Fin.last w.length))
      ((dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))).d
          (d.arrowDegree (Fin.last w.length))
          (d.arrowDegree (Fin.last w.length) + 1)) := by
    unfold factorDifferential
    simp only [eq_self, dif_pos]
    apply dgHomDifferential_heq <;> simp [DegreeProfile.raise]
  have htarget : factorModule (d.raise (Fin.last w.length)) (Fin.last w.length) =
      (dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))).X
          (d.arrowDegree (Fin.last w.length) + 1) := by
    unfold factorModule
    simp [DegreeProfile.raise]
  have htensor := tensorHom_heq rfl htarget rfl rfl hfd
    (by rfl : HEq (𝟙 (factorModule e 0))
      (𝟙 ((dgHomZModuleCochainComplex
        (v.arrowSource 0) (v.arrowTarget 0)).X (e.arrowDegree 0))))
  have hsource : factorModule d (Fin.last w.length) ⊗ factorModule e 0 =
      (dgHomZModuleCochainComplex
          (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))).X
            (d.arrowDegree (Fin.last w.length)) ⊗
        (dgHomZModuleCochainComplex
          (v.arrowSource 0) (v.arrowTarget 0)).X (e.arrowDegree 0) := rfl
  have hmiddle : factorModule (d.raise (Fin.last w.length)) (Fin.last w.length) ⊗
        factorModule e 0 =
      (dgHomZModuleCochainComplex
          (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))).X
            (d.arrowDegree (Fin.last w.length) + 1) ⊗
        (dgHomZModuleCochainComplex
          (v.arrowSource 0) (v.arrowTarget 0)).X (e.arrowDegree 0) :=
    congrArg₂ (· ⊗ ·) htarget rfl
  have hboundary : w.arrowTarget (Fin.last w.length) = v.arrowSource 0 := by
    change w.vertex (Fin.last w.length).succ =
      v.vertex (0 : Fin (v.length + 1)).castSucc
    rw [show (Fin.last w.length).succ = Fin.last (w.length + 1) by ext; rfl]
    rw [vertex_last]
    rfl
  have hdegree : d.arrowDegree (Fin.last w.length) + 1 + e.arrowDegree 0 =
      (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 := by omega
  have hdegreeRaised :
      (d.raise (Fin.last w.length)).arrowDegree (Fin.last w.length) + e.arrowDegree 0 =
        (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1 := by
    simp [DegreeProfile.raise]
    omega
  have hcomp := CategoryTheory.heq_comp
    (f := factorDifferential d (Fin.last w.length) (Fin.last w.length) ⊗ₘ
      𝟙 (factorModule e 0))
    (g := dgCochainCompTensorOfEq
      (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))
      (v.arrowSource 0) (v.arrowTarget 0) hboundary hdegreeRaised)
    (f' := (dgHomZModuleCochainComplex
      (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))).d
        (d.arrowDegree (Fin.last w.length))
        (d.arrowDegree (Fin.last w.length) + 1) ⊗ₘ
      𝟙 ((dgHomZModuleCochainComplex
        (v.arrowSource 0) (v.arrowTarget 0)).X (e.arrowDegree 0)))
    (g' := dgCochainCompTensorOfEq
      (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))
      (v.arrowSource 0) (v.arrowTarget 0) hboundary hdegree)
    hsource hmiddle rfl htensor (by
      exact dgCochainCompTensorOfEq_heq
        (K₁ := w.arrowSource (Fin.last w.length))
        (L₁ := w.arrowTarget (Fin.last w.length))
        (L₁' := v.arrowSource 0) (M₁ := v.arrowTarget 0)
        (K₂ := w.arrowSource (Fin.last w.length))
        (L₂ := w.arrowTarget (Fin.last w.length))
        (L₂' := v.arrowSource 0) (M₂ := v.arrowTarget 0)
        (p₁ := (d.raise (Fin.last w.length)).arrowDegree (Fin.last w.length))
        (q₁ := e.arrowDegree 0)
        (r₁ := (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)
        (p₂ := d.arrowDegree (Fin.last w.length) + 1)
        (q₂ := e.arrowDegree 0)
        (r₂ := (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)
        rfl rfl rfl rfl hboundary hboundary
        (by simp [DegreeProfile.raise]) rfl rfl hdegreeRaised hdegree)
  exact hcomp

theorem compositionBoundaryMap_comp_d_raw
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionBoundaryMap d e ≫
        (dgHomZModuleCochainComplex
          (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).d
          (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
          ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1) =
      compositionBoundaryRawRightDifferentialPath d e +
        (e.arrowDegree 0).negOnePow • compositionBoundaryRawLeftDifferentialPath d e := by
  simp only [compositionBoundaryMap, compositionBoundaryRawRightDifferentialPath,
    compositionBoundaryRawLeftDifferentialPath, factorModule]
  exact dgCochainCompTensorOfEq_comp_d
    (w.arrowSource (Fin.last w.length)) (w.arrowTarget (Fin.last w.length))
    (v.arrowSource 0) (v.arrowTarget 0)
    (by
      change w.vertex (Fin.last w.length).succ =
        v.vertex (0 : Fin (v.length + 1)).castSucc
      rw [show (Fin.last w.length).succ = Fin.last (w.length + 1) by ext; rfl]
      rw [vertex_last]
      rfl)
    (d.arrowDegree (Fin.last w.length)) (e.arrowDegree 0)

theorem compositionBoundaryMap_comp_d
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionBoundaryMap d e ≫
        (dgHomZModuleCochainComplex
          (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).d
          (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
          ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1) =
      compositionBoundaryRightDifferentialPath d e +
        (e.arrowDegree 0).negOnePow • compositionBoundaryLeftDifferentialPath d e := by
  rw [compositionBoundaryMap_comp_d_raw,
    compositionBoundaryRightDifferentialPath_eq_raw,
    compositionBoundaryLeftDifferentialPath_eq_raw]


theorem normalizedSummandCompositionMap_assoc
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    (α_ (summandModule a) (summandModule d) (summandModule e)).inv ≫
        (normalizedSummandCompositionMap a d ⊗ₘ 𝟙 (summandModule e)) ≫
        normalizedSummandCompositionMap (a.append d) e ≫
        (summandAssocIso a d e).hom =
      (𝟙 (summandModule a) ⊗ₘ normalizedSummandCompositionMap d e) ≫
        normalizedSummandCompositionMap a (d.append e) := by
  rw [normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder]
  dsimp only [summandModule]
  rw [MonoidalCategory.comp_tensor_id, MonoidalCategory.id_tensor_comp]
  simp only [Category.assoc]
  rw [tensorModuleListAppendIso_whiskerRight_assoc,
    tensorModuleListAppendIso_whiskerLeft_assoc]
  slice_lhs 1 3 =>
    rw [tensorModuleListAppendIso_assoc_inv_transport]
  simp only [Category.assoc]
  rw [summandCompositionRemainder_assoc]

def summandCompositionMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom (summandModule d ⊗ summandModule e)
      (summandModule (d.append e)) :=
  (eqToHom (congrArg tensorModuleList
      (finFamilyList_factorModule_eq_prefix_last d)) ⊗ₘ
    eqToHom (congrArg tensorModuleList
      (finFamilyList_factorModule_eq_first_suffix e))) ≫
    (tensorModuleListAppendIso
      (compositionLeftPrefix d ++ [factorModule d (Fin.last w.length)])
      (factorModule e 0 :: compositionRightSuffix e)).hom ≫
    eqToHom (congrArg tensorModuleList
      (appendBoundaryListsEq (compositionLeftPrefix d)
        (factorModule d (Fin.last w.length)) (factorModule e 0)
        (compositionRightSuffix e))) ≫
    (adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap ≫
    eqToHom (congrArg tensorModuleList
      (finFamilyList_factorModule_append_boundary d e).symm)

theorem summandCompositionMap_eq_normalized
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    summandCompositionMap d e = normalizedSummandCompositionMap d e := by
  unfold summandCompositionMap normalizedSummandCompositionMap
  slice_lhs 1 2 =>
    rw [tensorModuleListAppendIso_eqToHom
      (finFamilyList_factorModule_eq_prefix_last d)
      (finFamilyList_factorModule_eq_first_suffix e)]
  simp only [Category.assoc]

theorem summandCompositionMap_assoc
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    (α_ (summandModule a) (summandModule d) (summandModule e)).inv ≫
        (summandCompositionMap a d ⊗ₘ 𝟙 (summandModule e)) ≫
        summandCompositionMap (a.append d) e ≫
        (summandAssocIso a d e).hom =
      (𝟙 (summandModule a) ⊗ₘ summandCompositionMap d e) ≫
        summandCompositionMap a (d.append e) := by
  rw [summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized]
  exact normalizedSummandCompositionMap_assoc a d e

theorem summandCompositionMap_eq_boundary_decomposition
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    summandCompositionMap d e =
      ((summandLastFactorIso d).hom ⊗ₘ (summandFirstFactorIso e).hom) ≫
        (tensorModuleListAppendIso
          (compositionLeftPrefix d ++ [factorModule d (Fin.last w.length)])
          (factorModule e 0 :: compositionRightSuffix e)).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq (compositionLeftPrefix d)
            (factorModule d (Fin.last w.length)) (factorModule e 0)
            (compositionRightSuffix e))) ≫
        (adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap ≫
        eqToHom (congrArg tensorModuleList
          (finFamilyList_factorModule_append_boundary d e).symm) := by
  rfl

theorem summandCompositionMap_right_unit
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (ρ_ (summandModule d)).inv ≫
        (𝟙 _ ⊗ₘ nilIdentitySummandMap Y) ≫
        summandCompositionMap d (nilDegreeProfile Y Y 0) ≫
        (summandRightUnitIso d).hom =
      𝟙 (summandModule d) := by
  rw [summandCompositionMap_eq_boundary_decomposition]
  simp only [Category.assoc]
  rw [summandRightUnitSource_decompose_assoc]
  rw [summandRightUnitTarget_transport]
  slice_lhs 4 5 =>
    exact compositionBoundaryMap_right_nil_tensorMap_post_assoc d
      (summandLastFactorIso d).inv
  rw [appendBoundaryListsEq_right_nil_eqToHom]
  change (summandLastFactorIso d).hom ≫
      ((ρ_ (tensorModuleList
          (compositionLeftPrefix d ++
            [factorModule d (Fin.last w.length)]))).inv ≫
        (𝟙 _ ⊗ₘ (identityCochainInclusion Y ≫
          (ρ_ (factorModule (nilDegreeProfile Y Y 0) 0)).inv)) ≫
        (tensorModuleListAppendIso
          (compositionLeftPrefix d ++
            [factorModule d (Fin.last w.length)])
          [factorModule (nilDegreeProfile Y Y 0) 0]).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendSingletonPairEq (compositionLeftPrefix d)
            (factorModule d (Fin.last w.length))
            (factorModule (nilDegreeProfile Y Y 0) 0))) ≫
        (adjacentMergeAfter (compositionLeftPrefix d) (ys := [])
          (rightUnitCompositionBoundaryMap d)).tensorMap) ≫
      (summandLastFactorIso d).inv = 𝟙 (summandModule d)
  rw [normalizedSummandRightUnit]
  simp

theorem summandCompositionMap_right_unit_apply
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (x : summandModule d) :
    (summandRightUnitIso d).hom.hom
        ((summandCompositionMap d (nilDegreeProfile Y Y 0)).hom
          (x ⊗ₜ[ℤ] (nilIdentitySummandMap Y).hom 1)) = x := by
  have h := congrArg
    (fun f : summandModule d ⟶ summandModule d ↦ f.hom x)
    (summandCompositionMap_right_unit d)
  simpa only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, CategoryTheory.id_apply] using h

theorem summandCompositionMap_left_unit
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (λ_ (summandModule d)).inv ≫
        (nilIdentitySummandMap X ⊗ₘ 𝟙 _) ≫
        summandCompositionMap (nilDegreeProfile X X 0) d ≫
        (summandLeftUnitIso d).hom =
      𝟙 (summandModule d) := by
  rw [summandCompositionMap_eq_boundary_decomposition]
  simp only [Category.assoc]
  rw [summandLeftUnitSource_decompose_assoc]
  rw [summandLeftUnitTarget_transport]
  slice_lhs 4 5 =>
    exact compositionBoundaryMap_left_nil_tensorMap_post_assoc d
      (summandFirstFactorIso d).inv
  change (summandFirstFactorIso d).hom ≫
      ((λ_ (tensorModuleList
          (factorModule d 0 :: compositionRightSuffix d))).inv ≫
        ((identityCochainInclusion X ≫
          (ρ_ (factorModule (nilDegreeProfile X X 0) 0)).inv) ⊗ₘ 𝟙 _) ≫
        (tensorModuleListAppendIso
          [factorModule (nilDegreeProfile X X 0) 0]
          (factorModule d 0 :: compositionRightSuffix d)).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq []
            (factorModule (nilDegreeProfile X X 0) 0)
            (factorModule d 0) (compositionRightSuffix d))) ≫
        (adjacentMergeAfter [] (ys := compositionRightSuffix d)
          (leftUnitCompositionBoundaryMap d)).tensorMap) ≫
      (summandFirstFactorIso d).inv = 𝟙 (summandModule d)
  rw [normalizedSummandLeftUnit]
  simp

theorem summandCompositionMap_left_unit_apply
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (x : summandModule d) :
    (summandLeftUnitIso d).hom.hom
        ((summandCompositionMap (nilDegreeProfile X X 0) d).hom
          ((nilIdentitySummandMap X).hom 1 ⊗ₜ[ℤ] x)) = x := by
  have h := congrArg
    (fun f : summandModule d ⟶ summandModule d ↦ f.hom x)
    (summandCompositionMap_left_unit d)
  simpa only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, CategoryTheory.id_apply] using h

def intLinearMapOfAddHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (f : A →+ B) : A →ₗ[ℤ] B where
  toFun := f
  map_add' := f.map_add
  map_smul' n x := by
    rw [RingHom.id_apply]
    exact (congrArg f (int_smul_eq_zsmul (inferInstance : Module ℤ A) n x)).trans
      ((f.map_zsmul n x).trans
        (int_smul_eq_zsmul (inferInstance : Module ℤ B) n (f x)).symm)

def intBilinearMapPostcomp {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ D]
    (f : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) : A →ₗ[ℤ] B →ₗ[ℤ] D := by
  let inner (x : A) : B →+ D := g.toAddMonoidHom.comp (f x).toAddMonoidHom
  exact intLinearMapOfAddHom ({
    toFun x := intLinearMapOfAddHom (inner x)
    map_zero' := by
      ext y
      change g (f 0 y) = 0
      rw [map_zero, LinearMap.zero_apply, map_zero]
    map_add' x₁ x₂ := by
      ext y
      change g (f (x₁ + x₂) y) = g (f x₁ y) + g (f x₂ y)
      rw [map_add, LinearMap.add_apply, map_add] } : A →+ (B →ₗ[ℤ] D))

def uliftBilinearMap {M N P : ModuleCat.{0} ℤ}
    (f : Quiver.Hom (M ⊗ N) P) :
    ((ModuleCat.uliftFunctor.{1} ℤ).obj M) →ₗ[ℤ]
      ((ModuleCat.uliftFunctor.{1} ℤ).obj N) →ₗ[ℤ]
        ((ModuleCat.uliftFunctor.{1} ℤ).obj P) := by
  let inner (x : (ModuleCat.uliftFunctor.{1} ℤ).obj M) :
      ((ModuleCat.uliftFunctor.{1} ℤ).obj N) →+
        ((ModuleCat.uliftFunctor.{1} ℤ).obj P) := {
    toFun y := ULift.up (f.hom (x.down ⊗ₜ[ℤ] y.down))
    map_zero' := by
      have hzero : (0 : (ModuleCat.uliftFunctor.{1} ℤ).obj N).down = 0 := rfl
      change ULift.up (f.hom (x.down ⊗ₜ[ℤ] (0 :
        (ModuleCat.uliftFunctor.{1} ℤ).obj N).down)) = ULift.up 0
      rw [hzero, TensorProduct.tmul_zero, map_zero]
    map_add' y₁ y₂ := by
      have hadd : (y₁ + y₂).down = y₁.down + y₂.down := rfl
      change ULift.up (f.hom (x.down ⊗ₜ[ℤ] (y₁ + y₂).down)) =
        ULift.up (f.hom (x.down ⊗ₜ[ℤ] y₁.down) +
          f.hom (x.down ⊗ₜ[ℤ] y₂.down))
      rw [hadd, TensorProduct.tmul_add, map_add] }
  exact intLinearMapOfAddHom ({
    toFun x := intLinearMapOfAddHom (inner x)
    map_zero' := by
      ext y
      have hzero : (0 : (ModuleCat.uliftFunctor.{1} ℤ).obj M).down = 0 := rfl
      change ULift.up (f.hom ((0 :
        (ModuleCat.uliftFunctor.{1} ℤ).obj M).down ⊗ₜ[ℤ] y.down)) = ULift.up 0
      rw [hzero, TensorProduct.zero_tmul, map_zero]
    map_add' x₁ x₂ := by
      ext y
      have hadd : (x₁ + x₂).down = x₁.down + x₂.down := rfl
      change ULift.up (f.hom ((x₁ + x₂).down ⊗ₜ[ℤ] y.down)) =
        ULift.up (f.hom (x₁.down ⊗ₜ[ℤ] y.down) +
          f.hom (x₂.down ⊗ₜ[ℤ] y.down))
      rw [hadd, TensorProduct.add_tmul, map_add] } :
        ((ModuleCat.uliftFunctor.{1} ℤ).obj M) →+
          (((ModuleCat.uliftFunctor.{1} ℤ).obj N) →ₗ[ℤ]
            ((ModuleCat.uliftFunctor.{1} ℤ).obj P)))

def largeSummandCompositionMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n) →ₗ[ℤ]
      largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m) →ₗ[ℤ]
        quotientGradedModule X Z (n + m) :=
  intBilinearMapPostcomp (uliftBilinearMap (summandCompositionMap d e))
    (Limits.Sigma.ι
      (fun s : GradedSummandIndex X Z (n + m) ↦ largeSummandModule s)
      ⟨w.append v, d.append e⟩).hom

def rightCoproductCompositionMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (d : DegreeProfile w n)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n)) :
    Quiver.Hom (quotientGradedModule Y Z m) (quotientGradedModule X Z (n + m)) :=
  Limits.Sigma.desc fun s : GradedSummandIndex Y Z m ↦
    ModuleCat.ofHom (largeSummandCompositionMap d s.2 x)

theorem rightCoproductCompositionMap_zero
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (d : DegreeProfile w n) :
    rightCoproductCompositionMap (Z := Z) (m := m) d 0 = 0 := by
  apply Limits.Sigma.hom_ext
  intro s
  rw [rightCoproductCompositionMap, Limits.Sigma.ι_desc]
  change ModuleCat.ofHom (largeSummandCompositionMap d s.2 0) = 0
  rw [map_zero]
  rfl

theorem rightCoproductCompositionMap_add
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (d : DegreeProfile w n)
    (x₁ x₂ : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n)) :
    rightCoproductCompositionMap (Z := Z) (m := m) d (x₁ + x₂) =
      rightCoproductCompositionMap d x₁ + rightCoproductCompositionMap d x₂ := by
  apply Limits.Sigma.hom_ext
  intro s
  rw [rightCoproductCompositionMap, Limits.Sigma.ι_desc]
  change ModuleCat.ofHom (largeSummandCompositionMap d s.2 (x₁ + x₂)) =
    Limits.Sigma.ι (fun t : GradedSummandIndex Y Z m ↦ largeSummandModule t) s ≫
      (rightCoproductCompositionMap d x₁ + rightCoproductCompositionMap d x₂)
  rw [map_add, Preadditive.comp_add, rightCoproductCompositionMap,
    rightCoproductCompositionMap, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
  rfl

def leftSummandCompositionMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (d : DegreeProfile w n) :
    largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n) →ₗ[ℤ]
      quotientGradedModule Y Z m →ₗ[ℤ] quotientGradedModule X Z (n + m) :=
  intLinearMapOfAddHom ({
    toFun x := (rightCoproductCompositionMap (Z := Z) (m := m) d x).hom
    map_zero' := congrArg ModuleCat.Hom.hom (rightCoproductCompositionMap_zero d)
    map_add' x₁ x₂ := congrArg ModuleCat.Hom.hom
      (rightCoproductCompositionMap_add d x₁ x₂) } :
        largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n) →+
          (quotientGradedModule Y Z m →ₗ[ℤ] quotientGradedModule X Z (n + m)))

def quotientCompositionMap (X Y Z : ComplexCategory) (n m : ℤ) :
    quotientGradedModule X Y n →ₗ[ℤ]
      quotientGradedModule Y Z m →ₗ[ℤ] quotientGradedModule X Z (n + m) :=
  (Limits.Sigma.desc fun s : GradedSummandIndex X Y n ↦
    ModuleCat.ofHom (leftSummandCompositionMap (Z := Z) (m := m) s.2)).hom

theorem quotientCompositionMap_on_summands
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    quotientCompositionMap X Y Z n m
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) =
      largeSummandCompositionMap d e x y := by
  change ((Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩ ≫
        Limits.Sigma.desc (fun s : GradedSummandIndex X Y n ↦
          ModuleCat.ofHom (leftSummandCompositionMap (Z := Z) (m := m) s.2))).hom x)
      ((Limits.Sigma.ι
        (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) = _
  rw [Limits.Sigma.ι_desc]
  change (rightCoproductCompositionMap d x).hom
      ((Limits.Sigma.ι
        (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) = _
  change (Limits.Sigma.ι
      (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩ ≫
        rightCoproductCompositionMap d x).hom y = _
  rw [rightCoproductCompositionMap, Limits.Sigma.ι_desc]
  rfl

theorem largeSummandCompositionMap_assoc_transport
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r)
    (x : largeSummandModule
      (⟨u, a⟩ : GradedSummandIndex W X p))
    (y : largeSummandModule
      (⟨w, d⟩ : GradedSummandIndex X Y q))
    (z : largeSummandModule
      (⟨v, e⟩ : GradedSummandIndex Y Z r)) :
    (eqToHom (congrArg (quotientGradedModule W Z)
        (Int.add_assoc p q r))).hom
      (quotientCompositionMap W Y Z (p + q) r
        (largeSummandCompositionMap a d x y)
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex Y Z r ↦ largeSummandModule t)
          ⟨v, e⟩).hom z)) =
      quotientCompositionMap W X Z p (q + r)
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex W X p ↦ largeSummandModule t)
          ⟨u, a⟩).hom x)
        (largeSummandCompositionMap d e y z) := by
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  rcases z with ⟨z⟩
  change
    (eqToHom (congrArg (quotientGradedModule W Z)
        (Int.add_assoc p q r))).hom
      (quotientCompositionMap W Y Z (p + q) r
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex W Y (p + q) ↦ largeSummandModule t)
          ⟨u.append w, a.append d⟩).hom
            (ULift.up ((summandCompositionMap a d).hom (x ⊗ₜ[ℤ] y))))
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex Y Z r ↦ largeSummandModule t)
          ⟨v, e⟩).hom (ULift.up z))) =
      quotientCompositionMap W X Z p (q + r)
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex W X p ↦ largeSummandModule t)
          ⟨u, a⟩).hom (ULift.up x))
        ((Limits.Sigma.ι
          (fun t : GradedSummandIndex X Z (q + r) ↦ largeSummandModule t)
          ⟨w.append v, d.append e⟩).hom
            (ULift.up ((summandCompositionMap d e).hom (y ⊗ₜ[ℤ] z))))
  rw [quotientCompositionMap_on_summands,
    quotientCompositionMap_on_summands]
  change
    (Limits.Sigma.ι
          (fun t : GradedSummandIndex W Z ((p + q) + r) ↦
            largeSummandModule t)
          ⟨(u.append w).append v, (a.append d).append e⟩ ≫
        eqToHom (congrArg (quotientGradedModule W Z)
          (Int.add_assoc p q r))).hom
      (ULift.up ((summandCompositionMap (a.append d) e).hom
        ((summandCompositionMap a d).hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z))) =
      (Limits.Sigma.ι
        (fun t : GradedSummandIndex W Z (p + (q + r)) ↦
          largeSummandModule t)
        ⟨u.append (w.append v), a.append (d.append e)⟩).hom
      (ULift.up ((summandCompositionMap a (d.append e)).hom
        (x ⊗ₜ[ℤ] (summandCompositionMap d e).hom (y ⊗ₜ[ℤ] z))))
  rw [largeSummandAssocInclusion_transport]
  simp only [ModuleCat.comp_apply, uliftFunctor_map_up]
  have h := congrArg
    (fun f : Quiver.Hom
        (summandModule a ⊗ (summandModule d ⊗ summandModule e))
        (summandModule (a.append (d.append e))) ↦
      f.hom (x ⊗ₜ[ℤ] (y ⊗ₜ[ℤ] z)))
    (summandCompositionMap_assoc a d e)
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.associator_inv_apply] at h
  have h' :
      (summandAssocIso a d e).hom.hom
          ((summandCompositionMap (a.append d) e).hom
            ((summandCompositionMap a d).hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)) =
        (summandCompositionMap a (d.append e)).hom
          (x ⊗ₜ[ℤ] (summandCompositionMap d e).hom (y ⊗ₜ[ℤ] z)) := by
    change
      (summandAssocIso a d e).hom.hom
          ((summandCompositionMap (a.append d) e).hom
            ((summandCompositionMap a d).hom (x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)) =
        (summandCompositionMap a (d.append e)).hom
          (x ⊗ₜ[ℤ] (summandCompositionMap d e).hom (y ⊗ₜ[ℤ] z)) at h
    exact h
  exact congrArg
    (fun t : summandModule (a.append (d.append e)) ↦
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex W Z (p + (q + r)) ↦
          largeSummandModule s)
        ⟨u.append (w.append v), a.append (d.append e)⟩).hom (ULift.up t)) h'

def quotientCompositionLeftAssociatedMap
    (W X Y Z : ComplexCategory) (p q r : ℤ) :
    quotientGradedModule W X p →ₗ[ℤ]
      quotientGradedModule X Y q →ₗ[ℤ]
        quotientGradedModule Y Z r →ₗ[ℤ]
          quotientGradedModule W Z (p + (q + r)) := by
  let transport :=
    (eqToHom (congrArg (quotientGradedModule W Z)
      (Int.add_assoc p q r))).hom
  exact intLinearMapOfAddHom ({
    toFun x := intLinearMapOfAddHom ({
      toFun y := transport.comp
        (quotientCompositionMap W Y Z (p + q) r
          (quotientCompositionMap W X Y p q x y))
      map_zero' := by
        ext z
        simp
      map_add' y₁ y₂ := by
        ext z
        simp } : quotientGradedModule X Y q →+
          (quotientGradedModule Y Z r →ₗ[ℤ]
            quotientGradedModule W Z (p + (q + r))))
    map_zero' := by
      ext y z
      change transport
        (quotientCompositionMap W Y Z (p + q) r
          (quotientCompositionMap W X Y p q 0 y) z) = 0
      simp
    map_add' x₁ x₂ := by
      ext y z
      change transport
        (quotientCompositionMap W Y Z (p + q) r
          (quotientCompositionMap W X Y p q (x₁ + x₂) y) z) =
        transport
            (quotientCompositionMap W Y Z (p + q) r
              (quotientCompositionMap W X Y p q x₁ y) z) +
          transport
            (quotientCompositionMap W Y Z (p + q) r
              (quotientCompositionMap W X Y p q x₂ y) z)
      simp } : quotientGradedModule W X p →+
        (quotientGradedModule X Y q →ₗ[ℤ]
          quotientGradedModule Y Z r →ₗ[ℤ]
            quotientGradedModule W Z (p + (q + r))))

def quotientCompositionRightAssociatedMap
    (W X Y Z : ComplexCategory) (p q r : ℤ) :
    quotientGradedModule W X p →ₗ[ℤ]
      quotientGradedModule X Y q →ₗ[ℤ]
        quotientGradedModule Y Z r →ₗ[ℤ]
          quotientGradedModule W Z (p + (q + r)) := by
  exact intLinearMapOfAddHom ({
    toFun x := intLinearMapOfAddHom ({
      toFun y := (quotientCompositionMap W X Z p (q + r) x).comp
        (quotientCompositionMap X Y Z q r y)
      map_zero' := by
        ext z
        simp
      map_add' y₁ y₂ := by
        ext z
        simp } : quotientGradedModule X Y q →+
          (quotientGradedModule Y Z r →ₗ[ℤ]
            quotientGradedModule W Z (p + (q + r))))
    map_zero' := by
      ext y z
      change quotientCompositionMap W X Z p (q + r) 0
        (quotientCompositionMap X Y Z q r y z) = 0
      simp
    map_add' x₁ x₂ := by
      ext y z
      change quotientCompositionMap W X Z p (q + r) (x₁ + x₂)
          (quotientCompositionMap X Y Z q r y z) =
        quotientCompositionMap W X Z p (q + r) x₁
            (quotientCompositionMap X Y Z q r y z) +
          quotientCompositionMap W X Z p (q + r) x₂
            (quotientCompositionMap X Y Z q r y z)
      simp } : quotientGradedModule W X p →+
        (quotientGradedModule X Y q →ₗ[ℤ]
          quotientGradedModule Y Z r →ₗ[ℤ]
            quotientGradedModule W Z (p + (q + r))))

@[simp]
theorem quotientCompositionLeftAssociatedMap_apply
    (W X Y Z : ComplexCategory) (p q r : ℤ)
    (x : quotientGradedModule W X p)
    (y : quotientGradedModule X Y q)
    (z : quotientGradedModule Y Z r) :
    quotientCompositionLeftAssociatedMap W X Y Z p q r x y z =
      (eqToHom (congrArg (quotientGradedModule W Z)
        (Int.add_assoc p q r))).hom
        (quotientCompositionMap W Y Z (p + q) r
          (quotientCompositionMap W X Y p q x y) z) := rfl

@[simp]
theorem quotientCompositionRightAssociatedMap_apply
    (W X Y Z : ComplexCategory) (p q r : ℤ)
    (x : quotientGradedModule W X p)
    (y : quotientGradedModule X Y q)
    (z : quotientGradedModule Y Z r) :
    quotientCompositionRightAssociatedMap W X Y Z p q r x y z =
      quotientCompositionMap W X Z p (q + r) x
        (quotientCompositionMap X Y Z q r y z) := rfl

theorem quotientCompositionAssociatedMaps_eq
    (W X Y Z : ComplexCategory) (p q r : ℤ) :
    quotientCompositionLeftAssociatedMap W X Y Z p q r =
      quotientCompositionRightAssociatedMap W X Y Z p q r := by
  let left := quotientCompositionLeftAssociatedMap W X Y Z p q r
  let right := quotientCompositionRightAssociatedMap W X Y Z p q r
  have hx : ModuleCat.ofHom left = ModuleCat.ofHom right := by
    apply Limits.Sigma.hom_ext
    rintro ⟨u, a⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hy : ModuleCat.ofHom
          (left ((Limits.Sigma.ι
            (fun s : GradedSummandIndex W X p ↦ largeSummandModule s)
            ⟨u, a⟩).hom x)) =
        ModuleCat.ofHom
          (right ((Limits.Sigma.ι
            (fun s : GradedSummandIndex W X p ↦ largeSummandModule s)
            ⟨u, a⟩).hom x)) := by
      apply Limits.Sigma.hom_ext
      rintro ⟨w, d⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      have hz : ModuleCat.ofHom
            (left ((Limits.Sigma.ι
              (fun s : GradedSummandIndex W X p ↦ largeSummandModule s)
              ⟨u, a⟩).hom x)
              ((Limits.Sigma.ι
                (fun s : GradedSummandIndex X Y q ↦ largeSummandModule s)
                ⟨w, d⟩).hom y)) =
          ModuleCat.ofHom
            (right ((Limits.Sigma.ι
              (fun s : GradedSummandIndex W X p ↦ largeSummandModule s)
              ⟨u, a⟩).hom x)
              ((Limits.Sigma.ι
                (fun s : GradedSummandIndex X Y q ↦ largeSummandModule s)
                ⟨w, d⟩).hom y)) := by
        apply Limits.Sigma.hom_ext
        rintro ⟨v, e⟩
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change left
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex W X p ↦ largeSummandModule s)
              ⟨u, a⟩).hom x)
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex X Y q ↦ largeSummandModule s)
              ⟨w, d⟩).hom y)
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex Y Z r ↦ largeSummandModule s)
              ⟨v, e⟩).hom z) =
          right
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex W X p ↦ largeSummandModule s)
              ⟨u, a⟩).hom x)
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex X Y q ↦ largeSummandModule s)
              ⟨w, d⟩).hom y)
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex Y Z r ↦ largeSummandModule s)
              ⟨v, e⟩).hom z)
        simp only [left, right,
          quotientCompositionLeftAssociatedMap_apply,
          quotientCompositionRightAssociatedMap_apply]
        rw [quotientCompositionMap_on_summands a d x y,
          quotientCompositionMap_on_summands d e y z]
        exact largeSummandCompositionMap_assoc_transport a d e x y z
      exact congrArg ModuleCat.Hom.hom hz
    exact congrArg ModuleCat.Hom.hom hy
  exact congrArg ModuleCat.Hom.hom hx

theorem quotientCompositionMap_assoc
    (W X Y Z : ComplexCategory) (p q r : ℤ)
    (x : quotientGradedModule W X p)
    (y : quotientGradedModule X Y q)
    (z : quotientGradedModule Y Z r) :
    (eqToHom (congrArg (quotientGradedModule W Z)
        (Int.add_assoc p q r))).hom
      (quotientCompositionMap W Y Z (p + q) r
        (quotientCompositionMap W X Y p q x y) z) =
      quotientCompositionMap W X Z p (q + r) x
        (quotientCompositionMap X Y Z q r y z) := by
  have h := congrArg
    (fun f : quotientGradedModule W X p →ₗ[ℤ]
        quotientGradedModule X Y q →ₗ[ℤ]
          quotientGradedModule Y Z r →ₗ[ℤ]
            quotientGradedModule W Z (p + (q + r)) ↦ f x y z)
    (quotientCompositionAssociatedMaps_eq W X Y Z p q r)
  simpa only [quotientCompositionLeftAssociatedMap_apply,
    quotientCompositionRightAssociatedMap_apply] using h

theorem largeSummandCompositionMap_right_unit_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n)) :
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.add_zero n))).hom
        (largeSummandCompositionMap d (nilDegreeProfile Y Y 0) x
          (ULift.up ((nilIdentitySummandMap Y).hom 1))) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom x := by
  rcases x with ⟨x⟩
  change
    (Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y (n + 0) ↦ largeSummandModule q)
          ⟨w.append (nil Y Y), d.append (nilDegreeProfile Y Y 0)⟩ ≫
        eqToHom (congrArg (quotientGradedModule X Y) (Int.add_zero n))).hom
      (ULift.up ((summandCompositionMap d (nilDegreeProfile Y Y 0)).hom
        (x ⊗ₜ[ℤ] (nilIdentitySummandMap Y).hom 1))) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom
          (ULift.up x)
  rw [largeSummandRightUnitInclusion_transport]
  simp only [ModuleCat.comp_apply, uliftFunctor_map_up]
  rw [summandCompositionMap_right_unit_apply]

theorem largeSummandCompositionMap_left_unit_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n)) :
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.zero_add n))).hom
        (largeSummandCompositionMap (nilDegreeProfile X X 0) d
          (ULift.up ((nilIdentitySummandMap X).hom 1)) x) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom x := by
  rcases x with ⟨x⟩
  change
    (Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y (0 + n) ↦ largeSummandModule q)
          ⟨(nil X X).append w, (nilDegreeProfile X X 0).append d⟩ ≫
        eqToHom (congrArg (quotientGradedModule X Y) (Int.zero_add n))).hom
      (ULift.up ((summandCompositionMap (nilDegreeProfile X X 0) d).hom
        ((nilIdentitySummandMap X).hom 1 ⊗ₜ[ℤ] x))) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom
          (ULift.up x)
  rw [largeSummandLeftUnitInclusion_transport]
  simp only [ModuleCat.comp_apply, uliftFunctor_map_up]
  rw [summandCompositionMap_left_unit_apply]

def quotientIdentityElement (K : ComplexCategory) : quotientGradedModule K K 0 :=
  (originalHomInclusion K K 0).hom (ULift.up (identityCochain K))

theorem quotientIdentityElement_eq_nil_summand (K : ComplexCategory) :
    quotientIdentityElement K =
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex K K 0 ↦ largeSummandModule s)
        ⟨nil K K, nilDegreeProfile K K 0⟩).hom
          (ULift.up ((nilIdentitySummandMap K).hom 1)) := by
  have h := congrArg
    (fun f : 𝟙_ (ModuleCat.{0} ℤ) ⟶
        summandModule (nilDegreeProfile K K 0) ↦ f.hom 1)
    (identityCochainInclusion_comp_nilSummandIsoOriginal_inv K)
  have hid : (identityCochainInclusion K).hom 1 = identityCochain K := by
    exact LinearMap.toSpanSingleton_apply_one ℤ _ (identityCochain K)
  have hpoint :
      (nilSummandIsoOriginal K K (nilDegreeProfile K K 0)).inv.hom
          (identityCochain K) =
        (nilIdentitySummandMap K).hom 1 := by
    simpa only [ModuleCat.comp_apply, hid] using h
  unfold quotientIdentityElement originalHomInclusion
  simp only [ModuleCat.comp_apply, uliftFunctor_map_up]
  rw [hpoint]

theorem quotientCompositionMap_right_unit_on_summand
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n)) :
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.add_zero n))).hom
        (quotientCompositionMap X Y Y n 0
          ((Limits.Sigma.ι
            (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q)
            ⟨w, d⟩).hom x)
          (quotientIdentityElement Y)) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom x := by
  rw [quotientIdentityElement_eq_nil_summand,
    quotientCompositionMap_on_summands]
  exact largeSummandCompositionMap_right_unit_transport d x

theorem quotientCompositionMap_left_unit_on_summand
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n)) :
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.zero_add n))).hom
        (quotientCompositionMap X X Y 0 n
          (quotientIdentityElement X)
          ((Limits.Sigma.ι
            (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q)
            ⟨w, d⟩).hom x)) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom x := by
  rw [quotientIdentityElement_eq_nil_summand,
    quotientCompositionMap_on_summands]
  exact largeSummandCompositionMap_left_unit_transport d x

def quotientRightUnitLinearMap (X Y : ComplexCategory) (n : ℤ) :
    quotientGradedModule X Y n →ₗ[ℤ] quotientGradedModule X Y (n + 0) :=
  intLinearMapOfAddHom ({
    toFun x := quotientCompositionMap X Y Y n 0 x (quotientIdentityElement Y)
    map_zero' := by
      rw [map_zero, LinearMap.zero_apply]
    map_add' x y := by
      rw [map_add, LinearMap.add_apply] } :
        quotientGradedModule X Y n →+
          quotientGradedModule X Y (n + 0))

def quotientRightUnitMap (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom (quotientGradedModule X Y n) (quotientGradedModule X Y n) :=
  ModuleCat.ofHom
    ((eqToHom (congrArg (quotientGradedModule X Y) (Int.add_zero n))).hom.comp
      (quotientRightUnitLinearMap X Y n))

def quotientLeftUnitMap (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom (quotientGradedModule X Y n) (quotientGradedModule X Y n) :=
  ModuleCat.ofHom
    ((eqToHom (congrArg (quotientGradedModule X Y) (Int.zero_add n))).hom.comp
      (quotientCompositionMap X X Y 0 n (quotientIdentityElement X)))

theorem quotientRightUnitMap_eq_id (X Y : ComplexCategory) (n : ℤ) :
    quotientRightUnitMap X Y n = 𝟙 (quotientGradedModule X Y n) := by
  apply Limits.Sigma.hom_ext
  rintro ⟨w, d⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.add_zero n))).hom
        (quotientCompositionMap X Y Y n 0
          ((Limits.Sigma.ι
            (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q)
            ⟨w, d⟩).hom x)
          (quotientIdentityElement Y)) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom x
  exact quotientCompositionMap_right_unit_on_summand d x

theorem quotientLeftUnitMap_eq_id (X Y : ComplexCategory) (n : ℤ) :
    quotientLeftUnitMap X Y n = 𝟙 (quotientGradedModule X Y n) := by
  apply Limits.Sigma.hom_ext
  rintro ⟨w, d⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.zero_add n))).hom
        (quotientCompositionMap X X Y 0 n
          (quotientIdentityElement X)
          ((Limits.Sigma.ι
            (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q)
            ⟨w, d⟩).hom x)) =
      (Limits.Sigma.ι
        (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩).hom x
  exact quotientCompositionMap_left_unit_on_summand d x

theorem quotientCompositionMap_right_unit
    (X Y : ComplexCategory) (n : ℤ) (x : quotientGradedModule X Y n) :
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.add_zero n))).hom
        (quotientCompositionMap X Y Y n 0 x (quotientIdentityElement Y)) = x := by
  change (quotientRightUnitMap X Y n).hom x = x
  rw [quotientRightUnitMap_eq_id]
  rfl

theorem quotientCompositionMap_left_unit
    (X Y : ComplexCategory) (n : ℤ) (x : quotientGradedModule X Y n) :
    (eqToHom (congrArg (quotientGradedModule X Y) (Int.zero_add n))).hom
        (quotientCompositionMap X X Y 0 n (quotientIdentityElement X) x) = x := by
  change (quotientLeftUnitMap X Y n).hom x = x
  rw [quotientLeftUnitMap_eq_id]
  rfl

theorem quotientIdentityElement_closed (K : ComplexCategory) :
    (quotientTotalDifferential K K 0).hom (quotientIdentityElement K) = 0 := by
  have h := originalHomInclusion_comp_totalDifferential K K 0
  have happ := congrArg (fun f ↦ f.hom (ULift.up (identityCochain K))) h
  change (quotientTotalDifferential K K 0).hom (quotientIdentityElement K) =
    (originalHomInclusion K K 1).hom
      (((ModuleCat.uliftFunctor.{1} ℤ).map
        ((dgHomZModuleCochainComplex K K).d 0 1)).hom
          (ULift.up (identityCochain K))) at happ
  rw [uliftFunctor_map_up, identityCochain_d] at happ
  exact happ.trans (map_zero _)

theorem sum_filter_fin_addCases_right
    {A B : ℕ} (a : Fin A → ℤ) (b : Fin B → ℤ) (j : Fin B) :
    ∑ x with Fin.natAdd A j < x, Fin.addCases a b x =
      ∑ k with j < k, b k := by
  classical
  calc
    _ = ∑ x : Fin (A + B), if Fin.natAdd A j < x then Fin.addCases a b x else 0 := by
      exact Finset.sum_filter _ _
    _ = (∑ i : Fin A,
          if Fin.natAdd A j < Fin.castAdd B i then a i else 0) +
        ∑ k : Fin B, if Fin.natAdd A j < Fin.natAdd A k then b k else 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
    _ = _ := by
      rw [show (∑ i : Fin A,
          if Fin.natAdd A j < Fin.castAdd B i then a i else 0) = 0 by
        apply Finset.sum_eq_zero
        intro i _
        have hnot : ¬Fin.natAdd A j < Fin.castAdd B i := by
          change ¬A + j.val < i.val
          omega
        rw [if_neg hnot]]
      rw [zero_add]
      calc
        (∑ k : Fin B, if Fin.natAdd A j < Fin.natAdd A k then b k else 0) =
            ∑ k : Fin B, if j < k then b k else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases h : j < k
          · rw [if_pos h, if_pos (by
              change A + j.val < A + k.val
              omega)]
          · rw [if_neg h, if_neg (by
              change ¬A + j.val < A + k.val
              omega)]
        _ = _ := (Finset.sum_filter _ _).symm

theorem sum_filter_fin_addCases_left
    {A B : ℕ} (a : Fin A → ℤ) (b : Fin B → ℤ) (i : Fin A) :
    ∑ x with Fin.castAdd B i < x, Fin.addCases a b x =
      (∑ k with i < k, a k) + ∑ k, b k := by
  classical
  calc
    _ = ∑ x : Fin (A + B), if Fin.castAdd B i < x then Fin.addCases a b x else 0 := by
      exact Finset.sum_filter _ _
    _ = (∑ k : Fin A, if Fin.castAdd B i < Fin.castAdd B k then a k else 0) +
        ∑ k : Fin B, if Fin.castAdd B i < Fin.natAdd A k then b k else 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
    _ = _ := by
      congr 1
      · calc
          (∑ k : Fin A, if Fin.castAdd B i < Fin.castAdd B k then a k else 0) =
              ∑ k : Fin A, if i < k then a k else 0 := by
            apply Finset.sum_congr rfl
            intro k _
            by_cases h : i < k
            · rw [if_pos h, if_pos (by
                change i.val < k.val
                exact h)]
            · rw [if_neg h, if_neg (by
                change ¬i.val < k.val
                exact h)]
          _ = _ := (Finset.sum_filter _ _).symm
      · apply Finset.sum_congr rfl
        intro k _
        rw [if_pos]
        change i.val < A + k.val
        omega

theorem sum_filter_fin_cast {A B : ℕ} (h : A = B)
    (a : Fin A → ℤ) (i : Fin A) :
    ∑ x with i < x, a x =
      ∑ y with Fin.cast h i < y, a (Fin.cast h.symm y) := by
  subst B
  rfl

theorem sum_filter_fin_castSucc {A : ℕ} (a : Fin (A + 1) → ℤ) (i : Fin A) :
    ∑ q with i.castSucc < q, a q =
      (∑ k with i < k, a k.castSucc) + a (Fin.last A) := by
  classical
  calc
    _ = ∑ q : Fin (A + 1), if i.castSucc < q then a q else 0 := by
      exact Finset.sum_filter _ _
    _ = (∑ k : Fin A, if i.castSucc < k.castSucc then a k.castSucc else 0) +
        (if i.castSucc < Fin.last A then a (Fin.last A) else 0) := by
      rw [Fin.sum_univ_castSucc]
    _ = _ := by
      rw [if_pos (by
        change i.val < A
        exact i.isLt)]
      congr 1
      calc
        (∑ k : Fin A, if i.castSucc < k.castSucc then a k.castSucc else 0) =
            ∑ k : Fin A, if i < k then a k.castSucc else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          congr 1
        _ = _ := (Finset.sum_filter _ _).symm



theorem suffixTotal_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    (d.append e).suffixTotal (appendRightArrowIndex j) =
      e.suffixTotal j.succ := by
  unfold DegreeProfile.suffixTotal
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  change (∑ q with appendRightArrowIndex j < q, appendArrowDegree d e q) - _ = _
  rw [sum_filter_fin_cast hlen (appendArrowDegree d e)
    (appendRightArrowIndex j)]
  have hindex : Fin.cast hlen (appendRightArrowIndex j) =
      Fin.natAdd w.length j.succ := by
    apply Fin.ext
    simp only [Fin.val_cast, appendRightArrowIndex,
      Fin.val_natAdd, Fin.val_succ]
    omega
  rw [hindex]
  have hfun :
      (fun q ↦ appendArrowDegree d e (Fin.cast hlen.symm q)) =
      Fin.addCases
        (fun i : Fin w.length ↦ d.arrowDegree i.castSucc)
        (Fin.cases (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
          (fun k : Fin v.length ↦ e.arrowDegree k.succ)) := by
    funext q
    unfold appendArrowDegree
    congr 1
  rw [hfun]
  rw [sum_filter_fin_addCases_right]
  rw [show (∑ k with j.succ < k,
      Fin.cases (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
        (fun q : Fin v.length ↦ e.arrowDegree q.succ) k) =
      ∑ k with j.succ < k, e.arrowDegree k by
    apply Finset.sum_congr rfl
    intro k hk
    have hjk := (Finset.mem_filter.mp hk).2
    induction k using Fin.cases with
    | zero => simp at hjk
    | succ k => rfl]
  congr 1
  simp only [append_length, appendRightArrowIndex, Fin.val_mk, Fin.val_succ]
  omega

theorem suffixTotal_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    (d.append e).suffixTotal (appendLeftArrowIndex i) =
      d.suffixTotal i.castSucc + m := by
  unfold DegreeProfile.suffixTotal
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  change (∑ q with appendLeftArrowIndex i < q, appendArrowDegree d e q) - _ = _
  rw [sum_filter_fin_cast hlen (appendArrowDegree d e)
    (appendLeftArrowIndex i)]
  have hindex : Fin.cast hlen (appendLeftArrowIndex i) =
      Fin.castAdd (v.length + 1) i := by
    apply Fin.ext
    rfl
  rw [hindex]
  have hfun :
      (fun q ↦ appendArrowDegree d e (Fin.cast hlen.symm q)) =
      Fin.addCases
        (fun k : Fin w.length ↦ d.arrowDegree k.castSucc)
        (Fin.cases (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
          (fun k : Fin v.length ↦ e.arrowDegree k.succ)) := by
    funext q
    unfold appendArrowDegree
    congr 1
  rw [hfun]
  rw [sum_filter_fin_addCases_left]
  rw [sum_filter_fin_castSucc]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  have he := e.totalDegree
  rw [Fin.sum_univ_succ] at he
  simp only [append_length, appendLeftArrowIndex, Fin.val_mk, Fin.val_castSucc]
  omega

theorem suffixTotal_append_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (d.append e).suffixTotal (appendBoundaryArrowIndex w v) =
      e.suffixTotal 0 := by
  unfold DegreeProfile.suffixTotal
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  change (∑ q with appendBoundaryArrowIndex w v < q, appendArrowDegree d e q) - _ = _
  rw [sum_filter_fin_cast hlen (appendArrowDegree d e)
    (appendBoundaryArrowIndex w v)]
  have hindex : Fin.cast hlen (appendBoundaryArrowIndex w v) =
      Fin.natAdd w.length (0 : Fin (v.length + 1)) := by
    apply Fin.ext
    rfl
  rw [hindex]
  have hfun :
      (fun q ↦ appendArrowDegree d e (Fin.cast hlen.symm q)) =
      Fin.addCases
        (fun i : Fin w.length ↦ d.arrowDegree i.castSucc)
        (Fin.cases (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
          (fun k : Fin v.length ↦ e.arrowDegree k.succ)) := by
    funext q
    unfold appendArrowDegree
    congr 1
  rw [hfun]
  rw [sum_filter_fin_addCases_right]
  rw [show (∑ k with (0 : Fin (v.length + 1)) < k,
      Fin.cases (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
        (fun q : Fin v.length ↦ e.arrowDegree q.succ) k) =
      ∑ k with (0 : Fin (v.length + 1)) < k, e.arrowDegree k by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 := (Finset.mem_filter.mp hk).2
    induction k using Fin.cases with
    | zero => simp at hk0
    | succ k => rfl]
  congr 1
  simp only [append_length, appendBoundaryArrowIndex, Fin.val_mk]
  simp

def appendRightSuffixIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin (v.length + 1)) : Fin ((w.append v).length + 1) :=
  ⟨w.length + j.val, by simp [append_length]; omega⟩

theorem suffixTotal_append_right'
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin (v.length + 1)) :
    (d.append e).suffixTotal (appendRightSuffixIndex j) =
      e.suffixTotal j := by
  induction j using Fin.cases with
  | zero =>
      have hindex : appendRightSuffixIndex (w := w) (v := v) 0 =
          appendBoundaryArrowIndex w v := by
        apply Fin.ext
        rfl
      rw [hindex]
      exact suffixTotal_append_boundary d e
  | succ j =>
      convert suffixTotal_append_right d e j using 1
      congr 1
      apply Fin.ext
      simp only [appendRightSuffixIndex, Fin.val_mk, Fin.val_succ,
        appendRightArrowIndex]
      omega

def appendLeftContractionIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin w.length) : Fin (w.append v).length :=
  ⟨i.val, by simp; omega⟩

def appendRightContractionIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin v.length) : Fin (w.append v).length :=
  ⟨w.length + j.val, by
    simpa only [append_length] using (Nat.add_lt_add_left j.isLt w.length)⟩



theorem contractionSuffix_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    (d.append e).contractionSuffix (appendLeftContractionIndex i) =
      d.contractionSuffix i + m := by
  rw [← (d.append e).suffixTotal_castSucc_add_one (appendLeftContractionIndex i)]
  have hindex : (appendLeftContractionIndex (v := v) i).castSucc =
      appendLeftArrowIndex i := by
    apply Fin.ext
    rfl
  rw [hindex, suffixTotal_append_left]
  have hd := d.suffixTotal_castSucc_add_one i
  omega

theorem contractionSuffix_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    (d.append e).contractionSuffix (appendRightContractionIndex j) =
      e.contractionSuffix j := by
  rw [← (d.append e).suffixTotal_castSucc_add_one (appendRightContractionIndex j)]
  have hindex : (appendRightContractionIndex (w := w) j).castSucc =
      appendRightSuffixIndex (w := w) (v := v) j.castSucc := by
    apply Fin.ext
    rfl
  rw [hindex, suffixTotal_append_right']
  exact e.suffixTotal_castSucc_add_one j



theorem internalSign_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    (d.append e).internalSign (appendLeftArrowIndex i) =
      d.internalSign i.castSucc * (m.negOnePow : ℤ) := by
  rw [(d.append e).internalSign_eq_negOnePow, d.internalSign_eq_negOnePow,
    suffixTotal_append_left, Int.negOnePow_add]
  rfl

theorem internalSign_append_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (d.append e).internalSign (appendBoundaryArrowIndex w v) =
      e.internalSign 0 := by
  rw [(d.append e).internalSign_eq_negOnePow, e.internalSign_eq_negOnePow,
    suffixTotal_append_boundary]

theorem internalSign_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    (d.append e).internalSign (appendRightArrowIndex j) =
      e.internalSign j.succ := by
  rw [(d.append e).internalSign_eq_negOnePow, e.internalSign_eq_negOnePow,
    suffixTotal_append_right]

theorem internalSign_append_boundary_mul
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (d.append e).internalSign (appendBoundaryArrowIndex w v) *
        (e.arrowDegree 0).negOnePow = m.negOnePow := by
  rw [internalSign_append_boundary, e.internalSign_eq_negOnePow]
  have hdegree : e.suffixTotal 0 + e.arrowDegree 0 = m := by
    unfold DegreeProfile.suffixTotal
    have hsum : (∑ j with (0 : Fin (v.length + 1)) < j, e.arrowDegree j) =
        ∑ i : Fin v.length, e.arrowDegree i.succ := by
      rw [show (∑ j with (0 : Fin (v.length + 1)) < j, e.arrowDegree j) =
          ∑ j, if (0 : Fin (v.length + 1)) < j then e.arrowDegree j else 0 from
        Finset.sum_filter _ _]
      rw [Fin.sum_univ_succ]
      simp
    rw [hsum]
    have he := e.totalDegree
    rw [Fin.sum_univ_succ] at he
    simp
    omega
  calc
    _ = ((e.suffixTotal 0 + e.arrowDegree 0).negOnePow : ℤ) :=
      congrArg (fun u : ℤˣ ↦ (u : ℤ))
        (Int.negOnePow_add (e.suffixTotal 0) (e.arrowDegree 0)).symm
    _ = _ := congrArg (fun z : ℤ ↦ (z.negOnePow : ℤ)) hdegree



theorem contractionSign_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    (d.append e).contractionSign (appendLeftContractionIndex i) =
      d.contractionSign i * (m.negOnePow : ℤ) := by
  rw [(d.append e).contractionSign_eq_negOnePow, d.contractionSign_eq_negOnePow,
    contractionSuffix_append_left, Int.negOnePow_add]
  rfl

theorem contractionSign_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    (d.append e).contractionSign (appendRightContractionIndex j) =
      e.contractionSign j := by
  rw [(d.append e).contractionSign_eq_negOnePow, e.contractionSign_eq_negOnePow,
    contractionSuffix_append_right]



theorem DegreeProfile.raise_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    (d.append e).raise (appendLeftArrowIndex i) =
      ((d.raise i.castSucc).append e).castTotal (by omega) := by
  apply DegreeProfile.ext
  funext q
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  let q' : Fin (w.length + (v.length + 1)) := Fin.cast hlen q
  have hq : q = Fin.cast hlen.symm q' := by
    simp [q']
  rw [hq]
  induction q' using Fin.addCases with
  | left j =>
      simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
        DegreeProfile.append, appendArrowDegree]
      simp [appendLeftArrowIndex, Fin.ext_iff]
  | right j =>
      induction j using Fin.cases with
      | zero =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendLeftArrowIndex, Fin.ext_iff, add_comm]
          omega
      | succ j =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendLeftArrowIndex, Fin.ext_iff]
          omega

theorem DegreeProfile.raise_append_boundary_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (d.append e).raise (appendBoundaryArrowIndex w v) =
      ((d.raise (Fin.last w.length)).append e).castTotal (by omega) := by
  apply DegreeProfile.ext
  funext q
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  let q' : Fin (w.length + (v.length + 1)) := Fin.cast hlen q
  have hq : q = Fin.cast hlen.symm q' := by
    simp [q']
  rw [hq]
  induction q' using Fin.addCases with
  | left j =>
      simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
        DegreeProfile.append, appendArrowDegree]
      simp [appendBoundaryArrowIndex, Fin.ext_iff]
  | right j =>
      induction j using Fin.cases with
      | zero =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendBoundaryArrowIndex, Fin.ext_iff, add_comm]
          omega
      | succ j =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendBoundaryArrowIndex, Fin.ext_iff]

theorem DegreeProfile.raise_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    (d.append e).raise (appendRightArrowIndex j) =
      (d.append (e.raise j.succ)).castTotal (by omega) := by
  apply DegreeProfile.ext
  funext q
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  let q' : Fin (w.length + (v.length + 1)) := Fin.cast hlen q
  have hq : q = Fin.cast hlen.symm q' := by
    simp [q']
  rw [hq]
  induction q' using Fin.addCases with
  | left k =>
      simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
        DegreeProfile.append, appendArrowDegree]
      simp [appendRightArrowIndex, Fin.ext_iff]
      omega
  | right k =>
      induction k using Fin.cases with
      | zero =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendRightArrowIndex, Fin.ext_iff]
          omega
      | succ k =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendRightArrowIndex, Fin.ext_iff]
          omega

theorem DegreeProfile.raise_append_boundary_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (d.append e).raise (appendBoundaryArrowIndex w v) =
      (d.append (e.raise 0)).castTotal (by omega) := by
  apply DegreeProfile.ext
  funext q
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  let q' : Fin (w.length + (v.length + 1)) := Fin.cast hlen q
  have hq : q = Fin.cast hlen.symm q' := by
    simp [q']
  rw [hq]
  induction q' using Fin.addCases with
  | left j =>
      simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
        DegreeProfile.append, appendArrowDegree]
      simp [appendBoundaryArrowIndex, Fin.ext_iff]
      omega
  | right j =>
      induction j using Fin.cases with
      | zero =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendBoundaryArrowIndex, Fin.ext_iff, add_comm]
          omega
      | succ j =>
          simp only [DegreeProfile.raise, DegreeProfile.castTotal_arrowDegree,
            DegreeProfile.append, appendArrowDegree]
          simp [appendBoundaryArrowIndex, Fin.ext_iff]

theorem factorDifferential_append_boundary_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    HEq (factorDifferential (d.append e)
        (appendBoundaryArrowIndex w v) (appendBoundaryArrowIndex w v))
      ((dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).d
          (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
          ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)) := by
  unfold factorDifferential
  simp only [eq_self, dif_pos]
  apply dgHomDifferential_heq
  · rw [arrowSource_append_boundary]
  · rw [arrowTarget_append_boundary]
  · change appendArrowDegree d e (appendBoundaryArrowIndex w v) = _
    rw [appendArrowDegree_boundary]
  · rw [DegreeProfile.raise_append_boundary_left]
    simp only [DegreeProfile.castTotal_arrowDegree]
    change appendArrowDegree (d.raise (Fin.last w.length)) e
      (appendBoundaryArrowIndex w v) = _
    rw [appendArrowDegree_boundary]
    simp [DegreeProfile.raise]
    omega

theorem factorDifferential_append_left_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    HEq (factorDifferential (d.append e)
        (appendLeftArrowIndex i) (appendLeftArrowIndex i))
      ((dgHomZModuleCochainComplex
        (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).d
          (d.arrowDegree i.castSucc) (d.arrowDegree i.castSucc + 1)) := by
  unfold factorDifferential
  simp only [eq_self, dif_pos]
  apply dgHomDifferential_heq
  · rw [arrowSource_append_left]
  · rw [arrowTarget_append_left]
  · change appendArrowDegree d e (appendLeftArrowIndex i) = _
    rw [appendArrowDegree_left]
  · rw [DegreeProfile.raise_append_left]
    simp only [DegreeProfile.castTotal_arrowDegree]
    change appendArrowDegree (d.raise i.castSucc) e
      (appendLeftArrowIndex i) = _
    rw [appendArrowDegree_left]
    simp [DegreeProfile.raise]

theorem factorDifferential_append_right_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    HEq (factorDifferential (d.append e)
        (appendRightArrowIndex j) (appendRightArrowIndex j))
      ((dgHomZModuleCochainComplex
        (v.arrowSource j.succ) (v.arrowTarget j.succ)).d
          (e.arrowDegree j.succ) (e.arrowDegree j.succ + 1)) := by
  unfold factorDifferential
  simp only [eq_self, dif_pos]
  apply dgHomDifferential_heq
  · rw [arrowSource_append_right]
  · rw [arrowTarget_append_right]
  · change appendArrowDegree d e (appendRightArrowIndex j) = _
    rw [appendArrowDegree_right]
  · rw [DegreeProfile.raise_append_right]
    simp only [DegreeProfile.castTotal_arrowDegree]
    change appendArrowDegree d (e.raise j.succ)
      (appendRightArrowIndex j) = _
    rw [appendArrowDegree_right]
    simp [DegreeProfile.raise]

theorem compositionBoundaryMap_raise_right_internal_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    HEq (compositionBoundaryMap d (e.raise j.succ))
      (compositionBoundaryMap d e) := by
  unfold compositionBoundaryMap
  apply dgCochainCompTensorOfEq_heq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have hj : (0 : Fin (v.length + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    simp [DegreeProfile.raise, hj]
  · have hj : (0 : Fin (v.length + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    simp [DegreeProfile.raise, hj]

theorem compositionBoundaryMap_raise_left_internal_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    HEq (compositionBoundaryMap (d.raise i.castSucc) e)
      (compositionBoundaryMap d e) := by
  have hi : (i.castSucc : Fin (w.length + 1)) ≠ Fin.last w.length :=
    Fin.castSucc_ne_last i
  have hlast : (Fin.last w.length : Fin (w.length + 1)) ≠ i.castSucc := hi.symm
  unfold compositionBoundaryMap
  apply dgCochainCompTensorOfEq_heq
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [DegreeProfile.raise, hlast]
  · rfl
  · simp [DegreeProfile.raise, hlast]

theorem summandModule_castTotal_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (h : n = m) (d : DegreeProfile w n) :
    summandModule (d.castTotal h) = summandModule d := by
  apply congrArg tensorModuleList
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
  apply (List.ofFn_inj).2
  funext i
  unfold factorModule
  rw [DegreeProfile.castTotal_arrowDegree]

def appendBoundaryRightSummandModuleEq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    summandModule (d.append (e.raise 0)) =
      summandModule ((d.append e).raise (appendBoundaryArrowIndex w v)) := by
  let htot : n + (m + 1) = (n + m) + 1 := by omega
  have hraise := congrArg summandModule
    (DegreeProfile.raise_append_boundary_right d e)
  have hcast := summandModule_castTotal_eq htot
    (d.append (e.raise 0))
  exact (hraise.trans hcast).symm

def appendBoundaryLeftSummandModuleEq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    summandModule ((d.raise (Fin.last w.length)).append e) =
      summandModule ((d.append e).raise (appendBoundaryArrowIndex w v)) := by
  let htot : (n + 1) + m = (n + m) + 1 := by omega
  have hraise := congrArg summandModule
    (DegreeProfile.raise_append_boundary_left d e)
  have hcast := summandModule_castTotal_eq htot
    ((d.raise (Fin.last w.length)).append e)
  exact (hraise.trans hcast).symm

theorem compositionRightSuffix_raise_zero_eq
    {Y Z : ComplexCategory} {v : DrinfeldWord Y Z} {m : ℤ}
    (e : DegreeProfile v m) :
    compositionRightSuffix e = compositionRightSuffix (e.raise 0) := by
  unfold compositionRightSuffix
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
  apply (List.ofFn_inj).2
  funext i
  unfold factorModule
  simp [DegreeProfile.raise]

theorem compositionBoundaryTarget_raise_zero_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (dgHomZModuleCochainComplex
      (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
        ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1) =
      compositionBoundaryModule d (e.raise 0) := by
  unfold compositionBoundaryModule
  congr 1
  simp [DegreeProfile.raise]
  omega

theorem compositionBoundaryCanonicalTarget_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    tensorModuleList
        (compositionLeftPrefix d ++
          (dgHomZModuleCochainComplex
            (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
              ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1) ::
            compositionRightSuffix e) =
      summandModule ((d.append e).raise (appendBoundaryArrowIndex w v)) := by
  have htot : n + (m + 1) = (n + m) + 1 := by omega
  have hcast := summandModule_castTotal_eq htot (d.append (e.raise 0))
  have hlist :
      compositionLeftPrefix d ++
          (dgHomZModuleCochainComplex
            (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
              ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1) ::
            compositionRightSuffix e =
        finFamilyList (factorModule (d.append (e.raise 0))) := by
    rw [compositionBoundaryTarget_raise_zero_eq,
      compositionRightSuffix_raise_zero_eq,
      finFamilyList_factorModule_append_boundary]
  exact (congrArg tensorModuleList hlist).trans
    (hcast.symm.trans
      (congrArg summandModule
        (DegreeProfile.raise_append_boundary_right d e)).symm)

theorem tensorMapData_ofFn_eqToHom_of_family_eq
    {k : ℕ} (M N : Fin k → ModuleCat.{0} ℤ) (h : M = N)
    (f : (q : Fin k) → M q ⟶ N q)
    (hf : ∀ q, f q = eqToHom (congrFun h q)) :
    (TensorMapData.ofFn M N f).tensorMap =
      eqToHom (congrArg tensorModuleList (congrArg finFamilyList h)) := by
  cases h
  have hfun : f = fun q ↦ 𝟙 (M q) := by
    funext q
    simpa using hf q
  subst f
  simp

theorem comp_eqToHom_heq_left
    {A B C : ModuleCat.{0} ℤ} (f : A ⟶ B) (h : B = C) :
    HEq (f ≫ eqToHom h) f := by
  subst C
  simp

theorem contractionTensorMap_recursive_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    HEq (contractionTensorMap d i)
      (recursiveContractionAdjacentMergeData d i).tensorMap := by
  let hfamily :
      (fun q ↦ recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i) q) =
        contractedFactorAtOldIndex d i :=
    funext (recursiveContractionMergedFactor_eq d i)
  have hmap : recursiveContractionMergedFactorsTensorMap d i =
      eqToHom (congrArg tensorModuleList (congrArg finFamilyList hfamily)) := by
    unfold recursiveContractionMergedFactorsTensorMap
    exact tensorMapData_ofFn_eqToHom_of_family_eq _ _ hfamily _ (fun q ↦ by
      unfold recursiveContractionMergedFactorMap
      rw [Subsingleton.elim (recursiveContractionMergedFactor_eq d i q)
        (congrFun hfamily q)])
  unfold contractionTensorMap contractionTensorMapAtOldIndex
    recursiveContractionTensorMapAtOldIndex contractedFactorsOldIndexIso
  rw [hmap]
  let hmerged := congrArg tensorModuleList (congrArg finFamilyList hfamily)
  let hcontract := congrArg tensorModuleList (contractedFactorsOldIndex_eq d i)
  change HEq
    (((recursiveContractionAdjacentMergeData d i).tensorMap ≫ eqToHom hmerged) ≫
      eqToHom hcontract)
    (recursiveContractionAdjacentMergeData d i).tensorMap
  rw [Category.assoc, eqToHom_trans]
  exact comp_eqToHom_heq_left _ _

theorem tensorMapData_cons_heq
    {M M' N N' : ModuleCat.{0} ℤ}
    {Ms Ms' Ns Ns' : List (ModuleCat.{0} ℤ)}
    {f : Quiver.Hom M N} {g : Quiver.Hom M' N'}
    {fs : TensorMapData Ms Ns} {gs : TensorMapData Ms' Ns'}
    (hM : M = M') (hN : N = N') (hMs : Ms = Ms') (hNs : Ns = Ns')
    (hf : HEq f g) (h : HEq fs gs) :
    HEq (@TensorMapData.cons M N Ms Ns f fs)
      (@TensorMapData.cons M' N' Ms' Ns' g gs) := by
  subst M'
  subst N'
  subst Ms'
  subst Ns'
  have hfg : f = g := eq_of_heq hf
  subst g
  have hfs : fs = gs := eq_of_heq h
  subst gs
  rfl

theorem tensorMapData_tensorMap_heq
    {source target source' target' : List (ModuleCat.{0} ℤ)}
    {f : TensorMapData source target} {g : TensorMapData source' target'}
    (hsource : source = source') (htarget : target = target') (h : HEq f g) :
    HEq f.tensorMap g.tensorMap := by
  subst source'
  subst target'
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

def tensorMapDataPrefixId
    (xs : List (ModuleCat.{0} ℤ))
    {source target : List (ModuleCat.{0} ℤ)}
    (f : TensorMapData source target) :
    TensorMapData (xs ++ source) (xs ++ target) := by
  induction xs with
  | nil => exact f
  | cons M xs ih => exact .cons (𝟙 M) ih

theorem tensorMapDataPrefixId_tensorMap
    (xs : List (ModuleCat.{0} ℤ))
    {source target : List (ModuleCat.{0} ℤ)}
    (f : TensorMapData source target) :
    (tensorMapDataPrefixId xs f).tensorMap = tensorModuleListWhiskerLeft xs f.tensorMap := by
  induction xs with
  | nil =>
      change f.tensorMap =
        (λ_ (tensorModuleList source)).inv ≫
          (𝟙_ (ModuleCat.{0} ℤ) ◁ f.tensorMap) ≫
            (λ_ (tensorModuleList target)).hom
      apply (cancel_epi (λ_ (tensorModuleList source)).hom).mp
      rw [Iso.hom_inv_id_assoc]
      exact (MonoidalCategory.leftUnitor_naturality f.tensorMap).symm
  | cons M xs ih =>
      change (𝟙 M ⊗ₘ (tensorMapDataPrefixId xs f).tensorMap) = _
      dsimp [tensorModuleListWhiskerLeft, tensorModuleListAppendIso]
      dsimp only [tensorModuleList, tensorModuleListOver]
      simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
        Iso.refl_hom]
      rw [ih]
      simp [tensorModuleListWhiskerLeft, Category.assoc]

theorem tensorMapDataPrefixId_append_heq
    (xs ys : List (ModuleCat.{0} ℤ))
    {source target : List (ModuleCat.{0} ℤ)}
    (f : TensorMapData source target) :
    HEq (tensorMapDataPrefixId (xs ++ ys) f)
      (tensorMapDataPrefixId xs (tensorMapDataPrefixId ys f)) := by
  induction xs with
  | nil =>
      simp [tensorMapDataPrefixId]
  | cons M xs ih =>
      change HEq
        (TensorMapData.cons (𝟙 M) (tensorMapDataPrefixId (xs ++ ys) f))
        (TensorMapData.cons (𝟙 M)
          (tensorMapDataPrefixId xs (tensorMapDataPrefixId ys f)))
      have h := ih
      apply tensorMapData_cons_heq rfl rfl (List.append_assoc xs ys source)
        (List.append_assoc xs ys target) HEq.rfl
      exact h

theorem adjacentMergeAfter_naturality
    (xs : List (ModuleCat.{0} ℤ))
    {M N P M' N' P' : ModuleCat.{0} ℤ}
    {ys ys' : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) P) (f' : Quiver.Hom (M' ⊗ N') P')
    (a : Quiver.Hom M M') (b : Quiver.Hom N N') (c : Quiver.Hom P P')
    (tailMap : TensorMapData ys ys')
    (h : (a ⊗ₘ b) ≫ f' = f ≫ c) :
    AdjacentMergeNaturality
      (adjacentMergeAfter xs f) (adjacentMergeAfter xs f')
      (tensorMapDataPrefixId xs (.cons a (.cons b tailMap)))
      (tensorMapDataPrefixId xs (.cons c tailMap)) := by
  induction xs with
  | nil =>
      exact .head f f' a b c tailMap h
  | cons R xs ih =>
      exact .tail (𝟙 R) ih

theorem AdjacentMergeData.head_tensorMap_leibniz_prefix
    {M N M' N' P P' : ModuleCat.{0} ℤ}
    (xs Ms : List (ModuleCat.{0} ℤ))
    (f : M ⊗ N ⟶ P) (fR : M ⊗ N' ⟶ P') (fL : M' ⊗ N ⟶ P')
    (a : M ⟶ M') (b : N ⟶ N') (g : P ⟶ P') (c : ℤ)
    (h : f ≫ g = (𝟙 M ⊗ₘ b) ≫ fR + c • ((a ⊗ₘ 𝟙 N) ≫ fL)) :
    (adjacentMergeAfter xs (ys := Ms) f).tensorMap ≫
        (tensorMapDataPrefixId xs
          (TensorMapData.cons g (TensorMapData.identity Ms))).tensorMap =
      (tensorMapDataPrefixId xs
          (TensorMapData.cons (𝟙 M)
            (TensorMapData.cons b (TensorMapData.identity Ms)))).tensorMap ≫
          (adjacentMergeAfter xs (ys := Ms) fR).tensorMap +
        c • ((tensorMapDataPrefixId xs
          (TensorMapData.cons a
            (TensorMapData.cons (𝟙 N) (TensorMapData.identity Ms)))).tensorMap ≫
          (adjacentMergeAfter xs (ys := Ms) fL).tensorMap) := by
  induction xs with
  | nil =>
      exact AdjacentMergeData.head_tensorMap_leibniz f fR fL a b g c h
  | cons Q xs ih =>
      simp only [adjacentMergeAfter, tensorMapDataPrefixId]
      change (𝟙 Q ⊗ₘ (adjacentMergeAfter xs f).tensorMap) ≫
            (𝟙 Q ⊗ₘ (tensorMapDataPrefixId xs
              (TensorMapData.cons g (TensorMapData.identity Ms))).tensorMap) =
        (𝟙 Q ⊗ₘ (tensorMapDataPrefixId xs
              (TensorMapData.cons (𝟙 M)
                (TensorMapData.cons b (TensorMapData.identity Ms)))).tensorMap) ≫
            (𝟙 Q ⊗ₘ (adjacentMergeAfter xs fR).tensorMap) +
          c • ((𝟙 Q ⊗ₘ (tensorMapDataPrefixId xs
              (TensorMapData.cons a
                (TensorMapData.cons (𝟙 N)
                  (TensorMapData.identity Ms)))).tensorMap) ≫
            (𝟙 Q ⊗ₘ (adjacentMergeAfter xs fL).tensorMap))
      rw [MonoidalCategory.tensorHom_comp_tensorHom, ih]
      simp only [Category.comp_id, id_tensorHom,
        MonoidalPreadditive.whiskerLeft_add, whiskerLeft_comp, add_right_inj]
      let l := (tensorMapDataPrefixId xs
        (TensorMapData.cons a
          (TensorMapData.cons (𝟙 N) (TensorMapData.identity Ms)))).tensorMap
      let r := (adjacentMergeAfter xs (ys := Ms) fL).tensorMap
      have hz : ((tensoringLeft (ModuleCat.{0} ℤ)).obj Q).map
          (c • (l ≫ r)) =
          c • ((tensoringLeft (ModuleCat.{0} ℤ)).obj Q).map (l ≫ r) :=
        Functor.map_zsmul ((tensoringLeft (ModuleCat.{0} ℤ)).obj Q)
      exact hz.trans (congrArg (c • ·)
        (((tensoringLeft (ModuleCat.{0} ℤ)).obj Q).map_comp l r))

def tensorMapDataPrefixOfFn : {k : ℕ} →
    (M N : Fin k → ModuleCat.{0} ℤ) → ((i : Fin k) → M i ⟶ N i) →
    {source target : List (ModuleCat.{0} ℤ)} → TensorMapData source target →
      TensorMapData (finFamilyList M ++ source) (finFamilyList N ++ target)
  | 0, _, _, _, _, _, tail => tail
  | k + 1, M, N, f, _, _, tail => .cons (f 0)
      (tensorMapDataPrefixOfFn (fun i : Fin k ↦ M i.succ)
        (fun i : Fin k ↦ N i.succ) (fun i ↦ f i.succ) tail)

theorem adjacentMergeAfter_naturality_ofFn
    {k l : ℕ} (Mleft Nleft : Fin k → ModuleCat.{0} ℤ)
    (Mboundary Mboundary' Nboundary Nboundary' Pboundary Pboundary' :
      ModuleCat.{0} ℤ)
    (Mright Nright : Fin l → ModuleCat.{0} ℤ)
    (f : Mboundary ⊗ Nboundary ⟶ Pboundary)
    (f' : Mboundary' ⊗ Nboundary' ⟶ Pboundary')
    (fleft : (i : Fin k) → Mleft i ⟶ Nleft i)
    (a : Mboundary ⟶ Mboundary') (b : Nboundary ⟶ Nboundary')
    (c : Pboundary ⟶ Pboundary')
    (fright : (i : Fin l) → Mright i ⟶ Nright i)
    (h : (a ⊗ₘ b) ≫ f' = f ≫ c) :
    AdjacentMergeNaturality
      (adjacentMergeAfter (finFamilyList Mleft) f)
      (adjacentMergeAfter (finFamilyList Nleft) f')
      (tensorMapDataPrefixOfFn Mleft Nleft fleft
        (.cons a (.cons b (TensorMapData.ofFn Mright Nright fright))))
      (tensorMapDataPrefixOfFn Mleft Nleft fleft
        (.cons c (TensorMapData.ofFn Mright Nright fright))) := by
  induction k with
  | zero =>
      exact AdjacentMergeNaturality.head f f' a b c
        (TensorMapData.ofFn Mright Nright fright) h
  | succ k ih =>
      exact AdjacentMergeNaturality.tail (fleft 0)
        (ih (fun q : Fin k ↦ Mleft q.succ) (fun q : Fin k ↦ Nleft q.succ)
          (fun q ↦ fleft q.succ))

theorem factorDifferential_eqToHom_of_ne_comp
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (q r : Fin (w.length + 1)) (h : q ≠ r) :
    ∃ hM : factorModule d r = factorModule (d.raise q) r,
      factorDifferential d q r = eqToHom hM := by
  have hM : factorModule d r = factorModule (d.raise q) r := by
    simp [factorModule, DegreeProfile.raise, Ne.symm h]
  have hfd : HEq (factorDifferential d q r) (𝟙 (factorModule d r)) := by
    simpa [factorDifferential, DegreeProfile.raise, factorModule, Ne.symm h] using
      (eqToHom_heq_id_dom (factorModule d r) (factorModule (d.raise q) r) hM)
  exact ⟨hM, eq_of_heq (hfd.trans (test_eqToHom_heq_id hM).symm)⟩

def finiteFamilyPrefixBoundarySuffix {α : Type*} : {k l : ℕ} →
    (Fin k → α) → α → (Fin l → α) → Fin ((l + k) + 1) → α
  | 0, _, _, boundary, right => Fin.cases boundary right
  | k + 1, _, left, boundary, right =>
      Fin.cases (left 0)
        (finiteFamilyPrefixBoundarySuffix
          (fun i : Fin k ↦ left i.succ) boundary right)

theorem finFamilyList_finiteFamilyPrefixBoundarySuffix
    {α : Type*} {k l : ℕ} (left : Fin k → α) (boundary : α)
    (right : Fin l → α) :
    finFamilyList (finiteFamilyPrefixBoundarySuffix left boundary right) =
      finFamilyList left ++ boundary :: finFamilyList right := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change left 0 ::
          finFamilyList (finiteFamilyPrefixBoundarySuffix
            (fun i : Fin k ↦ left i.succ) boundary right) =
        left 0 :: (finFamilyList (fun i : Fin k ↦ left i.succ) ++
          boundary :: finFamilyList right)
      exact congrArg (left 0 :: ·) (ih (fun i ↦ left i.succ))

def finiteFamilyPrefixBoundarySuffixMap : {k l : ℕ} →
    (Mleft Nleft : Fin k → ModuleCat.{0} ℤ) →
    (Mboundary Nboundary : ModuleCat.{0} ℤ) →
    (Mright Nright : Fin l → ModuleCat.{0} ℤ) →
    ((i : Fin k) → Mleft i ⟶ Nleft i) →
    (Mboundary ⟶ Nboundary) →
    ((i : Fin l) → Mright i ⟶ Nright i) →
    ((q : Fin ((l + k) + 1)) →
      finiteFamilyPrefixBoundarySuffix Mleft Mboundary Mright q ⟶
        finiteFamilyPrefixBoundarySuffix Nleft Nboundary Nright q)
  | 0, _, _, _, _, _, _, _, _, fboundary, fright =>
      Fin.cases fboundary fright
  | k + 1, _, Mleft, Nleft, Mboundary, Nboundary, Mright, Nright,
      fleft, fboundary, fright =>
      Fin.cases (fleft 0)
        (finiteFamilyPrefixBoundarySuffixMap
          (fun i : Fin k ↦ Mleft i.succ)
          (fun i : Fin k ↦ Nleft i.succ)
          Mboundary Nboundary Mright Nright
          (fun i ↦ fleft i.succ) fboundary fright)

def finiteFamilyPrefixIndex {l : ℕ} : {k : ℕ} → Fin k → Fin ((l + k) + 1)
  | 0, i => Fin.elim0 i
  | _ + 1, i => Fin.cases 0 (fun q ↦ (finiteFamilyPrefixIndex q).succ) i

def finiteFamilyBoundaryIndex : (k l : ℕ) → Fin ((l + k) + 1)
  | 0, _ => 0
  | k + 1, l => (finiteFamilyBoundaryIndex k l).succ

def finiteFamilySuffixIndex {l : ℕ} : (k : ℕ) → Fin l → Fin ((l + k) + 1)
  | 0, i => i.succ
  | k + 1, i => (finiteFamilySuffixIndex k i).succ

@[simp]
theorem finiteFamilyPrefixIndex_val {k l : ℕ} (i : Fin k) :
    (finiteFamilyPrefixIndex (l := l) i).val = i.val := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i => simp [finiteFamilyPrefixIndex, ih]

@[simp]
theorem finiteFamilyBoundaryIndex_val (k l : ℕ) :
    (finiteFamilyBoundaryIndex k l).val = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [finiteFamilyBoundaryIndex, ih]

@[simp]
theorem finiteFamilySuffixIndex_val {k l : ℕ} (i : Fin l) :
    (finiteFamilySuffixIndex k i).val = k + 1 + i.val := by
  induction k with
  | zero => simp [finiteFamilySuffixIndex, Nat.add_comm]
  | succ k ih =>
      simp [finiteFamilySuffixIndex, ih]
      omega

theorem finiteFamilyPrefixBoundarySuffixIndex_cases
    {k l : ℕ} (q : Fin ((l + k) + 1)) :
    (∃ i : Fin k, q = finiteFamilyPrefixIndex i) ∨
      q = finiteFamilyBoundaryIndex k l ∨
        ∃ i : Fin l, q = finiteFamilySuffixIndex k i := by
  induction k with
  | zero =>
      cases q using Fin.cases with
      | zero => exact Or.inr (Or.inl rfl)
      | succ i => exact Or.inr (Or.inr ⟨i, rfl⟩)
  | succ k ih =>
      cases q using Fin.cases with
      | zero => exact Or.inl ⟨0, rfl⟩
      | succ q =>
          rcases ih q with ⟨i, hi⟩ | hi | ⟨i, hi⟩
          · exact Or.inl ⟨i.succ, congrArg Fin.succ hi⟩
          · exact Or.inr (Or.inl (congrArg Fin.succ hi))
          · exact Or.inr (Or.inr ⟨i, congrArg Fin.succ hi⟩)

theorem finiteFamilyPrefixBoundarySuffixMap_prefix_heq
    {k l : ℕ}
    (Mleft Nleft : Fin k → ModuleCat.{0} ℤ)
    (Mboundary Nboundary : ModuleCat.{0} ℤ)
    (Mright Nright : Fin l → ModuleCat.{0} ℤ)
    (fleft : (i : Fin k) → Mleft i ⟶ Nleft i)
    (fboundary : Mboundary ⟶ Nboundary)
    (fright : (i : Fin l) → Mright i ⟶ Nright i) (i : Fin k) :
    HEq
      (finiteFamilyPrefixBoundarySuffixMap Mleft Nleft Mboundary Nboundary
        Mright Nright fleft fboundary fright (finiteFamilyPrefixIndex i))
      (fleft i) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          exact ih (fun q : Fin k ↦ Mleft q.succ)
            (fun q : Fin k ↦ Nleft q.succ) (fun q ↦ fleft q.succ) i

theorem finiteFamilyPrefixBoundarySuffixMap_boundary_heq
    {k l : ℕ}
    (Mleft Nleft : Fin k → ModuleCat.{0} ℤ)
    (Mboundary Nboundary : ModuleCat.{0} ℤ)
    (Mright Nright : Fin l → ModuleCat.{0} ℤ)
    (fleft : (i : Fin k) → Mleft i ⟶ Nleft i)
    (fboundary : Mboundary ⟶ Nboundary)
    (fright : (i : Fin l) → Mright i ⟶ Nright i) :
    HEq
      (finiteFamilyPrefixBoundarySuffixMap Mleft Nleft Mboundary Nboundary
        Mright Nright fleft fboundary fright (finiteFamilyBoundaryIndex k l))
      fboundary := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact ih (fun q : Fin k ↦ Mleft q.succ)
        (fun q : Fin k ↦ Nleft q.succ) (fun q ↦ fleft q.succ)

theorem finiteFamilyPrefixBoundarySuffixMap_suffix_heq
    {k l : ℕ}
    (Mleft Nleft : Fin k → ModuleCat.{0} ℤ)
    (Mboundary Nboundary : ModuleCat.{0} ℤ)
    (Mright Nright : Fin l → ModuleCat.{0} ℤ)
    (fleft : (i : Fin k) → Mleft i ⟶ Nleft i)
    (fboundary : Mboundary ⟶ Nboundary)
    (fright : (i : Fin l) → Mright i ⟶ Nright i) (i : Fin l) :
    HEq
      (finiteFamilyPrefixBoundarySuffixMap Mleft Nleft Mboundary Nboundary
        Mright Nright fleft fboundary fright (finiteFamilySuffixIndex k i))
      (fright i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact ih (fun q : Fin k ↦ Mleft q.succ)
        (fun q : Fin k ↦ Nleft q.succ) (fun q ↦ fleft q.succ)

theorem tensorMapDataPrefixId_cons_ofFn_heq
    {k l : ℕ}
    (Mleft : Fin k → ModuleCat.{0} ℤ)
    (Mboundary Nboundary : ModuleCat.{0} ℤ)
    (Mright Nright : Fin l → ModuleCat.{0} ℤ)
    (fboundary : Mboundary ⟶ Nboundary)
    (fright : (i : Fin l) → Mright i ⟶ Nright i) :
    HEq
      (tensorMapDataPrefixId (finFamilyList Mleft)
        (TensorMapData.cons fboundary
          (TensorMapData.ofFn Mright Nright fright)))
      (TensorMapData.ofFn
        (finiteFamilyPrefixBoundarySuffix Mleft Mboundary Mright)
        (finiteFamilyPrefixBoundarySuffix Mleft Nboundary Nright)
        (finiteFamilyPrefixBoundarySuffixMap Mleft Mleft Mboundary Nboundary
          Mright Nright (fun i ↦ 𝟙 (Mleft i)) fboundary fright)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let leftTail := fun i : Fin k ↦ Mleft i.succ
      let fs := tensorMapDataPrefixId (finFamilyList leftTail)
        (TensorMapData.cons fboundary
          (TensorMapData.ofFn Mright Nright fright))
      let gs := TensorMapData.ofFn
        (finiteFamilyPrefixBoundarySuffix leftTail Mboundary Mright)
        (finiteFamilyPrefixBoundarySuffix leftTail Nboundary Nright)
        (finiteFamilyPrefixBoundarySuffixMap leftTail leftTail
          Mboundary Nboundary Mright Nright (fun i ↦ 𝟙 (leftTail i))
          fboundary fright)
      change HEq (TensorMapData.cons (𝟙 (Mleft 0)) fs)
        (TensorMapData.cons (𝟙 (Mleft 0)) gs)
      exact tensorMapData_cons_heq
        (f := 𝟙 (Mleft 0)) (g := 𝟙 (Mleft 0)) (fs := fs) (gs := gs)
        rfl rfl
        (finFamilyList_finiteFamilyPrefixBoundarySuffix
          leftTail Mboundary Mright).symm
        (finFamilyList_finiteFamilyPrefixBoundarySuffix
          leftTail Nboundary Nright).symm
        HEq.rfl (ih leftTail)

theorem finFamilyList_reindex
    {α : Type*} {k l : ℕ} (h : k = l) (M : Fin l → α) :
    finFamilyList (fun i : Fin k ↦ M (Fin.cast h i)) = finFamilyList M := by
  subst l
  rfl

theorem TensorMapData.ofFn_reindex_tensorMap_heq
    {k l : ℕ} (h : k = l)
    (M N : Fin l → ModuleCat.{0} ℤ) (f : (i : Fin l) → M i ⟶ N i) :
    HEq
      (TensorMapData.ofFn
        (fun i : Fin k ↦ M (Fin.cast h i))
        (fun i : Fin k ↦ N (Fin.cast h i))
        (fun i : Fin k ↦ f (Fin.cast h i))).tensorMap
      (TensorMapData.ofFn M N f).tensorMap := by
  subst l
  rfl

theorem compositionTargetInternalDifferential_append_right_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length)
    (hC : compositionBoundaryModule d e =
      compositionBoundaryModule d (e.raise j.succ)) :
    HEq
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons (eqToHom hC)
          (TensorMapData.ofFn
            (fun r : Fin v.length ↦ factorModule e r.succ)
            (fun r : Fin v.length ↦ factorModule (e.raise j.succ) r.succ)
            (fun r ↦ factorDifferential e j.succ r.succ)))).tensorMap
      (internalDifferentialTensorMap (d.append e) (appendRightArrowIndex j)) := by
  let Mleft := fun i : Fin w.length ↦ factorModule d i.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let Nright := fun r : Fin v.length ↦ factorModule (e.raise j.succ) r.succ
  let fright := fun r : Fin v.length ↦ factorDifferential e j.succ r.succ
  let explicitSource :=
    finiteFamilyPrefixBoundarySuffix Mleft (compositionBoundaryModule d e) Mright
  let explicitTarget := finiteFamilyPrefixBoundarySuffix Mleft
    (compositionBoundaryModule d (e.raise j.succ)) Nright
  let explicitMap := finiteFamilyPrefixBoundarySuffixMap Mleft Mleft
    (compositionBoundaryModule d e)
    (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
    (fun i ↦ 𝟙 (Mleft i)) (eqToHom hC) fright
  have hdata := tensorMapDataPrefixId_cons_ofFn_heq Mleft
    (compositionBoundaryModule d e)
    (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
    (eqToHom hC) fright
  have hdataMap := tensorMapData_tensorMap_heq
    (finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft
      (compositionBoundaryModule d e) Mright).symm
    (finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft
      (compositionBoundaryModule d (e.raise j.succ)) Nright).symm hdata
  have hleftExplicit : HEq
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons (eqToHom hC)
          (TensorMapData.ofFn Mright Nright fright))).tensorMap
      (TensorMapData.ofFn explicitSource explicitTarget explicitMap).tensorMap := by
    simpa [Mleft, Mright, Nright, fright, explicitSource, explicitTarget,
      explicitMap, compositionLeftPrefix] using hdataMap
  have hlen : (v.length + w.length) + 1 = (w.append v).length + 1 := by
    rw [append_length]
    omega
  let appendIndex := fun q : Fin ((v.length + w.length) + 1) ↦ Fin.cast hlen q
  let appendSource := fun q : Fin ((v.length + w.length) + 1) ↦
    factorModule (d.append e) (appendIndex q)
  let appendTarget := fun q : Fin ((v.length + w.length) + 1) ↦
    factorModule ((d.append e).raise (appendRightArrowIndex j)) (appendIndex q)
  let appendMap := fun q : Fin ((v.length + w.length) + 1) ↦
    factorDifferential (d.append e) (appendRightArrowIndex j) (appendIndex q)
  have hsourceList : finFamilyList explicitSource = finFamilyList appendSource := by
    calc
      _ = compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e := by
        simpa [explicitSource, Mleft, Mright, compositionLeftPrefix,
          compositionRightSuffix] using
            finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft
              (compositionBoundaryModule d e) Mright
      _ = finFamilyList (factorModule (d.append e)) :=
        (finFamilyList_factorModule_append_boundary d e).symm
      _ = finFamilyList appendSource := by
        simpa [appendSource, appendIndex] using
          (finFamilyList_reindex hlen (factorModule (d.append e))).symm
  have htot : n + (m + 1) = (n + m) + 1 := by omega
  have hraise := DegreeProfile.raise_append_right d e j
  have hfactor :
      finFamilyList (factorModule ((d.append (e.raise j.succ)).castTotal htot)) =
        finFamilyList (factorModule (d.append (e.raise j.succ))) := by
    rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
    apply (List.ofFn_inj).2
    funext i
    unfold factorModule
    rw [DegreeProfile.castTotal_arrowDegree]
  have hraisedList :
      finFamilyList
          (factorModule ((d.append e).raise (appendRightArrowIndex j))) =
        compositionLeftPrefix d ++
          compositionBoundaryModule d (e.raise j.succ) ::
            compositionRightSuffix (e.raise j.succ) := by
    rw [hraise, hfactor, finFamilyList_factorModule_append_boundary]
  have htargetList : finFamilyList explicitTarget = finFamilyList appendTarget := by
    calc
      _ = compositionLeftPrefix d ++
          compositionBoundaryModule d (e.raise j.succ) ::
            compositionRightSuffix (e.raise j.succ) := by
        simpa [explicitTarget, Mleft, Nright, compositionLeftPrefix,
          compositionRightSuffix] using
            finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft
              (compositionBoundaryModule d (e.raise j.succ)) Nright
      _ = finFamilyList
          (factorModule ((d.append e).raise (appendRightArrowIndex j))) :=
        hraisedList.symm
      _ = finFamilyList appendTarget := by
        simpa [appendTarget, appendIndex] using
          (finFamilyList_reindex hlen
            (factorModule ((d.append e).raise (appendRightArrowIndex j)))).symm
  have hsource : explicitSource = appendSource := by
    apply (List.ofFn_inj).1
    simpa only [← finFamilyList_eq_ofFn] using hsourceList
  have htarget : explicitTarget = appendTarget := by
    apply (List.ofFn_inj).1
    simpa only [← finFamilyList_eq_ofFn] using htargetList
  have hpointwise : ∀ q, HEq (explicitMap q) (appendMap q) := by
    intro q
    rcases finiteFamilyPrefixBoundarySuffixIndex_cases q with
      ⟨i, hi⟩ | hi | ⟨r, hr⟩
    · subst q
      have hindex : appendIndex (finiteFamilyPrefixIndex i) =
          appendLeftArrowIndex (v := v) i := by
        apply Fin.ext
        simp [appendIndex, appendLeftArrowIndex]
      have hne : appendRightArrowIndex (w := w) j ≠
          appendLeftArrowIndex (v := v) i := by
        intro h
        have hv := congrArg Fin.val h
        simp [appendRightArrowIndex, appendLeftArrowIndex] at hv
        omega
      obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne_comp
        (d.append e) (appendRightArrowIndex j) (appendLeftArrowIndex i) hne
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Mleft
          (compositionBoundaryModule d e)
          (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
          (fun i ↦ 𝟙 (Mleft i)) (eqToHom hC) fright
          (finiteFamilyPrefixIndex i))
        (factorDifferential (d.append e) (appendRightArrowIndex j)
          (appendIndex (finiteFamilyPrefixIndex i)))
      rw [hindex, hmap]
      exact (finiteFamilyPrefixBoundarySuffixMap_prefix_heq Mleft Mleft
        (compositionBoundaryModule d e)
        (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
        (fun i ↦ 𝟙 (Mleft i)) (eqToHom hC) fright i).trans
          (equalityTransport_heq_of_source_eq rfl hAB
            (factorModule_append_left d e i).symm)
    · subst q
      have hindex : appendIndex (finiteFamilyBoundaryIndex w.length v.length) =
          appendBoundaryArrowIndex w v := by
        apply Fin.ext
        simp [appendIndex, appendBoundaryArrowIndex]
      have hne : appendRightArrowIndex (w := w) j ≠
          appendBoundaryArrowIndex w v := by
        intro h
        have hv := congrArg Fin.val h
        (simp [appendRightArrowIndex, appendBoundaryArrowIndex] at hv; omega)
      obtain ⟨hAB, hmap⟩ := factorDifferential_eqToHom_of_ne_comp
        (d.append e) (appendRightArrowIndex j) (appendBoundaryArrowIndex w v) hne
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Mleft
          (compositionBoundaryModule d e)
          (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
          (fun i ↦ 𝟙 (Mleft i)) (eqToHom hC) fright
          (finiteFamilyBoundaryIndex w.length v.length))
        (factorDifferential (d.append e) (appendRightArrowIndex j)
          (appendIndex (finiteFamilyBoundaryIndex w.length v.length)))
      rw [hindex, hmap]
      exact (finiteFamilyPrefixBoundarySuffixMap_boundary_heq Mleft Mleft
        (compositionBoundaryModule d e)
        (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
        (fun i ↦ 𝟙 (Mleft i)) (eqToHom hC) fright).trans
          (equalityTransport_heq_of_source_eq hC hAB
            (factorModule_append_boundary d e).symm)
    · subst q
      have hindex : appendIndex (finiteFamilySuffixIndex w.length r) =
          appendRightArrowIndex (w := w) r := by
        apply Fin.ext
        simp [appendIndex, appendRightArrowIndex]
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Mleft
          (compositionBoundaryModule d e)
          (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
          (fun i ↦ 𝟙 (Mleft i)) (eqToHom hC) fright
          (finiteFamilySuffixIndex w.length r))
        (factorDifferential (d.append e) (appendRightArrowIndex j)
          (appendIndex (finiteFamilySuffixIndex w.length r)))
      rw [hindex]
      refine (finiteFamilyPrefixBoundarySuffixMap_suffix_heq Mleft Mleft
        (compositionBoundaryModule d e)
        (compositionBoundaryModule d (e.raise j.succ)) Mright Nright
        (fun i ↦ 𝟙 (Mleft i)) (eqToHom hC) fright r).trans ?_
      by_cases hrj : r = j
      · subst r
        have hraw : HEq (factorDifferential e j.succ j.succ)
            ((dgHomZModuleCochainComplex
              (v.arrowSource j.succ) (v.arrowTarget j.succ)).d
                (e.arrowDegree j.succ) (e.arrowDegree j.succ + 1)) := by
          unfold factorDifferential
          simp only [eq_self, dif_pos]
          apply dgHomDifferential_heq <;> simp [DegreeProfile.raise]
        exact hraw.trans (factorDifferential_append_right_heq d e j).symm
      · have hq : j.succ ≠ r.succ := by
          intro h
          exact hrj (Fin.succ_injective _ h.symm)
        obtain ⟨hE, hEmap⟩ := factorDifferential_eqToHom_of_ne_comp
          e j.succ r.succ hq
        have happend : appendRightArrowIndex (w := w) j ≠
            appendRightArrowIndex r := by
          intro h
          apply hrj
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa [appendRightArrowIndex] using hv.symm
        obtain ⟨hA, hAmap⟩ := factorDifferential_eqToHom_of_ne_comp
          (d.append e) (appendRightArrowIndex j) (appendRightArrowIndex r) happend
        dsimp [fright]
        rw [hEmap, hAmap]
        exact equalityTransport_heq_of_source_eq hE hA
          (factorModule_append_right d e r).symm
  have hcanonical := TensorMapData.ofFn_tensorMap_heq_of_pointwise
    explicitSource explicitTarget appendSource appendTarget explicitMap appendMap
    hsource htarget hpointwise
  have hreindex := TensorMapData.ofFn_reindex_tensorMap_heq hlen
    (factorModule (d.append e))
    (factorModule ((d.append e).raise (appendRightArrowIndex j)))
    (factorDifferential (d.append e) (appendRightArrowIndex j))
  simpa [appendSource, appendTarget, appendMap, appendIndex, summandModule,
    internalDifferentialTensorMap] using hleftExplicit.trans (hcanonical.trans hreindex)

theorem summandCompositionMap_internalDifferential_append_right_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    HEq
      (summandCompositionMap d e ≫
        internalDifferentialTensorMap (d.append e) (appendRightArrowIndex j))
      ((𝟙 (summandModule d) ⊗ₘ internalDifferentialTensorMap e j.succ) ≫
        summandCompositionMap d (e.raise j.succ)) := by
  rw [summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized]
  rw [normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder]
  dsimp only [summandModule]
  simp only [Category.assoc]
  rw [tensorModuleListAppendIso_whiskerLeft_assoc]
  let A := (tensorModuleListAppendIso (finFamilyList (factorModule d))
    (finFamilyList (factorModule e))).hom
  let R := summandCompositionRemainder d e
  let D := internalDifferentialTensorMap (d.append e) (appendRightArrowIndex j)
  let W := tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
    (internalDifferentialTensorMap e j.succ)
  let R' := summandCompositionRemainder d (e.raise j.succ)
  change HEq ((A ≫ R) ≫ D) ((A ≫ W) ≫ R')
  have htot : n + (m + 1) = (n + m) + 1 := by omega
  have hraise := DegreeProfile.raise_append_right d e j
  have hfactor :
      finFamilyList (factorModule ((d.append (e.raise j.succ)).castTotal htot)) =
        finFamilyList (factorModule (d.append (e.raise j.succ))) := by
    rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
    apply (List.ofFn_inj).2
    funext i
    unfold factorModule
    rw [DegreeProfile.castTotal_arrowDegree]
  have hcast : summandModule ((d.append (e.raise j.succ)).castTotal htot) =
      summandModule (d.append (e.raise j.succ)) :=
    congrArg tensorModuleList hfactor
  have ht := (congrArg summandModule hraise).trans hcast
  rw [Category.assoc, Category.assoc]
  refine CategoryTheory.heq_comp
    (f := A) (g := R ≫ D) (f' := A) (g' := W ≫ R')
    rfl rfl ht HEq.rfl ?_
  dsimp [R, R', summandCompositionRemainder]
  change HEq
    ((eqToHom (congrArg tensorModuleList (compositionSourceListEq d e)) ≫
        eqToHom (congrArg tensorModuleList (compositionBoundaryListEq d e)) ≫
        (adjacentMergeAfter (compositionLeftPrefix d)
          (compositionBoundaryMap d e)).tensorMap ≫
        eqToHom (congrArg tensorModuleList (compositionTargetListEq d e))) ≫ D)
    (W ≫
      eqToHom (congrArg tensorModuleList
        (compositionSourceListEq d (e.raise j.succ))) ≫
      eqToHom (congrArg tensorModuleList
        (compositionBoundaryListEq d (e.raise j.succ))) ≫
      (adjacentMergeAfter (compositionLeftPrefix d)
        (compositionBoundaryMap d (e.raise j.succ))).tensorMap ≫
      eqToHom (congrArg tensorModuleList
        (compositionTargetListEq d (e.raise j.succ))))
  have hq : j.succ ≠ (0 : Fin (v.length + 1)) := Fin.succ_ne_zero j
  obtain ⟨hB, hBmap⟩ := factorDifferential_eqToHom_of_ne_comp e j.succ 0 hq
  have hC : compositionBoundaryModule d e =
      compositionBoundaryModule d (e.raise j.succ) := by
    unfold compositionBoundaryModule
    congr 1
    simp [DegreeProfile.raise, Ne.symm hq]
  let tailMap : TensorMapData (compositionRightSuffix e)
      (compositionRightSuffix (e.raise j.succ)) :=
    TensorMapData.ofFn
      (fun r : Fin v.length ↦ factorModule e r.succ)
      (fun r : Fin v.length ↦ factorModule (e.raise j.succ) r.succ)
      (fun r ↦ factorDifferential e j.succ r.succ)
  have hboundary :
      (𝟙 (factorModule d (Fin.last w.length)) ⊗ₘ eqToHom hB) ≫
          compositionBoundaryMap d (e.raise j.succ) =
        compositionBoundaryMap d e ≫ eqToHom hC := by
    exact test_tensor_comp_transport_of_heq rfl hB hC
      (compositionBoundaryMap d e)
      (compositionBoundaryMap d (e.raise j.succ))
      (compositionBoundaryMap_raise_right_internal_heq d e j)
  have hnatural := adjacentMergeAfter_naturality
    (compositionLeftPrefix d)
    (compositionBoundaryMap d e)
    (compositionBoundaryMap d (e.raise j.succ))
    (𝟙 _) (eqToHom hB) (eqToHom hC) tailMap hboundary
  have hcomm := hnatural.tensorMap_comm
  rw [tensorMapDataPrefixId_tensorMap,
    tensorMapDataPrefixId_tensorMap] at hcomm
  let hS := congrArg tensorModuleList (compositionSourceListEq d e)
  let hBdy := congrArg tensorModuleList (compositionBoundaryListEq d e)
  let hT := congrArg tensorModuleList (compositionTargetListEq d e)
  let hS' := congrArg tensorModuleList
    (compositionSourceListEq d (e.raise j.succ))
  let hBdy' := congrArg tensorModuleList
    (compositionBoundaryListEq d (e.raise j.succ))
  let hT' := congrArg tensorModuleList
    (compositionTargetListEq d (e.raise j.succ))
  let sourceMap :=
    (tensorMapDataPrefixId (compositionLeftPrefix d)
      (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length)))
        (TensorMapData.cons (eqToHom hB) tailMap))).tensorMap
  let targetMap :=
    (tensorMapDataPrefixId (compositionLeftPrefix d)
      (TensorMapData.cons (eqToHom hC) tailMap)).tensorMap
  have tensorMapData_tensorMap_heq_local :
      ∀ {source target source' target' : List (ModuleCat.{0} ℤ)}
        {f : TensorMapData source target} {g : TensorMapData source' target'},
        source = source' → target = target' → HEq f g →
          HEq (f.tensorMap) (g.tensorMap) := by
    intro source target source' target' f g hs ht h
    subst source'
    subst target'
    have hfg : f = g := eq_of_heq h
    subst g
    rfl
  have hdata : HEq
      (TensorMapData.ofFn (factorModule e)
        (factorModule (e.raise j.succ))
        (factorDifferential e j.succ))
      (TensorMapData.cons (eqToHom hB) tailMap) := by
    cases v with
    | mk k intermediate =>
        cases k with
        | zero => exact Fin.elim0 j
        | succ k =>
            change HEq
              (TensorMapData.cons (factorDifferential e j.succ 0)
                (TensorMapData.ofFn
                  (fun i : Fin (k + 1) ↦ factorModule e i.succ)
                  (fun i : Fin (k + 1) ↦ factorModule (e.raise j.succ) i.succ)
                  (fun i ↦ factorDifferential e j.succ i.succ)))
              (TensorMapData.cons (eqToHom hB) tailMap)
            apply tensorMapData_cons_heq rfl rfl rfl rfl
            · exact heq_of_eq hBmap
            · exact HEq.rfl
  have hdataMap := tensorMapData_tensorMap_heq_local rfl rfl hdata
  have tensorMapDataPrefixId_heq_local :
      ∀ (xs : List (ModuleCat.{0} ℤ))
        {source target source' target' : List (ModuleCat.{0} ℤ)}
        {f : TensorMapData source target} {g : TensorMapData source' target'},
        source = source' → target = target' → HEq f g →
          HEq (tensorMapDataPrefixId xs f) (tensorMapDataPrefixId xs g) := by
    intro xs
    induction xs with
    | nil =>
        intro source target source' target' f g hs ht h
        exact h
    | cons M xs ih =>
        intro source target source' target' f g hs ht h
        change HEq
          (TensorMapData.cons (𝟙 M) (tensorMapDataPrefixId xs f))
          (TensorMapData.cons (𝟙 M) (tensorMapDataPrefixId xs g))
        apply tensorMapData_cons_heq rfl rfl
          (congrArg (List.append xs) hs)
          (congrArg (List.append xs) ht) HEq.rfl
        exact ih hs ht h
  let prefixLast := compositionLeftPrefix d ++
    [factorModule d (Fin.last w.length)]
  let fullData := TensorMapData.ofFn (factorModule e)
    (factorModule (e.raise j.succ)) (factorDifferential e j.succ)
  have hinnerData : HEq
      (tensorMapDataPrefixId [factorModule d (Fin.last w.length)] fullData)
      (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length)))
        (TensorMapData.cons (eqToHom hB) tailMap)) := by
    change HEq
      (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length))) fullData)
      (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length)))
        (TensorMapData.cons (eqToHom hB) tailMap))
    apply tensorMapData_cons_heq rfl rfl
      (finFamilyList_factorModule_eq_first_suffix e)
      (finFamilyList_factorModule_eq_first_suffix (e.raise j.succ)) HEq.rfl
    exact hdata
  have hprefixData : HEq
      (tensorMapDataPrefixId prefixLast fullData)
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length)))
          (TensorMapData.cons (eqToHom hB) tailMap))) := by
    have happ := tensorMapDataPrefixId_append_heq
      (compositionLeftPrefix d)
      [factorModule d (Fin.last w.length)] fullData
    have hcongr := tensorMapDataPrefixId_heq_local
      (compositionLeftPrefix d)
      (congrArg (List.append [factorModule d (Fin.last w.length)])
        (finFamilyList_factorModule_eq_first_suffix e))
      (congrArg (List.append [factorModule d (Fin.last w.length)])
        (finFamilyList_factorModule_eq_first_suffix (e.raise j.succ)))
      hinnerData
    exact happ.trans hcongr
  have hsourceSplit : HEq sourceMap
      (tensorModuleListWhiskerLeft prefixLast
        (internalDifferentialTensorMap e j.succ)) := by
    have hmap := tensorMapData_tensorMap_heq_local
      (by
        rw [List.append_assoc,
          finFamilyList_factorModule_eq_first_suffix e]
        rfl)
      (by
        rw [List.append_assoc,
          finFamilyList_factorModule_eq_first_suffix (e.raise j.succ)]
        rfl)
      hprefixData
    have hleft := tensorMapDataPrefixId_tensorMap prefixLast fullData
    have hchain := hmap.symm.trans (heq_of_eq hleft)
    simpa [fullData, internalDifferentialTensorMap] using hchain
  have hsplitCanonical : HEq
      (tensorModuleListWhiskerLeft prefixLast
        (internalDifferentialTensorMap e j.succ)) W := by
    have hp : prefixLast = finFamilyList (factorModule d) := by
      exact finFamilyList_factorModule_eq_prefix_last d |>.symm
    simpa [W] using congr_arg_heq
      (fun xs ↦ tensorModuleListWhiskerLeft xs
        (internalDifferentialTensorMap e j.succ)) hp
  have hsourceCore : HEq sourceMap W := hsourceSplit.trans hsplitCanonical
  let hpreL := hS.trans hBdy
  let hpreR := hS'.trans hBdy'
  have hsourceTransport : HEq
      (eqToHom hS ≫ eqToHom hBdy ≫ sourceMap)
      (W ≫ eqToHom hS' ≫ eqToHom hBdy') := by
    have hleftStep : HEq
        ((eqToHom hS ≫ eqToHom hBdy) ≫ sourceMap) W := by
      simpa only [Category.id_comp] using
        (CategoryTheory.heq_comp
          (f := eqToHom hS ≫ eqToHom hBdy)
          (g := sourceMap)
          (f' := 𝟙 _)
          (g' := W)
          rfl hpreL.symm hpreR.symm
          (eqToHom_comp_heq_id hS hBdy) hsourceCore)
    have hrightStep : HEq W
        (W ≫ eqToHom hS' ≫ eqToHom hBdy') := by
      simpa only [Category.comp_id, Category.assoc] using
        (CategoryTheory.heq_comp
          (f := W) (g := 𝟙 _) (f' := W)
          (g' := eqToHom hS' ≫ eqToHom hBdy')
          rfl rfl hpreR HEq.rfl
          (eqToHom_comp_heq_id hS' hBdy').symm)
    exact hleftStep.trans hrightStep
  have htargetCore : HEq targetMap D :=
    compositionTargetInternalDifferential_append_right_heq d e j hC
  have htargetTransport : HEq (eqToHom hT ≫ D)
      (targetMap ≫ eqToHom hT') :=
    (CategoryTheory.eqToHom_comp_heq D hT).trans
      (htargetCore.symm.trans
        (CategoryTheory.comp_eqToHom_heq targetMap hT').symm)
  let mergeMap :=
    (adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix e)
      (compositionBoundaryMap d e)).tensorMap
  let mergeMap' :=
    (adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix (e.raise j.succ))
      (compositionBoundaryMap d (e.raise j.succ))).tensorMap
  have hcomm' : sourceMap ≫ mergeMap' = mergeMap ≫ targetMap := by
    simpa [sourceMap, targetMap, mergeMap, mergeMap',
      tensorMapDataPrefixId_tensorMap] using hcomm
  let pre := eqToHom hS ≫ eqToHom hBdy
  let pre' := eqToHom hS' ≫ eqToHom hBdy'
  have htargetWhisker : HEq
      ((pre ≫ mergeMap) ≫ (eqToHom hT ≫ D))
      ((pre ≫ mergeMap) ≫ (targetMap ≫ eqToHom hT')) := by
    exact CategoryTheory.heq_comp rfl rfl ht HEq.rfl htargetTransport
  have hmiddle :
      pre ≫ mergeMap ≫ targetMap ≫ eqToHom hT' =
        pre ≫ sourceMap ≫ mergeMap' ≫ eqToHom hT' := by
    simpa only [Category.assoc] using
      congrArg (fun z ↦ pre ≫ z ≫ eqToHom hT') hcomm'.symm
  have hsourceWhisker : HEq
      ((pre ≫ sourceMap) ≫ (mergeMap' ≫ eqToHom hT'))
      ((W ≫ pre') ≫ (mergeMap' ≫ eqToHom hT')) := by
    exact CategoryTheory.heq_comp rfl rfl rfl hsourceTransport HEq.rfl
  simpa only [Category.assoc, pre, pre', mergeMap, mergeMap'] using
    htargetWhisker.trans (heq_of_eq hmiddle) |>.trans hsourceWhisker


theorem tensorMapDataPrefixOfFn_cons_ofFn_heq
    {k l : ℕ}
    (Mleft Nleft : Fin k → ModuleCat.{0} ℤ)
    (Mboundary Nboundary : ModuleCat.{0} ℤ)
    (Mright Nright : Fin l → ModuleCat.{0} ℤ)
    (fleft : (i : Fin k) → Mleft i ⟶ Nleft i)
    (fboundary : Mboundary ⟶ Nboundary)
    (fright : (i : Fin l) → Mright i ⟶ Nright i) :
    HEq
      (tensorMapDataPrefixOfFn Mleft Nleft fleft
        (.cons fboundary (TensorMapData.ofFn Mright Nright fright)))
      (TensorMapData.ofFn
        (finiteFamilyPrefixBoundarySuffix Mleft Mboundary Mright)
        (finiteFamilyPrefixBoundarySuffix Nleft Nboundary Nright)
        (finiteFamilyPrefixBoundarySuffixMap Mleft Nleft Mboundary Nboundary
          Mright Nright fleft fboundary fright)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let MleftTail := fun i : Fin k ↦ Mleft i.succ
      let NleftTail := fun i : Fin k ↦ Nleft i.succ
      let fleftTail := fun i : Fin k ↦ fleft i.succ
      let fs := tensorMapDataPrefixOfFn MleftTail NleftTail fleftTail
        (TensorMapData.cons fboundary (TensorMapData.ofFn Mright Nright fright))
      let gs := TensorMapData.ofFn
        (finiteFamilyPrefixBoundarySuffix MleftTail Mboundary Mright)
        (finiteFamilyPrefixBoundarySuffix NleftTail Nboundary Nright)
        (finiteFamilyPrefixBoundarySuffixMap MleftTail NleftTail
          Mboundary Nboundary Mright Nright fleftTail fboundary fright)
      change HEq (TensorMapData.cons (fleft 0) fs)
        (TensorMapData.cons (fleft 0) gs)
      exact tensorMapData_cons_heq
        (f := fleft 0) (g := fleft 0) (fs := fs) (gs := gs)
        rfl rfl
        (finFamilyList_finiteFamilyPrefixBoundarySuffix
          MleftTail Mboundary Mright).symm
        (finFamilyList_finiteFamilyPrefixBoundarySuffix
          NleftTail Nboundary Nright).symm
        HEq.rfl (ih MleftTail NleftTail fleftTail)

theorem compositionTargetInternalDifferential_append_left_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length)
    (hC : compositionBoundaryModule d e =
      compositionBoundaryModule (d.raise i.castSucc) e) :
    let Mleft := fun q : Fin w.length ↦ factorModule d q.castSucc
    let Nleft := fun q : Fin w.length ↦ factorModule (d.raise i.castSucc) q.castSucc
    let fleft := fun q : Fin w.length ↦ factorDifferential d i.castSucc q.castSucc
    let Mright := fun r : Fin v.length ↦ factorModule e r.succ
    let tailId := TensorMapData.ofFn Mright Mright (fun r ↦ 𝟙 (Mright r))
    HEq
      (tensorMapDataPrefixOfFn Mleft Nleft fleft
        (.cons (eqToHom hC) tailId)).tensorMap
      (internalDifferentialTensorMap (d.append e) (appendLeftArrowIndex i)) := by
  dsimp only
  let Mleft := fun q : Fin w.length ↦ factorModule d q.castSucc
  let Nleft := fun q : Fin w.length ↦ factorModule (d.raise i.castSucc) q.castSucc
  let fleft := fun q : Fin w.length ↦ factorDifferential d i.castSucc q.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let fright := fun r : Fin v.length ↦ 𝟙 (Mright r)
  let explicitSource :=
    finiteFamilyPrefixBoundarySuffix Mleft (compositionBoundaryModule d e) Mright
  let explicitTarget := finiteFamilyPrefixBoundarySuffix Nleft
    (compositionBoundaryModule (d.raise i.castSucc) e) Mright
  let explicitMap := finiteFamilyPrefixBoundarySuffixMap Mleft Nleft
    (compositionBoundaryModule d e)
    (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
    fleft (eqToHom hC) fright
  have hdata := tensorMapDataPrefixOfFn_cons_ofFn_heq Mleft Nleft
    (compositionBoundaryModule d e)
    (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
    fleft (eqToHom hC) fright
  have hdataMap := tensorMapData_tensorMap_heq
    (finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft
      (compositionBoundaryModule d e) Mright).symm
    (finFamilyList_finiteFamilyPrefixBoundarySuffix Nleft
      (compositionBoundaryModule (d.raise i.castSucc) e) Mright).symm hdata
  have hleftExplicit : HEq
      (tensorMapDataPrefixOfFn Mleft Nleft fleft
        (.cons (eqToHom hC) (TensorMapData.ofFn Mright Mright fright))).tensorMap
      (TensorMapData.ofFn explicitSource explicitTarget explicitMap).tensorMap := by
    simpa [explicitSource, explicitTarget, explicitMap] using hdataMap
  have hlen : (v.length + w.length) + 1 = (w.append v).length + 1 := by
    rw [append_length]
    omega
  let appendIndex := fun q : Fin ((v.length + w.length) + 1) ↦ Fin.cast hlen q
  let appendSource := fun q : Fin ((v.length + w.length) + 1) ↦
    factorModule (d.append e) (appendIndex q)
  let appendTarget := fun q : Fin ((v.length + w.length) + 1) ↦
    factorModule ((d.append e).raise (appendLeftArrowIndex i)) (appendIndex q)
  let appendMap := fun q : Fin ((v.length + w.length) + 1) ↦
    factorDifferential (d.append e) (appendLeftArrowIndex i) (appendIndex q)
  have hsourceList : finFamilyList explicitSource = finFamilyList appendSource := by
    calc
      _ = compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e := by
        simpa [explicitSource, Mleft, Mright, compositionLeftPrefix,
          compositionRightSuffix] using
            finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft
              (compositionBoundaryModule d e) Mright
      _ = finFamilyList (factorModule (d.append e)) :=
        (finFamilyList_factorModule_append_boundary d e).symm
      _ = finFamilyList appendSource := by
        simpa [appendSource, appendIndex] using
          (finFamilyList_reindex hlen (factorModule (d.append e))).symm
  have htot : (n + 1) + m = (n + m) + 1 := by omega
  have hraise := DegreeProfile.raise_append_left d e i
  have hfactor :
      finFamilyList (factorModule (((d.raise i.castSucc).append e).castTotal htot)) =
        finFamilyList (factorModule ((d.raise i.castSucc).append e)) := by
    rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
    apply (List.ofFn_inj).2
    funext q
    unfold factorModule
    rw [DegreeProfile.castTotal_arrowDegree]
  have hraisedList :
      finFamilyList
          (factorModule ((d.append e).raise (appendLeftArrowIndex i))) =
        compositionLeftPrefix (d.raise i.castSucc) ++
          compositionBoundaryModule (d.raise i.castSucc) e ::
            compositionRightSuffix e := by
    rw [hraise, hfactor, finFamilyList_factorModule_append_boundary]
  have htargetList : finFamilyList explicitTarget = finFamilyList appendTarget := by
    calc
      _ = compositionLeftPrefix (d.raise i.castSucc) ++
          compositionBoundaryModule (d.raise i.castSucc) e ::
            compositionRightSuffix e := by
        simpa [explicitTarget, Nleft, Mright, compositionLeftPrefix,
          compositionRightSuffix] using
            finFamilyList_finiteFamilyPrefixBoundarySuffix Nleft
              (compositionBoundaryModule (d.raise i.castSucc) e) Mright
      _ = finFamilyList
          (factorModule ((d.append e).raise (appendLeftArrowIndex i))) :=
        hraisedList.symm
      _ = finFamilyList appendTarget := by
        simpa [appendTarget, appendIndex] using
          (finFamilyList_reindex hlen
            (factorModule ((d.append e).raise (appendLeftArrowIndex i)))).symm
  have hsource : explicitSource = appendSource := by
    apply (List.ofFn_inj).1
    simpa only [← finFamilyList_eq_ofFn] using hsourceList
  have htarget : explicitTarget = appendTarget := by
    apply (List.ofFn_inj).1
    simpa only [← finFamilyList_eq_ofFn] using htargetList
  have hpointwise : ∀ q, HEq (explicitMap q) (appendMap q) := by
    intro q
    rcases finiteFamilyPrefixBoundarySuffixIndex_cases q with
      ⟨r, hr⟩ | hr | ⟨r, hr⟩
    · subst q
      have hindex : appendIndex (finiteFamilyPrefixIndex r) =
          appendLeftArrowIndex (v := v) r := by
        apply Fin.ext
        simp [appendIndex, appendLeftArrowIndex]
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Nleft
          (compositionBoundaryModule d e)
          (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
          fleft (eqToHom hC) fright (finiteFamilyPrefixIndex r))
        (factorDifferential (d.append e) (appendLeftArrowIndex i)
          (appendIndex (finiteFamilyPrefixIndex r)))
      rw [hindex]
      refine (finiteFamilyPrefixBoundarySuffixMap_prefix_heq Mleft Nleft
        (compositionBoundaryModule d e)
        (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
        fleft (eqToHom hC) fright r).trans ?_
      by_cases hri : r = i
      · subst r
        have hraw : HEq (factorDifferential d i.castSucc i.castSucc)
            ((dgHomZModuleCochainComplex
              (w.arrowSource i.castSucc) (w.arrowTarget i.castSucc)).d
                (d.arrowDegree i.castSucc) (d.arrowDegree i.castSucc + 1)) := by
          unfold factorDifferential
          simp only [eq_self, dif_pos]
          apply dgHomDifferential_heq <;> simp [DegreeProfile.raise]
        exact hraw.trans (factorDifferential_append_left_heq d e i).symm
      · have hq : i.castSucc ≠ r.castSucc := by
          intro h
          exact hri (Fin.castSucc_injective _ h.symm)
        obtain ⟨hD, hDmap⟩ := factorDifferential_eqToHom_of_ne_comp
          d i.castSucc r.castSucc hq
        have happend : appendLeftArrowIndex (v := v) i ≠
            appendLeftArrowIndex r := by
          intro h
          apply hri
          apply Fin.ext
          have hv := congrArg Fin.val h
          simpa [appendLeftArrowIndex] using hv.symm
        obtain ⟨hA, hAmap⟩ := factorDifferential_eqToHom_of_ne_comp
          (d.append e) (appendLeftArrowIndex i) (appendLeftArrowIndex r) happend
        dsimp [fleft]
        rw [hDmap, hAmap]
        exact equalityTransport_heq_of_source_eq hD hA
          (factorModule_append_left d e r).symm
    · subst q
      have hindex : appendIndex (finiteFamilyBoundaryIndex w.length v.length) =
          appendBoundaryArrowIndex w v := by
        apply Fin.ext
        simp [appendIndex, appendBoundaryArrowIndex]
      have hne : appendLeftArrowIndex (v := v) i ≠
          appendBoundaryArrowIndex w v := by
        intro h
        have hv := congrArg Fin.val h
        simp [appendLeftArrowIndex, appendBoundaryArrowIndex] at hv
        omega
      obtain ⟨hA, hAmap⟩ := factorDifferential_eqToHom_of_ne_comp
        (d.append e) (appendLeftArrowIndex i) (appendBoundaryArrowIndex w v) hne
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Nleft
          (compositionBoundaryModule d e)
          (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
          fleft (eqToHom hC) fright
          (finiteFamilyBoundaryIndex w.length v.length))
        (factorDifferential (d.append e) (appendLeftArrowIndex i)
          (appendIndex (finiteFamilyBoundaryIndex w.length v.length)))
      rw [hindex, hAmap]
      exact (finiteFamilyPrefixBoundarySuffixMap_boundary_heq Mleft Nleft
        (compositionBoundaryModule d e)
        (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
        fleft (eqToHom hC) fright).trans
          (equalityTransport_heq_of_source_eq hC hA
            (factorModule_append_boundary d e).symm)
    · subst q
      have hindex : appendIndex (finiteFamilySuffixIndex w.length r) =
          appendRightArrowIndex (w := w) r := by
        apply Fin.ext
        simp [appendIndex, appendRightArrowIndex]
      have hne : appendLeftArrowIndex (v := v) i ≠
          appendRightArrowIndex (w := w) r := by
        intro h
        have hv := congrArg Fin.val h
        simp [appendLeftArrowIndex, appendRightArrowIndex] at hv
        omega
      obtain ⟨hA, hAmap⟩ := factorDifferential_eqToHom_of_ne_comp
        (d.append e) (appendLeftArrowIndex i) (appendRightArrowIndex r) hne
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Nleft
          (compositionBoundaryModule d e)
          (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
          fleft (eqToHom hC) fright (finiteFamilySuffixIndex w.length r))
        (factorDifferential (d.append e) (appendLeftArrowIndex i)
          (appendIndex (finiteFamilySuffixIndex w.length r)))
      rw [hindex, hAmap]
      exact (finiteFamilyPrefixBoundarySuffixMap_suffix_heq Mleft Nleft
        (compositionBoundaryModule d e)
        (compositionBoundaryModule (d.raise i.castSucc) e) Mright Mright
        fleft (eqToHom hC) fright r).trans
          (equalityTransport_heq_of_source_eq rfl hA
            (factorModule_append_right d e r).symm)
  have hcanonical := TensorMapData.ofFn_tensorMap_heq_of_pointwise
    explicitSource explicitTarget appendSource appendTarget explicitMap appendMap
    hsource htarget hpointwise
  have hreindex := TensorMapData.ofFn_reindex_tensorMap_heq hlen
    (factorModule (d.append e))
    (factorModule ((d.append e).raise (appendLeftArrowIndex i)))
    (factorDifferential (d.append e) (appendLeftArrowIndex i))
  simpa [appendSource, appendTarget, appendMap, appendIndex, summandModule,
    internalDifferentialTensorMap, fright] using
      hleftExplicit.trans (hcanonical.trans hreindex)

theorem appendLeftTargetTransport_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length)
    (hC : compositionBoundaryModule d e =
      compositionBoundaryModule (d.raise i.castSucc) e) :
  let Mleft := fun q : Fin w.length ↦ factorModule d q.castSucc
  let Nleft := fun q : Fin w.length ↦ factorModule (d.raise i.castSucc) q.castSucc
  let fleft := fun q : Fin w.length ↦ factorDifferential d i.castSucc q.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let tailId := TensorMapData.ofFn Mright Mright (fun r ↦ 𝟙 (Mright r))
  let targetData := tensorMapDataPrefixOfFn Mleft Nleft fleft
    (.cons (eqToHom hC) tailId)
  HEq
    (eqToHom (congrArg tensorModuleList (compositionTargetListEq d e)) ≫
      internalDifferentialTensorMap (d.append e) (appendLeftArrowIndex i))
    (targetData.tensorMap ≫
      eqToHom (congrArg tensorModuleList
        (compositionTargetListEq (d.raise i.castSucc) e))) := by
  dsimp only
  let Mleft := fun q : Fin w.length ↦ factorModule d q.castSucc
  let Nleft := fun q : Fin w.length ↦ factorModule (d.raise i.castSucc) q.castSucc
  let fleft := fun q : Fin w.length ↦ factorDifferential d i.castSucc q.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let tailId := TensorMapData.ofFn Mright Mright (fun r ↦ 𝟙 (Mright r))
  let targetData := tensorMapDataPrefixOfFn Mleft Nleft fleft
    (.cons (eqToHom hC) tailId)
  let hT := congrArg tensorModuleList (compositionTargetListEq d e)
  let hT' := congrArg tensorModuleList
    (compositionTargetListEq (d.raise i.castSucc) e)
  let D := internalDifferentialTensorMap (d.append e) (appendLeftArrowIndex i)
  have hcore : HEq targetData.tensorMap D := by
    simpa [targetData, Mleft, Nleft, fleft, Mright, tailId, D] using
      compositionTargetInternalDifferential_append_left_heq d e i hC
  exact (CategoryTheory.eqToHom_comp_heq D hT).trans
    (hcore.symm.trans
      (CategoryTheory.comp_eqToHom_heq targetData.tensorMap hT').symm)

theorem tensorMapDataPrefixOfFn_id_tensorMap
    {k l : ℕ} (M N : Fin k → ModuleCat.{0} ℤ)
    (f : (q : Fin k) → M q ⟶ N q)
    (P : Fin l → ModuleCat.{0} ℤ) :
    (tensorMapDataPrefixOfFn M N f
      (TensorMapData.ofFn P P (fun q ↦ 𝟙 (P q)))).tensorMap =
      tensorModuleListWhiskerRight (finFamilyList P)
        (TensorMapData.ofFn M N f).tensorMap := by
  induction k with
  | zero =>
      change (TensorMapData.ofFn P P (fun q ↦ 𝟙 (P q))).tensorMap =
        tensorModuleListWhiskerRight (finFamilyList P)
          (𝟙 (tensorModuleList []))
      rw [TensorMapData.ofFn_id_tensorMap]
      simp [tensorModuleListWhiskerRight]
  | succ k ih =>
      let fTail := (TensorMapData.ofFn
        (fun q : Fin k ↦ M q.succ) (fun q : Fin k ↦ N q.succ)
        (fun q ↦ f q.succ)).tensorMap
      change f 0 ⊗ₘ
          (tensorMapDataPrefixOfFn
            (fun q : Fin k ↦ M q.succ) (fun q : Fin k ↦ N q.succ)
            (fun q ↦ f q.succ)
            (TensorMapData.ofFn P P (fun q ↦ 𝟙 (P q)))).tensorMap = _
      rw [ih (fun q : Fin k ↦ M q.succ) (fun q : Fin k ↦ N q.succ)
        (fun q ↦ f q.succ)]
      change f 0 ⊗ₘ
          tensorModuleListWhiskerRight (finFamilyList P) fTail =
        tensorModuleListWhiskerRight (finFamilyList P)
          (TensorMapData.ofFn M N f).tensorMap
      dsimp [tensorModuleListWhiskerRight, tensorModuleListAppendIso,
        tensorModuleList, tensorModuleListOver]
      simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
        Iso.refl_hom]
      dsimp only [TensorMapData.ofFn, TensorMapData.tensorMap]
      simp only [TensorMapData.tensorMap]
      change _ = _ ≫ ((f 0 ⊗ₘ fTail) ⊗ₘ 𝟙 _) ≫ _
      suffices
          f 0 ▷ tensorModuleListOver ℤ
              (finFamilyList (fun q ↦ M q.succ) ++ finFamilyList P) ≫
            N 0 ◁ (tensorModuleListAppendIso
              (finFamilyList (fun q ↦ M q.succ)) (finFamilyList P)).inv ≫
            N 0 ◁ fTail ▷ tensorModuleListOver ℤ (finFamilyList P) ≫
            N 0 ◁ (tensorModuleListAppendIso
              (finFamilyList (fun q ↦ N q.succ)) (finFamilyList P)).hom =
          M 0 ◁ (tensorModuleListAppendIso
              (finFamilyList (fun q ↦ M q.succ)) (finFamilyList P)).inv ≫
            (α_ (M 0) (tensorModuleListOver ℤ
                (finFamilyList (fun i ↦ M i.succ)))
              (tensorModuleListOver ℤ (finFamilyList P))).inv ≫
            f 0 ▷ tensorModuleList (finFamilyList (fun q ↦ M q.succ)) ▷
              tensorModuleListOver ℤ (finFamilyList P) ≫
            (α_ (N 0) (tensorModuleList
                (finFamilyList (fun q ↦ M q.succ)))
              (tensorModuleListOver ℤ (finFamilyList P))).hom ≫
            N 0 ◁ fTail ▷ tensorModuleListOver ℤ (finFamilyList P) ≫
            N 0 ◁ (tensorModuleListAppendIso
              (finFamilyList (fun q ↦ N q.succ)) (finFamilyList P)).hom by
        simpa [tensorHom_def, Category.assoc]
      rw [← MonoidalCategory.whisker_exchange_assoc]
      rw [MonoidalCategory.whiskerRight_tensor_assoc]

theorem tensorMapDataPrefixOfFn_castSucc_last_heq
    {k : ℕ} (M N : Fin (k + 1) → ModuleCat.{0} ℤ)
    (f : (q : Fin (k + 1)) → M q ⟶ N q)
    {source target : List (ModuleCat.{0} ℤ)}
    (tail : TensorMapData source target)
    (g : M (Fin.last k) ⟶ N (Fin.last k))
    (hg : HEq g (f (Fin.last k))) :
    HEq
      (tensorMapDataPrefixOfFn
        (fun q : Fin k ↦ M q.castSucc) (fun q : Fin k ↦ N q.castSucc)
        (fun q ↦ f q.castSucc) (.cons g tail))
      (tensorMapDataPrefixOfFn M N f tail) := by
  induction k with
  | zero =>
      change HEq (TensorMapData.cons g tail) (TensorMapData.cons (f 0) tail)
      exact tensorMapData_cons_heq rfl rfl rfl rfl hg HEq.rfl
  | succ k ih =>
      change HEq
        (TensorMapData.cons (f 0)
          (tensorMapDataPrefixOfFn
            (fun q : Fin k ↦ M q.succ.castSucc)
            (fun q : Fin k ↦ N q.succ.castSucc)
            (fun q ↦ f q.succ.castSucc) (.cons g tail)))
        (TensorMapData.cons (f 0)
          (tensorMapDataPrefixOfFn
            (fun q : Fin (k + 1) ↦ M q.succ)
            (fun q : Fin (k + 1) ↦ N q.succ)
            (fun q ↦ f q.succ) tail))
      have hs :
          (finFamilyList fun q : Fin k ↦ M q.succ.castSucc) ++
              M (Fin.last (k + 1)) :: source =
            (finFamilyList fun q : Fin (k + 1) ↦ M q.succ) ++ source := by
        have hcastSucc :
            (fun q : Fin k ↦ M q.succ.castSucc) =
              fun q : Fin k ↦ M q.castSucc.succ := by
          funext q
          congr 1
        have hlast : (Fin.last (k + 1) : Fin (k + 2)) =
            (Fin.last k).succ := by
          apply Fin.ext
          rfl
        rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn, List.ofFn_succ_last]
        rw [hcastSucc, congrArg M hlast]
        simp only [List.singleton_append, List.append_assoc]
      have ht :
          (finFamilyList fun q : Fin k ↦ N q.succ.castSucc) ++
              N (Fin.last (k + 1)) :: target =
            (finFamilyList fun q : Fin (k + 1) ↦ N q.succ) ++ target := by
        have hcastSucc :
            (fun q : Fin k ↦ N q.succ.castSucc) =
              fun q : Fin k ↦ N q.castSucc.succ := by
          funext q
          congr 1
        have hlast : (Fin.last (k + 1) : Fin (k + 2)) =
            (Fin.last k).succ := by
          apply Fin.ext
          rfl
        rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn, List.ofFn_succ_last]
        rw [hcastSucc, congrArg N hlast]
        simp only [List.singleton_append, List.append_assoc]
      exact tensorMapData_cons_heq rfl rfl hs ht HEq.rfl
        (ih (fun q : Fin (k + 1) ↦ M q.succ)
          (fun q : Fin (k + 1) ↦ N q.succ) (fun q ↦ f q.succ) g hg)

theorem appendLeftSourceTransport_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length)
    (hA : factorModule d (Fin.last w.length) =
      factorModule (d.raise i.castSucc) (Fin.last w.length)) :
  let Mleft := fun q : Fin w.length ↦ factorModule d q.castSucc
  let Nleft := fun q : Fin w.length ↦ factorModule (d.raise i.castSucc) q.castSucc
  let fleft := fun q : Fin w.length ↦ factorDifferential d i.castSucc q.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let tailId := TensorMapData.ofFn Mright Mright (fun r ↦ 𝟙 (Mright r))
  let sourceData := tensorMapDataPrefixOfFn Mleft Nleft fleft
    (.cons (eqToHom hA) (.cons (𝟙 (factorModule e 0)) tailId))
  HEq
    ((internalDifferentialTensorMap d i.castSucc ⊗ₘ 𝟙 (summandModule e)) ≫
      (tensorModuleListAppendIso (finFamilyList (factorModule (d.raise i.castSucc)))
        (finFamilyList (factorModule e))).hom ≫
      eqToHom (congrArg tensorModuleList
        (compositionSourceListEq (d.raise i.castSucc) e)) ≫
      eqToHom (congrArg tensorModuleList
        (compositionBoundaryListEq (d.raise i.castSucc) e)))
    ((tensorModuleListAppendIso (finFamilyList (factorModule d))
        (finFamilyList (factorModule e))).hom ≫
      eqToHom (congrArg tensorModuleList (compositionSourceListEq d e)) ≫
      eqToHom (congrArg tensorModuleList (compositionBoundaryListEq d e)) ≫
      sourceData.tensorMap) := by
  dsimp only
  rw [tensorModuleListAppendIso_whiskerRight_assoc]
  let Mleft := fun q : Fin w.length ↦ factorModule d q.castSucc
  let Nleft := fun q : Fin w.length ↦
    factorModule (d.raise i.castSucc) q.castSucc
  let fleft := fun q : Fin w.length ↦
    factorDifferential d i.castSucc q.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let tailId := TensorMapData.ofFn Mright Mright (fun r ↦ 𝟙 (Mright r))
  let sourceData := tensorMapDataPrefixOfFn Mleft Nleft fleft
    (.cons (eqToHom hA) (.cons (𝟙 (factorModule e 0)) tailId))
  let fullData := tensorMapDataPrefixOfFn (factorModule d)
    (factorModule (d.raise i.castSucc))
    (factorDifferential d i.castSucc)
    (TensorMapData.ofFn (factorModule e) (factorModule e)
      (fun q ↦ 𝟙 (factorModule e q)))
  have hne : (i.castSucc : Fin (w.length + 1)) ≠ Fin.last w.length :=
    Fin.castSucc_ne_last i
  obtain ⟨hA', hmap⟩ := factorDifferential_eqToHom_of_ne_comp d i.castSucc
    (Fin.last w.length) hne
  have hlast : HEq (eqToHom hA)
      (factorDifferential d i.castSucc (Fin.last w.length)) := by
    rw [hmap]
  have hdata : HEq sourceData fullData := by
    exact tensorMapDataPrefixOfFn_castSucc_last_heq
      (factorModule d) (factorModule (d.raise i.castSucc))
      (factorDifferential d i.castSucc)
      (TensorMapData.ofFn (factorModule e) (factorModule e)
        (fun q ↦ 𝟙 (factorModule e q)))
      (eqToHom hA) hlast
  have hsource :
      finFamilyList Mleft ++
          factorModule d (Fin.last w.length) :: finFamilyList (factorModule e) =
        finFamilyList (factorModule d) ++ finFamilyList (factorModule e) := by
    simpa [Mleft, compositionLeftPrefix, List.append_assoc] using
      congrArg (fun xs ↦ xs ++ finFamilyList (factorModule e))
        (finFamilyList_factorModule_eq_prefix_last d).symm
  have htarget :
      finFamilyList Nleft ++
          factorModule (d.raise i.castSucc) (Fin.last w.length) ::
            finFamilyList (factorModule e) =
        finFamilyList (factorModule (d.raise i.castSucc)) ++
          finFamilyList (factorModule e) := by
    simpa [Nleft, compositionLeftPrefix, List.append_assoc] using
      congrArg (fun xs ↦ xs ++ finFamilyList (factorModule e))
        (finFamilyList_factorModule_eq_prefix_last (d.raise i.castSucc)).symm
  have hdataMap : HEq sourceData.tensorMap fullData.tensorMap :=
    tensorMapData_tensorMap_heq hsource htarget hdata
  have hfull : fullData.tensorMap =
      tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (internalDifferentialTensorMap d i.castSucc) := by
    simpa [fullData, internalDifferentialTensorMap] using
      tensorMapDataPrefixOfFn_id_tensorMap
        (factorModule d) (factorModule (d.raise i.castSucc))
        (factorDifferential d i.castSucc) (factorModule e)
  have hsourceCore : HEq sourceData.tensorMap
      (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (internalDifferentialTensorMap d i.castSucc)) :=
    hdataMap.trans (heq_of_eq hfull)
  let hS := congrArg tensorModuleList (compositionSourceListEq d e)
  let hBdy := congrArg tensorModuleList (compositionBoundaryListEq d e)
  let hS' := congrArg tensorModuleList
    (compositionSourceListEq (d.raise i.castSucc) e)
  let hBdy' := congrArg tensorModuleList
    (compositionBoundaryListEq (d.raise i.castSucc) e)
  let W := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
    (internalDifferentialTensorMap d i.castSucc)
  let pre := eqToHom hS ≫ eqToHom hBdy
  let pre' := eqToHom hS' ≫ eqToHom hBdy'
  have hpre : HEq (pre ≫ sourceData.tensorMap) W := by
    exact CategoryTheory.heq_comp
      (f := pre) (g := sourceData.tensorMap) (f' := 𝟙 _) (g' := W)
      rfl (hS.trans hBdy).symm (hS'.trans hBdy').symm
      (eqToHom_comp_heq_id hS hBdy) hsourceCore
  have hpost : HEq W (W ≫ pre') := by
    simpa only [Category.comp_id] using
      (CategoryTheory.heq_comp
        (f := W) (g := 𝟙 _) (f' := W) (g' := pre')
        rfl rfl (hS'.trans hBdy') HEq.rfl
        (eqToHom_comp_heq_id hS' hBdy').symm)
  have htransport : HEq (W ≫ pre') (pre ≫ sourceData.tensorMap) :=
    hpost.symm.trans hpre.symm
  exact CategoryTheory.heq_comp rfl rfl rfl HEq.rfl htransport

theorem sum_append_arrow_partition
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {A : Type*} [AddCommMonoid A]
    (f : Fin ((w.append v).length + 1) → A) :
    ∑ q, f q =
      (∑ i, f (appendLeftArrowIndex (v := v) i)) +
        f (appendBoundaryArrowIndex w v) +
        ∑ j, f (appendRightArrowIndex (w := w) j) := by
  let hlen : (w.append v).length + 1 = w.length + (v.length + 1) := by
    rw [append_length]
    omega
  calc
    ∑ q, f q = ∑ q : Fin (w.length + (v.length + 1)), f (Fin.cast hlen.symm q) := by
      exact ((Fin.castOrderIso hlen).toEquiv.symm.sum_comp f).symm
    _ = (∑ i : Fin w.length, f (Fin.cast hlen.symm (Fin.castAdd (v.length + 1) i))) +
        ∑ j : Fin (v.length + 1), f (Fin.cast hlen.symm (Fin.natAdd w.length j)) := by
      rw [Fin.sum_univ_add]
    _ = _ := by
      rw [Fin.sum_univ_succ]
      have hleft :
          (∑ i : Fin w.length, f (Fin.cast hlen.symm (Fin.castAdd (v.length + 1) i))) =
            ∑ i, f (appendLeftArrowIndex (v := v) i) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
      have hboundary : f (Fin.cast hlen.symm (Fin.natAdd w.length 0)) =
          f (appendBoundaryArrowIndex w v) := by
        congr 1
      have hright :
          (∑ j : Fin v.length, f (Fin.cast hlen.symm (Fin.natAdd w.length j.succ))) =
            ∑ j, f (appendRightArrowIndex (w := w) j) := by
        apply Finset.sum_congr rfl
        intro j _
        apply congrArg f
        apply Fin.ext
        change w.length + j.succ.val = w.length + 1 + j.val
        simp only [Fin.val_succ]
        omega
      rw [hleft, hboundary, hright, ← add_assoc]

theorem sum_append_contraction_partition
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {A : Type*} [AddCommMonoid A]
    (f : Fin (w.append v).length → A) :
    ∑ q, f q =
      (∑ i, f (appendLeftContractionIndex (v := v) i)) +
        ∑ j, f (appendRightContractionIndex (w := w) j) := by
  let hlen : (w.append v).length = w.length + v.length := append_length w v
  calc
    ∑ q, f q = ∑ q : Fin (w.length + v.length), f (Fin.cast hlen.symm q) := by
      exact ((Fin.castOrderIso hlen).toEquiv.symm.sum_comp f).symm
    _ = (∑ i : Fin w.length, f (Fin.cast hlen.symm (Fin.castAdd v.length i))) +
        ∑ j : Fin v.length, f (Fin.cast hlen.symm (Fin.natAdd w.length j)) := by
      rw [Fin.sum_univ_add]
    _ = _ := by
      have hleft : (∑ i : Fin w.length, f (Fin.cast hlen.symm (Fin.castAdd v.length i))) =
          ∑ i, f (appendLeftContractionIndex (v := v) i) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
      have hright : (∑ j : Fin v.length, f (Fin.cast hlen.symm (Fin.natAdd w.length j))) =
          ∑ j, f (appendRightContractionIndex (w := w) j) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
      rw [hleft, hright]

theorem internalSign_sum_append_partition
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    {A : Type*} [AddCommGroup A] [Module ℤ A]
    (f : Fin ((w.append v).length + 1) → A) :
    ∑ q, (d.append e).internalSign q • f q =
      m.negOnePow •
          (∑ i, d.internalSign i.castSucc • f (appendLeftArrowIndex (v := v) i)) +
        e.internalSign 0 • f (appendBoundaryArrowIndex w v) +
        ∑ j, e.internalSign j.succ • f (appendRightArrowIndex (w := w) j) := by
  have hleft :
      (∑ i, (d.internalSign i.castSucc * (m.negOnePow : ℤ)) •
        f (appendLeftArrowIndex (v := v) i)) =
        (m.negOnePow : ℤ) •
          ∑ i, d.internalSign i.castSucc • f (appendLeftArrowIndex (v := v) i) := by
    rw [← Finset.sum_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, mul_zsmul]
  rw [sum_append_arrow_partition]
  simp_rw [internalSign_append_left, internalSign_append_boundary,
    internalSign_append_right]
  rw [Units.smul_def, hleft]

theorem contractionSign_sum_append_partition
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    {A : Type*} [AddCommGroup A] [Module ℤ A]
    (f : Fin (w.append v).length → A) :
    ∑ q, (d.append e).contractionSign q • f q =
      m.negOnePow •
          (∑ i, d.contractionSign i • f (appendLeftContractionIndex (v := v) i)) +
        ∑ j, e.contractionSign j • f (appendRightContractionIndex (w := w) j) := by
  have hleft :
      (∑ i, (d.contractionSign i * (m.negOnePow : ℤ)) •
        f (appendLeftContractionIndex (v := v) i)) =
        (m.negOnePow : ℤ) •
          ∑ i, d.contractionSign i • f (appendLeftContractionIndex (v := v) i) := by
    rw [← Finset.sum_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm, mul_zsmul]
  rw [sum_append_contraction_partition]
  simp_rw [contractionSign_append_left, contractionSign_append_right]
  rw [Units.smul_def, hleft]

theorem internalBoundaryKoszul_assembly
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    {A : Type*} [AddCommGroup A] [Module ℤ A] (a b : A) :
    (d.append e).internalSign (appendBoundaryArrowIndex w v) •
        (a + (e.arrowDegree 0).negOnePow • b) =
      e.internalSign 0 • a + m.negOnePow • b := by
  rw [Units.smul_def, Units.smul_def]
  calc
    _ = (d.append e).internalSign (appendBoundaryArrowIndex w v) • a +
        (d.append e).internalSign (appendBoundaryArrowIndex w v) •
          ((e.arrowDegree 0).negOnePow : ℤ) • b := zsmul_add _ _ _
    _ = (d.append e).internalSign (appendBoundaryArrowIndex w v) • a +
        ((d.append e).internalSign (appendBoundaryArrowIndex w v) *
          (e.arrowDegree 0).negOnePow) • b := by rw [mul_zsmul]
    _ = _ := by
      rw [internalSign_append_boundary_mul, internalSign_append_boundary]

theorem quotientCompositionMap_internalDifferentialFromSummand_right_sum
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    quotientCompositionMap X Y Z n (m + 1)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
        ((internalDifferentialFromSummand e).hom y) =
      ∑ j, e.internalSign j •
        quotientCompositionMap X Y Z n (m + 1)
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
          ((internalDifferentialLargeMap e j).hom y) := by
  simp [internalDifferentialFromSummand, Pi.smul_apply]

theorem quotientCompositionMap_contractionDifferentialFromSummand_right_sum
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    quotientCompositionMap X Y Z n (m + 1)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
        ((contractionDifferentialFromSummand e).hom y) =
      ∑ j, quotientCompositionMap X Y Z n (m + 1)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
        ((contractionLargeMap e j).hom y) := by
  simp [contractionDifferentialFromSummand]

theorem quotientCompositionMap_internalDifferentialFromSummand_left_sum
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    quotientCompositionMap X Y Z (n + 1) m
        ((internalDifferentialFromSummand d).hom x)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) =
      ∑ i, d.internalSign i •
        quotientCompositionMap X Y Z (n + 1) m
          ((internalDifferentialLargeMap d i).hom x)
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) := by
  suffices
      (∑ c, (d.internalSign c •
          quotientCompositionMap X Y Z (n + 1) m
            ((internalDifferentialLargeMap d c).hom x))
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s)
          ⟨v, e⟩).hom y)) =
      ∑ i, d.internalSign i •
        quotientCompositionMap X Y Z (n + 1) m
          ((internalDifferentialLargeMap d i).hom x)
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s)
            ⟨v, e⟩).hom y) by
    simpa [internalDifferentialFromSummand, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

theorem quotientCompositionMap_contractionDifferentialFromSummand_left_sum
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    quotientCompositionMap X Y Z (n + 1) m
        ((contractionDifferentialFromSummand d).hom x)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) =
      ∑ i, quotientCompositionMap X Y Z (n + 1) m
        ((contractionLargeMap d i).hom x)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) := by
  simp [contractionDifferentialFromSummand]

theorem quotientCompositionMap_internalLargeMap_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (j : Fin (v.length + 1)) :
    quotientCompositionMap X Y Z n (m + 1)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
        ((internalDifferentialLargeMap e j).hom y) =
      largeSummandCompositionMap d (e.raise j) x
        (((ModuleCat.uliftFunctor.{1} ℤ).map
          (internalDifferentialTensorMap e j)).hom y) := by
  unfold internalDifferentialLargeMap
  simp only [ModuleCat.comp_apply]
  rw [quotientCompositionMap_on_summands]

theorem quotientCompositionMap_internalLargeMap_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (i : Fin (w.length + 1)) :
    quotientCompositionMap X Y Z (n + 1) m
        ((internalDifferentialLargeMap d i).hom x)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) =
      largeSummandCompositionMap (d.raise i) e
        (((ModuleCat.uliftFunctor.{1} ℤ).map
          (internalDifferentialTensorMap d i)).hom x) y := by
  unfold internalDifferentialLargeMap
  simp only [ModuleCat.comp_apply]
  rw [quotientCompositionMap_on_summands]

theorem summandCompositionMap_internalDifferential_append_left_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    HEq
      (summandCompositionMap d e ≫
        internalDifferentialTensorMap (d.append e) (appendLeftArrowIndex i))
      ((internalDifferentialTensorMap d i.castSucc ⊗ₘ 𝟙 (summandModule e)) ≫
        summandCompositionMap (d.raise i.castSucc) e) := by
  rw [summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized]
  rw [normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder]
  dsimp only [summandModule]
  let A := (tensorModuleListAppendIso (finFamilyList (factorModule d))
    (finFamilyList (factorModule e))).hom
  let A' := (tensorModuleListAppendIso
    (finFamilyList (factorModule (d.raise i.castSucc)))
    (finFamilyList (factorModule e))).hom
  let R := summandCompositionRemainder d e
  let D := internalDifferentialTensorMap (d.append e) (appendLeftArrowIndex i)
  let W := internalDifferentialTensorMap d i.castSucc ⊗ₘ
    𝟙 (tensorModuleList (finFamilyList (factorModule e)))
  let R' := summandCompositionRemainder (d.raise i.castSucc) e
  change HEq ((A ≫ R) ≫ D) ((W ≫ A') ≫ R')
  have htot : (n + 1) + m = (n + m) + 1 := by omega
  have hraise := DegreeProfile.raise_append_left d e i
  have hfactor :
      finFamilyList (factorModule (((d.raise i.castSucc).append e).castTotal htot)) =
        finFamilyList (factorModule ((d.raise i.castSucc).append e)) := by
    rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
    apply (List.ofFn_inj).2
    funext q
    unfold factorModule
    rw [DegreeProfile.castTotal_arrowDegree]
  have hcast : summandModule (((d.raise i.castSucc).append e).castTotal htot) =
      summandModule ((d.raise i.castSucc).append e) :=
    congrArg tensorModuleList hfactor
  have ht := (congrArg summandModule hraise).trans hcast
  dsimp [R, R', summandCompositionRemainder]
  have hne : (i.castSucc : Fin (w.length + 1)) ≠ Fin.last w.length :=
    Fin.castSucc_ne_last i
  obtain ⟨hA, _⟩ := factorDifferential_eqToHom_of_ne_comp d i.castSucc
    (Fin.last w.length) hne
  have hC : compositionBoundaryModule d e =
      compositionBoundaryModule (d.raise i.castSucc) e := by
    unfold compositionBoundaryModule
    congr 1
    simp [DegreeProfile.raise, Ne.symm hne]
  let Mleft := fun q : Fin w.length ↦ factorModule d q.castSucc
  let Nleft := fun q : Fin w.length ↦
    factorModule (d.raise i.castSucc) q.castSucc
  let fleft := fun q : Fin w.length ↦
    factorDifferential d i.castSucc q.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let fright := fun r : Fin v.length ↦ 𝟙 (Mright r)
  let tailId := TensorMapData.ofFn Mright Mright fright
  let sourceData := tensorMapDataPrefixOfFn Mleft Nleft fleft
    (.cons (eqToHom hA) (.cons (𝟙 (factorModule e 0)) tailId))
  let targetData := tensorMapDataPrefixOfFn Mleft Nleft fleft
    (.cons (eqToHom hC) tailId)
  have hboundary :
      (eqToHom hA ⊗ₘ 𝟙 (factorModule e 0)) ≫
          compositionBoundaryMap (d.raise i.castSucc) e =
        compositionBoundaryMap d e ≫ eqToHom hC := by
    exact test_tensor_comp_transport_of_heq hA rfl hC
      (compositionBoundaryMap d e)
      (compositionBoundaryMap (d.raise i.castSucc) e)
      (compositionBoundaryMap_raise_left_internal_heq d e i)
  have hnatural := adjacentMergeAfter_naturality_ofFn Mleft Nleft
    (factorModule d (Fin.last w.length))
    (factorModule (d.raise i.castSucc) (Fin.last w.length))
    (factorModule e 0) (factorModule e 0)
    (compositionBoundaryModule d e)
    (compositionBoundaryModule (d.raise i.castSucc) e)
    Mright Mright
    (compositionBoundaryMap d e)
    (compositionBoundaryMap (d.raise i.castSucc) e)
    fleft (eqToHom hA) (𝟙 _) (eqToHom hC) fright hboundary
  have hcomm := hnatural.tensorMap_comm
  let hS := congrArg tensorModuleList (compositionSourceListEq d e)
  let hBdy := congrArg tensorModuleList (compositionBoundaryListEq d e)
  let hT := congrArg tensorModuleList (compositionTargetListEq d e)
  let hS' := congrArg tensorModuleList
    (compositionSourceListEq (d.raise i.castSucc) e)
  let hBdy' := congrArg tensorModuleList
    (compositionBoundaryListEq (d.raise i.castSucc) e)
  let hT' := congrArg tensorModuleList
    (compositionTargetListEq (d.raise i.castSucc) e)
  have hsourceTransport := appendLeftSourceTransport_heq d e i hA
  have htargetTransport := appendLeftTargetTransport_heq d e i hC
  let mergeMap :=
    (adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix e)
      (compositionBoundaryMap d e)).tensorMap
  let mergeMap' :=
    (adjacentMergeAfter (compositionLeftPrefix (d.raise i.castSucc))
      (ys := compositionRightSuffix e)
      (compositionBoundaryMap (d.raise i.castSucc) e)).tensorMap
  have hcomm' : sourceData.tensorMap ≫ mergeMap' =
      mergeMap ≫ targetData.tensorMap := by
    simpa [sourceData, targetData, mergeMap, mergeMap', tailId, fright,
      Mleft, Nleft, fleft, Mright, compositionLeftPrefix,
      compositionRightSuffix] using hcomm
  let pre := A ≫ eqToHom hS ≫ eqToHom hBdy
  let pre' := W ≫ A' ≫ eqToHom hS' ≫ eqToHom hBdy'
  have htargetWhisker : HEq
      ((pre ≫ mergeMap) ≫ (eqToHom hT ≫ D))
      ((pre ≫ mergeMap) ≫ (targetData.tensorMap ≫ eqToHom hT')) := by
    exact CategoryTheory.heq_comp rfl rfl ht HEq.rfl htargetTransport
  have hmiddle :
      pre ≫ (mergeMap ≫ targetData.tensorMap) ≫ eqToHom hT' =
        pre ≫ (sourceData.tensorMap ≫ mergeMap') ≫ eqToHom hT' :=
    congrArg (fun z ↦ pre ≫ z ≫ eqToHom hT') hcomm'.symm
  have hsourceWhisker : HEq
      ((pre ≫ sourceData.tensorMap) ≫ (mergeMap' ≫ eqToHom hT'))
      (pre' ≫ (mergeMap' ≫ eqToHom hT')) := by
    exact CategoryTheory.heq_comp rfl rfl rfl hsourceTransport.symm HEq.rfl
  change HEq
    (A ≫ eqToHom hS ≫ eqToHom hBdy ≫ mergeMap ≫ eqToHom hT ≫ D)
    (W ≫ A' ≫ eqToHom hS' ≫ eqToHom hBdy' ≫ mergeMap' ≫ eqToHom hT')
  simpa only [Category.assoc, pre, pre'] using
    htargetWhisker.trans (heq_of_eq hmiddle) |>.trans hsourceWhisker

theorem quotientCompositionMap_contractionLargeMap_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (j : Fin v.length) :
    quotientCompositionMap X Y Z n (m + 1)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
        ((contractionLargeMap e j).hom y) =
      e.contractionSign j •
        largeSummandCompositionMap d (e.contract j) x
          (((ModuleCat.uliftFunctor.{1} ℤ).map
            (contractionTensorMap e j)).hom y) := by
  unfold contractionLargeMap
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [map_zsmul]
  simp only [ModuleCat.comp_apply]
  rw [quotientCompositionMap_on_summands]

theorem quotientCompositionMap_contractionLargeMap_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (i : Fin w.length) :
    quotientCompositionMap X Y Z (n + 1) m
        ((contractionLargeMap d i).hom x)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) =
      d.contractionSign i •
        largeSummandCompositionMap (d.contract i) e
          (((ModuleCat.uliftFunctor.{1} ℤ).map
            (contractionTensorMap d i)).hom x) y := by
  unfold contractionLargeMap
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [map_zsmul]
  change d.contractionSign i •
      quotientCompositionMap X Y Z (n + 1) m
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
          ⟨eraseIntermediate w i, d.contract i⟩).hom
          (((ModuleCat.uliftFunctor.{1} ℤ).map
            (contractionTensorMap d i)).hom x))
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y) = _
  rw [quotientCompositionMap_on_summands]

theorem transported_totalDifferentialComposition_right_sum
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m k : ℤ} (h : n + (m + 1) = k)
    (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    (eqToHom (congrArg (quotientGradedModule X Z) h)).hom
        (quotientCompositionMap X Y Z n (m + 1)
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨w, d⟩).hom x)
          ((internalDifferentialFromSummand e +
            contractionDifferentialFromSummand e).hom y)) =
      (∑ j, e.internalSign j •
        (eqToHom (congrArg (quotientGradedModule X Z) h)).hom
          (largeSummandCompositionMap d (e.raise j) x
            (((ModuleCat.uliftFunctor.{1} ℤ).map
              (internalDifferentialTensorMap e j)).hom y))) +
        ∑ j, e.contractionSign j •
          (eqToHom (congrArg (quotientGradedModule X Z) h)).hom
            (largeSummandCompositionMap d (e.contract j) x
              (((ModuleCat.uliftFunctor.{1} ℤ).map
                (contractionTensorMap e j)).hom y)) := by
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add]
  rw [quotientCompositionMap_internalDifferentialFromSummand_right_sum,
    quotientCompositionMap_contractionDifferentialFromSummand_right_sum]
  simp only [map_sum, map_zsmul]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    rw [quotientCompositionMap_internalLargeMap_right]
  · apply Finset.sum_congr rfl
    intro j _
    rw [quotientCompositionMap_contractionLargeMap_right, map_zsmul]

theorem transported_totalDifferentialComposition_left_sum
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m k : ℤ} (h : (n + 1) + m = k)
    (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    (eqToHom (congrArg (quotientGradedModule X Z) h)).hom
        (quotientCompositionMap X Y Z (n + 1) m
          ((internalDifferentialFromSummand d +
            contractionDifferentialFromSummand d).hom x)
          ((Limits.Sigma.ι
            (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s) ⟨v, e⟩).hom y)) =
      (∑ i, d.internalSign i •
        (eqToHom (congrArg (quotientGradedModule X Z) h)).hom
          (largeSummandCompositionMap (d.raise i) e
            (((ModuleCat.uliftFunctor.{1} ℤ).map
              (internalDifferentialTensorMap d i)).hom x) y)) +
        ∑ i, d.contractionSign i •
          (eqToHom (congrArg (quotientGradedModule X Z) h)).hom
            (largeSummandCompositionMap (d.contract i) e
              (((ModuleCat.uliftFunctor.{1} ℤ).map
                (contractionTensorMap d i)).hom x) y) := by
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add]
  rw [quotientCompositionMap_internalDifferentialFromSummand_left_sum,
    quotientCompositionMap_contractionDifferentialFromSummand_left_sum]
  simp only [map_sum, map_zsmul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [quotientCompositionMap_internalLargeMap_left]
  · apply Finset.sum_congr rfl
    intro i _
    rw [quotientCompositionMap_contractionLargeMap_left, map_zsmul]

def largeSummandCompositionValue
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    largeSummandModule
      (⟨w.append v, d.append e⟩ : GradedSummandIndex X Z (n + m)) :=
  ULift.up ((summandCompositionMap d e).hom (x.down ⊗ₜ[ℤ] y.down))

theorem largeSummandCompositionMap_eq_inclusion
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    largeSummandCompositionMap d e x y =
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z (n + m) ↦ largeSummandModule s)
        ⟨w.append v, d.append e⟩).hom
        (largeSummandCompositionValue d e x y) := by
  rfl

theorem quotientTotalDifferential_largeSummandCompositionMap_partition
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    (quotientTotalDifferential X Z (n + m)).hom
        (largeSummandCompositionMap d e x y) =
      ((∑ i, (d.append e).internalSign (appendLeftArrowIndex (v := v) i) •
          (internalDifferentialLargeMap (d.append e)
            (appendLeftArrowIndex (v := v) i)).hom
            (largeSummandCompositionValue d e x y)) +
        (d.append e).internalSign (appendBoundaryArrowIndex w v) •
          (internalDifferentialLargeMap (d.append e)
            (appendBoundaryArrowIndex w v)).hom
            (largeSummandCompositionValue d e x y) +
        ∑ j, (d.append e).internalSign (appendRightArrowIndex (w := w) j) •
          (internalDifferentialLargeMap (d.append e)
            (appendRightArrowIndex (w := w) j)).hom
            (largeSummandCompositionValue d e x y)) +
      ((∑ i, (contractionLargeMap (d.append e)
          (appendLeftContractionIndex (v := v) i)).hom
          (largeSummandCompositionValue d e x y)) +
        ∑ j, (contractionLargeMap (d.append e)
          (appendRightContractionIndex (w := w) j)).hom
          (largeSummandCompositionValue d e x y)) := by
  rw [largeSummandCompositionMap_eq_inclusion]
  change (Limits.Sigma.ι
      (fun s : GradedSummandIndex X Z (n + m) ↦ largeSummandModule s)
      ⟨w.append v, d.append e⟩ ≫ quotientTotalDifferential X Z (n + m)).hom
      (largeSummandCompositionValue d e x y) = _
  rw [quotientTotalDifferential_inclusion]
  simp only [ModuleCat.hom_add, LinearMap.add_apply]
  unfold internalDifferentialFromSummand contractionDifferentialFromSummand
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
  rw [sum_append_arrow_partition, sum_append_contraction_partition]
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]

def rightLeibnizDegreeEq (n m : ℤ) :
    n + (m + 1) = (n + m) + 1 := by omega

def leftLeibnizDegreeEq (n m : ℤ) :
    (n + 1) + m = (n + m) + 1 := by omega

theorem quotientGradedModule_eqToHom_inclusion_apply
    {X Y : ComplexCategory} {p q : ℤ} (h : p = q)
    (s : GradedSummandIndex X Y p) (t : GradedSummandIndex X Y q)
    (hst : HEq s t) (a : largeSummandModule s) (b : largeSummandModule t)
    (hab : HEq a b) :
    (eqToHom (congrArg (quotientGradedModule X Y) h)).hom
        ((Limits.Sigma.ι
          (fun u : GradedSummandIndex X Y p ↦ largeSummandModule u) s).hom a) =
      (Limits.Sigma.ι
        (fun u : GradedSummandIndex X Y q ↦ largeSummandModule u) t).hom b := by
  subst q
  have hst' : s = t := eq_of_heq hst
  subst t
  have hab' : a = b := eq_of_heq hab
  subst b
  rfl

theorem moduleCatHom_apply_heq
    {M N N' : ModuleCat.{0} ℤ} {f : M ⟶ N} {g : M ⟶ N'}
    (hN : N = N') (hfg : HEq f g) (a : M) : HEq (f.hom a) (g.hom a) := by
  subst N'
  rw [eq_of_heq hfg]

theorem uliftUp_heq {A B : Type} {a : A} {b : B} (hab : HEq a b) :
    HEq (ULift.up a) (ULift.up b) := by
  cases hab
  rfl

theorem moduleCat_eqToHom_apply_heq
    {M N : ModuleCat.{0} ℤ} (h : M = N) (a : M) :
    HEq a ((eqToHom h).hom a) := by
  subst N
  rfl

theorem degreeProfile_castTotal_heq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {p q : ℤ}
    (h : p = q) (d : DegreeProfile w p) : HEq d (d.castTotal h) := by
  exact (eqRec_heq h d).symm

theorem gradedSummandIndex_mk_heq_of_eq
    {X Y : ComplexCategory} {p q : ℤ} {w w' : DrinfeldWord X Y}
    {d : DegreeProfile w p} {e : DegreeProfile w' q}
    (htotal : p = q) (hword : w = w') (hprofile : HEq d e) :
    HEq (⟨w, d⟩ : GradedSummandIndex X Y p)
      (⟨w', e⟩ : GradedSummandIndex X Y q) := by
  subst q
  subst w'
  have hprofile' : d = e := eq_of_heq hprofile
  subst e
  rfl

theorem internalDifferentialLargeMap_append_left_apply
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (i : Fin w.length) :
    (internalDifferentialLargeMap (d.append e)
        (appendLeftArrowIndex (v := v) i)).hom
        (largeSummandCompositionValue d e x y) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (leftLeibnizDegreeEq n m))).hom
        (largeSummandCompositionMap (d.raise i.castSucc) e
          (((ModuleCat.uliftFunctor.{1} ℤ).map
            (internalDifferentialTensorMap d i.castSucc)).hom x) y) := by
  change
    (Limits.Sigma.ι
      (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
      ⟨w.append v, (d.append e).raise (appendLeftArrowIndex i)⟩).hom
        (ULift.up ((summandCompositionMap d e ≫
          internalDifferentialTensorMap (d.append e)
            (appendLeftArrowIndex i)).hom (x.down ⊗ₜ[ℤ] y.down))) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (leftLeibnizDegreeEq n m))).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z ((n + 1) + m) ↦ largeSummandModule s)
          ⟨w.append v, (d.raise i.castSucc).append e⟩).hom
            (ULift.up (((internalDifferentialTensorMap d i.castSucc ⊗ₘ
              𝟙 (summandModule e)) ≫
                summandCompositionMap (d.raise i.castSucc) e).hom
                  (x.down ⊗ₜ[ℤ] y.down))))
  apply (quotientGradedModule_eqToHom_inclusion_apply
    (leftLeibnizDegreeEq n m)
    (⟨w.append v, (d.raise i.castSucc).append e⟩ :
      GradedSummandIndex X Z ((n + 1) + m))
    (⟨w.append v, (d.append e).raise (appendLeftArrowIndex i)⟩ :
      GradedSummandIndex X Z ((n + m) + 1)) ?_ _ _ ?_).symm
  · apply gradedSummandIndex_mk_heq_of_eq (leftLeibnizDegreeEq n m) rfl
    exact (degreeProfile_castTotal_heq (leftLeibnizDegreeEq n m)
      ((d.raise i.castSucc).append e)).trans
        (heq_of_eq (DegreeProfile.raise_append_left d e i).symm)
  · apply uliftUp_heq
    have htarget :
        summandModule ((d.raise i.castSucc).append e) =
          summandModule ((d.append e).raise (appendLeftArrowIndex i)) := by
      exact (summandModule_castTotal_eq (leftLeibnizDegreeEq n m)
        ((d.raise i.castSucc).append e)).symm.trans
          (congrArg summandModule
            (DegreeProfile.raise_append_left d e i).symm)
    exact moduleCatHom_apply_heq
      htarget
      (summandCompositionMap_internalDifferential_append_left_heq d e i).symm
      (x.down ⊗ₜ[ℤ] y.down)

theorem internalDifferentialLargeMap_append_right_apply
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (j : Fin v.length) :
    (internalDifferentialLargeMap (d.append e)
        (appendRightArrowIndex (w := w) j)).hom
        (largeSummandCompositionValue d e x y) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (rightLeibnizDegreeEq n m))).hom
        (largeSummandCompositionMap d (e.raise j.succ) x
          (((ModuleCat.uliftFunctor.{1} ℤ).map
            (internalDifferentialTensorMap e j.succ)).hom y)) := by
  change
    (Limits.Sigma.ι
      (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
      ⟨w.append v, (d.append e).raise (appendRightArrowIndex j)⟩).hom
        (ULift.up ((summandCompositionMap d e ≫
          internalDifferentialTensorMap (d.append e)
            (appendRightArrowIndex j)).hom (x.down ⊗ₜ[ℤ] y.down))) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (rightLeibnizDegreeEq n m))).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z (n + (m + 1)) ↦ largeSummandModule s)
          ⟨w.append v, d.append (e.raise j.succ)⟩).hom
            (ULift.up (((𝟙 (summandModule d) ⊗ₘ
              internalDifferentialTensorMap e j.succ) ≫
                summandCompositionMap d (e.raise j.succ)).hom
                  (x.down ⊗ₜ[ℤ] y.down))))
  apply (quotientGradedModule_eqToHom_inclusion_apply
    (rightLeibnizDegreeEq n m)
    (⟨w.append v, d.append (e.raise j.succ)⟩ :
      GradedSummandIndex X Z (n + (m + 1)))
    (⟨w.append v, (d.append e).raise (appendRightArrowIndex j)⟩ :
      GradedSummandIndex X Z ((n + m) + 1)) ?_ _ _ ?_).symm
  · apply gradedSummandIndex_mk_heq_of_eq (rightLeibnizDegreeEq n m) rfl
    exact (degreeProfile_castTotal_heq (rightLeibnizDegreeEq n m)
      (d.append (e.raise j.succ))).trans
        (heq_of_eq (DegreeProfile.raise_append_right d e j).symm)
  · apply uliftUp_heq
    have htarget :
        summandModule (d.append (e.raise j.succ)) =
          summandModule ((d.append e).raise (appendRightArrowIndex j)) := by
      exact (summandModule_castTotal_eq (rightLeibnizDegreeEq n m)
        (d.append (e.raise j.succ))).symm.trans
          (congrArg summandModule
            (DegreeProfile.raise_append_right d e j).symm)
    exact moduleCatHom_apply_heq htarget
      (summandCompositionMap_internalDifferential_append_right_heq d e j).symm
      (x.down ⊗ₜ[ℤ] y.down)

theorem transported_boundary_internal_right_apply
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    (eqToHom (congrArg (quotientGradedModule X Z)
      (rightLeibnizDegreeEq n m))).hom
        (largeSummandCompositionMap d (e.raise 0) x
          (((ModuleCat.uliftFunctor.{1} ℤ).map
            (internalDifferentialTensorMap e 0)).hom y)) =
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v, (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
          (ULift.up (((𝟙 (summandModule d) ⊗ₘ
              internalDifferentialTensorMap e 0) ≫
            summandCompositionMap d (e.raise 0) ≫
            eqToHom (appendBoundaryRightSummandModuleEq d e)).hom
              (x.down ⊗ₜ[ℤ] y.down))) := by
  change
    (eqToHom (congrArg (quotientGradedModule X Z)
      (rightLeibnizDegreeEq n m))).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z (n + (m + 1)) ↦ largeSummandModule s)
          ⟨w.append v, d.append (e.raise 0)⟩).hom
            (ULift.up (((𝟙 (summandModule d) ⊗ₘ
              internalDifferentialTensorMap e 0) ≫
                summandCompositionMap d (e.raise 0)).hom
                  (x.down ⊗ₜ[ℤ] y.down)))) = _
  apply quotientGradedModule_eqToHom_inclusion_apply (rightLeibnizDegreeEq n m)
  · apply gradedSummandIndex_mk_heq_of_eq (rightLeibnizDegreeEq n m) rfl
    exact (degreeProfile_castTotal_heq (rightLeibnizDegreeEq n m)
      (d.append (e.raise 0))).trans
        (heq_of_eq (DegreeProfile.raise_append_boundary_right d e).symm)
  · let z := ((𝟙 (summandModule d) ⊗ₘ internalDifferentialTensorMap e 0) ≫
      summandCompositionMap d (e.raise 0)).hom (x.down ⊗ₜ[ℤ] y.down)
    change HEq (ULift.up z)
      (ULift.up ((eqToHom (appendBoundaryRightSummandModuleEq d e)).hom z))
    exact uliftUp_heq
      (moduleCat_eqToHom_apply_heq (appendBoundaryRightSummandModuleEq d e) z)

theorem transported_boundary_internal_left_apply
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    (eqToHom (congrArg (quotientGradedModule X Z)
      (leftLeibnizDegreeEq n m))).hom
        (largeSummandCompositionMap (d.raise (Fin.last w.length)) e
          (((ModuleCat.uliftFunctor.{1} ℤ).map
            (internalDifferentialTensorMap d (Fin.last w.length))).hom x) y) =
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v, (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
          (ULift.up (((internalDifferentialTensorMap d (Fin.last w.length) ⊗ₘ
              𝟙 (summandModule e)) ≫
            summandCompositionMap (d.raise (Fin.last w.length)) e ≫
            eqToHom (appendBoundaryLeftSummandModuleEq d e)).hom
              (x.down ⊗ₜ[ℤ] y.down))) := by
  change
    (eqToHom (congrArg (quotientGradedModule X Z)
      (leftLeibnizDegreeEq n m))).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z ((n + 1) + m) ↦ largeSummandModule s)
          ⟨w.append v, (d.raise (Fin.last w.length)).append e⟩).hom
            (ULift.up (((internalDifferentialTensorMap d (Fin.last w.length) ⊗ₘ
              𝟙 (summandModule e)) ≫
                summandCompositionMap (d.raise (Fin.last w.length)) e).hom
                  (x.down ⊗ₜ[ℤ] y.down)))) = _
  apply quotientGradedModule_eqToHom_inclusion_apply (leftLeibnizDegreeEq n m)
  · apply gradedSummandIndex_mk_heq_of_eq (leftLeibnizDegreeEq n m) rfl
    exact (degreeProfile_castTotal_heq (leftLeibnizDegreeEq n m)
      ((d.raise (Fin.last w.length)).append e)).trans
        (heq_of_eq (DegreeProfile.raise_append_boundary_left d e).symm)
  · let z := ((internalDifferentialTensorMap d (Fin.last w.length) ⊗ₘ
      𝟙 (summandModule e)) ≫
        summandCompositionMap (d.raise (Fin.last w.length)) e).hom
          (x.down ⊗ₜ[ℤ] y.down)
    change HEq (ULift.up z)
      (ULift.up ((eqToHom (appendBoundaryLeftSummandModuleEq d e)).hom z))
    exact uliftUp_heq
      (moduleCat_eqToHom_apply_heq (appendBoundaryLeftSummandModuleEq d e) z)

theorem recursiveContractionTarget_eq_left_last
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    tensorModuleList
        (finFamilyList
          (recursiveMergedFactor (factorModule d) i
            (contractedFactorAtOldIndex d i i))) =
      summandModule (d.contract i) := by
  apply congrArg tensorModuleList
  calc
    _ = finFamilyList (contractedFactorAtOldIndex d i) := by
      exact congrArg finFamilyList
        (funext (recursiveContractionMergedFactor_eq d i))
    _ = _ := contractedFactorsOldIndex_eq d i

def leftLastZeroHeadDegreeProfile
    {X Y : ComplexCategory}
    {intermediate : Fin 1 → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    DegreeProfile (nil X (intermediate 0).obj) (d.arrowDegree 0) where
  arrowDegree _ := d.arrowDegree 0
  totalDegree := by simp [nil]

def leftLastZeroTailDegreeProfile
    {X Y : ComplexCategory}
    {intermediate : Fin 1 → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    DegreeProfile (nil (intermediate 0).obj Y) (d.arrowDegree 1) where
  arrowDegree _ := d.arrowDegree 1
  totalDegree := by simp [nil]

theorem leftLastZeroNormalizedPairTensorMap_heq
    {X Y Z : ComplexCategory}
    {intermediate : Fin 1 → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      ((@AdjacentMergeData.head
          (factorModule (leftLastZeroHeadDegreeProfile d) 0)
          (factorModule (leftLastZeroTailDegreeProfile d) 0)
          (compositionBoundaryModule (leftLastZeroHeadDegreeProfile d)
            (leftLastZeroTailDegreeProfile d))
          (factorModule e 0 :: compositionRightSuffix e)
          (compositionBoundaryMap (leftLastZeroHeadDegreeProfile d)
            (leftLastZeroTailDegreeProfile d))).tensorMap ≫
        (@AdjacentMergeData.head
          (compositionBoundaryModule (leftLastZeroHeadDegreeProfile d)
            (leftLastZeroTailDegreeProfile d))
          (factorModule e 0)
          (tripleCompositionBoundaryModule (leftLastZeroHeadDegreeProfile d)
            (leftLastZeroTailDegreeProfile d) e)
          (compositionRightSuffix e)
          (leftAssociatedBoundaryMap (leftLastZeroHeadDegreeProfile d)
            (leftLastZeroTailDegreeProfile d) e)).tensorMap)
      ((@AdjacentMergeData.tail
          (factorModule (leftLastZeroHeadDegreeProfile d) 0)
          (factorModule (leftLastZeroTailDegreeProfile d) 0 ::
            factorModule e 0 :: compositionRightSuffix e)
          (zeroMiddleRightBoundaryModule (leftLastZeroTailDegreeProfile d) e ::
            compositionRightSuffix e)
          (@AdjacentMergeData.head
            (factorModule (leftLastZeroTailDegreeProfile d) 0)
            (factorModule e 0)
            (zeroMiddleRightBoundaryModule (leftLastZeroTailDegreeProfile d) e)
            (compositionRightSuffix e)
            (zeroMiddleRightBoundaryMap (leftLastZeroTailDegreeProfile d) e))).tensorMap ≫
        (@AdjacentMergeData.head
          (factorModule (leftLastZeroHeadDegreeProfile d) 0)
          (zeroMiddleRightBoundaryModule (leftLastZeroTailDegreeProfile d) e)
          (tripleCompositionBoundaryModule (leftLastZeroHeadDegreeProfile d)
            (leftLastZeroTailDegreeProfile d) e)
          (compositionRightSuffix e)
          (rightAssociatedBoundaryMap (leftLastZeroHeadDegreeProfile d)
            (leftLastZeroTailDegreeProfile d) e)).tensorMap) := by
  exact (normalizedBoundaryPairCoherence [] (compositionRightSuffix e)
    (leftLastZeroHeadDegreeProfile d) (leftLastZeroTailDegreeProfile d) e).tensorMap_heq

def contractionRecursiveTargetListEq_right_zero_core
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    finFamilyList (factorModule (d.contract i)) =
      finFamilyList (recursiveMergedFactor (factorModule d) i
        (contractedFactorAtOldIndex d i i)) :=
  (contractedFactorsOldIndex_eq d i).symm.trans
    (congrArg finFamilyList
      (funext (recursiveContractionMergedFactor_eq d i))).symm

def rightZeroHeadDegreeProfile
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    DegreeProfile (nil Y (intermediate 0).obj) (e.arrowDegree 0) where
  arrowDegree := fun _ ↦ e.arrowDegree 0
  totalDegree := by
    simp [nil]

theorem rightZeroNormalizedPairTensorMap_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (((@AdjacentMergeData.head
          (factorModule d (Fin.last w.length))
          (factorModule (rightZeroHeadDegreeProfile e) 0)
          (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
          (factorModule (tailDegreeProfile e) 0 ::
            compositionRightSuffix (tailDegreeProfile e))
          (compositionBoundaryMap d (rightZeroHeadDegreeProfile e))).prefix
            (compositionLeftPrefix d)).tensorMap ≫
        ((@AdjacentMergeData.head
          (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
          (factorModule (tailDegreeProfile e) 0)
          (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (compositionRightSuffix (tailDegreeProfile e))
          (leftAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap)
      (((@AdjacentMergeData.tail (factorModule d (Fin.last w.length))
          (factorModule (rightZeroHeadDegreeProfile e) 0 ::
            factorModule (tailDegreeProfile e) 0 ::
              compositionRightSuffix (tailDegreeProfile e))
          (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
              (tailDegreeProfile e) :: compositionRightSuffix (tailDegreeProfile e))
          (@AdjacentMergeData.head
            (factorModule (rightZeroHeadDegreeProfile e) 0)
            (factorModule (tailDegreeProfile e) 0)
            (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
              (tailDegreeProfile e))
            (compositionRightSuffix (tailDegreeProfile e))
            (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
              (tailDegreeProfile e)))).prefix (compositionLeftPrefix d)).tensorMap ≫
        ((@AdjacentMergeData.head
          (factorModule d (Fin.last w.length))
          (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (compositionRightSuffix (tailDegreeProfile e))
          (rightAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap) := by
  exact (normalizedBoundaryPairCoherence (compositionLeftPrefix d)
    (compositionRightSuffix (tailDegreeProfile e)) d
    (rightZeroHeadDegreeProfile e) (tailDegreeProfile e)).tensorMap_heq

theorem finAddCases_succAbove_append_left
    {α : Type*} (k l : ℕ) (f : Fin (k + 1) → α) (g : Fin l → α)
    (i : Fin (k + 1)) :
    let htotal : (k + 1) + l = (k + l) + 1 := by omega
    let itotal : Fin ((k + l) + 1) := ⟨i.val, by omega⟩
    (fun q : Fin (k + l) =>
      Fin.addCases (motive := fun _ => α) f g
        (Fin.cast htotal.symm (itotal.succAbove q))) =
    fun q => Fin.addCases (motive := fun _ => α)
      (fun r : Fin k => f (i.succAbove r)) g q := by
  dsimp only
  funext q
  induction q using Fin.addCases with
  | left r =>
      rw [Fin.addCases_left]
      have hindex :
          Fin.cast (show (k + l) + 1 = (k + 1) + l by omega)
              ((⟨i.val, by omega⟩ : Fin ((k + l) + 1)).succAbove
                (Fin.castAdd l r)) =
            Fin.castAdd l (i.succAbove r) := by
        ext
        simp [Fin.succAbove, Fin.lt_def]
        split_ifs <;> rfl
      rw [hindex, Fin.addCases_left]
  | right s =>
      rw [Fin.addCases_right]
      have hindex :
          Fin.cast (show (k + l) + 1 = (k + 1) + l by omega)
              ((⟨i.val, by omega⟩ : Fin ((k + l) + 1)).succAbove
                (Fin.natAdd k s)) =
            Fin.natAdd (k + 1) s := by
        have hle :
            (⟨i.val, by omega⟩ : Fin ((k + l) + 1)) ≤
              (Fin.natAdd k s).castSucc := by
          change i.val ≤ k + s.val
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ hle]
        ext
        simp only [Fin.val_cast, Fin.val_succ, Fin.val_natAdd]
        omega
      rw [hindex, Fin.addCases_right]

theorem eraseIntermediate_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin w.length) :
    eraseIntermediate (w.append v) (appendLeftContractionIndex i) =
      (eraseIntermediate w i).append v := by
  cases w with
  | mk wl wi =>
      cases wl with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases v with
          | mk vl vi =>
              cases k with
              | zero =>
                  change Fin 1 at i
                  cases vl with
                  | zero =>
                      exact (eq_nil_of_length_eq_zero _ rfl).symm
                  | succ l =>
                      cases l with
                      | zero =>
                          have hindex : appendLeftContractionIndex
                              (X := X) (Y := Y) (Z := Z)
                              (w := { length := 1, intermediate := wi })
                              (v := { length := 1, intermediate := vi }) i =
                              (⟨i.val, by omega⟩ : Fin (1 + 1)) := Fin.ext rfl
                          rw [hindex]
                          simp only [append, eraseIntermediate, DrinfeldWord.mk.injEq, nil,
                            Nat.zero_add]
                          constructor
                          · trivial
                          · apply heq_of_eq
                            exact finAddCases_succAbove_append_left 0 1 wi vi i
                      | succ l =>
                          have hindex : appendLeftContractionIndex
                              (X := X) (Y := Y) (Z := Z)
                              (w := { length := 1, intermediate := wi })
                              (v := { length := l + 2, intermediate := vi }) i =
                              (⟨i.val, by omega⟩ : Fin (1 + (l + 2))) := Fin.ext rfl
                          rw [hindex]
                          simp only [append, eraseIntermediate, DrinfeldWord.mk.injEq, nil,
                            Nat.zero_add]
                          let hlength : Nat.add 1 l + 1 = l + 1 + 1 := by
                            exact congrArg (· + 1) (Nat.add_comm 1 l)
                          constructor
                          · exact hlength
                          · refine (Fin.heq_fun_iff (by
                              change (0 + 1) + l + 1 = 0 + (l + (1 + 1))
                              omega)).mpr ?_
                            intro q
                            let q' : Fin (0 + (l + 2)) :=
                              ⟨q.val, by
                                have hcast : Nat.add 1 l + 1 = 0 + (l + 2) := by
                                  simpa only [Nat.zero_add, Nat.add_assoc] using hlength
                                exact hcast ▸ q.isLt⟩
                            fin_cases i
                            simp [Fin.succAbove, Fin.addCases]
                            congr 2
              | succ k =>
                  change Fin (k + 2) at i
                  cases vl with
                  | zero =>
                      have hindex : appendLeftContractionIndex
                          (X := X) (Y := Y) (Z := Z)
                          (w := { length := k + 2, intermediate := wi })
                          (v := { length := 0, intermediate := vi }) i =
                          (⟨i.val, by omega⟩ : Fin ((k + 2) + 0)) := Fin.ext rfl
                      rw [hindex]
                      simp only [append, eraseIntermediate, DrinfeldWord.mk.injEq,
                        Nat.add_zero]
                      constructor
                      · trivial
                      · apply heq_of_eq
                        exact finAddCases_succAbove_append_left (k + 1) 0 wi vi i
                  | succ l =>
                      cases l with
                      | zero =>
                          have hindex : appendLeftContractionIndex
                              (X := X) (Y := Y) (Z := Z)
                              (w := { length := k + 2, intermediate := wi })
                              (v := { length := 1, intermediate := vi }) i =
                              (⟨i.val, by omega⟩ : Fin ((k + 2) + 1)) := Fin.ext rfl
                          rw [hindex]
                          simp only [append, eraseIntermediate, DrinfeldWord.mk.injEq]
                          constructor
                          · trivial
                          · apply heq_of_eq
                            exact finAddCases_succAbove_append_left (k + 1) 1 wi vi i
                      | succ l =>
                          have hindex : appendLeftContractionIndex
                              (X := X) (Y := Y) (Z := Z)
                              (w := { length := k + 2, intermediate := wi })
                              (v := { length := l + 2, intermediate := vi }) i =
                              (⟨i.val, by omega⟩ : Fin ((k + 2) + (l + 2))) := Fin.ext rfl
                          rw [hindex]
                          simp only [append, eraseIntermediate, DrinfeldWord.mk.injEq]
                          let hlength : (k + 1 + 1).add l + 1 =
                              k + 1 + (l + 1 + 1) := by
                            change (k + 1 + 1) + l + 1 = k + 1 + (l + 1 + 1)
                            omega
                          constructor
                          · exact hlength
                          · refine (Fin.heq_fun_iff (by
                              exact hlength)).mpr ?_
                            intro q
                            let q' : Fin (k + 1 + (l + 1 + 1)) :=
                              Fin.cast hlength q
                            have hq := congrFun (finAddCases_succAbove_append_left
                              (k + 1) (l + 2) wi vi i) q'
                            convert hq using 1
                            · congr 1
                              apply Fin.ext
                              dsimp [q', Fin.succAbove]
                              split_ifs <;>
                                simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ,
                                  Fin.val_cast] at * <;>
                                  omega
                            · congr 1

theorem DegreeProfile.contract_append_left_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    HEq ((d.append e).contract (appendLeftContractionIndex i))
      ((d.contract i).append e) := by
  have hword := eraseIntermediate_append_left (v := v) i
  have htotal : n + m + 1 = (n + 1) + m := by omega
  let rhs' := ((d.contract i).append e).transport hword.symm htotal.symm
  have heq : (d.append e).contract (appendLeftContractionIndex i) = rhs' := by
    apply DegreeProfile.ext
    funext q
    rw [DegreeProfile.transport_arrowDegree]
    let hlen : (eraseIntermediate (w.append v)
        (appendLeftContractionIndex i)).length + 1 =
          w.length + v.length := by simp
    let q' : Fin (w.length + v.length) := Fin.cast hlen q
    have hq : q = Fin.cast hlen.symm q' := by simp [q']
    rw [hq]
    induction q' using Fin.addCases with
    | left k =>
        let qleft := Fin.cast hlen.symm (Fin.castAdd v.length k)
        have hold : Fin.cast (eraseIntermediate_length (w.append v)
              (appendLeftContractionIndex i)) qleft =
            appendLeftContractionIndex (v := v) k := by
          apply Fin.ext
          rfl
        by_cases hklast : k.val + 1 = w.length
        · have htarget : Fin.cast
              (congrArg (fun u : DrinfeldWord X Z ↦ u.length + 1)
                hword.symm).symm qleft =
            appendBoundaryArrowIndex (eraseIntermediate w i) v := by
            apply Fin.ext
            change qleft.val = (eraseIntermediate w i).length
            dsimp [qleft]
            have herase := eraseIntermediate_length w i
            omega
          change contractedArrowDegree (appendArrowDegree d e)
              (appendLeftContractionIndex i)
                (Fin.cast (eraseIntermediate_length (w.append v)
                  (appendLeftContractionIndex i)) qleft) =
            appendArrowDegree (d.contract i) e
              (Fin.cast (congrArg
                (fun u : DrinfeldWord X Z ↦ u.length + 1)
                  hword.symm).symm qleft)
          rw [hold, htarget, appendArrowDegree_boundary]
          change contractedArrowDegree (appendArrowDegree d e)
              (appendLeftContractionIndex i)
                (appendLeftContractionIndex (v := v) k) =
            contractedArrowDegree d.arrowDegree i
                (Fin.cast (eraseIntermediate_length w i)
                  (Fin.last (eraseIntermediate w i).length)) +
              e.arrowDegree 0
          have hkcast : Fin.cast (eraseIntermediate_length w i)
                (Fin.last (eraseIntermediate w i).length) = k := by
            apply Fin.ext
            have herase := eraseIntermediate_length w i
            change (eraseIntermediate w i).length = k.val
            omega
          rw [hkcast]
          unfold contractedArrowDegree
          have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (by omega)
          have hfull :
              (appendLeftContractionIndex (v := v) i).castSucc ≤
                (appendLeftContractionIndex (v := v) k).castSucc := by
            change i.val ≤ k.val
            omega
          rw [Fin.succAbove_of_le_castSucc _ _ hfull,
            Fin.succAbove_of_le_castSucc _ _ hik]
          have hboundary :
              (appendLeftContractionIndex (v := v) k).succ =
                appendBoundaryArrowIndex w v := by
            apply Fin.ext
            change k.val + 1 = w.length
            exact hklast
          have hlast : k.succ = Fin.last w.length := by
            apply Fin.ext
            change k.val + 1 = w.length
            exact hklast
          have hleft :
              (appendLeftContractionIndex (v := v) i).castSucc =
                appendLeftArrowIndex (v := v) i := by
            apply Fin.ext
            rfl
          rw [hboundary, hlast, hleft, appendArrowDegree_boundary,
            appendArrowDegree_left]
          have hiff : appendLeftContractionIndex (v := v) k =
                appendLeftContractionIndex i ↔ k = i := by
            constructor
            · intro h
              apply Fin.ext
              have hval := congrArg Fin.val h
              exact hval
            · intro h
              exact congrArg (fun r ↦ appendLeftContractionIndex (v := v) r) h
          by_cases hki : k = i
          · rw [if_pos (hiff.mpr hki), if_pos hki]
            ring
          · rw [if_neg (fun h ↦ hki (hiff.mp h)), if_neg hki]
            ring
        · let kleft : Fin (eraseIntermediate w i).length :=
              ⟨k.val, by
                have hklt := k.isLt
                have herase := eraseIntermediate_length w i
                omega⟩
          have htarget : Fin.cast
                (congrArg (fun u : DrinfeldWord X Z ↦ u.length + 1)
                  hword.symm).symm qleft =
              appendLeftArrowIndex (v := v) kleft := by
            apply Fin.ext
            rfl
          change contractedArrowDegree (appendArrowDegree d e)
              (appendLeftContractionIndex i)
                (Fin.cast (eraseIntermediate_length (w.append v)
                  (appendLeftContractionIndex i)) qleft) =
            appendArrowDegree (d.contract i) e
              (Fin.cast (congrArg
                (fun u : DrinfeldWord X Z ↦ u.length + 1)
                  hword.symm).symm qleft)
          rw [hold, htarget, appendArrowDegree_left]
          change contractedArrowDegree (appendArrowDegree d e)
              (appendLeftContractionIndex i)
                (appendLeftContractionIndex (v := v) k) =
            contractedArrowDegree d.arrowDegree i
              (Fin.cast (eraseIntermediate_length w i) kleft.castSucc)
          have hkcast : Fin.cast (eraseIntermediate_length w i) kleft.castSucc = k := by
            apply Fin.ext
            rfl
          rw [hkcast]
          unfold contractedArrowDegree
          let ksucc : Fin w.length :=
            ⟨(i.castSucc.succAbove k).val, by
              by_cases hki : k < i
              · rw [Fin.succAbove_of_castSucc_lt _ _ hki]
                exact k.isLt
              · have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (by omega)
                rw [Fin.succAbove_of_le_castSucc _ _ hik]
                change k.val + 1 < w.length
                omega⟩
          have hksucc : ksucc.castSucc = i.castSucc.succAbove k := by
            apply Fin.ext
            rfl
          have hsucc :
              (appendLeftContractionIndex (v := v) i).castSucc.succAbove
                  (appendLeftContractionIndex (v := v) k) =
                appendLeftArrowIndex (v := v) ksucc := by
            apply Fin.ext
            by_cases hki : k < i
            · have hfull :
                  (appendLeftContractionIndex (v := v) k).castSucc <
                    (appendLeftContractionIndex (v := v) i).castSucc := by
                change k.val < i.val
                omega
              rw [Fin.succAbove_of_castSucc_lt _ _ hfull]
              change k.val = ksucc.val
              dsimp [ksucc]
              rw [Fin.succAbove_of_castSucc_lt _ _ hki]
              rfl
            · have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (by omega)
              have hfull :
                  (appendLeftContractionIndex (v := v) i).castSucc ≤
                    (appendLeftContractionIndex (v := v) k).castSucc := by
                change i.val ≤ k.val
                omega
              rw [Fin.succAbove_of_le_castSucc _ _ hfull]
              change k.val + 1 = ksucc.val
              dsimp [ksucc]
              rw [Fin.succAbove_of_le_castSucc _ _ hik]
              rfl
          have hleft :
              (appendLeftContractionIndex (v := v) i).castSucc =
                appendLeftArrowIndex (v := v) i := by
            apply Fin.ext
            rfl
          rw [hsucc, hleft, appendArrowDegree_left, appendArrowDegree_left,
            hksucc]
          have hiff : appendLeftContractionIndex (v := v) k =
                appendLeftContractionIndex i ↔ k = i := by
            constructor
            · intro h
              apply Fin.ext
              have hval := congrArg Fin.val h
              exact hval
            · intro h
              exact congrArg (fun r ↦ appendLeftContractionIndex (v := v) r) h
          by_cases hki : k = i
          · rw [if_pos (hiff.mpr hki), if_pos hki]
          · rw [if_neg (fun h ↦ hki (hiff.mp h)), if_neg hki]
    | right k =>
        let qright := Fin.cast hlen.symm (Fin.natAdd w.length k)
        have hold : Fin.cast (eraseIntermediate_length (w.append v)
              (appendLeftContractionIndex i)) qright =
            appendRightContractionIndex (w := w) k := by
          apply Fin.ext
          rfl
        have htarget : Fin.cast
              (congrArg (fun u : DrinfeldWord X Z ↦ u.length + 1)
                hword.symm).symm qright =
            appendRightArrowIndex (w := eraseIntermediate w i) k := by
          apply Fin.ext
          change qright.val = (eraseIntermediate w i).length + 1 + k.val
          dsimp [qright]
          have herase := eraseIntermediate_length w i
          omega
        change contractedArrowDegree (appendArrowDegree d e)
            (appendLeftContractionIndex i)
              (Fin.cast (eraseIntermediate_length (w.append v)
                (appendLeftContractionIndex i)) qright) =
          appendArrowDegree (d.contract i) e
            (Fin.cast (congrArg
              (fun u : DrinfeldWord X Z ↦ u.length + 1)
                hword.symm).symm qright)
        rw [hold, htarget]
        unfold contractedArrowDegree
        have hafter :
            (appendLeftContractionIndex (v := v) i).castSucc ≤
              (appendRightContractionIndex (w := w) k).castSucc := by
          change i.val ≤ w.length + k.val
          omega
        rw [Fin.succAbove_of_le_castSucc _ _ hafter]
        have hright : (appendRightContractionIndex (w := w) k).succ =
            appendRightArrowIndex (w := w) k := by
          apply Fin.ext
          change w.length + k.val + 1 = w.length + 1 + k.val
          omega
        rw [hright, appendArrowDegree_right, appendArrowDegree_right]
        have hne : appendRightContractionIndex (w := w) k ≠
            appendLeftContractionIndex i := by
          intro h
          have hval := congrArg Fin.val h
          change w.length + k.val = i.val at hval
          omega
        rw [if_neg hne]
        simp
  exact (heq_of_eq heq).trans (by
    unfold rhs' DegreeProfile.transport
    simp only [eqRec_heq_iff_heq]
    exact HEq.rfl)

theorem summandModule_contract_append_left_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    HEq (summandModule ((d.append e).contract (appendLeftContractionIndex i)))
      (summandModule ((d.contract i).append e)) := by
  have hword := eraseIntermediate_append_left (v := v) i
  have htotal : n + m + 1 = (n + 1) + m := by omega
  let rhs' := ((d.contract i).append e).transport hword.symm htotal.symm
  have htransport : HEq rhs' ((d.contract i).append e) := by
    unfold rhs' DegreeProfile.transport
    simp only [eqRec_heq_iff_heq]
    exact HEq.rfl
  have hprofile : (d.append e).contract (appendLeftContractionIndex i) =
      rhs' := eq_of_heq ((DegreeProfile.contract_append_left_heq d e i).trans
        htransport.symm)
  exact heq_of_eq ((congrArg summandModule hprofile).trans
    (summandModuleTransportEq hword.symm htotal.symm
      ((d.contract i).append e)).symm)

theorem eraseIntermediate_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin v.length) :
    eraseIntermediate (w.append v) (appendRightContractionIndex j) =
      w.append (eraseIntermediate v j) := by
  cases w with
  | mk wl wi =>
      cases v with
      | mk vl vi =>
          cases vl with
          | zero => exact Fin.elim0 j
          | succ vk =>
              cases wl with
              | zero =>
                  cases vk with
                  | zero =>
                      apply (eq_nil_of_length_eq_zero _ rfl).symm
                  | succ vk =>
                      simp only [append, eraseIntermediate,
                        appendRightContractionIndex, DrinfeldWord.mk.injEq]
                      let hlen : Nat.add 0 vk + 1 = 0 + (vk + 1) := by simp
                      constructor
                      · exact hlen
                      · refine (Fin.heq_fun_iff hlen).mpr ?_
                        intro q
                        simp only [Fin.addCases, Fin.succAbove, not_lt_zero,
                          ↓reduceDIte, Nat.add_zero, Fin.subNat_zero,
                          eq_rec_constant]
                        apply congrArg vi
                        apply Fin.ext
                        simp only [Fin.val_cast]
                        split <;> rename_i hleft
                        · split <;> rename_i hright
                          · rfl
                          · change q.val < 0 + j.val at hleft
                            change ¬q.val < j.val at hright
                            omega
                        · split <;> rename_i hright
                          · change ¬q.val < 0 + j.val at hleft
                            change q.val < j.val at hright
                            omega
                          · rfl
              | succ wl =>
                  cases vk with
                  | zero =>
                      simp only [append, eraseIntermediate,
                        appendRightContractionIndex, DrinfeldWord.mk.injEq]
                      let hlen : wl + 1 = wl + 1 + (nil Y Z).length := by simp [nil]
                      constructor
                      · exact hlen
                      · refine (Fin.heq_fun_iff hlen).mpr ?_
                        intro q
                        have hj : j = 0 := Fin.eq_zero j
                        subst j
                        simp only [Fin.succAbove]
                        split
                        · have hq : q.val ≤ wl := by omega
                          suffices wi q = wi (q.castLT (by omega)) by
                            simpa [Fin.addCases, nil, hq]
                          apply congrArg wi
                          apply Fin.ext
                          rfl
                        · rename_i hsucc
                          exfalso
                          apply hsucc
                          exact q.isLt
                  | succ vk =>
                      simp only [append, eraseIntermediate,
                        appendRightContractionIndex, DrinfeldWord.mk.injEq]
                      let hlen : (wl + 1).add vk + 1 =
                          wl + 1 + (vk + 1) := by simp [Nat.add_assoc]
                      constructor
                      · exact hlen
                      · refine (Fin.heq_fun_iff hlen).mpr ?_
                        intro q
                        by_cases hq : q.val < wl + 1
                        · simp only [Fin.succAbove]
                          split
                          · simp [Fin.addCases, hq]
                            congr 1
                          · rename_i hsucc
                            exfalso
                            apply hsucc
                            change q.val < wl + 1 + j.val
                            omega
                        · simp only [Fin.succAbove]
                          split <;> rename_i hsucc
                          · change q.val < wl + 1 + j.val at hsucc
                            let r : Fin (vk + 1) :=
                              ⟨q.val - (wl + 1), by omega⟩
                            suffices vi r.castSucc =
                                vi (if r.castSucc < j then r.castSucc else r.succ) by
                              simpa [r, Fin.addCases, hq]
                            apply congrArg vi
                            split <;> rename_i hinner
                            · rfl
                            · change ¬q.val - (wl + 1) < j.val at hinner
                              exfalso
                              omega
                          · have hq0 : ¬q.val < wl := by omega
                            change ¬q.val < wl + 1 + j.val at hsucc
                            let r : Fin (vk + 1) :=
                              ⟨q.val - (wl + 1), by omega⟩
                            let qbase : Fin ((vk + 1) + (wl + 1)) :=
                              Fin.cast (by omega) q
                            have hqbase : wl + 1 ≤ qbase.val := by
                              dsimp only [qbase]
                              simp only [Fin.val_cast]
                              omega
                            let base : Fin (vk + 1) :=
                              Fin.subNat (wl + 1) qbase hqbase
                            let qhead : Fin ((vk + 1 + 1) + (wl + 1)) :=
                              Fin.cast (by omega) qbase.succ
                            have hqhead : wl + 1 ≤ qhead.val := by
                              dsimp only [qhead, qbase]
                              simp only [Fin.val_cast, Fin.val_succ]
                              omega
                            suffices
                                vi (Fin.subNat (wl + 1) qhead hqhead) =
                                  vi (if base.castSucc < j then base.castSucc
                                    else base.succ) by
                              simpa [Fin.addCases, hq, hq0, qbase, base, qhead]
                            have hhead : Fin.subNat (wl + 1) qhead hqhead =
                                r.succ := by
                              apply Fin.ext
                              dsimp only [qhead, qbase, r]
                              simp only [Fin.val_subNat, Fin.val_succ, Fin.val_cast]
                              omega
                            have hbase : base = r := by
                              apply Fin.ext
                              rfl
                            rw [hhead, hbase]
                            apply congrArg vi
                            split <;> rename_i hinner
                            · change q.val - (wl + 1) < j.val at hinner
                              exfalso
                              omega
                            · rfl

theorem DegreeProfile.contract_append_right_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    HEq ((d.append e).contract (appendRightContractionIndex j))
      (d.append (e.contract j)) := by
  have hword := eraseIntermediate_append_right (w := w) j
  have htotal : n + m + 1 = n + (m + 1) := by omega
  let rhs' := (d.append (e.contract j)).transport hword.symm htotal.symm
  have heq : (d.append e).contract (appendRightContractionIndex j) = rhs' := by
    apply DegreeProfile.ext
    funext q
    rw [DegreeProfile.transport_arrowDegree]
    let hlen : (eraseIntermediate (w.append v)
        (appendRightContractionIndex j)).length + 1 =
          w.length + v.length := by simp
    let q' : Fin (w.length + v.length) := Fin.cast hlen q
    have hq : q = Fin.cast hlen.symm q' := by simp [q']
    rw [hq]
    have hindex : (appendRightContractionIndex (w := w) j).val =
        w.length + j.val := rfl
    induction q' using Fin.addCases with
    | left k =>
        let qleft := Fin.cast hlen.symm (Fin.castAdd v.length k)
        have hold : Fin.cast (eraseIntermediate_length (w.append v)
              (appendRightContractionIndex j)) qleft =
            appendLeftContractionIndex (v := v) k := by
          apply Fin.ext
          rfl
        have htarget : Fin.cast
              (congrArg (fun u : DrinfeldWord X Z ↦ u.length + 1)
                hword.symm).symm qleft =
            appendLeftArrowIndex (v := eraseIntermediate v j) k := by
          apply Fin.ext
          rfl
        change contractedArrowDegree (appendArrowDegree d e)
            (appendRightContractionIndex j)
              (Fin.cast (eraseIntermediate_length (w.append v)
                (appendRightContractionIndex j)) qleft) =
          appendArrowDegree d (e.contract j)
            (Fin.cast (congrArg
              (fun u : DrinfeldWord X Z ↦ u.length + 1)
                hword.symm).symm qleft)
        rw [hold, htarget]
        unfold contractedArrowDegree
        have hbefore : (appendLeftContractionIndex (v := v) k).castSucc <
            (appendRightContractionIndex j).castSucc := by
          change k.val < w.length + j.val
          omega
        rw [Fin.succAbove_of_castSucc_lt _ _ hbefore]
        have harrow : (appendLeftContractionIndex (v := v) k).castSucc =
            appendLeftArrowIndex (v := v) k := by
          apply Fin.ext
          rfl
        rw [harrow, appendArrowDegree_left, appendArrowDegree_left]
        have hne : appendLeftContractionIndex (v := v) k ≠
            appendRightContractionIndex j := by
          intro heq
          have hval := congrArg Fin.val heq
          change k.val = w.length + j.val at hval
          omega
        split
        · rename_i heq
          exact (hne heq).elim
        · simp
    | right k =>
        let qright := Fin.cast hlen.symm (Fin.natAdd w.length k)
        have hold : Fin.cast (eraseIntermediate_length (w.append v)
              (appendRightContractionIndex j)) qright =
            appendRightContractionIndex (w := w) k := by
          apply Fin.ext
          rfl
        let qtarget : Fin ((w.append (eraseIntermediate v j)).length + 1) :=
          ⟨w.length + k.val, by
            rw [append_length]
            have herase := eraseIntermediate_length v j
            omega⟩
        have htarget : Fin.cast
              (congrArg (fun u : DrinfeldWord X Z ↦ u.length + 1)
                hword.symm).symm qright = qtarget := by
          apply Fin.ext
          rfl
        change contractedArrowDegree (appendArrowDegree d e)
            (appendRightContractionIndex j)
              (Fin.cast (eraseIntermediate_length (w.append v)
                (appendRightContractionIndex j)) qright) =
          appendArrowDegree d (e.contract j)
            (Fin.cast (congrArg
              (fun u : DrinfeldWord X Z ↦ u.length + 1)
                hword.symm).symm qright)
        rw [hold, htarget]
        by_cases hk0 : k.val = 0
        · have hboundary : qtarget =
              appendBoundaryArrowIndex w (eraseIntermediate v j) := by
            apply Fin.ext
            dsimp [qtarget, appendBoundaryArrowIndex]
            omega
          rw [hboundary, appendArrowDegree_boundary]
          by_cases hj0 : j.val = 0
          · have hkj : appendRightContractionIndex (w := w) k =
                appendRightContractionIndex j := by
              apply Fin.ext
              change w.length + k.val = w.length + j.val
              omega
            rw [hkj, contractedArrowDegree_self]
            have hright : (appendRightContractionIndex j).succ =
                appendRightArrowIndex (w := w) j := by
              apply Fin.ext
              dsimp [appendRightContractionIndex, appendRightArrowIndex]
              omega
            have hbound : (appendRightContractionIndex j).castSucc =
                appendBoundaryArrowIndex w v := by
              apply Fin.ext
              change w.length + j.val = w.length
              omega
            rw [hright, hbound, appendArrowDegree_right,
              appendArrowDegree_boundary]
            change e.arrowDegree j.succ +
                (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) =
              d.arrowDegree (Fin.last w.length) +
                contractedArrowDegree e.arrowDegree j
                  (Fin.cast (eraseIntermediate_length v j) 0)
            have hout : Fin.cast (eraseIntermediate_length v j) 0 = j := by
              apply Fin.ext
              simpa using hj0.symm
            rw [hout, contractedArrowDegree_self]
            have hjcast : j.castSucc = (0 : Fin (v.length + 1)) := by
              apply Fin.ext
              exact hj0
            rw [hjcast]
            ring
          · have hbefore :
                (appendRightContractionIndex (w := w) k).castSucc <
                  (appendRightContractionIndex j).castSucc := by
              change w.length + k.val < w.length + j.val
              omega
            unfold contractedArrowDegree
            rw [Fin.succAbove_of_castSucc_lt _ _ hbefore]
            have hbound :
                (appendRightContractionIndex (w := w) k).castSucc =
                  appendBoundaryArrowIndex w v := by
              apply Fin.ext
              change w.length + k.val = w.length
              omega
            have hne : appendRightContractionIndex (w := w) k ≠
                appendRightContractionIndex j := by
              intro heq
              have hval := congrArg Fin.val heq
              change w.length + k.val = w.length + j.val at hval
              omega
            rw [hbound, appendArrowDegree_boundary]
            simp only [if_neg hne]
            change d.arrowDegree (Fin.last w.length) + e.arrowDegree 0 + 0 =
              d.arrowDegree (Fin.last w.length) +
                contractedArrowDegree e.arrowDegree j
                  (Fin.cast (eraseIntermediate_length v j) 0)
            let z : Fin v.length := ⟨0, by omega⟩
            have hout : Fin.cast (eraseIntermediate_length v j) 0 =
                z := by
              apply Fin.ext
              rfl
            rw [hout]
            unfold contractedArrowDegree
            have hzbefore : z.castSucc < j.castSucc := by
              change 0 < j.val
              omega
            rw [Fin.succAbove_of_castSucc_lt _ _ hzbefore]
            have hzne : z ≠ j := by
              intro heq
              have hval := congrArg Fin.val heq
              exact hj0 hval.symm
            simp only [if_neg hzne, add_zero]
            congr 1
        · let kp : Fin (eraseIntermediate v j).length :=
              ⟨k.val - 1, by
                have hklt := k.isLt
                have herase := eraseIntermediate_length v j
                omega⟩
          have hrightTarget : qtarget =
              appendRightArrowIndex (w := w) kp := by
            apply Fin.ext
            dsimp [qtarget, kp, appendRightArrowIndex]
            omega
          rw [hrightTarget, appendArrowDegree_right]
          change contractedArrowDegree (appendArrowDegree d e)
              (appendRightContractionIndex j)
                (appendRightContractionIndex (w := w) k) =
            contractedArrowDegree e.arrowDegree j
              (Fin.cast (eraseIntermediate_length v j) kp.succ)
          have hout : Fin.cast (eraseIntermediate_length v j) kp.succ = k := by
            apply Fin.ext
            change k.val - 1 + 1 = k.val
            omega
          rw [hout]
          unfold contractedArrowDegree
          by_cases hkj : k < j
          · have hbefore :
                (appendRightContractionIndex (w := w) k).castSucc <
                  (appendRightContractionIndex j).castSucc := by
              change w.length + k.val < w.length + j.val
              omega
            rw [Fin.succAbove_of_castSucc_lt _ _ hbefore,
              Fin.succAbove_of_castSucc_lt _ _ hkj]
            let kpred : Fin v.length :=
              ⟨k.val - 1, by omega⟩
            have holdArrow :
                (appendRightContractionIndex (w := w) k).castSucc =
                  appendRightArrowIndex (w := w) kpred := by
              apply Fin.ext
              dsimp [appendRightContractionIndex, appendRightArrowIndex, kpred]
              omega
            have hkpred : kpred.succ = k.castSucc := by
              apply Fin.ext
              change k.val - 1 + 1 = k.val
              omega
            rw [holdArrow, appendArrowDegree_right, hkpred]
            have hne : appendRightContractionIndex (w := w) k ≠
                appendRightContractionIndex j := by
              intro heq
              have hval := congrArg Fin.val heq
              change w.length + k.val = w.length + j.val at hval
              omega
            rw [if_neg hne, if_neg (Fin.ne_of_lt hkj)]
          · have hjk : j ≤ k := Fin.le_iff_val_le_val.mpr (by omega)
            have hafter : (appendRightContractionIndex j).castSucc ≤
                (appendRightContractionIndex (w := w) k).castSucc := by
              change w.length + j.val ≤ w.length + k.val
              omega
            rw [Fin.succAbove_of_le_castSucc _ _ hafter,
              Fin.succAbove_of_le_castSucc _ _ hjk]
            have holdArrow : (appendRightContractionIndex (w := w) k).succ =
                appendRightArrowIndex (w := w) k := by
              apply Fin.ext
              dsimp [appendRightContractionIndex, appendRightArrowIndex]
              omega
            rw [holdArrow, appendArrowDegree_right]
            have heq : appendRightContractionIndex (w := w) k =
                appendRightContractionIndex j ↔ k = j := by
              constructor
              · intro h
                apply Fin.ext
                have hval := congrArg Fin.val h
                change w.length + k.val = w.length + j.val at hval
                omega
              · intro h
                exact congrArg
                  (fun r ↦ appendRightContractionIndex (w := w) r) h
            by_cases hEq : k = j
            · have hFull : appendRightContractionIndex (w := w) k =
                  appendRightContractionIndex j := heq.mpr hEq
              rw [if_pos hFull, if_pos hEq]
              let jpred : Fin v.length := ⟨j.val - 1, by omega⟩
              have hleftArrow : (appendRightContractionIndex (w := w) j).castSucc =
                  appendRightArrowIndex (w := w) jpred := by
                apply Fin.ext
                dsimp [appendRightContractionIndex, appendRightArrowIndex, jpred]
                omega
              rw [hleftArrow, appendArrowDegree_right]
              apply congrArg (fun x : ℤ ↦ e.arrowDegree k.succ + x)
              apply congrArg e.arrowDegree
              apply Fin.ext
              dsimp [jpred]
              have hval := congrArg Fin.val hEq
              omega
            · have hFull : appendRightContractionIndex (w := w) k ≠
                  appendRightContractionIndex j := fun h ↦ hEq (heq.mp h)
              rw [if_neg hFull, if_neg hEq]
  exact (heq_of_eq heq).trans (by
    unfold rhs' DegreeProfile.transport
    simp only [eqRec_heq_iff_heq]
    exact HEq.rfl)

theorem summandModule_contract_append_right_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    HEq (summandModule ((d.append e).contract (appendRightContractionIndex j)))
      (summandModule (d.append (e.contract j))) := by
  have hword := eraseIntermediate_append_right (w := w) j
  have htotal : n + m + 1 = n + (m + 1) := by omega
  let rhs' := (d.append (e.contract j)).transport hword.symm htotal.symm
  have htransport : HEq rhs' (d.append (e.contract j)) := by
    unfold rhs' DegreeProfile.transport
    simp only [eqRec_heq_iff_heq]
    exact HEq.rfl
  have hprofile : (d.append e).contract (appendRightContractionIndex j) =
      rhs' := eq_of_heq ((DegreeProfile.contract_append_right_heq d e j).trans
        htransport.symm)
  exact heq_of_eq ((congrArg summandModule hprofile).trans
    (summandModuleTransportEq hword.symm htotal.symm
      (d.append (e.contract j))).symm)

theorem compositionTargetInternalDifferential_append_boundary_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    HEq
      (eqToHom (congrArg tensorModuleList (compositionTargetListEq d e)) ≫
        internalDifferentialTensorMap (d.append e) (appendBoundaryArrowIndex w v))
      ((tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons
          ((dgHomZModuleCochainComplex
            (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).d
              (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
              ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1))
          (TensorMapData.identity (compositionRightSuffix e)))).tensorMap) := by
  let Mleft := fun i : Fin w.length ↦ factorModule d i.castSucc
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let P := compositionBoundaryModule d e
  let P' := (dgHomZModuleCochainComplex
    (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
      ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)
  let g := (dgHomZModuleCochainComplex
    (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).d
      (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
      ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)
  let explicitSource := finiteFamilyPrefixBoundarySuffix Mleft P Mright
  let explicitTarget := finiteFamilyPrefixBoundarySuffix Mleft P' Mright
  let explicitMap := finiteFamilyPrefixBoundarySuffixMap Mleft Mleft P P' Mright Mright
    (fun i ↦ 𝟙 (Mleft i)) g (fun r ↦ 𝟙 (Mright r))
  have hdata := tensorMapDataPrefixId_cons_ofFn_heq Mleft P P' Mright Mright g
    (fun r ↦ 𝟙 (Mright r))
  have hdataMap := tensorMapData_tensorMap_heq
    (finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft P Mright).symm
    (finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft P' Mright).symm hdata
  let tailOfFn : TensorMapData (compositionRightSuffix e) (compositionRightSuffix e) := by
    unfold compositionRightSuffix
    exact TensorMapData.ofFn Mright Mright (fun r ↦ 𝟙 (Mright r))
  have htail : (TensorMapData.identity (compositionRightSuffix e)).tensorMap =
      tailOfFn.tensorMap := by
    rw [TensorMapData.identity_tensorMap]
    simp [tailOfFn, Mright, compositionRightSuffix,
      TensorMapData.ofFn_id_tensorMap]
  have hcons :
      (TensorMapData.cons g
        (TensorMapData.identity (compositionRightSuffix e))).tensorMap =
      (TensorMapData.cons g tailOfFn).tensorMap := by
    change g ⊗ₘ (TensorMapData.identity (compositionRightSuffix e)).tensorMap =
      g ⊗ₘ tailOfFn.tensorMap
    rw [htail]
  have hprefix :
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons g
          (TensorMapData.identity (compositionRightSuffix e)))).tensorMap =
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons g tailOfFn)).tensorMap := by
    calc
      _ = tensorModuleListWhiskerLeft (compositionLeftPrefix d)
          (TensorMapData.cons g
            (TensorMapData.identity (compositionRightSuffix e))).tensorMap :=
        tensorMapDataPrefixId_tensorMap _ _
      _ = tensorModuleListWhiskerLeft (compositionLeftPrefix d)
          (TensorMapData.cons g tailOfFn).tensorMap :=
        congrArg (tensorModuleListWhiskerLeft (compositionLeftPrefix d)) hcons
      _ = _ := (tensorMapDataPrefixId_tensorMap _ _).symm
  have hleftExplicit : HEq
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons g (TensorMapData.identity (compositionRightSuffix e)))).tensorMap
      (TensorMapData.ofFn explicitSource explicitTarget explicitMap).tensorMap := by
    refine (heq_of_eq hprefix).trans ?_
    simpa [Mleft, Mright, P, P', g, tailOfFn, explicitSource, explicitTarget,
      explicitMap, compositionLeftPrefix, compositionRightSuffix,
      compositionBoundaryModule] using hdataMap
  have hlen : (v.length + w.length) + 1 = (w.append v).length + 1 := by
    rw [append_length]
    omega
  let appendIndex := fun q : Fin ((v.length + w.length) + 1) ↦ Fin.cast hlen q
  let appendSource := fun q : Fin ((v.length + w.length) + 1) ↦
    factorModule (d.append e) (appendIndex q)
  let appendTarget := fun q : Fin ((v.length + w.length) + 1) ↦
    factorModule ((d.append e).raise (appendBoundaryArrowIndex w v)) (appendIndex q)
  let appendMap := fun q : Fin ((v.length + w.length) + 1) ↦
    factorDifferential (d.append e) (appendBoundaryArrowIndex w v) (appendIndex q)
  have hsourceList : finFamilyList explicitSource = finFamilyList appendSource := by
    calc
      _ = compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e := by
        simpa [explicitSource, Mleft, Mright, P, compositionLeftPrefix,
          compositionRightSuffix] using
            finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft P Mright
      _ = finFamilyList (factorModule (d.append e)) :=
        (finFamilyList_factorModule_append_boundary d e).symm
      _ = finFamilyList appendSource := by
        simpa [appendSource, appendIndex] using
          (finFamilyList_reindex hlen (factorModule (d.append e))).symm
  have htot : n + (m + 1) = (n + m) + 1 := by omega
  have hraise := DegreeProfile.raise_append_boundary_right d e
  have hfactor :
      finFamilyList (factorModule ((d.append (e.raise 0)).castTotal htot)) =
        finFamilyList (factorModule (d.append (e.raise 0))) := by
    rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
    apply (List.ofFn_inj).2
    funext q
    unfold factorModule
    rw [DegreeProfile.castTotal_arrowDegree]
  have hraisedList :
      finFamilyList
          (factorModule ((d.append e).raise (appendBoundaryArrowIndex w v))) =
        compositionLeftPrefix d ++ P' :: compositionRightSuffix e := by
    rw [hraise, hfactor, finFamilyList_factorModule_append_boundary]
    congr 2
    · unfold P' compositionBoundaryModule
      congr 1
      simp [DegreeProfile.raise]
      omega
    · unfold compositionRightSuffix
      rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
      apply (List.ofFn_inj).2
      funext i
      unfold factorModule
      simp [DegreeProfile.raise]
  have htargetList : finFamilyList explicitTarget = finFamilyList appendTarget := by
    calc
      _ = compositionLeftPrefix d ++ P' :: compositionRightSuffix e := by
        simpa [explicitTarget, Mleft, Mright, P', compositionLeftPrefix,
          compositionRightSuffix] using
            finFamilyList_finiteFamilyPrefixBoundarySuffix Mleft P' Mright
      _ = finFamilyList
          (factorModule ((d.append e).raise (appendBoundaryArrowIndex w v))) :=
        hraisedList.symm
      _ = finFamilyList appendTarget := by
        simpa [appendTarget, appendIndex] using
          (finFamilyList_reindex hlen
            (factorModule ((d.append e).raise (appendBoundaryArrowIndex w v)))).symm
  have hsource : explicitSource = appendSource := by
    apply (List.ofFn_inj).1
    simpa only [← finFamilyList_eq_ofFn] using hsourceList
  have htarget : explicitTarget = appendTarget := by
    apply (List.ofFn_inj).1
    simpa only [← finFamilyList_eq_ofFn] using htargetList
  have hpointwise : ∀ q, HEq (explicitMap q) (appendMap q) := by
    intro q
    rcases finiteFamilyPrefixBoundarySuffixIndex_cases q with
      ⟨i, hi⟩ | hi | ⟨r, hr⟩
    · subst q
      have hindex : appendIndex (finiteFamilyPrefixIndex i) =
          appendLeftArrowIndex (v := v) i := by
        apply Fin.ext
        simp [appendIndex, appendLeftArrowIndex]
      have hne : appendBoundaryArrowIndex w v ≠ appendLeftArrowIndex (v := v) i := by
        intro h
        have hv := congrArg Fin.val h
        simp [appendBoundaryArrowIndex, appendLeftArrowIndex] at hv
        omega
      obtain ⟨hA, hmap⟩ := factorDifferential_eqToHom_of_ne_comp
        (d.append e) (appendBoundaryArrowIndex w v) (appendLeftArrowIndex i) hne
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Mleft P P' Mright Mright
          (fun i ↦ 𝟙 (Mleft i)) g (fun r ↦ 𝟙 (Mright r))
          (finiteFamilyPrefixIndex i))
        (factorDifferential (d.append e) (appendBoundaryArrowIndex w v)
          (appendIndex (finiteFamilyPrefixIndex i)))
      rw [hindex, hmap]
      exact (finiteFamilyPrefixBoundarySuffixMap_prefix_heq Mleft Mleft P P'
        Mright Mright (fun i ↦ 𝟙 (Mleft i)) g (fun r ↦ 𝟙 (Mright r)) i).trans
          (equalityTransport_heq_of_source_eq rfl hA
            (factorModule_append_left d e i).symm)
    · subst q
      have hindex : appendIndex (finiteFamilyBoundaryIndex w.length v.length) =
          appendBoundaryArrowIndex w v := by
        apply Fin.ext
        simp [appendIndex, appendBoundaryArrowIndex]
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Mleft P P' Mright Mright
          (fun i ↦ 𝟙 (Mleft i)) g (fun r ↦ 𝟙 (Mright r))
          (finiteFamilyBoundaryIndex w.length v.length))
        (factorDifferential (d.append e) (appendBoundaryArrowIndex w v)
          (appendIndex (finiteFamilyBoundaryIndex w.length v.length)))
      rw [hindex]
      exact (finiteFamilyPrefixBoundarySuffixMap_boundary_heq Mleft Mleft P P'
        Mright Mright (fun i ↦ 𝟙 (Mleft i)) g (fun r ↦ 𝟙 (Mright r))).trans
          (factorDifferential_append_boundary_heq d e).symm
    · subst q
      have hindex : appendIndex (finiteFamilySuffixIndex w.length r) =
          appendRightArrowIndex (w := w) r := by
        apply Fin.ext
        simp [appendIndex, appendRightArrowIndex]
      have hne : appendBoundaryArrowIndex w v ≠ appendRightArrowIndex (w := w) r := by
        intro h
        have hv := congrArg Fin.val h
        simp [appendBoundaryArrowIndex, appendRightArrowIndex] at hv
        omega
      obtain ⟨hA, hmap⟩ := factorDifferential_eqToHom_of_ne_comp
        (d.append e) (appendBoundaryArrowIndex w v) (appendRightArrowIndex r) hne
      change HEq
        (finiteFamilyPrefixBoundarySuffixMap Mleft Mleft P P' Mright Mright
          (fun i ↦ 𝟙 (Mleft i)) g (fun r ↦ 𝟙 (Mright r))
          (finiteFamilySuffixIndex w.length r))
        (factorDifferential (d.append e) (appendBoundaryArrowIndex w v)
          (appendIndex (finiteFamilySuffixIndex w.length r)))
      rw [hindex, hmap]
      exact (finiteFamilyPrefixBoundarySuffixMap_suffix_heq Mleft Mleft P P'
        Mright Mright (fun i ↦ 𝟙 (Mleft i)) g (fun r ↦ 𝟙 (Mright r)) r).trans
          (equalityTransport_heq_of_source_eq rfl hA
            (factorModule_append_right d e r).symm)
  have hcanonical := TensorMapData.ofFn_tensorMap_heq_of_pointwise
    explicitSource explicitTarget appendSource appendTarget explicitMap appendMap
    hsource htarget hpointwise
  have hreindex := TensorMapData.ofFn_reindex_tensorMap_heq hlen
    (factorModule (d.append e))
    (factorModule ((d.append e).raise (appendBoundaryArrowIndex w v)))
    (factorDifferential (d.append e) (appendBoundaryArrowIndex w v))
  have hdataToD : HEq
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons g (TensorMapData.identity (compositionRightSuffix e)))).tensorMap
      (internalDifferentialTensorMap (d.append e) (appendBoundaryArrowIndex w v)) := by
    simpa [appendSource, appendTarget, appendMap, appendIndex, summandModule,
      internalDifferentialTensorMap, g] using
        hleftExplicit.trans (hcanonical.trans hreindex)
  exact (CategoryTheory.eqToHom_comp_heq
    (internalDifferentialTensorMap (d.append e) (appendBoundaryArrowIndex w v))
    (congrArg tensorModuleList (compositionTargetListEq d e))).trans hdataToD.symm

theorem TensorMapData.ofFn_heq_identity_of_pointwise
    {k : ℕ} (M N : Fin k → ModuleCat.{0} ℤ)
    (f : (i : Fin k) → M i ⟶ N i) (hMN : M = N)
    (hf : ∀ i, HEq (f i) (𝟙 (M i))) :
    HEq (TensorMapData.ofFn M N f) (TensorMapData.identity (finFamilyList M)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      let Mtail := fun i : Fin k ↦ M i.succ
      let Ntail := fun i : Fin k ↦ N i.succ
      let ftail := fun i : Fin k ↦ f i.succ
      have htail : Mtail = Ntail := by
        funext i
        exact congrFun hMN i.succ
      change HEq
        (TensorMapData.cons (f 0) (TensorMapData.ofFn Mtail Ntail ftail))
        (TensorMapData.cons (𝟙 (M 0)) (TensorMapData.identity (finFamilyList Mtail)))
      exact tensorMapData_cons_heq rfl (congrFun hMN 0).symm rfl
        (congrArg finFamilyList htail).symm (hf 0)
        (ih Mtail Ntail ftail htail (fun i ↦ hf i.succ))

theorem tensorMapDataPrefixId_heq_boundary
    (xs : List (ModuleCat.{0} ℤ))
    {source target source' target' : List (ModuleCat.{0} ℤ)}
    {f : TensorMapData source target} {g : TensorMapData source' target'}
    (hsource : source = source') (htarget : target = target') (h : HEq f g) :
    HEq (tensorMapDataPrefixId xs f) (tensorMapDataPrefixId xs g) := by
  induction xs with
  | nil => exact h
  | cons M xs ih =>
      change HEq
        (TensorMapData.cons (𝟙 M) (tensorMapDataPrefixId xs f))
        (TensorMapData.cons (𝟙 M) (tensorMapDataPrefixId xs g))
      exact tensorMapData_cons_heq rfl rfl
        (congrArg (List.append xs) hsource)
        (congrArg (List.append xs) htarget) HEq.rfl ih

theorem tensorMapDataPrefixOfFn_heq_prefixId_of_pointwise
    {k : ℕ} (M N : Fin k → ModuleCat.{0} ℤ)
    (f : (i : Fin k) → M i ⟶ N i) (hMN : M = N)
    (hf : ∀ i, HEq (f i) (𝟙 (M i)))
    {source target : List (ModuleCat.{0} ℤ)} (tail : TensorMapData source target) :
    HEq (tensorMapDataPrefixOfFn M N f tail)
      (tensorMapDataPrefixId (finFamilyList M) tail) := by
  induction k with
  | zero => exact HEq.rfl
  | succ k ih =>
      let Mtail := fun i : Fin k ↦ M i.succ
      let Ntail := fun i : Fin k ↦ N i.succ
      let ftail := fun i : Fin k ↦ f i.succ
      have htail : Mtail = Ntail := by
        funext i
        exact congrFun hMN i.succ
      change HEq
        (TensorMapData.cons (f 0)
          (tensorMapDataPrefixOfFn Mtail Ntail ftail tail))
        (TensorMapData.cons (𝟙 (M 0))
          (tensorMapDataPrefixId (finFamilyList Mtail) tail))
      exact tensorMapData_cons_heq rfl (congrFun hMN 0).symm rfl
        (congrArg (fun xs ↦ xs ++ target) (congrArg finFamilyList htail).symm)
        (hf 0) (ih Mtail Ntail ftail htail (fun i ↦ hf i.succ))


theorem compositionLeftPrefix_raise_last_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    compositionLeftPrefix d =
      compositionLeftPrefix (d.raise (Fin.last w.length)) := by
  unfold compositionLeftPrefix
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
  apply (List.ofFn_inj).2
  funext i
  unfold factorModule
  have hne : (i.castSucc : Fin (w.length + 1)) ≠ Fin.last w.length :=
    Fin.castSucc_ne_last i
  simp [DegreeProfile.raise, hne]

theorem compositionBoundaryTarget_raise_last_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (dgHomZModuleCochainComplex
      (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
        ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1) =
      compositionBoundaryModule (d.raise (Fin.last w.length)) e := by
  unfold compositionBoundaryModule
  congr 1
  simp [DegreeProfile.raise]
  omega

theorem compositionRemainder_internalDifferential_boundary_right_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    HEq
      (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
          (internalDifferentialTensorMap e 0) ≫
        summandCompositionRemainder d (e.raise 0) ≫
        eqToHom (appendBoundaryRightSummandModuleEq d e))
      ((tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length)))
          (TensorMapData.cons (factorDifferential e 0 0)
            (TensorMapData.identity (compositionRightSuffix e))))).tensorMap ≫
        (adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d (e.raise 0) ≫
            eqToHom (show compositionBoundaryModule d (e.raise 0) = _ from by
              exact (compositionBoundaryTarget_raise_zero_eq d e).symm))).tensorMap) := by
  let Mright := fun r : Fin v.length ↦ factorModule e r.succ
  let Nright := fun r : Fin v.length ↦ factorModule (e.raise 0) r.succ
  let fright := fun r : Fin v.length ↦ factorDifferential e 0 r.succ
  have hMN : Mright = Nright := by
    funext r
    unfold Mright Nright factorModule
    simp [DegreeProfile.raise]
  let tailActual := TensorMapData.ofFn Mright Nright fright
  have htail : HEq tailActual (TensorMapData.identity (compositionRightSuffix e)) := by
    have hf : ∀ r, HEq (fright r) (𝟙 (Mright r)) := by
      intro r
      have hne : (0 : Fin (v.length + 1)) ≠ r.succ := (Fin.succ_ne_zero r).symm
      obtain ⟨hR, hmap⟩ := factorDifferential_eqToHom_of_ne_comp e 0 r.succ hne
      dsimp [fright, Mright]
      rw [hmap]
      exact test_eqToHom_heq_id hR
    simpa [tailActual, Mright, Nright, fright, compositionRightSuffix] using
      TensorMapData.ofFn_heq_identity_of_pointwise Mright Nright fright hMN hf
  let fullData := TensorMapData.ofFn (factorModule e)
    (factorModule (e.raise 0)) (factorDifferential e 0)
  let boundaryData := TensorMapData.cons (factorDifferential e 0 0)
    (TensorMapData.identity (compositionRightSuffix e))
  have hsourceE := finFamilyList_factorModule_eq_first_suffix e
  have htargetE : finFamilyList (factorModule (e.raise 0)) =
      factorModule (e.raise 0) 0 :: compositionRightSuffix e := by
    exact (finFamilyList_factorModule_eq_first_suffix (e.raise 0)).trans
      (congrArg (factorModule (e.raise 0) 0 :: ·) (congrArg finFamilyList hMN).symm)
  have hfull : HEq fullData boundaryData := by
    change HEq (TensorMapData.cons (factorDifferential e 0 0) tailActual) boundaryData
    have hMNList : finFamilyList Nright = compositionRightSuffix e := by
      simpa [Mright, compositionRightSuffix] using (congrArg finFamilyList hMN).symm
    exact tensorMapData_cons_heq rfl rfl rfl hMNList
      HEq.rfl htail
  let prefixLast := compositionLeftPrefix d ++ [factorModule d (Fin.last w.length)]
  let sourceData := tensorMapDataPrefixId (compositionLeftPrefix d)
    (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length))) boundaryData)
  have hinner : HEq
      (tensorMapDataPrefixId [factorModule d (Fin.last w.length)] fullData)
      (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length))) boundaryData) := by
    exact tensorMapDataPrefixId_heq_boundary [factorModule d (Fin.last w.length)]
      hsourceE htargetE hfull
  have hprefixData : HEq
      (tensorMapDataPrefixId (finFamilyList (factorModule d)) fullData) sourceData := by
    rw [finFamilyList_factorModule_eq_prefix_last d]
    refine (tensorMapDataPrefixId_append_heq (compositionLeftPrefix d)
      [factorModule d (Fin.last w.length)] fullData).trans ?_
    exact tensorMapDataPrefixId_heq_boundary (compositionLeftPrefix d)
      (congrArg (List.append [factorModule d (Fin.last w.length)]) hsourceE)
      (congrArg (List.append [factorModule d (Fin.last w.length)]) htargetE)
      hinner
  have hsourceList := (compositionSourceListEq d e).trans
    (compositionBoundaryListEq d e)
  have htargetList :
      finFamilyList (factorModule d) ++ finFamilyList (factorModule (e.raise 0)) =
        compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
          factorModule (e.raise 0) 0 :: compositionRightSuffix e := by
    exact ((compositionSourceListEq d (e.raise 0)).trans
      (compositionBoundaryListEq d (e.raise 0))).trans
        (congrArg
          (fun xs ↦ compositionLeftPrefix d ++
            factorModule d (Fin.last w.length) :: factorModule (e.raise 0) 0 :: xs)
          (congrArg finFamilyList hMN).symm)
  have hprefixDataMap : HEq
      (tensorMapDataPrefixId (finFamilyList (factorModule d)) fullData).tensorMap
      sourceData.tensorMap :=
    tensorMapData_tensorMap_heq hsourceList htargetList hprefixData
  have hprefixMap := tensorMapDataPrefixId_tensorMap
    (finFamilyList (factorModule d)) fullData
  have hsourceCore : HEq sourceData.tensorMap
      (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
        (internalDifferentialTensorMap e 0)) := by
    exact hprefixDataMap.symm.trans (heq_of_eq (by
      simpa [fullData, internalDifferentialTensorMap] using hprefixMap))
  let hS' := congrArg tensorModuleList (compositionSourceListEq d (e.raise 0))
  let hBdy' := congrArg tensorModuleList (compositionBoundaryListEq d (e.raise 0))
  let W := tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
    (internalDifferentialTensorMap e 0)
  have hsourceTransport : HEq (W ≫ eqToHom hS' ≫ eqToHom hBdy')
      sourceData.tensorMap := by
    have hcollapse : W ≫ eqToHom hS' ≫ eqToHom hBdy' =
        W ≫ eqToHom (hS'.trans hBdy') := by
      simp only [eqToHom_trans]
    rw [hcollapse]
    exact (CategoryTheory.comp_eqToHom_heq W (hS'.trans hBdy')).trans
      hsourceCore.symm
  unfold summandCompositionRemainder
  change HEq
    ((W ≫ eqToHom hS' ≫ eqToHom hBdy') ≫
      (adjacentMergeAfter (compositionLeftPrefix d)
        (compositionBoundaryMap d (e.raise 0))).tensorMap ≫
      eqToHom (congrArg tensorModuleList
        (compositionTargetListEq d (e.raise 0))) ≫
      eqToHom (appendBoundaryRightSummandModuleEq d e))
    (sourceData.tensorMap ≫
      (adjacentMergeAfter (compositionLeftPrefix d)
        (compositionBoundaryMap d (e.raise 0) ≫
          eqToHom (compositionBoundaryTarget_raise_zero_eq d e).symm)).tensorMap)
  let mergeRaised := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix (e.raise 0))
    (compositionBoundaryMap d (e.raise 0))).tensorMap
  let mergePost := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e)
    (compositionBoundaryMap d (e.raise 0) ≫
      eqToHom (compositionBoundaryTarget_raise_zero_eq d e).symm)).tensorMap
  let hT' := congrArg tensorModuleList (compositionTargetListEq d (e.raise 0))
  let hR := appendBoundaryRightSummandModuleEq d e
  have hleftTarget : HEq (mergeRaised ≫ eqToHom hT' ≫ eqToHom hR) mergeRaised :=
    (CategoryTheory.comp_eqToHom_heq (mergeRaised ≫ eqToHom hT') hR).trans
      (CategoryTheory.comp_eqToHom_heq mergeRaised hT')
  have hboundaryPost : HEq
      (compositionBoundaryMap d (e.raise 0) ≫
        eqToHom (compositionBoundaryTarget_raise_zero_eq d e).symm)
      (compositionBoundaryMap d (e.raise 0)) :=
    CategoryTheory.comp_eqToHom_heq _ _
  have hmergePost : HEq mergePost mergeRaised := by
    dsimp [mergePost, mergeRaised]
    let hsuffix := compositionRightSuffix_raise_zero_eq e
    let hP := compositionBoundaryTarget_raise_zero_eq d e
    have hdata := adjacentMergeAfter_congr
      (xs := compositionLeftPrefix d) (xs' := compositionLeftPrefix d) rfl
      (M := factorModule d (Fin.last w.length))
      (M' := factorModule d (Fin.last w.length)) rfl
      (N := factorModule (e.raise 0) 0) (N' := factorModule (e.raise 0) 0) rfl
      (P := (dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
          ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1))
      (P' := compositionBoundaryModule d (e.raise 0)) hP
      (ys := compositionRightSuffix e)
      (ys' := compositionRightSuffix (e.raise 0)) hsuffix hboundaryPost
    exact AdjacentMergeData.tensorMap_heq
      (congrArg
        (fun ys ↦ compositionLeftPrefix d ++
          factorModule d (Fin.last w.length) :: factorModule (e.raise 0) 0 :: ys)
        hsuffix)
      (congrArg₂
        (fun P ys ↦ compositionLeftPrefix d ++ P :: ys) hP hsuffix)
      hdata
  have htargetTransport : HEq
      (mergeRaised ≫ eqToHom hT' ≫ eqToHom hR) mergePost :=
    hleftTarget.trans hmergePost.symm
  exact CategoryTheory.heq_comp (congrArg tensorModuleList hsourceList)
    (congrArg tensorModuleList (congrArg
      (fun ys ↦ compositionLeftPrefix d ++
        factorModule d (Fin.last w.length) :: factorModule (e.raise 0) 0 :: ys)
      (compositionRightSuffix_raise_zero_eq e).symm))
    (compositionBoundaryCanonicalTarget_eq d e).symm
    hsourceTransport htargetTransport


theorem compositionRemainder_internalDifferential_boundary_left_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    HEq
      (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
          (internalDifferentialTensorMap d (Fin.last w.length)) ≫
        summandCompositionRemainder (d.raise (Fin.last w.length)) e ≫
        eqToHom (appendBoundaryLeftSummandModuleEq d e))
      ((tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons
          (factorDifferential d (Fin.last w.length) (Fin.last w.length))
          (TensorMapData.cons (𝟙 (factorModule e 0))
            (TensorMapData.identity (compositionRightSuffix e))))).tensorMap ≫
        (adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap (d.raise (Fin.last w.length)) e ≫
            eqToHom (show compositionBoundaryModule
                (d.raise (Fin.last w.length)) e = _ from by
              exact (compositionBoundaryTarget_raise_last_eq d e).symm))).tensorMap) := by
  let q := Fin.last w.length
  let d' := d.raise q
  let Mleft := fun i : Fin w.length ↦ factorModule d i.castSucc
  let Nleft := fun i : Fin w.length ↦ factorModule d' i.castSucc
  let fleft := fun i : Fin w.length ↦ factorDifferential d q i.castSucc
  have hMN : Mleft = Nleft := by
    funext i
    unfold Mleft Nleft d' factorModule
    have hne : (i.castSucc : Fin (w.length + 1)) ≠ q :=
      Fin.castSucc_ne_last i
    simp [DegreeProfile.raise, hne, q]
  have hfleft : ∀ i, HEq (fleft i) (𝟙 (Mleft i)) := by
    intro i
    have hne : q ≠ (i.castSucc : Fin (w.length + 1)) :=
      (Fin.castSucc_ne_last i).symm
    obtain ⟨hL, hmap⟩ := factorDifferential_eqToHom_of_ne_comp d q i.castSucc hne
    dsimp [fleft, Mleft]
    rw [hmap]
    exact test_eqToHom_heq_id hL
  let tailFull := TensorMapData.ofFn (factorModule e) (factorModule e)
    (fun i ↦ 𝟙 (factorModule e i))
  let tailBoundary := TensorMapData.cons (𝟙 (factorModule e 0))
    (TensorMapData.identity (compositionRightSuffix e))
  have htail : HEq tailFull tailBoundary := by
    let Mright := fun i : Fin v.length ↦ factorModule e i.succ
    change HEq
      (TensorMapData.cons (𝟙 (factorModule e 0))
        (TensorMapData.ofFn Mright Mright (fun i ↦ 𝟙 (Mright i))))
      tailBoundary
    apply tensorMapData_cons_heq rfl rfl rfl rfl HEq.rfl
    simpa [Mright, compositionRightSuffix] using
      TensorMapData.ofFn_heq_identity_of_pointwise Mright Mright
        (fun i ↦ 𝟙 (Mright i)) rfl (fun i ↦ HEq.rfl)
  let g := factorDifferential d q q
  let actualData := tensorMapDataPrefixOfFn Mleft Nleft fleft
    (TensorMapData.cons g tailFull)
  let sourceData := tensorMapDataPrefixId (compositionLeftPrefix d)
    (TensorMapData.cons g tailBoundary)
  let fullData := tensorMapDataPrefixOfFn (factorModule d) (factorModule d')
    (factorDifferential d q) tailFull
  have hactualFull : HEq actualData fullData := by
    exact tensorMapDataPrefixOfFn_castSucc_last_heq
      (factorModule d) (factorModule d') (factorDifferential d q) tailFull g HEq.rfl
  have hactualPrefix : HEq actualData
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons g tailFull)) := by
    simpa [actualData, Mleft, Nleft, fleft, compositionLeftPrefix] using
      tensorMapDataPrefixOfFn_heq_prefixId_of_pointwise Mleft Nleft fleft hMN
        hfleft (TensorMapData.cons g tailFull)
  have htailCons : HEq (TensorMapData.cons g tailFull)
      (TensorMapData.cons g tailBoundary) := by
    have hfirst := finFamilyList_factorModule_eq_first_suffix e
    exact tensorMapData_cons_heq rfl rfl
      hfirst hfirst HEq.rfl htail
  have hprefixTail : HEq
      (tensorMapDataPrefixId (compositionLeftPrefix d)
        (TensorMapData.cons g tailFull)) sourceData := by
    have hfirst := finFamilyList_factorModule_eq_first_suffix e
    exact tensorMapDataPrefixId_heq_boundary (compositionLeftPrefix d)
      (congrArg (factorModule d q :: ·) hfirst)
      (congrArg (factorModule d' q :: ·) hfirst) htailCons
  have hsourceData : HEq sourceData fullData :=
    (hactualPrefix.trans hprefixTail).symm.trans hactualFull
  have hsourceList :
      compositionLeftPrefix d ++ factorModule d q ::
          factorModule e 0 :: compositionRightSuffix e =
        finFamilyList (factorModule d) ++ finFamilyList (factorModule e) :=
    ((compositionSourceListEq d e).trans (compositionBoundaryListEq d e)).symm
  have hprefix := compositionLeftPrefix_raise_last_eq d
  have htargetList :
      compositionLeftPrefix d ++ factorModule d' q ::
          factorModule e 0 :: compositionRightSuffix e =
        finFamilyList (factorModule d') ++ finFamilyList (factorModule e) := by
    exact (congrArg
      (fun xs ↦ xs ++ factorModule d' q ::
        factorModule e 0 :: compositionRightSuffix e) hprefix).trans
      (((compositionSourceListEq d' e).trans (compositionBoundaryListEq d' e)).symm)
  have hdataMap : HEq sourceData.tensorMap fullData.tensorMap :=
    tensorMapData_tensorMap_heq hsourceList htargetList hsourceData
  have hfullMap := tensorMapDataPrefixOfFn_id_tensorMap
    (factorModule d) (factorModule d') (factorDifferential d q) (factorModule e)
  have hsourceCore : HEq sourceData.tensorMap
      (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (internalDifferentialTensorMap d q)) := by
    exact hdataMap.trans (heq_of_eq (by
      simpa [fullData, tailFull, d', internalDifferentialTensorMap] using hfullMap))
  let hS' := congrArg tensorModuleList (compositionSourceListEq d' e)
  let hBdy' := congrArg tensorModuleList (compositionBoundaryListEq d' e)
  let W := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
    (internalDifferentialTensorMap d q)
  have hsourceTransport : HEq (W ≫ eqToHom hS' ≫ eqToHom hBdy')
      sourceData.tensorMap := by
    have hcollapse : W ≫ eqToHom hS' ≫ eqToHom hBdy' =
        W ≫ eqToHom (hS'.trans hBdy') := by
      simp only [eqToHom_trans]
    rw [hcollapse]
    exact (CategoryTheory.comp_eqToHom_heq W (hS'.trans hBdy')).trans
      hsourceCore.symm
  unfold summandCompositionRemainder
  change HEq
    ((W ≫ eqToHom hS' ≫ eqToHom hBdy') ≫
      (adjacentMergeAfter (compositionLeftPrefix d')
        (compositionBoundaryMap d' e)).tensorMap ≫
      eqToHom (congrArg tensorModuleList (compositionTargetListEq d' e)) ≫
      eqToHom (appendBoundaryLeftSummandModuleEq d e))
    (sourceData.tensorMap ≫
      (adjacentMergeAfter (compositionLeftPrefix d)
        (compositionBoundaryMap d' e ≫
          eqToHom (compositionBoundaryTarget_raise_last_eq d e).symm)).tensorMap)
  let mergeRaised := (adjacentMergeAfter (compositionLeftPrefix d')
    (ys := compositionRightSuffix e) (compositionBoundaryMap d' e)).tensorMap
  let mergePost := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e)
    (compositionBoundaryMap d' e ≫
      eqToHom (compositionBoundaryTarget_raise_last_eq d e).symm)).tensorMap
  let hT' := congrArg tensorModuleList (compositionTargetListEq d' e)
  let hL := appendBoundaryLeftSummandModuleEq d e
  have hleftTarget : HEq (mergeRaised ≫ eqToHom hT' ≫ eqToHom hL) mergeRaised :=
    (CategoryTheory.comp_eqToHom_heq (mergeRaised ≫ eqToHom hT') hL).trans
      (CategoryTheory.comp_eqToHom_heq mergeRaised hT')
  have hboundaryPost : HEq
      (compositionBoundaryMap d' e ≫
        eqToHom (compositionBoundaryTarget_raise_last_eq d e).symm)
      (compositionBoundaryMap d' e) :=
    CategoryTheory.comp_eqToHom_heq _ _
  have hmergePost : HEq mergePost mergeRaised := by
    dsimp [mergePost, mergeRaised]
    let hP := compositionBoundaryTarget_raise_last_eq d e
    have hdata := adjacentMergeAfter_congr
      (xs := compositionLeftPrefix d) (xs' := compositionLeftPrefix d') hprefix
      (M := factorModule d' q) (M' := factorModule d' q) rfl
      (N := factorModule e 0) (N' := factorModule e 0) rfl
      (P := (dgHomZModuleCochainComplex
        (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
          ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1))
      (P' := compositionBoundaryModule d' e) hP
      (ys := compositionRightSuffix e) (ys' := compositionRightSuffix e) rfl
      hboundaryPost
    exact AdjacentMergeData.tensorMap_heq
      (congrArg
        (fun xs ↦ xs ++ factorModule d' q :: factorModule e 0 ::
          compositionRightSuffix e) hprefix)
      (congrArg₂
        (fun xs P ↦ xs ++ P :: compositionRightSuffix e) hprefix hP)
      hdata
  have htargetTransport : HEq
      (mergeRaised ≫ eqToHom hT' ≫ eqToHom hL) mergePost :=
    hleftTarget.trans hmergePost.symm
  exact CategoryTheory.heq_comp (congrArg tensorModuleList hsourceList.symm)
    (congrArg tensorModuleList (congrArg
      (fun xs ↦ xs ++ factorModule d' q :: factorModule e 0 ::
        compositionRightSuffix e) hprefix.symm))
    (compositionBoundaryCanonicalTarget_eq d e).symm
    hsourceTransport htargetTransport

theorem summandCompositionRemainder_internalDifferential_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    summandCompositionRemainder d e ≫
        internalDifferentialTensorMap (d.append e) (appendBoundaryArrowIndex w v) =
      (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
          (internalDifferentialTensorMap e 0) ≫
        summandCompositionRemainder d (e.raise 0) ≫
        eqToHom (appendBoundaryRightSummandModuleEq d e)) +
      (e.arrowDegree 0).negOnePow •
        (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
            (internalDifferentialTensorMap d (Fin.last w.length)) ≫
          summandCompositionRemainder (d.raise (Fin.last w.length)) e ≫
          eqToHom (appendBoundaryLeftSummandModuleEq d e)) := by
  let P' := (dgHomZModuleCochainComplex
    (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
      ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)
  let g := (dgHomZModuleCochainComplex
    (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).d
      (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
      ((d.arrowDegree (Fin.last w.length) + e.arrowDegree 0) + 1)
  let sourceR := (tensorMapDataPrefixId (compositionLeftPrefix d)
    (TensorMapData.cons (𝟙 (factorModule d (Fin.last w.length)))
      (TensorMapData.cons (factorDifferential e 0 0)
        (TensorMapData.identity (compositionRightSuffix e))))).tensorMap
  let sourceL := (tensorMapDataPrefixId (compositionLeftPrefix d)
    (TensorMapData.cons
      (factorDifferential d (Fin.last w.length) (Fin.last w.length))
      (TensorMapData.cons (𝟙 (factorModule e 0))
        (TensorMapData.identity (compositionRightSuffix e))))).tensorMap
  let hRdeg := (compositionBoundaryTarget_raise_zero_eq d e).symm
  let hLdeg := (compositionBoundaryTarget_raise_last_eq d e).symm
  let merge := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap
  let mergeR := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e)
    (compositionBoundaryMap d (e.raise 0) ≫ eqToHom hRdeg)).tensorMap
  let mergeL := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e)
    (compositionBoundaryMap (d.raise (Fin.last w.length)) e ≫
      eqToHom hLdeg)).tensorMap
  let gMap := (tensorMapDataPrefixId (compositionLeftPrefix d)
    (TensorMapData.cons g
      (TensorMapData.identity (compositionRightSuffix e)))).tensorMap
  have hboundary :
      compositionBoundaryMap d e ≫ g =
        (𝟙 (factorModule d (Fin.last w.length)) ⊗ₘ
            factorDifferential e 0 0) ≫
            (compositionBoundaryMap d (e.raise 0) ≫ eqToHom hRdeg) +
          (e.arrowDegree 0).negOnePow •
            ((factorDifferential d (Fin.last w.length) (Fin.last w.length) ⊗ₘ
                𝟙 (factorModule e 0)) ≫
              (compositionBoundaryMap (d.raise (Fin.last w.length)) e ≫
                eqToHom hLdeg)) := by
    simpa [g, hRdeg, hLdeg, compositionBoundaryRightDifferentialPath,
      compositionBoundaryLeftDifferentialPath] using
      compositionBoundaryMap_comp_d d e
  have hhead := AdjacentMergeData.head_tensorMap_leibniz_prefix
    (compositionLeftPrefix d) (compositionRightSuffix e)
    (compositionBoundaryMap d e)
    (compositionBoundaryMap d (e.raise 0) ≫ eqToHom hRdeg)
    (compositionBoundaryMap (d.raise (Fin.last w.length)) e ≫ eqToHom hLdeg)
    (factorDifferential d (Fin.last w.length) (Fin.last w.length))
    (factorDifferential e 0 0) g (e.arrowDegree 0).negOnePow hboundary
  have hcanonical : merge ≫ gMap =
      sourceR ≫ mergeR + (e.arrowDegree 0).negOnePow • (sourceL ≫ mergeL) := by
    dsimp [merge, gMap, sourceR, sourceL, mergeR, mergeL]
    change (adjacentMergeAfter (compositionLeftPrefix d)
        (compositionBoundaryMap d e)).tensorMap ≫
          (tensorMapDataPrefixId (compositionLeftPrefix d)
            (TensorMapData.cons g
              (TensorMapData.identity (compositionRightSuffix e)))).tensorMap =
      _ at hhead
    exact hhead
  let hS := congrArg tensorModuleList (compositionSourceListEq d e)
  let hBdy := congrArg tensorModuleList (compositionBoundaryListEq d e)
  let pre := eqToHom hS ≫ eqToHom hBdy
  let hQ := compositionBoundaryCanonicalTarget_eq d e
  let post := eqToHom hQ
  have hcanonicalWhiskered : pre ≫ merge ≫ gMap ≫ post =
      pre ≫ sourceR ≫ mergeR ≫ post +
        (e.arrowDegree 0).negOnePow •
          (pre ≫ sourceL ≫ mergeL ≫ post) := by
    have hc := congrArg (fun z ↦ pre ≫ z ≫ post) hcanonical
    have hz : pre ≫ ((e.arrowDegree 0).negOnePow •
          (sourceL ≫ mergeL)) ≫ post =
        (e.arrowDegree 0).negOnePow •
          (pre ≫ sourceL ≫ mergeL ≫ post) := by
      rw [Units.smul_def, Units.smul_def]
      simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
    simpa only [Category.assoc, Preadditive.comp_add, Preadditive.add_comp, hz] using hc
  have htarget := compositionTargetInternalDifferential_append_boundary_heq d e
  have htargetPost : HEq
      (eqToHom (congrArg tensorModuleList (compositionTargetListEq d e)) ≫
        internalDifferentialTensorMap (d.append e) (appendBoundaryArrowIndex w v))
      (gMap ≫ post) :=
    htarget.trans (CategoryTheory.comp_eqToHom_heq gMap hQ).symm
  have hlhs :
      summandCompositionRemainder d e ≫
          internalDifferentialTensorMap (d.append e) (appendBoundaryArrowIndex w v) =
        pre ≫ merge ≫ gMap ≫ post := by
    unfold summandCompositionRemainder
    apply eq_of_heq
    simpa only [Category.assoc, pre, merge] using
      CategoryTheory.heq_comp
        (f := pre ≫ merge)
        (g := eqToHom (congrArg tensorModuleList (compositionTargetListEq d e)) ≫
          internalDifferentialTensorMap (d.append e) (appendBoundaryArrowIndex w v))
        (f' := pre ≫ merge) (g' := gMap ≫ post)
        rfl rfl rfl HEq.rfl htargetPost
  have hright := compositionRemainder_internalDifferential_boundary_right_heq d e
  have hleft := compositionRemainder_internalDifferential_boundary_left_heq d e
  have hpost : HEq post (𝟙 _) := test_eqToHom_heq_id hQ
  let hSourceObj := congrArg tensorModuleList
    ((compositionSourceListEq d e).trans (compositionBoundaryListEq d e))
  have hrightCanonical : HEq (pre ≫ sourceR ≫ mergeR ≫ post)
      (sourceR ≫ mergeR) := by
    have hfirst : HEq (pre ≫ sourceR) sourceR := by
      dsimp [pre]
      rw [eqToHom_trans]
      exact CategoryTheory.eqToHom_comp_heq sourceR (hS.trans hBdy)
    have hsecond : HEq ((pre ≫ sourceR) ≫ mergeR)
        (sourceR ≫ mergeR) :=
      CategoryTheory.heq_comp hSourceObj rfl rfl hfirst HEq.rfl
    have hthird := CategoryTheory.heq_comp
      (f := (pre ≫ sourceR) ≫ mergeR) (g := post)
      (f' := sourceR ≫ mergeR) (g' := 𝟙 _)
      hSourceObj rfl hQ.symm hsecond hpost
    simpa only [Category.assoc, Category.comp_id] using hthird
  have hleftCanonical : HEq (pre ≫ sourceL ≫ mergeL ≫ post)
      (sourceL ≫ mergeL) := by
    have hfirst : HEq (pre ≫ sourceL) sourceL := by
      dsimp [pre]
      rw [eqToHom_trans]
      exact CategoryTheory.eqToHom_comp_heq sourceL (hS.trans hBdy)
    have hsecond : HEq ((pre ≫ sourceL) ≫ mergeL)
        (sourceL ≫ mergeL) :=
      CategoryTheory.heq_comp hSourceObj rfl rfl hfirst HEq.rfl
    have hthird := CategoryTheory.heq_comp
      (f := (pre ≫ sourceL) ≫ mergeL) (g := post)
      (f' := sourceL ≫ mergeL) (g' := 𝟙 _)
      hSourceObj rfl hQ.symm hsecond hpost
    simpa only [Category.assoc, Category.comp_id] using hthird
  have hrightEq :
      tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
            (internalDifferentialTensorMap e 0) ≫
          summandCompositionRemainder d (e.raise 0) ≫
          eqToHom (appendBoundaryRightSummandModuleEq d e) =
        pre ≫ sourceR ≫ mergeR ≫ post := by
    exact eq_of_heq (hright.trans hrightCanonical.symm)
  have hleftEq :
      tensorModuleListWhiskerRight (finFamilyList (factorModule e))
            (internalDifferentialTensorMap d (Fin.last w.length)) ≫
          summandCompositionRemainder (d.raise (Fin.last w.length)) e ≫
          eqToHom (appendBoundaryLeftSummandModuleEq d e) =
        pre ≫ sourceL ≫ mergeL ≫ post := by
    exact eq_of_heq (hleft.trans hleftCanonical.symm)
  rw [hlhs, hrightEq, hleftEq]
  exact hcanonicalWhiskered

theorem summandCompositionMap_internalDifferential_append_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
  summandCompositionMap d e ≫
      internalDifferentialTensorMap (d.append e)
        (appendBoundaryArrowIndex w v) =
    ((𝟙 (summandModule d) ⊗ₘ internalDifferentialTensorMap e 0) ≫
        summandCompositionMap d (e.raise 0) ≫
        eqToHom (appendBoundaryRightSummandModuleEq d e)) +
      (e.arrowDegree 0).negOnePow •
        ((internalDifferentialTensorMap d (Fin.last w.length) ⊗ₘ
              𝟙 (summandModule e)) ≫
          summandCompositionMap (d.raise (Fin.last w.length)) e ≫
          eqToHom (appendBoundaryLeftSummandModuleEq d e)) := by
  rw [summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized]
  rw [normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder]
  dsimp only [summandModule]
  simp only [Category.assoc]
  rw [tensorModuleListAppendIso_whiskerLeft_assoc,
    tensorModuleListAppendIso_whiskerRight_assoc]
  rw [summandCompositionRemainder_internalDifferential_boundary]
  rw [Preadditive.comp_add]
  congr 1


def rawContractionTargetListEq_right_succ_core
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    finFamilyList (recursiveMergedFactor (factorModule d) i
        (rawContractionFactor d i)) =
      finFamilyList (factorModule (d.contract i)) :=
  (congrArg finFamilyList (test_rawContractionTarget_eq d i)).trans
    (contractedFactorsOldIndex_eq d i)

theorem tensorModuleListWhiskerLeft_heq_right_succ_core
    {Ms Ns Ms' Ns' : List (ModuleCat.{0} ℤ)}
    (Ps : List (ModuleCat.{0} ℤ)) (hMs : Ms = Ms') (hNs : Ns = Ns')
    {f : tensorModuleList Ms ⟶ tensorModuleList Ns}
    {f' : tensorModuleList Ms' ⟶ tensorModuleList Ns'} (h : HEq f f') :
    HEq (tensorModuleListWhiskerLeft Ps f)
      (tensorModuleListWhiskerLeft Ps f') := by
  subst Ms'
  subst Ns'
  have hff : f = f' := eq_of_heq h
  subst f'
  rfl

theorem adjacentMergeData_prefix_heq_right_succ_core
    {source target source' target' : List (ModuleCat.{0} ℤ)}
    {f : AdjacentMergeData source target}
    {g : AdjacentMergeData source' target'}
    (hsource : source = source') (htarget : target = target')
    (h : HEq f g) (Ps : List (ModuleCat.{0} ℤ)) :
    HEq (f.prefix Ps) (g.prefix Ps) := by
  induction Ps with
  | nil => exact h
  | cons P Ps ih =>
      exact adjacentMergeData_tail_heq rfl
        (congrArg (Ps ++ ·) hsource)
        (congrArg (Ps ++ ·) htarget) ih

def recursiveMergePrefix_right_succ_core : {k : ℕ} →
    (Fin (k + 2) → ModuleCat.{0} ℤ) → Fin (k + 1) →
      List (ModuleCat.{0} ℤ)
  | 0, _, _ => []
  | k + 1, M, i => Fin.cases []
      (fun q ↦ M 0 :: recursiveMergePrefix_right_succ_core
        (fun r : Fin (k + 2) ↦ M r.succ) q) i


def recursiveMergeSuffix_right_succ_core : {k : ℕ} →
    (Fin (k + 2) → ModuleCat.{0} ℤ) → Fin (k + 1) →
      List (ModuleCat.{0} ℤ)
  | 0, _, _ => []
  | k + 1, M, i => Fin.cases
      (finFamilyList (fun q : Fin (k + 1) ↦ M q.succ.succ))
      (fun q ↦ recursiveMergeSuffix_right_succ_core
        (fun r : Fin (k + 2) ↦ M r.succ) q) i

theorem finFamilyList_recursiveMerge_source_right_succ_core :
    {k : ℕ} → (M : Fin (k + 2) → ModuleCat.{0} ℤ) →
    (i : Fin (k + 1)) →
    finFamilyList M =
      recursiveMergePrefix_right_succ_core M i ++
        M i.castSucc :: M i.succ :: recursiveMergeSuffix_right_succ_core M i := by
  intro k
  induction k with
  | zero =>
      intro M i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ k ih =>
      intro M i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change M 0 :: finFamilyList (fun r : Fin (k + 2) ↦ M r.succ) =
            M 0 :: (recursiveMergePrefix_right_succ_core
              (fun r : Fin (k + 2) ↦ M r.succ) i ++
                M i.castSucc.succ :: M i.succ.succ ::
                  recursiveMergeSuffix_right_succ_core
                    (fun r : Fin (k + 2) ↦ M r.succ) i)
          exact congrArg (List.cons (M 0))
            (ih (fun r : Fin (k + 2) ↦ M r.succ) i)

theorem finFamilyList_recursiveMerge_target_right_succ_core :
    {k : ℕ} → (M : Fin (k + 2) → ModuleCat.{0} ℤ) →
    (i : Fin (k + 1)) → (P : ModuleCat.{0} ℤ) →
    finFamilyList (recursiveMergedFactor M i P) =
      recursiveMergePrefix_right_succ_core M i ++
        P :: recursiveMergeSuffix_right_succ_core M i := by
  intro k
  induction k with
  | zero =>
      intro M i P
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ k ih =>
      intro M i P
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change M 0 :: finFamilyList
              (recursiveMergedFactor (fun r : Fin (k + 2) ↦ M r.succ) i P) =
            M 0 :: (recursiveMergePrefix_right_succ_core
              (fun r : Fin (k + 2) ↦ M r.succ) i ++
                P :: recursiveMergeSuffix_right_succ_core
                  (fun r : Fin (k + 2) ↦ M r.succ) i)
          exact congrArg (List.cons (M 0))
            (ih (fun r : Fin (k + 2) ↦ M r.succ) i P)

theorem recursiveAdjacentMergeDataOfFn_eq_after_right_succ_core :
    {k : ℕ} → (M : Fin (k + 2) → ModuleCat.{0} ℤ) →
    (i : Fin (k + 1)) → (P : ModuleCat.{0} ℤ) →
    (f : M i.castSucc ⊗ M i.succ ⟶ P) →
    HEq (recursiveAdjacentMergeDataOfFn M i P f)
      (adjacentMergeAfter (recursiveMergePrefix_right_succ_core M i)
        (ys := recursiveMergeSuffix_right_succ_core M i) f) := by
  intro k
  induction k with
  | zero =>
      intro M i P f
      have hi : i = 0 := Fin.eq_zero i
      subst i
      change HEq (AdjacentMergeData.head f) (AdjacentMergeData.head f)
      exact HEq.rfl
  | succ k ih =>
      intro M i P f
      cases i using Fin.cases with
      | zero =>
          change HEq (AdjacentMergeData.head f) (AdjacentMergeData.head f)
          exact HEq.rfl
      | succ i =>
          apply HEq.trans (recursiveAdjacentMergeDataOfFn_succ_heq M i P f)
          dsimp only [recursiveMergePrefix_right_succ_core,
            recursiveMergeSuffix_right_succ_core, adjacentMergeAfter]
          exact adjacentMergeData_tail_heq rfl
            (finFamilyList_recursiveMerge_source_right_succ_core
              (fun r : Fin (k + 2) ↦ M r.succ) i)
            (finFamilyList_recursiveMerge_target_right_succ_core
              (fun r : Fin (k + 2) ↦ M r.succ) i P)
            (ih (fun r : Fin (k + 2) ↦ M r.succ) i P (by simpa using f))


theorem recursiveMergePrefix_eq_take_right_succ_core :
    {k : ℕ} → (M : Fin (k + 2) → ModuleCat.{0} ℤ) →
    (i : Fin (k + 1)) →
    recursiveMergePrefix_right_succ_core M i =
      (finFamilyList M).take i.val := by
  intro k
  induction k with
  | zero =>
      intro M i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ k ih =>
      intro M i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change M 0 :: recursiveMergePrefix_right_succ_core
              (fun r : Fin (k + 2) ↦ M r.succ) i =
            M 0 :: (finFamilyList (fun r : Fin (k + 2) ↦ M r.succ)).take i.val
          exact congrArg (List.cons (M 0))
            (ih (fun r : Fin (k + 2) ↦ M r.succ) i)

theorem length_recursiveMergePrefix_right_succ_core :
    {k : ℕ} → (M : Fin (k + 2) → ModuleCat.{0} ℤ) →
    (i : Fin (k + 1)) →
    (recursiveMergePrefix_right_succ_core M i).length = i.val := by
  intro k
  induction k with
  | zero =>
      intro M i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ k ih =>
      intro M i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change (M 0 :: recursiveMergePrefix_right_succ_core
            (fun r : Fin (k + 2) ↦ M r.succ) i).length = i.val + 1
          simp only [List.length_cons, ih]

theorem recursiveMergeSuffix_eq_drop_right_succ_core :
    {k : ℕ} → (M : Fin (k + 2) → ModuleCat.{0} ℤ) →
    (i : Fin (k + 1)) →
    recursiveMergeSuffix_right_succ_core M i =
      (finFamilyList M).drop (i.val + 2) := by
  intro k
  induction k with
  | zero =>
      intro M i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      rfl
  | succ k ih =>
      intro M i
      cases i using Fin.cases with
      | zero => rfl
      | succ i =>
          change recursiveMergeSuffix_right_succ_core
              (fun r : Fin (k + 2) ↦ M r.succ) i =
            (finFamilyList (fun r : Fin (k + 2) ↦ M r.succ)).drop (i.val + 2)
          exact ih (fun r : Fin (k + 2) ↦ M r.succ) i

theorem compositionRightSuffix_split_right_succ_core
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    compositionRightSuffix e =
      recursiveMergePrefix_right_succ_core
          (fun r : Fin (k + 2) ↦ factorModule e r.succ) j ++
        factorModule e j.succ.castSucc :: factorModule e j.succ.succ ::
          recursiveMergeSuffix_right_succ_core
            (fun r : Fin (k + 2) ↦ factorModule e r.succ) j := by
  simpa only [compositionRightSuffix, Fin.castSucc_succ] using
    (finFamilyList_recursiveMerge_source_right_succ_core
      (fun r : Fin (k + 2) ↦ factorModule e r.succ) j)


theorem recursiveMergePrefix_append_right_succ_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    recursiveMergePrefix_right_succ_core (factorModule (d.append e))
        (⟨w.length + j.succ.val, by omega⟩ : Fin (w.length + (k + 1) + 1)) =
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        recursiveMergePrefix_right_succ_core
          (fun r : Fin (k + 2) ↦ factorModule e r.succ) j := by
  rw (config := { transparency := .all }) [recursiveMergePrefix_eq_take_right_succ_core,
    finFamilyList_factorModule_append_boundary,
    compositionRightSuffix_split_right_succ_core e j]
  let L := compositionLeftPrefix d ++ compositionBoundaryModule d e ::
    recursiveMergePrefix_right_succ_core
      (fun r : Fin (k + 2) ↦ factorModule e r.succ) j
  have hL : L.length = w.length + (j.val + 1) := by
    simp [L, compositionLeftPrefix, finFamilyList_eq_ofFn,
      length_recursiveMergePrefix_right_succ_core]
  have hsource :
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          (recursiveMergePrefix_right_succ_core
              (fun r : Fin (k + 2) ↦ factorModule e r.succ) j ++
            factorModule e j.succ.castSucc :: factorModule e j.succ.succ ::
              recursiveMergeSuffix_right_succ_core
                (fun r : Fin (k + 2) ↦ factorModule e r.succ) j) =
        L ++ factorModule e j.succ.castSucc :: factorModule e j.succ.succ ::
          recursiveMergeSuffix_right_succ_core
            (fun r : Fin (k + 2) ↦ factorModule e r.succ) j := by
    simp [L, List.append_assoc]
  rw [hsource]
  change List.take (w.length + (j.val + 1)) _ = L
  rw [← hL]
  exact List.take_left

theorem recursiveMergeSuffix_append_right_succ_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    recursiveMergeSuffix_right_succ_core (factorModule (d.append e))
        (⟨w.length + j.succ.val, by omega⟩ : Fin (w.length + (k + 1) + 1)) =
      recursiveMergeSuffix_right_succ_core
        (fun r : Fin (k + 2) ↦ factorModule e r.succ) j := by
  rw (config := { transparency := .all }) [recursiveMergeSuffix_eq_drop_right_succ_core,
    finFamilyList_factorModule_append_boundary,
    compositionRightSuffix_split_right_succ_core e j]
  let L := compositionLeftPrefix d ++ compositionBoundaryModule d e ::
    recursiveMergePrefix_right_succ_core
      (fun r : Fin (k + 2) ↦ factorModule e r.succ) j
  have hL : L.length = w.length + (j.val + 1) := by
    simp [L, compositionLeftPrefix, finFamilyList_eq_ofFn,
      length_recursiveMergePrefix_right_succ_core]
  have hsource :
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          (recursiveMergePrefix_right_succ_core
              (fun r : Fin (k + 2) ↦ factorModule e r.succ) j ++
            factorModule e j.succ.castSucc :: factorModule e j.succ.succ ::
              recursiveMergeSuffix_right_succ_core
                (fun r : Fin (k + 2) ↦ factorModule e r.succ) j) =
        L ++ factorModule e j.succ.castSucc :: factorModule e j.succ.succ ::
          recursiveMergeSuffix_right_succ_core
            (fun r : Fin (k + 2) ↦ factorModule e r.succ) j := by
    simp [L, List.append_assoc]
  rw [hsource]
  change List.drop (w.length + (j.val + 1) + 2) _ = _
  rw [← hL, ← List.drop_drop, List.drop_left]
  rfl

theorem recursiveMergePrefix_append_right_succ_at_index_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    recursiveMergePrefix_right_succ_core (factorModule (d.append e))
        (appendRightContractionIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ) =
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        recursiveMergePrefix_right_succ_core
          (fun r : Fin (k + 2) ↦ factorModule e r.succ) j := by
  change recursiveMergePrefix_right_succ_core (factorModule (d.append e))
      (⟨w.length + j.succ.val, by omega⟩ : Fin (w.length + (k + 1) + 1)) = _
  exact recursiveMergePrefix_append_right_succ_core d e j

theorem recursiveMergeSuffix_append_right_succ_at_index_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    recursiveMergeSuffix_right_succ_core (factorModule (d.append e))
        (appendRightContractionIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ) =
      recursiveMergeSuffix_right_succ_core
        (fun r : Fin (k + 2) ↦ factorModule e r.succ) j := by
  change recursiveMergeSuffix_right_succ_core (factorModule (d.append e))
      (⟨w.length + j.succ.val, by omega⟩ : Fin (w.length + (k + 1) + 1)) = _
  exact recursiveMergeSuffix_append_right_succ_core d e j


theorem rawContractionFactor_append_right_succ_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    rawContractionFactor (d.append e) (appendRightContractionIndex j.succ) =
      rawContractionFactor e j.succ := by
  have hleft :
      (appendRightContractionIndex (w := w) j.succ).castSucc =
        appendRightArrowIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.castSucc := by
    apply Fin.ext
    change w.length + (j.val + 1) = w.length + 1 + j.val
    omega
  have hright :
      (appendRightContractionIndex (w := w) j.succ).succ =
        appendRightArrowIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ := by
    apply Fin.ext
    change w.length + (j.val + 1) + 1 = w.length + 1 + (j.val + 1)
    omega
  unfold rawContractionFactor
  change (dgHomZModuleCochainComplex
      ((w.append _).arrowSource
        (appendRightContractionIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ).castSucc)
      ((w.append _).arrowTarget
        (appendRightContractionIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ).succ)).X
      (appendArrowDegree d e
          (appendRightContractionIndex (w := w)
            (v := ({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord Y Z)) j.succ).castSucc +
        appendArrowDegree d e
          (appendRightContractionIndex (w := w)
            (v := ({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord Y Z)) j.succ).succ) = _
  rw [hleft, hright, arrowSource_append_right, arrowTarget_append_right,
    appendArrowDegree_right, appendArrowDegree_right]
  congr 2

theorem adjacentFactorComposition_append_right_succ_heq_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    HEq (adjacentFactorComposition (d.append e)
        (appendRightContractionIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ))
      (adjacentFactorComposition e j.succ) := by
  have hleft :
      (appendRightContractionIndex (w := w) j.succ).castSucc =
        appendRightArrowIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.castSucc := by
    apply Fin.ext
    change w.length + (j.val + 1) = w.length + 1 + j.val
    omega
  have hright :
      (appendRightContractionIndex (w := w) j.succ).succ =
        appendRightArrowIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ := by
    apply Fin.ext
    change w.length + (j.val + 1) + 1 = w.length + 1 + (j.val + 1)
    omega
  have hindex : j.castSucc.succ = j.succ.castSucc := by
    apply Fin.ext
    rfl
  unfold adjacentFactorComposition
  simp only [factorModule]
  apply dgCochainCompTensorOfEq_heq
  · rw [hleft, arrowSource_append_right]
    exact congrArg _ hindex
  · rw [hleft, arrowTarget_append_right]
    exact congrArg _ hindex
  · rw [hright, arrowSource_append_right]
  · rw [hright, arrowTarget_append_right]
  · rw [hleft]
    change appendArrowDegree d e (appendRightArrowIndex (w := w) j.castSucc) = _
    simpa only [hindex] using appendArrowDegree_right d e j.castSucc
  · rw [hright]
    change appendArrowDegree d e (appendRightArrowIndex (w := w) j.succ) = _
    exact appendArrowDegree_right d e j.succ
  · rw [hleft, hright]
    change appendArrowDegree d e (appendRightArrowIndex (w := w) j.castSucc) +
      appendArrowDegree d e (appendRightArrowIndex (w := w) j.succ) = _
    exact congrArg₂ (· + ·) (by
      simpa only [hindex] using appendArrowDegree_right d e j.castSucc)
      (appendArrowDegree_right d e j.succ)

theorem rawContractionAdjacentMergeData_append_right_succ_heq_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    let M := fun r : Fin (k + 2) ↦ factorModule e r.succ
    let ms := recursiveMergePrefix_right_succ_core M j
    let zs := recursiveMergeSuffix_right_succ_core M j
    HEq (rawContractionAdjacentMergeData (d.append e)
        (appendRightContractionIndex j.succ))
      (((@AdjacentMergeData.tail (compositionBoundaryModule d e)
        (ms ++ factorModule e j.succ.castSucc ::
          factorModule e j.succ.succ :: zs)
        (ms ++ rawContractionFactor e j.succ :: zs)
        (adjacentMergeAfter ms (ys := zs)
          (adjacentFactorComposition e j.succ))).prefix
            (compositionLeftPrefix d))) := by
  dsimp only
  unfold rawContractionAdjacentMergeData
  apply HEq.trans
    (recursiveAdjacentMergeDataOfFn_eq_after_right_succ_core
      (k := w.length + k + 1)
      (factorModule (d.append e))
      (appendRightContractionIndex (w := w)
        (v := ({ length := k + 2, intermediate := intermediate } :
          DrinfeldWord Y Z)) j.succ)
      (rawContractionFactor (d.append e)
        (appendRightContractionIndex j.succ))
      (adjacentFactorComposition (d.append e)
        (appendRightContractionIndex j.succ)))
  have hidxLeft :
      (appendRightContractionIndex (w := w) j.succ).castSucc =
        appendRightArrowIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.castSucc := by
    apply Fin.ext
    change w.length + (j.val + 1) = w.length + 1 + j.val
    omega
  have hidxRight :
      (appendRightContractionIndex (w := w) j.succ).succ =
        appendRightArrowIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ := by
    apply Fin.ext
    change w.length + (j.val + 1) + 1 = w.length + 1 + (j.val + 1)
    omega
  have hfactorLeft :
      factorModule (d.append e)
          (appendRightContractionIndex (w := w) j.succ).castSucc =
        factorModule e j.succ.castSucc := by
    rw [hidxLeft, factorModule_append_right]
    congr 1
  have hfactorRight :
      factorModule (d.append e)
          (appendRightContractionIndex (w := w) j.succ).succ =
        factorModule e j.succ.succ := by
    rw [hidxRight, factorModule_append_right]
  apply HEq.trans (adjacentMergeAfter_congr
    (f := adjacentFactorComposition (d.append e)
      (appendRightContractionIndex j.succ))
    (g := adjacentFactorComposition e j.succ)
    (recursiveMergePrefix_append_right_succ_at_index_core d e j)
    hfactorLeft hfactorRight
    (rawContractionFactor_append_right_succ_core d e j)
    (recursiveMergeSuffix_append_right_succ_at_index_core d e j)
    (adjacentFactorComposition_append_right_succ_heq_core d e j))
  apply HEq.trans (adjacentMergeAfter_prefix_heq
    (compositionBoundaryModule d e ::
      recursiveMergePrefix_right_succ_core
        (fun r : Fin (k + 2) ↦ factorModule e r.succ) j)
    (compositionLeftPrefix d) (adjacentFactorComposition e j.succ)).symm
  exact HEq.rfl

theorem rawContractionAdjacentMergeData_right_succ_heq_core
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    let M := fun r : Fin (k + 2) ↦ factorModule e r.succ
    let ms := recursiveMergePrefix_right_succ_core M j
    let zs := recursiveMergeSuffix_right_succ_core M j
    HEq (rawContractionAdjacentMergeData e j.succ)
      (@AdjacentMergeData.tail (factorModule e 0)
        (ms ++ factorModule e j.succ.castSucc ::
          factorModule e j.succ.succ :: zs)
        (ms ++ rawContractionFactor e j.succ :: zs)
        (adjacentMergeAfter ms (ys := zs)
          (adjacentFactorComposition e j.succ))) := by
  dsimp only
  unfold rawContractionAdjacentMergeData
  apply HEq.trans
    (recursiveAdjacentMergeDataOfFn_eq_after_right_succ_core
      (factorModule e) j.succ (rawContractionFactor e j.succ)
        (adjacentFactorComposition e j.succ))
  exact HEq.rfl


theorem compositionBoundaryMap_contract_right_succ_heq_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    HEq (compositionBoundaryMap d (e.contract j.succ))
      (compositionBoundaryMap d e) := by
  let v : DrinfeldWord Y Z :=
    { length := k + 2, intermediate := intermediate }
  have hindex : eraseFactorIndex v j.succ 0 = 0 := rfl
  have hbefore : eraseFactorIndex v j.succ 0 < j.succ := by
    change 0 < j.val + 1
    omega
  have hcast : (eraseFactorIndex v j.succ 0).castSucc = 0 := by
    rw [hindex]
    rfl
  have hdegree : (e.contract j.succ).arrowDegree 0 = e.arrowDegree 0 :=
    (contract_arrowDegree_of_before e j.succ 0 hbefore).trans
      (congrArg e.arrowDegree hcast)
  unfold compositionBoundaryMap
  apply dgCochainCompTensorOfEq_heq
  · rfl
  · rfl
  · exact eraseIntermediate_arrowSource_of_before v j.succ 0 hbefore
  · exact eraseIntermediate_arrowTarget_of_before v j.succ 0 hbefore
  · rfl
  · exact hdegree
  · exact congrArg (d.arrowDegree (Fin.last w.length) + ·) (by
      exact hdegree)

theorem compositionBoundaryModule_contract_right_succ_core
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    compositionBoundaryModule d (e.contract j.succ) =
      compositionBoundaryModule d e := by
  let v : DrinfeldWord Y Z :=
    { length := k + 2, intermediate := intermediate }
  have hindex : eraseFactorIndex v j.succ 0 = 0 := rfl
  have hbefore : eraseFactorIndex v j.succ 0 < j.succ := by
    change 0 < j.val + 1
    omega
  have hcast : (eraseFactorIndex v j.succ 0).castSucc = 0 := by
    rw [hindex]
    rfl
  have hdegree : (e.contract j.succ).arrowDegree 0 = e.arrowDegree 0 :=
    (contract_arrowDegree_of_before e j.succ 0 hbefore).trans
      (congrArg e.arrowDegree hcast)
  unfold compositionBoundaryModule
  rw [eraseIntermediate_arrowTarget_of_before v j.succ 0 hbefore, hcast,
    hdegree]

theorem summandCompositionRemainder_contraction_append_right_succ_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
  HEq
    (summandCompositionRemainder d e ≫
      contractionTensorMap (d.append e) (appendRightContractionIndex j.succ))
    (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
        (contractionTensorMap e j.succ) ≫
      summandCompositionRemainder d (e.contract j.succ)) := by
  let R := summandCompositionRemainder d e
  let C := contractionTensorMap (d.append e) (appendRightContractionIndex j.succ)
  let C₀ := (rawContractionAdjacentMergeData (d.append e)
    (appendRightContractionIndex j.succ)).tensorMap
  let W := tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
    (contractionTensorMap e j.succ)
  let W₀ := tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
    (rawContractionAdjacentMergeData e j.succ).tensorMap
  let R' := summandCompositionRemainder d (e.contract j.succ)
  let hCList := rawContractionTargetListEq_right_succ_core
    (d.append e) (appendRightContractionIndex j.succ)
  let hWList := rawContractionTargetListEq_right_succ_core e j.succ
  let hWAppend := congrArg (finFamilyList (factorModule d) ++ ·) hWList
  let T := eqToHom (congrArg tensorModuleList hWAppend)
  have hC : HEq C C₀ := test_contractionTensorMap_raw_heq _ _
  have hW : HEq W W₀ := tensorModuleListWhiskerLeft_heq_right_succ_core
    _ rfl hWList.symm (test_contractionTensorMap_raw_heq e j.succ)
  have hleft : HEq (R ≫ C) (R ≫ C₀) :=
    CategoryTheory.heq_comp rfl rfl
      (congrArg tensorModuleList hCList).symm HEq.rfl hC
  have hright : HEq (W ≫ R') (W₀ ≫ T ≫ R') := by
    apply CategoryTheory.heq_comp rfl
      (congrArg tensorModuleList hWAppend).symm rfl hW
    exact (CategoryTheory.eqToHom_comp_heq R'
      (congrArg tensorModuleList hWAppend)).symm
  refine hleft.trans ?_ |>.trans hright.symm
  dsimp [R, C₀, W₀, T, R', summandCompositionRemainder]
  rw [← AdjacentMergeData.prefix_tensorMap]
  let M := fun r : Fin (k + 2) ↦ factorModule e r.succ
  let ms := recursiveMergePrefix_right_succ_core M j
  let zs := recursiveMergeSuffix_right_succ_core M j
  let F₁ := (@AdjacentMergeData.head
    (factorModule d (Fin.last w.length)) (factorModule e 0)
    (compositionBoundaryModule d e)
    (ms ++ factorModule e j.succ.castSucc ::
      factorModule e j.succ.succ :: zs)
    (compositionBoundaryMap d e)).prefix (compositionLeftPrefix d)
  let G₁ := (@AdjacentMergeData.tail (compositionBoundaryModule d e)
    (ms ++ factorModule e j.succ.castSucc ::
      factorModule e j.succ.succ :: zs)
    (ms ++ rawContractionFactor e j.succ :: zs)
    (adjacentMergeAfter ms (ys := zs)
      (adjacentFactorComposition e j.succ))).prefix (compositionLeftPrefix d)
  let F₂ := (@AdjacentMergeData.tail (factorModule d (Fin.last w.length))
    (factorModule e 0 :: ms ++ factorModule e j.succ.castSucc ::
      factorModule e j.succ.succ :: zs)
    (factorModule e 0 :: ms ++ rawContractionFactor e j.succ :: zs)
    (@AdjacentMergeData.tail (factorModule e 0)
      (ms ++ factorModule e j.succ.castSucc ::
        factorModule e j.succ.succ :: zs)
      (ms ++ rawContractionFactor e j.succ :: zs)
      (adjacentMergeAfter ms (ys := zs)
        (adjacentFactorComposition e j.succ)))).prefix
          (compositionLeftPrefix d)
  let G₂ := (@AdjacentMergeData.head
    (factorModule d (Fin.last w.length)) (factorModule e 0)
    (compositionBoundaryModule d e)
    (ms ++ rawContractionFactor e j.succ :: zs)
    (compositionBoundaryMap d e)).prefix (compositionLeftPrefix d)
  have hmiddle : HEq (F₁.tensorMap ≫ G₁.tensorMap)
      (F₂.tensorMap ≫ G₂.tensorMap) := by
    exact (adjacentMergeAfter_pair_head_tail (compositionLeftPrefix d) ms
      (zs := zs) (compositionBoundaryMap d e)
      (adjacentFactorComposition e j.succ)).tensorMap_heq
  have hF₁Data : HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e) (compositionBoundaryMap d e)) F₁ := by
    apply HEq.trans (adjacentMergeAfter_congr
      (f := compositionBoundaryMap d e) (g := compositionBoundaryMap d e)
      rfl rfl rfl rfl (compositionRightSuffix_split_right_succ_core e j)
      HEq.rfl)
    exact heq_of_eq (adjacentMergeAfter_eq_prefix_head
      (compositionLeftPrefix d) (compositionBoundaryMap d e))
  have hG₁Data : HEq
      (rawContractionAdjacentMergeData (d.append e)
        (appendRightContractionIndex j.succ)) G₁ := by
    exact rawContractionAdjacentMergeData_append_right_succ_heq_core d e j
  have hrawE := rawContractionAdjacentMergeData_right_succ_heq_core e j
  have hF₂Data : HEq
      ((rawContractionAdjacentMergeData e j.succ).prefix
        (finFamilyList (factorModule d))) F₂ := by
    have hs : finFamilyList (factorModule e) =
        factorModule e 0 ::
          (ms ++ factorModule e j.succ.castSucc ::
            factorModule e j.succ.succ :: zs) := by
      rw [finFamilyList_factorModule_eq_first_suffix,
        compositionRightSuffix_split_right_succ_core e j]
    have ht : finFamilyList (recursiveMergedFactor (factorModule e) j.succ
          (rawContractionFactor e j.succ)) =
        factorModule e 0 ::
          (ms ++ rawContractionFactor e j.succ :: zs) := by
      change factorModule e 0 ::
          finFamilyList (recursiveMergedFactor M j
            (rawContractionFactor e j.succ)) = _
      exact congrArg (List.cons (factorModule e 0))
        (finFamilyList_recursiveMerge_target_right_succ_core M j
          (rawContractionFactor e j.succ))
    have hp := adjacentMergeData_prefix_heq_right_succ_core
      hs ht hrawE
      (finFamilyList (factorModule d))
    apply HEq.trans hp
    rw [finFamilyList_factorModule_eq_prefix_last]
    exact (AdjacentMergeData.prefix_prefix_heq
      (@AdjacentMergeData.tail (factorModule e 0)
        (ms ++ factorModule e j.succ.castSucc ::
          factorModule e j.succ.succ :: zs)
        (ms ++ rawContractionFactor e j.succ :: zs)
        (adjacentMergeAfter ms (ys := zs)
          (adjacentFactorComposition e j.succ)))
      [factorModule d (Fin.last w.length)] (compositionLeftPrefix d)).symm
  have hrawTarget :
      finFamilyList (recursiveMergedFactor (factorModule e) j.succ
        (rawContractionFactor e j.succ)) =
        factorModule e 0 ::
          (ms ++ rawContractionFactor e j.succ :: zs) := by
    change factorModule e 0 ::
        finFamilyList (recursiveMergedFactor M j
          (rawContractionFactor e j.succ)) = _
    exact congrArg (List.cons (factorModule e 0))
      (finFamilyList_recursiveMerge_target_right_succ_core M j
        (rawContractionFactor e j.succ))
  have hcontractList : finFamilyList (factorModule (e.contract j.succ)) =
      factorModule e 0 ::
        (ms ++ rawContractionFactor e j.succ :: zs) :=
    hWList.symm.trans hrawTarget
  have hcontractCons :
      factorModule (e.contract j.succ) 0 ::
          compositionRightSuffix (e.contract j.succ) =
        factorModule e 0 ::
          (ms ++ rawContractionFactor e j.succ :: zs) :=
    (finFamilyList_factorModule_eq_first_suffix (e.contract j.succ)).symm.trans
      hcontractList
  have hfirst : factorModule (e.contract j.succ) 0 = factorModule e 0 :=
    (List.cons.inj hcontractCons).1
  have hsuffix : compositionRightSuffix (e.contract j.succ) =
      ms ++ rawContractionFactor e j.succ :: zs :=
    (List.cons.inj hcontractCons).2
  have hG₂Data : HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix (e.contract j.succ))
        (compositionBoundaryMap d (e.contract j.succ))) G₂ := by
    apply HEq.trans (adjacentMergeAfter_congr
      (f := compositionBoundaryMap d (e.contract j.succ))
      (g := compositionBoundaryMap d e)
      rfl rfl hfirst
      (compositionBoundaryModule_contract_right_succ_core d e j)
      hsuffix (compositionBoundaryMap_contract_right_succ_heq_core d e j))
    exact heq_of_eq (adjacentMergeAfter_eq_prefix_head
      (compositionLeftPrefix d) (compositionBoundaryMap d e))
  have hF₁Map : HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap d e)).tensorMap F₁.tensorMap := by
    apply AdjacentMergeData.tensorMap_heq
    · exact congrArg (fun s ↦ compositionLeftPrefix d ++
        factorModule d (Fin.last w.length) :: factorModule e 0 :: s)
        (compositionRightSuffix_split_right_succ_core e j)
    · exact congrArg (fun s ↦ compositionLeftPrefix d ++
        compositionBoundaryModule d e :: s)
        (compositionRightSuffix_split_right_succ_core e j)
    · exact hF₁Data
  have hG₁Map : HEq
      (rawContractionAdjacentMergeData (d.append e)
        (appendRightContractionIndex j.succ)).tensorMap G₁.tensorMap := by
    apply AdjacentMergeData.tensorMap_heq
    · exact (finFamilyList_factorModule_append_boundary d e).trans
        (congrArg (fun s ↦ compositionLeftPrefix d ++
          compositionBoundaryModule d e :: s)
          (compositionRightSuffix_split_right_succ_core e j))
    · calc
        finFamilyList (recursiveMergedFactor (factorModule (d.append e))
            (appendRightContractionIndex (w := w)
              (v := ({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord Y Z)) j.succ)
            (rawContractionFactor (d.append e)
              (appendRightContractionIndex (w := w)
                (v := ({ length := k + 2, intermediate := intermediate } :
                  DrinfeldWord Y Z)) j.succ))) =
            recursiveMergePrefix_right_succ_core (factorModule (d.append e))
                (appendRightContractionIndex (w := w)
                  (v := ({ length := k + 2, intermediate := intermediate } :
                    DrinfeldWord Y Z)) j.succ) ++
              rawContractionFactor (d.append e)
                  (appendRightContractionIndex (w := w)
                    (v := ({ length := k + 2, intermediate := intermediate } :
                      DrinfeldWord Y Z)) j.succ) ::
                recursiveMergeSuffix_right_succ_core (factorModule (d.append e))
                  (appendRightContractionIndex (w := w)
                    (v := ({ length := k + 2, intermediate := intermediate } :
                      DrinfeldWord Y Z)) j.succ) :=
          finFamilyList_recursiveMerge_target_right_succ_core
            (k := w.length + k + 1) (factorModule (d.append e))
            (appendRightContractionIndex (w := w)
              (v := ({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord Y Z)) j.succ)
            (rawContractionFactor (d.append e)
              (appendRightContractionIndex (w := w)
                (v := ({ length := k + 2, intermediate := intermediate } :
                  DrinfeldWord Y Z)) j.succ))
        _ = compositionLeftPrefix d ++ compositionBoundaryModule d e ::
            (ms ++ rawContractionFactor e j.succ :: zs) := by
          rw [recursiveMergePrefix_append_right_succ_at_index_core d e j,
            recursiveMergeSuffix_append_right_succ_at_index_core d e j,
            rawContractionFactor_append_right_succ_core d e j]
          simp only [ms, zs, M, List.append_assoc, List.cons_append]
    · exact hG₁Data
  have hF₂Map : HEq
      (((rawContractionAdjacentMergeData e j.succ).prefix
        (finFamilyList (factorModule d))).tensorMap) F₂.tensorMap := by
    apply AdjacentMergeData.tensorMap_heq
    · exact (congrArg (finFamilyList (factorModule d) ++ ·)
        (finFamilyList_factorModule_eq_first_suffix e)).trans
        ((congrArg (fun s ↦ finFamilyList (factorModule d) ++
          factorModule e 0 :: s)
          (compositionRightSuffix_split_right_succ_core e j)).trans
        (by rw [finFamilyList_factorModule_eq_prefix_last d]
            simp only [ms, zs, M, List.append_assoc, List.cons_append,
              List.nil_append]))
    · exact (congrArg (finFamilyList (factorModule d) ++ ·) hrawTarget).trans
        (by rw [finFamilyList_factorModule_eq_prefix_last d]
            simp only [ms, zs, M, List.append_assoc, List.cons_append,
              List.nil_append])
    · exact hF₂Data
  have hG₂Map : HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix (e.contract j.succ))
        (compositionBoundaryMap d (e.contract j.succ))).tensorMap G₂.tensorMap := by
    apply AdjacentMergeData.tensorMap_heq
    · exact congrArg (fun s ↦ compositionLeftPrefix d ++
        factorModule d (Fin.last w.length) :: s)
        (congrArg₂ List.cons hfirst hsuffix)
    · exact congrArg (fun s ↦ compositionLeftPrefix d ++ s)
        (congrArg₂ List.cons
          (compositionBoundaryModule_contract_right_succ_core d e j) hsuffix)
    · exact hG₂Data
  let hS := congrArg tensorModuleList (compositionSourceListEq d e)
  let hBdy := congrArg tensorModuleList (compositionBoundaryListEq d e)
  let hTgt := congrArg tensorModuleList (compositionTargetListEq d e)
  have hF₁Target :
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e =
        compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          (ms ++ factorModule e j.succ.castSucc ::
            factorModule e j.succ.succ :: zs) :=
    congrArg (fun s ↦ compositionLeftPrefix d ++
      compositionBoundaryModule d e :: s)
      (compositionRightSuffix_split_right_succ_core e j)
  have hF₁Source :
      finFamilyList (factorModule d) ++ finFamilyList (factorModule e) =
        compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
          factorModule e 0 ::
            (ms ++ factorModule e j.succ.castSucc ::
              factorModule e j.succ.succ :: zs) :=
    (finFamilyList_factorModule_pair_boundary d e).trans
      (congrArg (fun s ↦ compositionLeftPrefix d ++
        factorModule d (Fin.last w.length) :: factorModule e 0 :: s)
        (compositionRightSuffix_split_right_succ_core e j))
  have hG₁Source : finFamilyList (factorModule (d.append e)) =
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        (ms ++ factorModule e j.succ.castSucc ::
          factorModule e j.succ.succ :: zs) :=
    (finFamilyList_factorModule_append_boundary d e).trans hF₁Target
  have hG₁Target :
      finFamilyList (recursiveMergedFactor (factorModule (d.append e))
        (appendRightContractionIndex (w := w)
          (v := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord Y Z)) j.succ)
        (rawContractionFactor (d.append e)
          (appendRightContractionIndex (w := w)
            (v := ({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord Y Z)) j.succ))) =
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        (ms ++ rawContractionFactor e j.succ :: zs) := by
    calc
      _ = recursiveMergePrefix_right_succ_core (factorModule (d.append e))
              (appendRightContractionIndex (w := w)
                (v := ({ length := k + 2, intermediate := intermediate } :
                  DrinfeldWord Y Z)) j.succ) ++
            rawContractionFactor (d.append e)
                (appendRightContractionIndex (w := w)
                  (v := ({ length := k + 2, intermediate := intermediate } :
                    DrinfeldWord Y Z)) j.succ) ::
              recursiveMergeSuffix_right_succ_core (factorModule (d.append e))
                (appendRightContractionIndex (w := w)
                  (v := ({ length := k + 2, intermediate := intermediate } :
                    DrinfeldWord Y Z)) j.succ) :=
        finFamilyList_recursiveMerge_target_right_succ_core
          (k := w.length + k + 1) (factorModule (d.append e))
          (appendRightContractionIndex (w := w)
            (v := ({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord Y Z)) j.succ)
          (rawContractionFactor (d.append e)
            (appendRightContractionIndex (w := w)
              (v := ({ length := k + 2, intermediate := intermediate } :
                DrinfeldWord Y Z)) j.succ))
      _ = _ := by
        rw [recursiveMergePrefix_append_right_succ_at_index_core d e j,
          recursiveMergeSuffix_append_right_succ_at_index_core d e j,
          rawContractionFactor_append_right_succ_core d e j]
        simp only [ms, zs, M, List.append_assoc, List.cons_append]
  have hcanonicalLeft : HEq
      ((eqToHom hS ≫ eqToHom hBdy ≫
          (adjacentMergeAfter (compositionLeftPrefix d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)).tensorMap ≫ eqToHom hTgt) ≫
        (rawContractionAdjacentMergeData (d.append e)
          (appendRightContractionIndex j.succ)).tensorMap)
      (F₁.tensorMap ≫ G₁.tensorMap) := by
    simpa only [Category.assoc, Category.comp_id] using
      (transportedPair₂_heq
        (congrArg tensorModuleList hF₁Source)
        (hS.trans hBdy)
        (congrArg tensorModuleList hF₁Target)
        (congrArg tensorModuleList hG₁Source)
        (congrArg tensorModuleList hG₁Target)
        (congrArg tensorModuleList hG₁Target)
        (congrArg tensorModuleList hG₁Target)
        (eqToHom hS ≫ eqToHom hBdy)
        (adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e)).tensorMap
        (eqToHom hTgt)
        (rawContractionAdjacentMergeData (d.append e)
          (appendRightContractionIndex j.succ)).tensorMap
        (𝟙 _)
        (𝟙 _)
        F₁.tensorMap G₁.tensorMap
        (eqToHom_comp_heq_id hS hBdy) hF₁Map
        (test_eqToHom_heq_id hTgt) hG₁Map HEq.rfl HEq.rfl)
  have hF₂Source :
      finFamilyList (factorModule d) ++ finFamilyList (factorModule e) =
        compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
          (factorModule e 0 :: ms ++ factorModule e j.succ.castSucc ::
            factorModule e j.succ.succ :: zs) :=
    (congrArg (finFamilyList (factorModule d) ++ ·)
      (finFamilyList_factorModule_eq_first_suffix e)).trans
      ((congrArg (fun s ↦ finFamilyList (factorModule d) ++
        factorModule e 0 :: s)
        (compositionRightSuffix_split_right_succ_core e j)).trans
      (by rw [finFamilyList_factorModule_eq_prefix_last d]
          simp only [ms, zs, M, List.append_assoc, List.cons_append,
            List.nil_append]))
  have hF₂Target : finFamilyList (factorModule d) ++
        finFamilyList (recursiveMergedFactor (factorModule e) j.succ
          (rawContractionFactor e j.succ)) =
      compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
        (factorModule e 0 :: ms ++ rawContractionFactor e j.succ :: zs) :=
    (congrArg (finFamilyList (factorModule d) ++ ·) hrawTarget).trans
      (by rw [finFamilyList_factorModule_eq_prefix_last d]
          simp only [ms, zs, M, List.append_assoc, List.cons_append,
            List.nil_append])
  have hG₂Source :
      compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
          factorModule (e.contract j.succ) 0 ::
            compositionRightSuffix (e.contract j.succ) =
        compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
          factorModule e 0 :: (ms ++ rawContractionFactor e j.succ :: zs) :=
    congrArg (fun s ↦ compositionLeftPrefix d ++
      factorModule d (Fin.last w.length) :: s)
      (congrArg₂ List.cons hfirst hsuffix)
  have hG₂BoundaryTarget :
      compositionLeftPrefix d ++ compositionBoundaryModule d (e.contract j.succ) ::
          compositionRightSuffix (e.contract j.succ) =
        compositionLeftPrefix d ++ compositionBoundaryModule d e ::
          (ms ++ rawContractionFactor e j.succ :: zs) :=
    congrArg (compositionLeftPrefix d ++ ·)
      (congrArg₂ List.cons
        (compositionBoundaryModule_contract_right_succ_core d e j) hsuffix)
  have hG₂AppendTarget : finFamilyList (factorModule (d.append (e.contract j.succ))) =
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        (ms ++ rawContractionFactor e j.succ :: zs) :=
    (finFamilyList_factorModule_append_boundary d (e.contract j.succ)).trans
      hG₂BoundaryTarget
  let hS' := congrArg tensorModuleList
    (compositionSourceListEq d (e.contract j.succ))
  let hBdy' := congrArg tensorModuleList
    (compositionBoundaryListEq d (e.contract j.succ))
  let hTgt' := congrArg tensorModuleList
    (compositionTargetListEq d (e.contract j.succ))
  let hW' := congrArg tensorModuleList hWAppend
  have hcanonicalRight : HEq
      (((rawContractionAdjacentMergeData e j.succ).prefix
          (finFamilyList (factorModule d))).tensorMap ≫
        eqToHom hW' ≫ eqToHom hS' ≫ eqToHom hBdy' ≫
        (adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix (e.contract j.succ))
          (compositionBoundaryMap d (e.contract j.succ))).tensorMap ≫
        eqToHom hTgt')
      (F₂.tensorMap ≫ G₂.tensorMap) := by
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
      (transportedPair₂_heq
        (congrArg tensorModuleList hF₂Source) rfl
        (congrArg tensorModuleList hF₂Target)
        (congrArg tensorModuleList hG₂Source)
        (congrArg tensorModuleList hG₂BoundaryTarget)
        (congrArg tensorModuleList hG₂AppendTarget)
        (congrArg tensorModuleList hG₂AppendTarget)
        (𝟙 _)
        ((rawContractionAdjacentMergeData e j.succ).prefix
          (finFamilyList (factorModule d))).tensorMap
        (eqToHom hW' ≫ eqToHom hS' ≫ eqToHom hBdy')
        (adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix (e.contract j.succ))
          (compositionBoundaryMap d (e.contract j.succ))).tensorMap
        (eqToHom hTgt') (𝟙 _)
        F₂.tensorMap G₂.tensorMap HEq.rfl hF₂Map
        (eqToHom_comp₃_heq_id hW' hS' hBdy') hG₂Map
        (test_eqToHom_heq_id hTgt') HEq.rfl)
  exact hcanonicalLeft.trans hmiddle |>.trans hcanonicalRight.symm

theorem adjacentMergeData_suffix_heq
    {source target source' target' : List (ModuleCat.{0} ℤ)}
    (hsource : source = source') (htarget : target = target')
    {f : AdjacentMergeData source target}
    {g : AdjacentMergeData source' target'} (h : HEq f g)
    (Ps : List (ModuleCat.{0} ℤ)) : HEq (f.suffix Ps) (g.suffix Ps) := by
  subst source'
  subst target'
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

theorem finFamilyList_castSucc_append_last
    {k : ℕ} (M : Fin (k + 2) → ModuleCat.{0} ℤ) :
    finFamilyList M =
      finFamilyList (fun q : Fin (k + 1) ↦ M q.castSucc) ++
        [M (Fin.last (k + 1))] := by
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
  exact List.ofFn_succ_last

theorem recursiveAdjacentMergeDataOfFn_eq_after
    {K : ℕ} (M : Fin (K + 1) → ModuleCat.{0} ℤ) (i : Fin K)
    (P : ModuleCat.{0} ℤ) (f : M i.castSucc ⊗ M i.succ ⟶ P) :
    HEq (recursiveAdjacentMergeDataOfFn M i P f)
      (adjacentMergeAfter ((finFamilyList M).take i.val)
        (ys := (finFamilyList M).drop (i.val + 2)) f) := by
  cases K with
  | zero => exact Fin.elim0 i
  | succ k =>
      have h := recursiveAdjacentMergeDataOfFn_eq_after_right_succ_core M i P f
      rw [recursiveMergePrefix_eq_take_right_succ_core,
        recursiveMergeSuffix_eq_drop_right_succ_core] at h
      exact h

theorem finFamilyList_recursiveMerge_source
    {K : ℕ} (M : Fin (K + 1) → ModuleCat.{0} ℤ) (i : Fin K) :
    finFamilyList M = (finFamilyList M).take i.val ++
      M i.castSucc :: M i.succ :: (finFamilyList M).drop (i.val + 2) := by
  cases K with
  | zero => exact Fin.elim0 i
  | succ k =>
      have h := finFamilyList_recursiveMerge_source_right_succ_core M i
      rw [recursiveMergePrefix_eq_take_right_succ_core,
        recursiveMergeSuffix_eq_drop_right_succ_core] at h
      exact h

theorem finFamilyList_recursiveMerge_target
    {K : ℕ} (M : Fin (K + 1) → ModuleCat.{0} ℤ) (i : Fin K)
    (P : ModuleCat.{0} ℤ) :
    finFamilyList (recursiveMergedFactor M i P) =
      (finFamilyList M).take i.val ++
        P :: (finFamilyList M).drop (i.val + 2) := by
  cases K with
  | zero => exact Fin.elim0 i
  | succ k =>
      have h := finFamilyList_recursiveMerge_target_right_succ_core M i P
      rw [recursiveMergePrefix_eq_take_right_succ_core,
        recursiveMergeSuffix_eq_drop_right_succ_core] at h
      exact h

theorem recursiveMergedFactorList_append_of_normal_form
    {K L : ℕ} {M : Fin (K + 1) → ModuleCat.{0} ℤ}
    {N : Fin (L + 1) → ModuleCat.{0} ℤ} {i : Fin K} {j : Fin L}
    {P Q : ModuleCat.{0} ℤ} (tail : List (ModuleCat.{0} ℤ))
    (hprefix : (finFamilyList M).take i.val =
      (finFamilyList N).take j.val)
    (hP : P = Q)
    (hsuffix : (finFamilyList M).drop (i.val + 2) =
      (finFamilyList N).drop (j.val + 2) ++ tail) :
    finFamilyList (recursiveMergedFactor M i P) =
      finFamilyList (recursiveMergedFactor N j Q) ++ tail := by
  rw [finFamilyList_recursiveMerge_target,
    finFamilyList_recursiveMerge_target, hprefix, hP, hsuffix]
  simp only [List.cons_append, List.append_assoc]

theorem recursiveAdjacentMergeDataOfFn_castSucc_suffix
    {k : ℕ} (M : Fin (k + 3) → ModuleCat.{0} ℤ)
    (i : Fin (k + 1)) (P : ModuleCat.{0} ℤ)
    (f : M i.castSucc.castSucc ⊗ M i.castSucc.succ ⟶ P) :
    HEq
      (recursiveAdjacentMergeDataOfFn M i.castSucc P f)
      ((recursiveAdjacentMergeDataOfFn
        (fun q : Fin (k + 2) ↦ M q.castSucc) i P (by
          have hindex : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
          simpa only [hindex] using f)).suffix
        [M (Fin.last (k + 2))]) := by
  let M' : Fin (k + 2) → ModuleCat.{0} ℤ := fun q ↦ M q.castSucc
  have hlist : finFamilyList M = finFamilyList M' ++
      [M (Fin.last (k + 2))] := finFamilyList_castSucc_append_last M
  have hprefix :
      (finFamilyList M).take i.castSucc.val =
        (finFamilyList M').take i.val := by
    rw [hlist]
    rw [List.take_append_of_le_length]
    · simp only [Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      simp only [Fin.val_castSucc]
      have hi := i.isLt
      omega
  have hsuffix :
      (finFamilyList M).drop (i.castSucc.val + 2) =
        (finFamilyList M').drop (i.val + 2) ++
          [M (Fin.last (k + 2))] := by
    rw [hlist]
    rw [List.drop_append_of_le_length]
    · simp only [Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      simp only [Fin.val_castSucc]
      have hi := i.isLt
      omega
  let f' : M' i.castSucc ⊗ M' i.succ ⟶ P := by
    have hindex : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    simpa only [M', hindex] using f
  change HEq (recursiveAdjacentMergeDataOfFn M i.castSucc P f)
    ((recursiveAdjacentMergeDataOfFn M' i P f').suffix
      [M (Fin.last (k + 2))])
  have hfull := recursiveAdjacentMergeDataOfFn_eq_after
    M i.castSucc P f
  have hshort := recursiveAdjacentMergeDataOfFn_eq_after
    M' i P f'
  have hshortSuffix := adjacentMergeAfter_suffix_heq
    ((finFamilyList M').take i.val)
    (ys := (finFamilyList M').drop (i.val + 2)) f'
    [M (Fin.last (k + 2))]
  have hshortDataSuffix := adjacentMergeData_suffix_heq
    (finFamilyList_recursiveMerge_source M' i)
    (finFamilyList_recursiveMerge_target M' i P)
    hshort [M (Fin.last (k + 2))]
  have hcanonical := adjacentMergeAfter_congr hprefix rfl rfl rfl hsuffix
    (show HEq f f' by exact HEq.rfl)
  exact hfull.trans (hcanonical.trans
    (hshortSuffix.symm.trans hshortDataSuffix.symm))

theorem rawContractionFactor_append_left_castSucc
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
    rawContractionFactor (d.append e)
        (appendLeftContractionIndex i.castSucc) =
      rawContractionFactor d i.castSucc := by
  have hleft :
      (appendLeftContractionIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc).castSucc =
        appendLeftArrowIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc := by
    apply Fin.ext
    rfl
  have hright :
      (appendLeftContractionIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc).succ =
        appendLeftArrowIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.succ := Fin.ext rfl
  unfold rawContractionFactor
  change (dgHomZModuleCochainComplex
      ((({ length := k + 2, intermediate := intermediate } :
        DrinfeldWord X Y).append v).arrowSource
        (appendLeftContractionIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc).castSucc)
      ((({ length := k + 2, intermediate := intermediate } :
        DrinfeldWord X Y).append v).arrowTarget
        (appendLeftContractionIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc).succ)).X
      (appendArrowDegree d e
          (appendLeftContractionIndex
            (w := ({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) (v := v) i.castSucc).castSucc +
        appendArrowDegree d e
          (appendLeftContractionIndex
            (w := ({ length := k + 2, intermediate := intermediate } :
              DrinfeldWord X Y)) (v := v) i.castSucc).succ) = _
  rw [hleft, hright, arrowSource_append_left, arrowTarget_append_left,
    appendArrowDegree_left, appendArrowDegree_left]
  rw [show i.succ.castSucc = i.castSucc.succ by apply Fin.ext; rfl]

theorem adjacentFactorComposition_append_left_castSucc
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
    HEq (adjacentFactorComposition (d.append e)
        (appendLeftContractionIndex i.castSucc))
      (adjacentFactorComposition d i.castSucc) := by
  have hleft :
      (appendLeftContractionIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc).castSucc =
        appendLeftArrowIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc := by
    apply Fin.ext
    rfl
  have hright :
      (appendLeftContractionIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.castSucc).succ =
        appendLeftArrowIndex
          (w := ({ length := k + 2, intermediate := intermediate } :
            DrinfeldWord X Y)) (v := v) i.succ := Fin.ext rfl
  unfold adjacentFactorComposition
  apply dgCochainCompTensorOfEq_heq
  · rw [hleft, arrowSource_append_left]
  · rw [hleft, arrowTarget_append_left]
  · rw [hright, arrowSource_append_left]
    congr 1
  · rw [hright, arrowTarget_append_left]
    congr 1
  · simp only [DegreeProfile.append, hleft, appendArrowDegree_left]
  · simp only [DegreeProfile.append, hright, appendArrowDegree_left]
    congr 1
  · simp only [DegreeProfile.append, hleft, hright,
      appendArrowDegree_left]
    congr 2

theorem rawContractionAdjacentMergeData_append_left_castSucc
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
    let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
      fun q ↦ factorModule d q.castSucc
    let F := recursiveAdjacentMergeDataOfFn Mleft i
      (rawContractionFactor d i.castSucc) (by
        exact adjacentFactorComposition d i.castSucc)
    HEq (rawContractionAdjacentMergeData (d.append e)
        (appendLeftContractionIndex i.castSucc))
      (F.suffix
        (compositionBoundaryModule d e :: compositionRightSuffix e)) := by
  dsimp only
  let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
    fun q ↦ factorModule d q.castSucc
  let F := recursiveAdjacentMergeDataOfFn Mleft i
    (rawContractionFactor d i.castSucc) (by
      exact adjacentFactorComposition d i.castSucc)
  let j := appendLeftContractionIndex
    (w := ({ length := k + 2, intermediate := intermediate } :
      DrinfeldWord X Y)) (v := v) i.castSucc
  let tail := compositionBoundaryModule d e :: compositionRightSuffix e
  have hlist : finFamilyList (factorModule (d.append e)) =
      finFamilyList Mleft ++ tail := by
    simpa only [Mleft, tail, compositionLeftPrefix] using
      finFamilyList_factorModule_append_boundary d e
  have hprefix :
      (finFamilyList (factorModule (d.append e))).take j.val =
        (finFamilyList Mleft).take i.val := by
    rw [hlist]
    rw [List.take_append_of_le_length]
    · simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      have hi := i.isLt
      simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
      omega
  have hsuffix :
      (finFamilyList (factorModule (d.append e))).drop (j.val + 2) =
        (finFamilyList Mleft).drop (i.val + 2) ++ tail := by
    rw [hlist]
    rw [List.drop_append_of_le_length]
    · simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      have hi := i.isLt
      simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
      omega
  have hP := rawContractionFactor_append_left_castSucc d e i
  have hf := adjacentFactorComposition_append_left_castSucc d e i
  have hfull := recursiveAdjacentMergeDataOfFn_eq_after
    (factorModule (d.append e)) j
      (rawContractionFactor (d.append e) j)
      (adjacentFactorComposition (d.append e) j)
  have hF := recursiveAdjacentMergeDataOfFn_eq_after
    Mleft i (rawContractionFactor d i.castSucc)
      (adjacentFactorComposition d i.castSucc)
  have hFSuffix := adjacentMergeData_suffix_heq
    (finFamilyList_recursiveMerge_source Mleft i)
    (finFamilyList_recursiveMerge_target Mleft i
      (rawContractionFactor d i.castSucc)) hF tail
  have hAfterSuffix := adjacentMergeAfter_suffix_heq
    ((finFamilyList Mleft).take i.val)
    (ys := (finFamilyList Mleft).drop (i.val + 2))
    (adjacentFactorComposition d i.castSucc) tail
  have hcanonical := adjacentMergeAfter_congr hprefix
    (factorModule_append_left d e i.castSucc)
    (factorModule_append_left d e i.succ) hP hsuffix hf
  unfold rawContractionAdjacentMergeData
  change HEq (recursiveAdjacentMergeDataOfFn
      (factorModule (d.append e)) j
      (rawContractionFactor (d.append e) j)
      (adjacentFactorComposition (d.append e) j)) (F.suffix tail)
  exact hfull.trans (hcanonical.trans
    (hAfterSuffix.symm.trans hFSuffix.symm))

theorem rawContractionTargetList_append_left_castSucc
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
    let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
      fun q ↦ factorModule d q.castSucc
    finFamilyList (recursiveMergedFactor (factorModule (d.append e))
        (appendLeftContractionIndex i.castSucc)
        (rawContractionFactor (d.append e)
          (appendLeftContractionIndex i.castSucc))) =
      finFamilyList (recursiveMergedFactor Mleft i
          (rawContractionFactor d i.castSucc)) ++
        compositionBoundaryModule d e :: compositionRightSuffix e := by
  dsimp only
  let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
    fun q ↦ factorModule d q.castSucc
  let j := appendLeftContractionIndex
    (w := ({ length := k + 2, intermediate := intermediate } :
      DrinfeldWord X Y)) (v := v) i.castSucc
  let tail := compositionBoundaryModule d e :: compositionRightSuffix e
  have hlist : finFamilyList (factorModule (d.append e)) =
      finFamilyList Mleft ++ tail := by
    simpa only [Mleft, tail, compositionLeftPrefix] using
      finFamilyList_factorModule_append_boundary d e
  have hprefix : (finFamilyList (factorModule (d.append e))).take j.val =
      (finFamilyList Mleft).take i.val := by
    rw [hlist, List.take_append_of_le_length]
    · simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      have hi := i.isLt
      simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
      omega
  have hsuffix : (finFamilyList (factorModule (d.append e))).drop (j.val + 2) =
      (finFamilyList Mleft).drop (i.val + 2) ++ tail := by
    rw [hlist, List.drop_append_of_le_length]
    · simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      have hi := i.isLt
      simp only [j, appendLeftContractionIndex, Fin.val_mk,
        Fin.val_castSucc]
      omega
  exact recursiveMergedFactorList_append_of_normal_form tail hprefix
    (rawContractionFactor_append_left_castSucc d e i) hsuffix

theorem rawContractionTargetList_castSucc_append_last
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
      fun q ↦ factorModule d q.castSucc
    finFamilyList (recursiveMergedFactor (factorModule d) i.castSucc
        (rawContractionFactor d i.castSucc)) =
      finFamilyList (recursiveMergedFactor Mleft i
          (rawContractionFactor d i.castSucc)) ++
        [factorModule d (Fin.last (k + 2))] := by
  dsimp only
  let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
    fun q ↦ factorModule d q.castSucc
  let tail := [factorModule d (Fin.last (k + 2))]
  have hlist : finFamilyList (factorModule d) =
      finFamilyList Mleft ++ tail := by
    simpa only [Mleft, tail, compositionLeftPrefix] using
      finFamilyList_factorModule_eq_prefix_last d
  have hprefix : (finFamilyList (factorModule d)).take i.castSucc.val =
      (finFamilyList Mleft).take i.val := by
    rw [hlist, List.take_append_of_le_length]
    · simp only [Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      simp only [Fin.val_castSucc]
      have hi := i.isLt
      omega
  have hsuffix : (finFamilyList (factorModule d)).drop (i.castSucc.val + 2) =
      (finFamilyList Mleft).drop (i.val + 2) ++ tail := by
    rw [hlist, List.drop_append_of_le_length]
    · simp only [Fin.val_castSucc]
    · rw [finFamilyList_eq_ofFn, List.length_ofFn]
      simp only [Fin.val_castSucc]
      have hi := i.isLt
      omega
  exact recursiveMergedFactorList_append_of_normal_form tail hprefix rfl
    hsuffix

theorem summandCompositionMap_contraction_append_right_of_remainder
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length)
    (hremainder :
      HEq
        (summandCompositionRemainder d e ≫
          contractionTensorMap (d.append e) (appendRightContractionIndex j))
        (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
            (contractionTensorMap e j) ≫
          summandCompositionRemainder d (e.contract j))) :
    HEq
      (summandCompositionMap d e ≫
        contractionTensorMap (d.append e) (appendRightContractionIndex j))
      ((𝟙 (summandModule d) ⊗ₘ contractionTensorMap e j) ≫
        summandCompositionMap d (e.contract j)) := by
  rw [summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized]
  rw [normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder]
  dsimp only [summandModule]
  simp only [Category.assoc]
  rw [tensorModuleListAppendIso_whiskerLeft_assoc]
  let A := (tensorModuleListAppendIso (finFamilyList (factorModule d))
    (finFamilyList (factorModule e))).hom
  let R := summandCompositionRemainder d e
  let C := contractionTensorMap (d.append e) (appendRightContractionIndex j)
  let W := tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
    (contractionTensorMap e j)
  let R' := summandCompositionRemainder d (e.contract j)
  change HEq (A ≫ (R ≫ C)) (A ≫ (W ≫ R'))
  exact CategoryTheory.heq_comp rfl rfl
    (eq_of_heq (summandModule_contract_append_right_heq d e j))
    HEq.rfl hremainder

theorem summandCompositionMap_contraction_append_right_succ_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord Y Z) m)
    (j : Fin (k + 1)) :
    HEq
      (summandCompositionMap d e ≫
        contractionTensorMap (d.append e)
          (appendRightContractionIndex j.succ))
      ((𝟙 (summandModule d) ⊗ₘ contractionTensorMap e j.succ) ≫
        summandCompositionMap d (e.contract j.succ)) :=
  summandCompositionMap_contraction_append_right_of_remainder d e j.succ
    (summandCompositionRemainder_contraction_append_right_succ_heq d e j)

section QuotientCoefficient

theorem adjacentMergeData_suffix_heq_left_last
    {source target source' target' : List (ModuleCat.{0} ℤ)}
    (hsource : source = source') (htarget : target = target')
    {f : AdjacentMergeData source target}
    {g : AdjacentMergeData source' target'} (h : HEq f g)
    (Ps : List (ModuleCat.{0} ℤ)) : HEq (f.suffix Ps) (g.suffix Ps) := by
  subst source'
  subst target'
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

def rawContractionTargetListEq_left_last_assembly
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    finFamilyList (factorModule (d.contract i)) =
      finFamilyList (recursiveMergedFactor (factorModule d) i
        (rawContractionFactor d i)) :=
  ((congrArg finFamilyList (test_rawContractionTarget_eq d i)).trans
    (contractedFactorsOldIndex_eq d i)).symm

def leftLastCommonPrefix
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    List (ModuleCat.{0} ℤ) :=
  finFamilyList (fun q : Fin k ↦ factorModule d q.castSucc.castSucc)

def leftLastHeadDegreeProfile
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    DegreeProfile
      (nil
        (arrowSource
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
          (Fin.last k).castSucc)
        (arrowTarget
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
          (Fin.last k).castSucc))
      (d.arrowDegree (Fin.last k).castSucc) where
  arrowDegree _ := d.arrowDegree (Fin.last k).castSucc
  totalDegree := by simp [nil]

def leftLastTailDegreeProfile
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    DegreeProfile
      (nil
        (arrowTarget
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
          (Fin.last k).castSucc) Y)
      (d.arrowDegree (Fin.last k).succ) where
  arrowDegree _ := d.arrowDegree (Fin.last k).succ
  totalDegree := by simp [nil]

theorem compositionLeftPrefix_eq_leftLastCommonPrefix_append
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionLeftPrefix d = leftLastCommonPrefix d ++
      [factorModule (leftLastHeadDegreeProfile d) 0] := by
  unfold compositionLeftPrefix leftLastCommonPrefix
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn, List.ofFn_succ_last]
  congr 2

theorem factorModule_eq_leftLastTailDegreeProfile
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d (Fin.last (k + 1)) =
      factorModule (leftLastTailDegreeProfile d) 0 := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  have hi : (Fin.last k).succ = Fin.last (k + 1) := Fin.ext rfl
  have hsource : w.arrowSource (Fin.last (k + 1)) = w.arrowTarget i.castSucc := by
    rw [← hi, ← arrowTarget_castSucc_eq_arrowSource_succ w i]
  have htarget : w.arrowTarget (Fin.last (k + 1)) = Y :=
    arrowTarget_last_eq_target w
  unfold factorModule leftLastTailDegreeProfile
  rw [hsource, htarget, ← hi]
  rfl

theorem finFamilyList_factorModule_eq_leftLast
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    finFamilyList (factorModule d) = leftLastCommonPrefix d ++
      [factorModule (leftLastHeadDegreeProfile d) 0,
        factorModule (leftLastTailDegreeProfile d) 0] := by
  rw [finFamilyList_factorModule_eq_prefix_last,
    compositionLeftPrefix_eq_leftLastCommonPrefix_append,
    factorModule_eq_leftLastTailDegreeProfile]
  rw [List.append_assoc]
  rfl


theorem leftLastNormalizedPairTensorMap_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    let P := leftLastCommonPrefix d
    let a := leftLastHeadDegreeProfile d
    let b := leftLastTailDegreeProfile d
    HEq
      (((@AdjacentMergeData.head
          (factorModule a 0) (factorModule b 0)
          (compositionBoundaryModule a b)
          (factorModule e 0 :: compositionRightSuffix e)
          (compositionBoundaryMap a b)).prefix P).tensorMap ≫
        ((@AdjacentMergeData.head
          (compositionBoundaryModule a b) (factorModule e 0)
          (tripleCompositionBoundaryModule a b e)
          (compositionRightSuffix e)
          (leftAssociatedBoundaryMap a b e)).prefix P).tensorMap)
      (((@AdjacentMergeData.tail (factorModule a 0)
          (factorModule b 0 :: factorModule e 0 :: compositionRightSuffix e)
          (zeroMiddleRightBoundaryModule b e :: compositionRightSuffix e)
          (@AdjacentMergeData.head (factorModule b 0) (factorModule e 0)
            (zeroMiddleRightBoundaryModule b e) (compositionRightSuffix e)
            (zeroMiddleRightBoundaryMap b e))).prefix P).tensorMap ≫
        ((@AdjacentMergeData.head (factorModule a 0)
          (zeroMiddleRightBoundaryModule b e)
          (tripleCompositionBoundaryModule a b e)
          (compositionRightSuffix e)
          (rightAssociatedBoundaryMap a b e)).prefix P).tensorMap) := by
  dsimp only
  exact (normalizedBoundaryPairCoherence (leftLastCommonPrefix d)
    (compositionRightSuffix e) (leftLastHeadDegreeProfile d)
    (leftLastTailDegreeProfile d) e).tensorMap_heq

theorem leftLastCompositionMergeTensorMap_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap
      (((@AdjacentMergeData.tail
          (factorModule (leftLastHeadDegreeProfile d) 0)
          (factorModule (leftLastTailDegreeProfile d) 0 ::
            factorModule e 0 :: compositionRightSuffix e)
          (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e ::
            compositionRightSuffix e)
          (@AdjacentMergeData.head
            (factorModule (leftLastTailDegreeProfile d) 0)
            (factorModule e 0)
            (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e)
            (compositionRightSuffix e)
            (zeroMiddleRightBoundaryMap (leftLastTailDegreeProfile d) e))).prefix
              (leftLastCommonPrefix d)).tensorMap) := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let P := leftLastCommonPrefix d
  let a := leftLastHeadDegreeProfile d
  let b := leftLastTailDegreeProfile d
  have hi : i.succ = Fin.last (k + 1) := Fin.ext rfl
  have hmeet : w.arrowTarget i.castSucc = w.arrowSource i.succ :=
    arrowTarget_castSucc_eq_arrowSource_succ w i
  have hfactor : factorModule d (Fin.last (k + 1)) = factorModule b 0 :=
    factorModule_eq_leftLastTailDegreeProfile d
  have hsource : w.arrowSource (Fin.last (k + 1)) = w.arrowTarget i.castSucc := by
    rw [← hi, ← hmeet]
  have htarget : w.arrowTarget (Fin.last (k + 1)) = Y :=
    arrowTarget_last_eq_target w
  have hdegree : d.arrowDegree (Fin.last (k + 1)) = d.arrowDegree i.succ := by
    rw [hi]
  have hboundary : compositionBoundaryModule d e =
      zeroMiddleRightBoundaryModule b e := by
    unfold compositionBoundaryModule zeroMiddleRightBoundaryModule b
    rw [← hi, ← hmeet]
    rfl
  have hprefix : compositionLeftPrefix d = P ++ [factorModule a 0] :=
    compositionLeftPrefix_eq_leftLastCommonPrefix_append d
  have hmap : HEq (compositionBoundaryMap d e)
      (zeroMiddleRightBoundaryMap b e) := by
    unfold compositionBoundaryMap zeroMiddleRightBoundaryMap b
    apply dgCochainCompTensorOfEq_heq
    · exact hsource
    · exact htarget
    · rfl
    · rfl
    · exact hdegree
    · rfl
    · change d.arrowDegree i.succ + e.arrowDegree 0 =
        d.arrowDegree i.succ + e.arrowDegree 0
      rfl
  have hdata := (adjacentMergeAfter_congr
    (f := compositionBoundaryMap d e)
    (g := zeroMiddleRightBoundaryMap b e)
    (ys := compositionRightSuffix e) (ys' := compositionRightSuffix e)
    hprefix hfactor rfl hboundary rfl hmap).trans
      (heq_of_eq (adjacentMergeAfter_eq_prefix_head
        (P ++ [factorModule a 0])
        (ys := compositionRightSuffix e) (zeroMiddleRightBoundaryMap b e)))
  apply AdjacentMergeData.tensorMap_heq
  · rw [hprefix, hfactor]
    rw [List.append_assoc]
    rfl
  · rw [hprefix, hboundary]
    rw [List.append_assoc]
    rfl
  · exact hdata.trans
      (AdjacentMergeData.prefix_prefix_heq
        (@AdjacentMergeData.head
          (factorModule b 0) (factorModule e 0)
          (zeroMiddleRightBoundaryModule b e) (compositionRightSuffix e)
          (zeroMiddleRightBoundaryMap b e)) [factorModule a 0] P).symm

theorem leftLastRawContractionAppendTensorMap_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (rawContractionAdjacentMergeData (d.append e)
        (appendLeftContractionIndex (v := v) (Fin.last k))).tensorMap
      (((@AdjacentMergeData.head
          (factorModule (leftLastHeadDegreeProfile d) 0)
          (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e)
          (tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)
          (compositionRightSuffix e)
          (rightAssociatedBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)).prefix
              (leftLastCommonPrefix d)).tensorMap) := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let j := appendLeftContractionIndex (w := w) (v := v) i
  let P := leftLastCommonPrefix d
  let a := leftLastHeadDegreeProfile d
  let b := leftLastTailDegreeProfile d
  have hj : j.val = k := rfl
  have hi : i.succ = Fin.last (k + 1) := Fin.ext rfl
  have hjLeft : j.castSucc =
      appendLeftArrowIndex (w := w) (v := v) i := Fin.ext rfl
  have hjBoundary : j.succ = appendBoundaryArrowIndex w v := Fin.ext rfl
  have hmeet : w.arrowTarget i.castSucc = w.arrowSource i.succ :=
    arrowTarget_castSucc_eq_arrowSource_succ w i
  have hprefix : compositionLeftPrefix d = P ++ [factorModule a 0] :=
    compositionLeftPrefix_eq_leftLastCommonPrefix_append d
  have hboundary : compositionBoundaryModule d e =
      zeroMiddleRightBoundaryModule b e := by
    unfold compositionBoundaryModule zeroMiddleRightBoundaryModule b
    rw [← hi, ← hmeet]
    rfl
  have hsource : finFamilyList (factorModule (d.append e)) =
      P ++ factorModule a 0 :: zeroMiddleRightBoundaryModule b e ::
        compositionRightSuffix e := by
    rw [finFamilyList_factorModule_append_boundary, hprefix, hboundary]
    rw [List.append_assoc]
    rfl
  have hraw : rawContractionFactor (d.append e) j =
      tripleCompositionBoundaryModule a b e := by
    unfold rawContractionFactor tripleCompositionBoundaryModule a b
    rw [hjLeft, arrowSource_append_left, hjBoundary, arrowTarget_append_boundary]
    congr 1
    change appendArrowDegree d e (appendLeftArrowIndex (v := v) i) +
        appendArrowDegree d e (appendBoundaryArrowIndex w v) = _
    rw [appendArrowDegree_left, appendArrowDegree_boundary, ← hi]
    change d.arrowDegree i.castSucc + (d.arrowDegree i.succ + e.arrowDegree 0) =
      (d.arrowDegree i.castSucc + d.arrowDegree i.succ) + e.arrowDegree 0
    omega
  have hmap : HEq (adjacentFactorComposition (d.append e) j)
      (rightAssociatedBoundaryMap a b e) := by
    unfold adjacentFactorComposition rightAssociatedBoundaryMap a b
    apply dgCochainCompTensorOfEq_heq
    · rw [hjLeft, arrowSource_append_left]
      rfl
    · rw [hjLeft, arrowTarget_append_left]
      rfl
    · rw [hjBoundary, arrowSource_append_boundary, ← hi, ← hmeet]
      rfl
    · rw [hjBoundary, arrowTarget_append_boundary]
    · rw [hjLeft]
      change appendArrowDegree d e (appendLeftArrowIndex (v := v) i) =
        d.arrowDegree i.castSucc
      rw [appendArrowDegree_left]
    · rw [hjBoundary]
      change appendArrowDegree d e (appendBoundaryArrowIndex w v) =
        d.arrowDegree i.succ + e.arrowDegree 0
      rw [appendArrowDegree_boundary, ← hi]
    · rw [hjLeft, hjBoundary]
      change appendArrowDegree d e (appendLeftArrowIndex (v := v) i) +
          appendArrowDegree d e (appendBoundaryArrowIndex w v) =
        (d.arrowDegree i.castSucc + d.arrowDegree i.succ) + e.arrowDegree 0
      rw [appendArrowDegree_left, appendArrowDegree_boundary, ← hi]
      omega
  have hPlength : P.length = k := by
    simp [P, leftLastCommonPrefix, finFamilyList_eq_ofFn]
  have htake : (finFamilyList (factorModule (d.append e))).take j.val = P := by
    rw [hsource, hj]
    simp [hPlength]
  have hdrop : (finFamilyList (factorModule (d.append e))).drop (j.val + 2) =
      compositionRightSuffix e := by
    rw [hsource, hj]
    rw [show k + 2 = P.length + 2 by omega, ← List.drop_drop]
    simp
  have htarget : finFamilyList
        (recursiveMergedFactor (factorModule (d.append e)) j
          (rawContractionFactor (d.append e) j)) =
      P ++ tripleCompositionBoundaryModule a b e :: compositionRightSuffix e := by
    rw [finFamilyList_recursiveMerge_target, htake, hraw, hdrop]
  have hleftFactor : factorModule (d.append e) j.castSucc = factorModule a 0 := by
    rw [hjLeft, factorModule_append_left]
    rfl
  have hrightFactor : factorModule (d.append e) j.succ =
      zeroMiddleRightBoundaryModule b e := by
    rw [hjBoundary, factorModule_append_boundary, hboundary]
  apply AdjacentMergeData.tensorMap_heq hsource htarget
  unfold rawContractionAdjacentMergeData
  exact (recursiveAdjacentMergeDataOfFn_eq_after
    (factorModule (d.append e)) j (rawContractionFactor (d.append e) j)
      (adjacentFactorComposition (d.append e) j)).trans
    ((adjacentMergeAfter_congr htake hleftFactor hrightFactor hraw hdrop hmap).trans
      (heq_of_eq (adjacentMergeAfter_eq_prefix_head P
        (rightAssociatedBoundaryMap a b e))))

theorem leftLastRawContractionAppendTargetList_eq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    finFamilyList
        (recursiveMergedFactor (factorModule (d.append e))
          (appendLeftContractionIndex (v := v) (Fin.last k))
          (rawContractionFactor (d.append e)
            (appendLeftContractionIndex (v := v) (Fin.last k)))) =
      leftLastCommonPrefix d ++
        tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e :: compositionRightSuffix e := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let j := appendLeftContractionIndex (w := w) (v := v) i
  let P := leftLastCommonPrefix d
  let a := leftLastHeadDegreeProfile d
  let b := leftLastTailDegreeProfile d
  have hj : j.val = k := rfl
  have hi : i.succ = Fin.last (k + 1) := Fin.ext rfl
  have hjLeft : j.castSucc =
      appendLeftArrowIndex (w := w) (v := v) i := Fin.ext rfl
  have hjBoundary : j.succ = appendBoundaryArrowIndex w v := Fin.ext rfl
  have hmeet : w.arrowTarget i.castSucc = w.arrowSource i.succ :=
    arrowTarget_castSucc_eq_arrowSource_succ w i
  have hprefix : compositionLeftPrefix d = P ++ [factorModule a 0] :=
    compositionLeftPrefix_eq_leftLastCommonPrefix_append d
  have hboundary : compositionBoundaryModule d e =
      zeroMiddleRightBoundaryModule b e := by
    unfold compositionBoundaryModule zeroMiddleRightBoundaryModule b
    rw [← hi, ← hmeet]
    rfl
  have hsource : finFamilyList (factorModule (d.append e)) =
      P ++ factorModule a 0 :: zeroMiddleRightBoundaryModule b e ::
        compositionRightSuffix e := by
    rw [finFamilyList_factorModule_append_boundary, hprefix, hboundary]
    rw [List.append_assoc]
    rfl
  have hraw : rawContractionFactor (d.append e) j =
      tripleCompositionBoundaryModule a b e := by
    unfold rawContractionFactor tripleCompositionBoundaryModule a b
    rw [hjLeft, arrowSource_append_left, hjBoundary, arrowTarget_append_boundary]
    congr 1
    change appendArrowDegree d e (appendLeftArrowIndex (v := v) i) +
        appendArrowDegree d e (appendBoundaryArrowIndex w v) = _
    rw [appendArrowDegree_left, appendArrowDegree_boundary, ← hi]
    change d.arrowDegree i.castSucc + (d.arrowDegree i.succ + e.arrowDegree 0) =
      (d.arrowDegree i.castSucc + d.arrowDegree i.succ) + e.arrowDegree 0
    omega
  have hPlength : P.length = k := by
    simp [P, leftLastCommonPrefix, finFamilyList_eq_ofFn]
  have htake : (finFamilyList (factorModule (d.append e))).take j.val = P := by
    rw [hsource, hj]
    simp [hPlength]
  have hdrop : (finFamilyList (factorModule (d.append e))).drop (j.val + 2) =
      compositionRightSuffix e := by
    rw [hsource, hj]
    rw [show k + 2 = P.length + 2 by omega, ← List.drop_drop]
    simp
  rw [finFamilyList_recursiveMerge_target, htake, hraw, hdrop]


theorem leftLastRawContractionWhiskerTensorMap_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (rawContractionAdjacentMergeData d (Fin.last k)).tensorMap)
      (((@AdjacentMergeData.head
          (factorModule (leftLastHeadDegreeProfile d) 0)
          (factorModule (leftLastTailDegreeProfile d) 0)
          (compositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))
          (factorModule e 0 :: compositionRightSuffix e)
          (compositionBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))).prefix
              (leftLastCommonPrefix d)).tensorMap) := by
  rw [← AdjacentMergeData.suffix_tensorMap]
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let P := leftLastCommonPrefix d
  let a := leftLastHeadDegreeProfile d
  let b := leftLastTailDegreeProfile d
  have hi : i.succ = Fin.last (k + 1) := Fin.ext rfl
  have hmeet : w.arrowTarget i.castSucc = w.arrowSource i.succ :=
    arrowTarget_castSucc_eq_arrowSource_succ w i
  have hsource : finFamilyList (factorModule d) =
      P ++ [factorModule a 0, factorModule b 0] :=
    finFamilyList_factorModule_eq_leftLast d
  have htargetLast : w.arrowTarget i.succ = Y := by
    rw [hi, arrowTarget_last_eq_target]
  have hraw : rawContractionFactor d i = compositionBoundaryModule a b := by
    unfold rawContractionFactor compositionBoundaryModule a b
    rw [htargetLast]
    rfl
  have hmap : HEq (adjacentFactorComposition d i)
      (compositionBoundaryMap a b) := by
    unfold adjacentFactorComposition compositionBoundaryMap a b
    have htarget : w.arrowTarget i.succ = Y := by
      rw [hi, arrowTarget_last_eq_target]
    apply dgCochainCompTensorOfEq_heq
    · rfl
    · rfl
    · exact hmeet.symm
    · exact htarget
    · rfl
    · rfl
    · rfl
  have hPlength : P.length = k := by
    simp [P, leftLastCommonPrefix, finFamilyList_eq_ofFn]
  have htake : (finFamilyList (factorModule d)).take i.val = P := by
    rw [hsource]
    simp [i, hPlength]
  have hdrop : (finFamilyList (factorModule d)).drop (i.val + 2) = [] := by
    rw [hsource]
    simp [i, hPlength]
  have htarget : finFamilyList
        (recursiveMergedFactor (factorModule d) i (rawContractionFactor d i)) =
      P ++ [compositionBoundaryModule a b] := by
    rw [finFamilyList_recursiveMerge_target, htake, hraw, hdrop]
  have hdata : HEq (rawContractionAdjacentMergeData d i)
      ((@AdjacentMergeData.head (factorModule a 0) (factorModule b 0)
        (compositionBoundaryModule a b) [] (compositionBoundaryMap a b)).prefix P) := by
    unfold rawContractionAdjacentMergeData
    exact (recursiveAdjacentMergeDataOfFn_eq_after
      (factorModule d) i (rawContractionFactor d i)
        (adjacentFactorComposition d i)).trans
      ((adjacentMergeAfter_congr htake rfl
        (factorModule_eq_leftLastTailDegreeProfile d) hraw hdrop hmap).trans
        (heq_of_eq (adjacentMergeAfter_eq_prefix_head P
          (compositionBoundaryMap a b))))
  apply AdjacentMergeData.tensorMap_heq
  · rw [hsource, finFamilyList_factorModule_eq_first_suffix]
    rw [List.append_assoc]
    rfl
  · rw [htarget, finFamilyList_factorModule_eq_first_suffix]
    rw [List.append_assoc]
    rfl
  · dsimp only [i, P, a, b] at hsource htarget hdata ⊢
    let E := finFamilyList (factorModule e)
    have hbase : HEq (rawContractionAdjacentMergeData d (Fin.last k))
        (adjacentMergeAfter (leftLastCommonPrefix d) (ys := [])
          (compositionBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))) :=
      hdata.trans (heq_of_eq (adjacentMergeAfter_eq_prefix_head
        (leftLastCommonPrefix d) (ys := [])
        (compositionBoundaryMap (leftLastHeadDegreeProfile d)
          (leftLastTailDegreeProfile d))).symm)
    have hsuffix := adjacentMergeData_suffix_heq_left_last
      hsource htarget hbase E
    exact hsuffix.trans (adjacentMergeAfter_suffix_heq
      (leftLastCommonPrefix d)
      (compositionBoundaryMap (leftLastHeadDegreeProfile d)
        (leftLastTailDegreeProfile d)) E) |>.trans
        (heq_of_eq (adjacentMergeAfter_eq_prefix_head
          (leftLastCommonPrefix d) (ys := E)
          (compositionBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))))

theorem leftLastRawContractionTargetList_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    finFamilyList
        (recursiveMergedFactor (factorModule d) (Fin.last k)
          (rawContractionFactor d (Fin.last k))) =
      leftLastCommonPrefix d ++
        [compositionBoundaryModule (leftLastHeadDegreeProfile d)
          (leftLastTailDegreeProfile d)] := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let P := leftLastCommonPrefix d
  let a := leftLastHeadDegreeProfile d
  let b := leftLastTailDegreeProfile d
  have hi : i.succ = Fin.last (k + 1) := Fin.ext rfl
  have hsource : finFamilyList (factorModule d) =
      P ++ [factorModule a 0, factorModule b 0] :=
    finFamilyList_factorModule_eq_leftLast d
  have htargetLast : w.arrowTarget i.succ = Y := by
    rw [hi, arrowTarget_last_eq_target]
  have hraw : rawContractionFactor d i = compositionBoundaryModule a b := by
    unfold rawContractionFactor compositionBoundaryModule a b
    rw [htargetLast]
    rfl
  have hPlength : P.length = k := by
    simp [P, leftLastCommonPrefix, finFamilyList_eq_ofFn]
  have htake : (finFamilyList (factorModule d)).take i.val = P := by
    rw [hsource]
    simp [i, hPlength]
  have hdrop : (finFamilyList (factorModule d)).drop (i.val + 2) = [] := by
    rw [hsource]
    simp [i, hPlength]
  rw [finFamilyList_recursiveMerge_target, htake, hraw, hdrop]

theorem leftLastContractedFactorList_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    finFamilyList (factorModule (d.contract (Fin.last k))) =
      leftLastCommonPrefix d ++
        [compositionBoundaryModule (leftLastHeadDegreeProfile d)
          (leftLastTailDegreeProfile d)] :=
  (rawContractionTargetListEq_left_last_assembly d (Fin.last k)).trans
    (leftLastRawContractionTargetList_eq d)

theorem eraseIntermediate_leftLast_length_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} :
    (eraseIntermediate
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
        (Fin.last k)).length = k := by
  have h := eraseIntermediate_length
    ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
      (Fin.last k)
  change (eraseIntermediate
    ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
      (Fin.last k)).length + 1 = k + 1 at h
  omega


theorem erasePosition_leftLast_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} :
    erasePosition
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
        (Fin.last k) =
      Fin.last (eraseIntermediate
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
        (Fin.last k)).length := by
  apply Fin.ext
  simp only [erasePosition, Fin.val_cast, Fin.val_last,
    eraseIntermediate_leftLast_length_eq]

theorem leftLastContractedCompositionLeftPrefix_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionLeftPrefix (d.contract (Fin.last k)) = leftLastCommonPrefix d := by
  have hfull := leftLastContractedFactorList_eq d
  rw [finFamilyList_factorModule_eq_prefix_last] at hfull
  have hprefixLength : (compositionLeftPrefix (d.contract (Fin.last k))).length = k := by
    simp only [compositionLeftPrefix, finFamilyList_eq_ofFn, List.length_ofFn,
      eraseIntermediate_leftLast_length_eq]
  have hcommonLength : (leftLastCommonPrefix d).length = k := by
    simp only [leftLastCommonPrefix, finFamilyList_eq_ofFn, List.length_ofFn]
  have htake := congrArg (List.take k) hfull
  simpa [hprefixLength, hcommonLength] using htake

theorem leftLastContractedLastFactor_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule (d.contract (Fin.last k))
        (Fin.last (eraseIntermediate
          ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
            (Fin.last k)).length) =
      compositionBoundaryModule (leftLastHeadDegreeProfile d)
        (leftLastTailDegreeProfile d) := by
  have hfull := leftLastContractedFactorList_eq d
  rw [finFamilyList_factorModule_eq_prefix_last,
    leftLastContractedCompositionLeftPrefix_eq] at hfull
  have hsingle := List.append_cancel_left hfull
  exact List.cons.inj hsingle |>.1

theorem leftLastContractedCompositionMergeTensorMap_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix (d.contract (Fin.last k)))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (d.contract (Fin.last k)) e)).tensorMap
      (((@AdjacentMergeData.head
          (compositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))
          (factorModule e 0)
          (tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)
          (compositionRightSuffix e)
          (leftAssociatedBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)).prefix
              (leftLastCommonPrefix d)).tensorMap) := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let P := leftLastCommonPrefix d
  let a := leftLastHeadDegreeProfile d
  let b := leftLastTailDegreeProfile d
  have hposition : erasePosition w i =
      Fin.last (eraseIntermediate w i).length := erasePosition_leftLast_eq
  have hprefix : compositionLeftPrefix (d.contract i) = P :=
    leftLastContractedCompositionLeftPrefix_eq d
  have hlast : factorModule (d.contract i)
      (Fin.last (eraseIntermediate w i).length) = compositionBoundaryModule a b :=
    leftLastContractedLastFactor_eq d
  have hdegree : (d.contract i).arrowDegree
      (Fin.last (eraseIntermediate w i).length) =
      d.arrowDegree i.castSucc + d.arrowDegree i.succ := by
    rw [← hposition, contract_arrowDegree_at]
  have hcontractSource : (eraseIntermediate w i).arrowSource
      (Fin.last (eraseIntermediate w i).length) = w.arrowSource i.castSucc := by
    rw [← hposition, eraseIntermediate_arrowSource_at]
  have hcontractTarget : (eraseIntermediate w i).arrowTarget
      (Fin.last (eraseIntermediate w i).length) = Y :=
    arrowTarget_last_eq_target (eraseIntermediate w i)
  have hboundary : compositionBoundaryModule (d.contract i) e =
      tripleCompositionBoundaryModule a b e := by
    unfold compositionBoundaryModule tripleCompositionBoundaryModule a b
    rw [hcontractSource, hdegree]
    rfl
  have hmap : HEq (compositionBoundaryMap (d.contract i) e)
      (leftAssociatedBoundaryMap a b e) := by
    unfold compositionBoundaryMap leftAssociatedBoundaryMap a b
    apply dgCochainCompTensorOfEq_heq
    · exact hcontractSource
    · exact hcontractTarget
    · rfl
    · rfl
    · exact hdegree
    · rfl
    · change (d.contract i).arrowDegree
          (Fin.last (eraseIntermediate w i).length) + e.arrowDegree 0 =
        (d.arrowDegree i.castSucc + d.arrowDegree i.succ) + e.arrowDegree 0
      rw [hdegree]
  have hdata := (adjacentMergeAfter_congr
    (f := compositionBoundaryMap (d.contract i) e)
    (g := leftAssociatedBoundaryMap a b e)
    (ys := compositionRightSuffix e) (ys' := compositionRightSuffix e)
    hprefix hlast rfl hboundary rfl hmap).trans
      (heq_of_eq (adjacentMergeAfter_eq_prefix_head P
        (ys := compositionRightSuffix e) (leftAssociatedBoundaryMap a b e)))
  apply AdjacentMergeData.tensorMap_heq
  · rw [hprefix, hlast]
  · rw [hprefix, hboundary]
  · exact hdata


theorem leftLastContractedCompositionBoundaryList_eq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    compositionLeftPrefix (d.contract (Fin.last k)) ++
        compositionBoundaryModule (d.contract (Fin.last k)) e ::
          compositionRightSuffix e =
      leftLastCommonPrefix d ++
        tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e :: compositionRightSuffix e := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let a := leftLastHeadDegreeProfile d
  let b := leftLastTailDegreeProfile d
  have hposition : erasePosition w i =
      Fin.last (eraseIntermediate w i).length := erasePosition_leftLast_eq
  have hdegree : (d.contract i).arrowDegree
      (Fin.last (eraseIntermediate w i).length) =
      d.arrowDegree i.castSucc + d.arrowDegree i.succ := by
    rw [← hposition, contract_arrowDegree_at]
  have hcontractSource : (eraseIntermediate w i).arrowSource
      (Fin.last (eraseIntermediate w i).length) = w.arrowSource i.castSucc := by
    rw [← hposition, eraseIntermediate_arrowSource_at]
  have hcontractTarget : (eraseIntermediate w i).arrowTarget
      (Fin.last (eraseIntermediate w i).length) = Y :=
    arrowTarget_last_eq_target (eraseIntermediate w i)
  have hboundary : compositionBoundaryModule (d.contract i) e =
      tripleCompositionBoundaryModule a b e := by
    unfold compositionBoundaryModule tripleCompositionBoundaryModule a b
    rw [hcontractSource, hdegree]
    rfl
  rw [leftLastContractedCompositionLeftPrefix_eq, hboundary]

theorem leftLastCompositionBoundaryList_eq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e =
      leftLastCommonPrefix d ++
        factorModule (leftLastHeadDegreeProfile d) 0 ::
          zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e ::
            compositionRightSuffix e := by
  let w := ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y)
  let i : Fin (k + 1) := Fin.last k
  let b := leftLastTailDegreeProfile d
  have hi : i.succ = Fin.last (k + 1) := Fin.ext rfl
  have hmeet : w.arrowTarget i.castSucc = w.arrowSource i.succ :=
    arrowTarget_castSucc_eq_arrowSource_succ w i
  have hboundary : compositionBoundaryModule d e =
      zeroMiddleRightBoundaryModule b e := by
    unfold compositionBoundaryModule zeroMiddleRightBoundaryModule b
    rw [← hi, ← hmeet]
    rfl
  rw [compositionLeftPrefix_eq_leftLastCommonPrefix_append, hboundary]
  rw [List.append_assoc]
  rfl

theorem leftLastActualRightPair_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (summandCompositionRemainder d e ≫
        (rawContractionAdjacentMergeData (d.append e)
          (appendLeftContractionIndex (v := v) (Fin.last k))).tensorMap ≫
        eqToHom (congrArg tensorModuleList
          (rawContractionTargetListEq_left_last_assembly
            (d.append e) (appendLeftContractionIndex (v := v) (Fin.last k))).symm))
      (((@AdjacentMergeData.tail
          (factorModule (leftLastHeadDegreeProfile d) 0)
          (factorModule (leftLastTailDegreeProfile d) 0 ::
            factorModule e 0 :: compositionRightSuffix e)
          (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e ::
            compositionRightSuffix e)
          (@AdjacentMergeData.head
            (factorModule (leftLastTailDegreeProfile d) 0)
            (factorModule e 0)
            (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e)
            (compositionRightSuffix e)
            (zeroMiddleRightBoundaryMap (leftLastTailDegreeProfile d) e))).prefix
              (leftLastCommonPrefix d)).tensorMap ≫
        ((@AdjacentMergeData.head
          (factorModule (leftLastHeadDegreeProfile d) 0)
          (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e)
          (tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)
          (compositionRightSuffix e)
          (rightAssociatedBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)).prefix
              (leftLastCommonPrefix d)).tensorMap) := by
  let pR := eqToHom (congrArg tensorModuleList (compositionSourceListEq d e)) ≫
    eqToHom (congrArg tensorModuleList (compositionBoundaryListEq d e))
  let fR := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap
  let mR := eqToHom (congrArg tensorModuleList (compositionTargetListEq d e))
  let gR := (rawContractionAdjacentMergeData (d.append e)
    (appendLeftContractionIndex (v := v) (Fin.last k))).tensorMap
  let qR := eqToHom (congrArg tensorModuleList
    (rawContractionTargetListEq_left_last_assembly
      (d.append e) (appendLeftContractionIndex (v := v) (Fin.last k))).symm)
  let FR := ((@AdjacentMergeData.tail
    (factorModule (leftLastHeadDegreeProfile d) 0)
    (factorModule (leftLastTailDegreeProfile d) 0 ::
      factorModule e 0 :: compositionRightSuffix e)
    (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e ::
      compositionRightSuffix e)
    (@AdjacentMergeData.head
      (factorModule (leftLastTailDegreeProfile d) 0)
      (factorModule e 0)
      (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e)
      (compositionRightSuffix e)
      (zeroMiddleRightBoundaryMap (leftLastTailDegreeProfile d) e))).prefix
        (leftLastCommonPrefix d)).tensorMap
  let GR := ((@AdjacentMergeData.head
    (factorModule (leftLastHeadDegreeProfile d) 0)
    (zeroMiddleRightBoundaryModule (leftLastTailDegreeProfile d) e)
    (tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
      (leftLastTailDegreeProfile d) e)
    (compositionRightSuffix e)
    (rightAssociatedBoundaryMap (leftLastHeadDegreeProfile d)
      (leftLastTailDegreeProfile d) e)).prefix
        (leftLastCommonPrefix d)).tensorMap
  have hSList : finFamilyList (factorModule d) ++
      finFamilyList (factorModule e) =
      leftLastCommonPrefix d ++
        factorModule (leftLastHeadDegreeProfile d) 0 ::
          factorModule (leftLastTailDegreeProfile d) 0 ::
            factorModule e 0 :: compositionRightSuffix e := by
    rw [finFamilyList_factorModule_eq_leftLast,
      finFamilyList_factorModule_eq_first_suffix]
    rw [List.append_assoc]
    rfl
  have hUList := leftLastCompositionBoundaryList_eq d e
  have hVList := leftLastRawContractionAppendTargetList_eq d e
  have h := transportedPair₂_heq
    (p := pR) (f := fR) (m := mR) (g := gR)
    (q₁ := qR) (q₂ := 𝟙 _) (F := FR) (G := GR)
    (hS := congrArg tensorModuleList hSList)
    (hA := congrArg tensorModuleList
      ((compositionSourceListEq d e).trans (compositionBoundaryListEq d e)))
    (hB := congrArg tensorModuleList hUList)
    (hC := congrArg tensorModuleList
      ((compositionTargetListEq d e).symm.trans hUList))
    (hD := congrArg tensorModuleList hVList)
    (hE := congrArg tensorModuleList
      ((rawContractionTargetListEq_left_last_assembly (d.append e)
        (appendLeftContractionIndex (v := v) (Fin.last k))).trans hVList))
    (hT := congrArg tensorModuleList
      ((rawContractionTargetListEq_left_last_assembly (d.append e)
        (appendLeftContractionIndex (v := v) (Fin.last k))).trans hVList))
    (hp := eqToHom_comp_heq_id _ _)
    (hf := leftLastCompositionMergeTensorMap_heq d e)
    (hm := test_eqToHom_heq_id _)
    (hg := leftLastRawContractionAppendTensorMap_heq d e)
    (hq₁ := test_eqToHom_heq_id _)
    (hq₂ := HEq.rfl)
  simpa only [pR, fR, mR, gR, qR, FR, GR, summandCompositionRemainder,
    Category.assoc, Category.comp_id] using h

theorem leftLastActualLeftPair_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
          ((rawContractionAdjacentMergeData d (Fin.last k)).tensorMap ≫
            eqToHom (congrArg tensorModuleList
              (rawContractionTargetListEq_left_last_assembly d
                (Fin.last k)).symm)) ≫
        summandCompositionRemainder (d.contract (Fin.last k)) e)
      (((@AdjacentMergeData.head
          (factorModule (leftLastHeadDegreeProfile d) 0)
          (factorModule (leftLastTailDegreeProfile d) 0)
          (compositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))
          (factorModule e 0 :: compositionRightSuffix e)
          (compositionBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))).prefix
              (leftLastCommonPrefix d)).tensorMap ≫
        ((@AdjacentMergeData.head
          (compositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d))
          (factorModule e 0)
          (tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)
          (compositionRightSuffix e)
          (leftAssociatedBoundaryMap (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) e)).prefix
              (leftLastCommonPrefix d)).tensorMap) := by
  let fL := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
    (rawContractionAdjacentMergeData d (Fin.last k)).tensorMap
  let mL := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
      (eqToHom (congrArg tensorModuleList
        (rawContractionTargetListEq_left_last_assembly d (Fin.last k)).symm)) ≫
    eqToHom (congrArg tensorModuleList
      (compositionSourceListEq (d.contract (Fin.last k)) e)) ≫
    eqToHom (congrArg tensorModuleList
      (compositionBoundaryListEq (d.contract (Fin.last k)) e))
  let gL := (adjacentMergeAfter
    (compositionLeftPrefix (d.contract (Fin.last k)))
    (ys := compositionRightSuffix e)
    (compositionBoundaryMap (d.contract (Fin.last k)) e)).tensorMap
  let qL := eqToHom (congrArg tensorModuleList
    (compositionTargetListEq (d.contract (Fin.last k)) e))
  let FL := ((@AdjacentMergeData.head
    (factorModule (leftLastHeadDegreeProfile d) 0)
    (factorModule (leftLastTailDegreeProfile d) 0)
    (compositionBoundaryModule (leftLastHeadDegreeProfile d)
      (leftLastTailDegreeProfile d))
    (factorModule e 0 :: compositionRightSuffix e)
    (compositionBoundaryMap (leftLastHeadDegreeProfile d)
      (leftLastTailDegreeProfile d))).prefix (leftLastCommonPrefix d)).tensorMap
  let GL := ((@AdjacentMergeData.head
    (compositionBoundaryModule (leftLastHeadDegreeProfile d)
      (leftLastTailDegreeProfile d))
    (factorModule e 0)
    (tripleCompositionBoundaryModule (leftLastHeadDegreeProfile d)
      (leftLastTailDegreeProfile d) e)
    (compositionRightSuffix e)
    (leftAssociatedBoundaryMap (leftLastHeadDegreeProfile d)
      (leftLastTailDegreeProfile d) e)).prefix (leftLastCommonPrefix d)).tensorMap
  have hSList : finFamilyList (factorModule d) ++
      finFamilyList (factorModule e) =
      leftLastCommonPrefix d ++
        factorModule (leftLastHeadDegreeProfile d) 0 ::
          factorModule (leftLastTailDegreeProfile d) 0 ::
            factorModule e 0 :: compositionRightSuffix e := by
    rw [finFamilyList_factorModule_eq_leftLast,
      finFamilyList_factorModule_eq_first_suffix]
    rw [List.append_assoc]
    rfl
  have hUList : finFamilyList
        (recursiveMergedFactor (factorModule d) (Fin.last k)
          (rawContractionFactor d (Fin.last k))) ++
      finFamilyList (factorModule e) =
      leftLastCommonPrefix d ++
        compositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) ::
          factorModule e 0 :: compositionRightSuffix e := by
    rw [leftLastRawContractionTargetList_eq,
      finFamilyList_factorModule_eq_first_suffix]
    rw [List.append_assoc]
    rfl
  have hCList : finFamilyList (factorModule (d.contract (Fin.last k))) ++
      finFamilyList (factorModule e) =
      leftLastCommonPrefix d ++
        compositionBoundaryModule (leftLastHeadDegreeProfile d)
            (leftLastTailDegreeProfile d) ::
          factorModule e 0 :: compositionRightSuffix e := by
    rw [leftLastContractedFactorList_eq,
      finFamilyList_factorModule_eq_first_suffix]
    rw [List.append_assoc]
    rfl
  have hVList := leftLastContractedCompositionBoundaryList_eq d e
  have h := transportedPair₂_heq
    (p := 𝟙 (tensorModuleList
      (finFamilyList (factorModule d) ++ finFamilyList (factorModule e))))
    (f := fL) (m := mL) (g := gL)
    (q₁ := qL) (q₂ := 𝟙 _) (F := FL) (G := GL)
    (hS := congrArg tensorModuleList hSList)
    (hA := rfl)
    (hB := congrArg tensorModuleList hUList)
    (hC := congrArg tensorModuleList
      ((compositionBoundaryListEq (d.contract (Fin.last k)) e).symm.trans
        ((compositionSourceListEq (d.contract (Fin.last k)) e).symm.trans hCList)))
    (hD := congrArg tensorModuleList hVList)
    (hE := congrArg tensorModuleList
      ((compositionTargetListEq (d.contract (Fin.last k)) e).symm.trans hVList))
    (hT := congrArg tensorModuleList
      ((compositionTargetListEq (d.contract (Fin.last k)) e).symm.trans hVList))
    (hp := HEq.rfl)
    (hf := leftLastRawContractionWhiskerTensorMap_heq d e)
    (hm := by
      dsimp only [mL]
      rw [tensorModuleListWhiskerRight_eqToHom]
      · exact eqToHom_comp₃_heq_id _ _ _
      · exact (rawContractionTargetListEq_left_last_assembly d
          (Fin.last k)).symm)
    (hg := leftLastContractedCompositionMergeTensorMap_heq d e)
    (hq₁ := test_eqToHom_heq_id _)
    (hq₂ := HEq.rfl)
  rw [tensorModuleListWhiskerRight_comp]
  have htrim : HEq (fL ≫ mL ≫ gL ≫ qL) (FL ≫ GL) := by
    apply HEq.trans ?_ h
    apply heq_of_eq
    rw [Category.comp_id]
    change fL ≫ mL ≫ gL ≫ qL =
      (𝟙 _ ≫ fL) ≫ mL ≫ gL ≫ qL
    rw [Category.id_comp]
  simpa [fL, mL, gL, qL, FL, GL, summandCompositionRemainder,
    summandModule] using htrim


theorem summandCompositionRemainder_contraction_append_left_last_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (summandCompositionRemainder d e ≫
        contractionTensorMap (d.append e)
          (appendLeftContractionIndex (v := v) (Fin.last k)))
      (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
          (contractionTensorMap d (Fin.last k)) ≫
        summandCompositionRemainder (d.contract (Fin.last k)) e) := by
  let R := summandCompositionRemainder d e
  let C := contractionTensorMap (d.append e)
    (appendLeftContractionIndex (v := v) (Fin.last k))
  let C₀ := (rawContractionAdjacentMergeData (d.append e)
    (appendLeftContractionIndex (v := v) (Fin.last k))).tensorMap
  let D := contractionTensorMap d (Fin.last k)
  let D₀ := (rawContractionAdjacentMergeData d (Fin.last k)).tensorMap
  let R' := summandCompositionRemainder (d.contract (Fin.last k)) e
  let hAppendTargetList := rawContractionTargetListEq_left_last_assembly
    (d.append e) (appendLeftContractionIndex (v := v) (Fin.last k))
  let hAppendTarget := congrArg tensorModuleList hAppendTargetList
  let hDTargetList := rawContractionTargetListEq_left_last_assembly d (Fin.last k)
  let C₁ := C₀ ≫ eqToHom hAppendTarget.symm
  let D₁ := D₀ ≫ eqToHom (congrArg tensorModuleList hDTargetList.symm)
  let W := tensorModuleListWhiskerRight (finFamilyList (factorModule e)) D
  let W₁ := tensorModuleListWhiskerRight (finFamilyList (factorModule e)) D₁
  have hC : HEq C C₀ := by
    have hrecursive := contractionTensorMap_recursive_heq
      (d.append e) (appendLeftContractionIndex (v := v) (Fin.last k))
    exact hrecursive.trans
      (hrecursive.symm.trans (test_contractionTensorMap_raw_heq _ _))
  have hD : HEq D D₀ := by
    have hrecursive := contractionTensorMap_recursive_heq d (Fin.last k)
    exact hrecursive.trans
      (hrecursive.symm.trans (test_contractionTensorMap_raw_heq d (Fin.last k)))
  have hC₁ : C = C₁ := eq_of_heq
    (hC.trans (CategoryTheory.comp_eqToHom_heq C₀ hAppendTarget.symm).symm)
  have hD₁ : D = D₁ := eq_of_heq
    (hD.trans (CategoryTheory.comp_eqToHom_heq D₀
      (congrArg tensorModuleList hDTargetList.symm)).symm)
  have hW₁ : W = W₁ := congrArg
    (tensorModuleListWhiskerRight (finFamilyList (factorModule e))) hD₁
  change HEq (R ≫ C) (W ≫ R')
  rw [hC₁, hW₁]
  have hmiddle := (leftLastNormalizedPairTensorMap_heq d e).symm
  apply transportedPairAssembler_heq (hmiddle := hmiddle)
  · simpa only [R, C₁, C₀, rawContractionAdjacentMergeData,
      Category.assoc] using leftLastActualRightPair_heq d e
  · simpa only [W₁, D₁, D₀, R', rawContractionAdjacentMergeData,
      Category.assoc] using leftLastActualLeftPair_heq d e

theorem leftLastContractAppendSummandModule_eq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    summandModule
        ((d.append e).contract (appendLeftContractionIndex (v := v) (Fin.last k))) =
      summandModule ((d.contract (Fin.last k)).append e) := by
  unfold summandModule
  apply congrArg tensorModuleList
  exact
    ((rawContractionTargetListEq_left_last_assembly (d.append e)
      (appendLeftContractionIndex (v := v) (Fin.last k))).trans
        (leftLastRawContractionAppendTargetList_eq d e)).trans
      ((finFamilyList_factorModule_append_boundary
        (d.contract (Fin.last k)) e).trans
          (leftLastContractedCompositionBoundaryList_eq d e)).symm

theorem summandCompositionMap_contraction_append_left_last_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) :
    HEq
      (summandCompositionMap d e ≫
        contractionTensorMap (d.append e)
          (appendLeftContractionIndex (v := v) (Fin.last k)))
      ((contractionTensorMap d (Fin.last k) ⊗ₘ 𝟙 (summandModule e)) ≫
        summandCompositionMap (d.contract (Fin.last k)) e) := by
  rw [summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized]
  rw [normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder]
  dsimp only [summandModule]
  simp only [Category.assoc]
  rw [tensorModuleListAppendIso_whiskerRight_assoc]
  let A := (tensorModuleListAppendIso (finFamilyList (factorModule d))
    (finFamilyList (factorModule e))).hom
  let R := summandCompositionRemainder d e
  let C := contractionTensorMap (d.append e)
    (appendLeftContractionIndex (v := v) (Fin.last k))
  let W := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
    (contractionTensorMap d (Fin.last k))
  let R' := summandCompositionRemainder (d.contract (Fin.last k)) e
  change HEq (A ≫ R ≫ C) (A ≫ W ≫ R')
  have hrem := summandCompositionRemainder_contraction_append_left_last_heq d e
  have hA : HEq A A := HEq.rfl
  have hpre : HEq (A ≫ (R ≫ C)) (A ≫ (W ≫ R')) :=
    CategoryTheory.heq_comp rfl rfl
      (leftLastContractAppendSummandModule_eq d e) hA hrem
  simpa only [Category.assoc] using hpre

def rawContractionTargetListEq_left_castSucc_case
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    finFamilyList (recursiveMergedFactor (factorModule d) i
        (rawContractionFactor d i)) =
      finFamilyList (factorModule (d.contract i)) :=
  (congrArg finFamilyList (test_rawContractionTarget_eq d i)).trans
    (contractedFactorsOldIndex_eq d i)

theorem tensorModuleListWhiskerRight_heq_left_castSucc_case
    {Ms Ns Ms' Ns' : List (ModuleCat.{0} ℤ)}
    (hMs : Ms = Ms') (hNs : Ns = Ns') (Ps : List (ModuleCat.{0} ℤ))
    {f : tensorModuleList Ms ⟶ tensorModuleList Ns}
    {f' : tensorModuleList Ms' ⟶ tensorModuleList Ns'} (h : HEq f f') :
    HEq (tensorModuleListWhiskerRight Ps f)
      (tensorModuleListWhiskerRight Ps f') := by
  subst Ms'
  subst Ns'
  have hff : f = f' := eq_of_heq h
  subst f'
  rfl

theorem AdjacentMergePairHCoherence.suffix_head_left_castSucc_case
    {source target : List (ModuleCat.{0} ℤ)}
    (f : AdjacentMergeData source target)
    {A B Q : ModuleCat.{0} ℤ} {zs : List (ModuleCat.{0} ℤ)}
    (g : A ⊗ B ⟶ Q) :
    AdjacentMergePairHCoherence
      (f.suffix (A :: B :: zs))
      (adjacentMergeAfter target (ys := zs) g)
      (adjacentMergeAfter source (ys := zs) g)
      (f.suffix (Q :: zs)) := by
  induction f with
  | @head M N P Ms h =>
      simpa [AdjacentMergeData.suffix] using
        (AdjacentMergePairHCoherence.head_tail h
          (adjacentMergeAfter Ms (ys := zs) g))
  | @tail M source target f ih =>
      exact AdjacentMergePairHCoherence.tail ih

theorem AdjacentMergeData.suffix_suffix_left_castSucc_case
    {source target : List (ModuleCat.{0} ℤ)}
    (f : AdjacentMergeData source target)
    (xs ys : List (ModuleCat.{0} ℤ)) :
    HEq ((f.suffix xs).suffix ys) (f.suffix (xs ++ ys)) := by
  induction f with
  | @head M N P Ms h =>
      exact adjacentMergeAfter_congr (xs := []) (xs' := [])
        rfl rfl rfl rfl (List.append_assoc Ms xs ys) HEq.rfl
  | @tail M source target f ih =>
      exact adjacentMergeData_tail_heq rfl
        (List.append_assoc source xs ys)
        (List.append_assoc target xs ys) ih

theorem factorModule_contract_left_castSucc_last_case
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (i : Fin (k + 1)) :
    factorModule (d.contract i.castSucc) (Fin.last (k + 1)) =
      factorModule d (Fin.last (k + 2)) := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  let j : Fin ((eraseIntermediate w i.castSucc).length + 1) :=
    Fin.last (k + 1)
  have hafter : i.castSucc < eraseFactorIndex w i.castSucc j := by
    change i.val < k + 1
    exact i.isLt
  have hold : (eraseFactorIndex w i.castSucc j).succ =
      Fin.last (k + 2) := Fin.ext rfl
  exact (factorModule_contract_after_eq d i.castSucc j hafter).symm.trans
    (congrArg (factorModule d) hold)

theorem compositionBoundaryModule_contract_left_castSucc_case
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
    compositionBoundaryModule (d.contract i.castSucc) e =
      compositionBoundaryModule d e := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  let j : Fin ((eraseIntermediate w i.castSucc).length + 1) :=
    Fin.last (k + 1)
  have hafter : i.castSucc < eraseFactorIndex w i.castSucc j := by
    change i.val < k + 1
    exact i.isLt
  have hold : (eraseFactorIndex w i.castSucc j).succ =
      Fin.last (k + 2) := Fin.ext rfl
  unfold compositionBoundaryModule
  change
    (dgHomZModuleCochainComplex
      ((eraseIntermediate w i.castSucc).arrowSource j)
      (v.arrowTarget 0)).X
        ((d.contract i.castSucc).arrowDegree j + e.arrowDegree 0) = _
  rw [eraseIntermediate_arrowSource_of_after w i.castSucc j hafter,
    contract_arrowDegree_of_after d i.castSucc j hafter, hold]

theorem compositionBoundaryMap_contract_left_castSucc_case
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
    HEq (compositionBoundaryMap (d.contract i.castSucc) e)
      (compositionBoundaryMap d e) := by
  let w : DrinfeldWord X Y :=
    { length := k + 2, intermediate := intermediate }
  let j : Fin ((eraseIntermediate w i.castSucc).length + 1) :=
    Fin.last (k + 1)
  have hafter : i.castSucc < eraseFactorIndex w i.castSucc j := by
    change i.val < k + 1
    exact i.isLt
  have hold : (eraseFactorIndex w i.castSucc j).succ =
      Fin.last (k + 2) := Fin.ext rfl
  unfold compositionBoundaryMap
  apply dgCochainCompTensorOfEq_heq
  · exact (eraseIntermediate_arrowSource_of_after w i.castSucc j hafter).trans
      (congrArg w.arrowSource hold)
  · exact (eraseIntermediate_arrowTarget_of_after w i.castSucc j hafter).trans
      (congrArg w.arrowTarget hold)
  · rfl
  · rfl
  · exact (contract_arrowDegree_of_after d i.castSucc j hafter).trans
      (congrArg d.arrowDegree hold)
  · rfl
  · exact congrArg (· + e.arrowDegree 0)
      ((contract_arrowDegree_of_after d i.castSucc j hafter).trans
        (congrArg d.arrowDegree hold))

theorem summandCompositionRemainder_contraction_append_left_castSucc_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
  HEq
    (summandCompositionRemainder d e ≫
      contractionTensorMap (d.append e)
        (appendLeftContractionIndex i.castSucc))
    (tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (contractionTensorMap d i.castSucc) ≫
      summandCompositionRemainder (d.contract i.castSucc) e) := by
  let R := summandCompositionRemainder d e
  let C := contractionTensorMap (d.append e)
    (appendLeftContractionIndex i.castSucc)
  let C₀ := (rawContractionAdjacentMergeData (d.append e)
    (appendLeftContractionIndex i.castSucc)).tensorMap
  let W := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
    (contractionTensorMap d i.castSucc)
  let W₀ := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
    (rawContractionAdjacentMergeData d i.castSucc).tensorMap
  let R' := summandCompositionRemainder (d.contract i.castSucc) e
  let hCList := rawContractionTargetListEq_left_castSucc_case (d.append e)
    (appendLeftContractionIndex i.castSucc)
  let hWList := rawContractionTargetListEq_left_castSucc_case d i.castSucc
  let hWAppend := congrArg (· ++ finFamilyList (factorModule e)) hWList
  let T := eqToHom (congrArg tensorModuleList hWAppend)
  have hC : HEq C C₀ := test_contractionTensorMap_raw_heq _ _
  have hW : HEq W W₀ := tensorModuleListWhiskerRight_heq_left_castSucc_case
    rfl hWList.symm _ (test_contractionTensorMap_raw_heq d i.castSucc)
  have hleft : HEq (R ≫ C) (R ≫ C₀) :=
    CategoryTheory.heq_comp rfl rfl
      (congrArg tensorModuleList hCList).symm HEq.rfl hC
  have hright : HEq (W ≫ R') (W₀ ≫ T ≫ R') := by
    apply CategoryTheory.heq_comp rfl
      (congrArg tensorModuleList hWAppend).symm rfl hW
    exact (CategoryTheory.eqToHom_comp_heq R'
      (congrArg tensorModuleList hWAppend)).symm
  refine hleft.trans ?_ |>.trans hright.symm
  dsimp [R, C₀, W₀, T, R', summandCompositionRemainder]
  rw [← AdjacentMergeData.suffix_tensorMap]
  let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
    fun q ↦ factorModule d q.castSucc
  let Mtarget : List (ModuleCat.{0} ℤ) :=
    finFamilyList (recursiveMergedFactor Mleft i
      (rawContractionFactor d i.castSucc))
  let A := factorModule d (Fin.last (k + 2))
  let B := factorModule e 0
  let Q := compositionBoundaryModule d e
  let zs := compositionRightSuffix e
  let F := recursiveAdjacentMergeDataOfFn Mleft i
    (rawContractionFactor d i.castSucc) (adjacentFactorComposition d i.castSucc)
  let F₁ := adjacentMergeAfter (finFamilyList Mleft)
    (ys := zs) (compositionBoundaryMap d e)
  let G₁ := F.suffix (Q :: zs)
  let F₂ := F.suffix (A :: B :: zs)
  let G₂ := adjacentMergeAfter Mtarget
    (ys := zs) (compositionBoundaryMap d e)
  have hmiddle : HEq (F₁.tensorMap ≫ G₁.tensorMap)
      (F₂.tensorMap ≫ G₂.tensorMap) := by
    exact (AdjacentMergePairHCoherence.suffix_head_left_castSucc_case F
      (zs := zs) (compositionBoundaryMap d e)).tensorMap_heq.symm
  have hF₁Data : HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e) (compositionBoundaryMap d e)) F₁ := by
    exact HEq.rfl
  have hG₁Data : HEq
      (rawContractionAdjacentMergeData (d.append e)
        (appendLeftContractionIndex i.castSucc)) G₁ := by
    exact rawContractionAdjacentMergeData_append_left_castSucc d e i
  have hrawD : HEq (rawContractionAdjacentMergeData d i.castSucc)
      (F.suffix [A]) := by
    unfold rawContractionAdjacentMergeData
    exact recursiveAdjacentMergeDataOfFn_castSucc_suffix
      (factorModule d) i (rawContractionFactor d i.castSucc)
        (adjacentFactorComposition d i.castSucc)
  have hrawTarget := rawContractionTargetList_castSucc_append_last d i
  have hF₂Data : HEq
      ((rawContractionAdjacentMergeData d i.castSucc).suffix
        (finFamilyList (factorModule e))) F₂ := by
    have hSuffix := adjacentMergeData_suffix_heq
      (finFamilyList_factorModule_eq_prefix_last d) hrawTarget hrawD
      (finFamilyList (factorModule e))
    have hPs : [A] ++ finFamilyList (factorModule e) = A :: B :: zs := by
      rw [finFamilyList_factorModule_eq_first_suffix]
      rfl
    have hAssoc : HEq
        ((F.suffix [A]).suffix (finFamilyList (factorModule e))) F₂ := by
      have h := F.suffix_suffix_left_castSucc_case [A]
        (finFamilyList (factorModule e))
      rw [hPs] at h
      exact h
    exact hSuffix.trans hAssoc
  have hcontractList : finFamilyList (factorModule (d.contract i.castSucc)) =
      Mtarget ++ [A] := hWList.symm.trans hrawTarget
  have hlast : factorModule (d.contract i.castSucc) (Fin.last (k + 1)) = A :=
    factorModule_contract_left_castSucc_last_case d i
  have hprefixLast : compositionLeftPrefix (d.contract i.castSucc) ++
      [factorModule (d.contract i.castSucc) (Fin.last (k + 1))] =
      Mtarget ++ [A] :=
    (finFamilyList_factorModule_eq_prefix_last
      (d.contract i.castSucc)).symm.trans hcontractList
  rw [hlast] at hprefixLast
  have hprefix : compositionLeftPrefix (d.contract i.castSucc) = Mtarget :=
    List.append_cancel_right hprefixLast
  have hQ := compositionBoundaryModule_contract_left_castSucc_case d e i
  have hG₂Data : HEq
      (adjacentMergeAfter (compositionLeftPrefix (d.contract i.castSucc))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (d.contract i.castSucc) e)) G₂ := by
    exact adjacentMergeAfter_congr hprefix hlast rfl hQ rfl
      (compositionBoundaryMap_contract_left_castSucc_case d e i)
  have hF₁Map : HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap d e)).tensorMap F₁.tensorMap := by
    exact AdjacentMergeData.tensorMap_heq rfl rfl hF₁Data
  have hG₁Map : HEq
      (rawContractionAdjacentMergeData (d.append e)
        (appendLeftContractionIndex i.castSucc)).tensorMap G₁.tensorMap := by
    apply AdjacentMergeData.tensorMap_heq
    · exact finFamilyList_factorModule_append_boundary d e
    · exact rawContractionTargetList_append_left_castSucc d e i
    · exact hG₁Data
  have hF₂Target : finFamilyList
        (recursiveMergedFactor (factorModule d) i.castSucc
          (rawContractionFactor d i.castSucc)) ++
        finFamilyList (factorModule e) =
      Mtarget ++ A :: B :: zs := by
    rw [hrawTarget, finFamilyList_factorModule_eq_first_suffix]
    simp only [List.append_assoc, List.singleton_append]
    change Mtarget ++ A :: B :: zs = Mtarget ++ A :: B :: zs
    rfl
  have hF₂Map : HEq
      (((rawContractionAdjacentMergeData d i.castSucc).suffix
        (finFamilyList (factorModule e))).tensorMap) F₂.tensorMap := by
    apply AdjacentMergeData.tensorMap_heq
    · exact finFamilyList_factorModule_pair_boundary d e
    · exact hF₂Target
    · exact hF₂Data
  have hG₂Source : compositionLeftPrefix (d.contract i.castSucc) ++
        factorModule (d.contract i.castSucc) (Fin.last (k + 1)) ::
          factorModule e 0 :: compositionRightSuffix e =
      Mtarget ++ A :: B :: zs := by
    rw [hprefix, hlast]
  have hG₂Target : compositionLeftPrefix (d.contract i.castSucc) ++
        compositionBoundaryModule (d.contract i.castSucc) e ::
          compositionRightSuffix e =
      Mtarget ++ Q :: zs := by
    rw [hprefix, hQ]
  have hG₂Map : HEq
      (adjacentMergeAfter (compositionLeftPrefix (d.contract i.castSucc))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (d.contract i.castSucc) e)).tensorMap
      G₂.tensorMap := by
    exact AdjacentMergeData.tensorMap_heq hG₂Source hG₂Target hG₂Data
  let hS := congrArg tensorModuleList (compositionSourceListEq d e)
  let hBdy := congrArg tensorModuleList (compositionBoundaryListEq d e)
  let hTgt := congrArg tensorModuleList (compositionTargetListEq d e)
  have hF₁Source : finFamilyList (factorModule d) ++
      finFamilyList (factorModule e) =
      finFamilyList Mleft ++ A :: B :: zs :=
    finFamilyList_factorModule_pair_boundary d e
  have hF₁Target : compositionLeftPrefix d ++
      compositionBoundaryModule d e :: compositionRightSuffix e =
      finFamilyList Mleft ++ Q :: zs := rfl
  have hG₁Source : finFamilyList (factorModule (d.append e)) =
      finFamilyList Mleft ++ Q :: zs :=
    finFamilyList_factorModule_append_boundary d e
  have hG₁Target : finFamilyList
      (recursiveMergedFactor (factorModule (d.append e))
        (appendLeftContractionIndex i.castSucc)
        (rawContractionFactor (d.append e)
          (appendLeftContractionIndex i.castSucc))) =
      Mtarget ++ Q :: zs := rawContractionTargetList_append_left_castSucc d e i
  have hcanonicalLeft : HEq
      ((eqToHom hS ≫ eqToHom hBdy ≫
          (adjacentMergeAfter (compositionLeftPrefix d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)).tensorMap ≫ eqToHom hTgt) ≫
        (rawContractionAdjacentMergeData (d.append e)
          (appendLeftContractionIndex i.castSucc)).tensorMap)
      (F₁.tensorMap ≫ G₁.tensorMap) := by
    simpa only [Category.assoc, Category.comp_id] using
      (transportedPair₂_heq
        (congrArg tensorModuleList hF₁Source)
        (hS.trans hBdy)
        (congrArg tensorModuleList hF₁Target)
        (congrArg tensorModuleList hG₁Source)
        (congrArg tensorModuleList hG₁Target)
        (congrArg tensorModuleList hG₁Target)
        (congrArg tensorModuleList hG₁Target)
        (eqToHom hS ≫ eqToHom hBdy)
        (adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e)).tensorMap
        (eqToHom hTgt)
        (rawContractionAdjacentMergeData (d.append e)
          (appendLeftContractionIndex i.castSucc)).tensorMap
        (𝟙 _) (𝟙 _) F₁.tensorMap G₁.tensorMap
        (eqToHom_comp_heq_id hS hBdy) hF₁Map
        (test_eqToHom_heq_id hTgt) hG₁Map HEq.rfl HEq.rfl)
  have hF₂Source : finFamilyList (factorModule d) ++
      finFamilyList (factorModule e) = finFamilyList Mleft ++ A :: B :: zs := by
    exact hF₁Source
  have hG₂AppendTarget : finFamilyList
      (factorModule ((d.contract i.castSucc).append e)) =
      Mtarget ++ Q :: zs :=
    (finFamilyList_factorModule_append_boundary
      (d.contract i.castSucc) e).trans hG₂Target
  let hS' := congrArg tensorModuleList
    (compositionSourceListEq (d.contract i.castSucc) e)
  let hBdy' := congrArg tensorModuleList
    (compositionBoundaryListEq (d.contract i.castSucc) e)
  let hTgt' := congrArg tensorModuleList
    (compositionTargetListEq (d.contract i.castSucc) e)
  let hW' := congrArg tensorModuleList hWAppend
  have hcanonicalRight : HEq
      (((rawContractionAdjacentMergeData d i.castSucc).suffix
          (finFamilyList (factorModule e))).tensorMap ≫
        eqToHom hW' ≫ eqToHom hS' ≫ eqToHom hBdy' ≫
        (adjacentMergeAfter (compositionLeftPrefix (d.contract i.castSucc))
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap (d.contract i.castSucc) e)).tensorMap ≫
        eqToHom hTgt')
      (F₂.tensorMap ≫ G₂.tensorMap) := by
    have h := transportedPair₂_heq
      (p := 𝟙 (tensorModuleList
        (finFamilyList (factorModule d) ++ finFamilyList (factorModule e))))
      (f := ((rawContractionAdjacentMergeData d i.castSucc).suffix
        (finFamilyList (factorModule e))).tensorMap)
      (m := eqToHom hW' ≫ eqToHom hS' ≫ eqToHom hBdy')
      (g := (adjacentMergeAfter
        (compositionLeftPrefix (d.contract i.castSucc))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (d.contract i.castSucc) e)).tensorMap)
      (q₁ := eqToHom hTgt') (q₂ := 𝟙 _)
      (F := F₂.tensorMap) (G := G₂.tensorMap)
      (hS := congrArg tensorModuleList hF₂Source)
      (hA := rfl)
      (hB := congrArg tensorModuleList hF₂Target)
      (hC := congrArg tensorModuleList hG₂Source)
      (hD := congrArg tensorModuleList hG₂Target)
      (hE := congrArg tensorModuleList hG₂AppendTarget)
      (hT := congrArg tensorModuleList hG₂AppendTarget)
      (hp := HEq.rfl) (hf := hF₂Map)
      (hm := eqToHom_comp₃_heq_id hW' hS' hBdy')
      (hg := hG₂Map) (hq₁ := test_eqToHom_heq_id hTgt')
      (hq₂ := HEq.rfl)
    exact h
  exact hcanonicalLeft.trans hmiddle |>.trans hcanonicalRight.symm

theorem summandModule_contract_append_left_castSucc_case
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
    summandModule
        ((d.append e).contract (appendLeftContractionIndex i.castSucc)) =
      summandModule ((d.contract i.castSucc).append e) := by
  let Mleft : Fin (k + 2) → ModuleCat.{0} ℤ :=
    fun q ↦ factorModule d q.castSucc
  let Mtarget : List (ModuleCat.{0} ℤ) :=
    finFamilyList (recursiveMergedFactor Mleft i
      (rawContractionFactor d i.castSucc))
  let Q := compositionBoundaryModule d e
  let zs := compositionRightSuffix e
  let hAppend := rawContractionTargetListEq_left_castSucc_case (d.append e)
    (appendLeftContractionIndex i.castSucc)
  let hD := rawContractionTargetListEq_left_castSucc_case d i.castSucc
  have hrawTarget := rawContractionTargetList_castSucc_append_last d i
  have hcontractList : finFamilyList (factorModule (d.contract i.castSucc)) =
      Mtarget ++ [factorModule d (Fin.last (k + 2))] :=
    hD.symm.trans hrawTarget
  have hlast := factorModule_contract_left_castSucc_last_case d i
  have hprefixLast : compositionLeftPrefix (d.contract i.castSucc) ++
      [factorModule (d.contract i.castSucc) (Fin.last (k + 1))] =
      Mtarget ++ [factorModule d (Fin.last (k + 2))] :=
    (finFamilyList_factorModule_eq_prefix_last
      (d.contract i.castSucc)).symm.trans hcontractList
  rw [hlast] at hprefixLast
  have hprefix : compositionLeftPrefix (d.contract i.castSucc) = Mtarget :=
    List.append_cancel_right hprefixLast
  have hQ := compositionBoundaryModule_contract_left_castSucc_case d e i
  have hboundary : compositionLeftPrefix (d.contract i.castSucc) ++
      compositionBoundaryModule (d.contract i.castSucc) e ::
        compositionRightSuffix e = Mtarget ++ Q :: zs := by
    rw [hprefix, hQ]
  unfold summandModule
  apply congrArg tensorModuleList
  exact (hAppend.symm.trans
      (rawContractionTargetList_append_left_castSucc d e i)).trans
    ((finFamilyList_factorModule_append_boundary
      (d.contract i.castSucc) e).trans hboundary).symm

theorem summandCompositionMap_contraction_append_left_castSucc_heq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 2) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {n m : ℤ}
    (d : DegreeProfile
      ({ length := k + 2, intermediate := intermediate } : DrinfeldWord X Y) n)
    (e : DegreeProfile v m) (i : Fin (k + 1)) :
  HEq
    (summandCompositionMap d e ≫
      contractionTensorMap (d.append e)
        (appendLeftContractionIndex i.castSucc))
    ((contractionTensorMap d i.castSucc ⊗ₘ 𝟙 (summandModule e)) ≫
      summandCompositionMap (d.contract i.castSucc) e) := by
  rw [summandCompositionMap_eq_normalized,
    summandCompositionMap_eq_normalized]
  rw [normalizedSummandCompositionMap_eq_append_remainder,
    normalizedSummandCompositionMap_eq_append_remainder]
  dsimp only [summandModule]
  simp only [Category.assoc]
  rw [tensorModuleListAppendIso_whiskerRight_assoc]
  let A := (tensorModuleListAppendIso (finFamilyList (factorModule d))
    (finFamilyList (factorModule e))).hom
  let R := summandCompositionRemainder d e
  let C := contractionTensorMap (d.append e)
    (appendLeftContractionIndex i.castSucc)
  let W := tensorModuleListWhiskerRight (finFamilyList (factorModule e))
    (contractionTensorMap d i.castSucc)
  let R' := summandCompositionRemainder (d.contract i.castSucc) e
  change HEq (A ≫ R ≫ C) (A ≫ W ≫ R')
  have hrem :=
    summandCompositionRemainder_contraction_append_left_castSucc_heq d e i
  have hA : HEq A A := HEq.rfl
  have hpre : HEq (A ≫ (R ≫ C)) (A ≫ (W ≫ R')) :=
    CategoryTheory.heq_comp rfl rfl
      (summandModule_contract_append_left_castSucc_case d e i) hA hrem
  exact hpre

theorem summandCompositionMap_contraction_append_left_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    HEq
      (summandCompositionMap d e ≫
        contractionTensorMap (d.append e) (appendLeftContractionIndex i))
      ((contractionTensorMap d i ⊗ₘ 𝟙 (summandModule e)) ≫
        summandCompositionMap (d.contract i) e) := by
  cases w with
  | mk length intermediate =>
      cases length with
      | zero => exact Fin.elim0 i
      | succ k =>
          cases k with
          | zero =>
              have hi : i = Fin.last 0 := by
                have hiLt : i.val < 1 := by
                  exact i.isLt
                apply Fin.ext
                change i.val = 0
                omega
              subst i
              exact summandCompositionMap_contraction_append_left_last_heq d e
          | succ k =>
              refine Fin.lastCases ?_ (fun j ↦ ?_) i
              · exact summandCompositionMap_contraction_append_left_last_heq d e
              · exact
                  summandCompositionMap_contraction_append_left_castSucc_heq
                    d e j
def rawContractionTargetListEq_right_zero_assembly
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    finFamilyList (factorModule (d.contract i)) =
      finFamilyList (recursiveMergedFactor (factorModule d) i
        (rawContractionFactor d i)) :=
  ((congrArg finFamilyList (test_rawContractionTarget_eq d i)).trans
    (contractedFactorsOldIndex_eq d i)).symm

theorem rightZeroHeadFactor_eq
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    factorModule e 0 = factorModule (rightZeroHeadDegreeProfile e) 0 := by
  unfold factorModule
  have hsource :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowSource 0 =
        (nil Y (intermediate 0).obj).arrowSource 0 := by
    rw [arrowSource_zero_eq_source, nil_arrowSource_zero]
  have htarget :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowTarget 0 =
        (nil Y (intermediate 0).obj).arrowTarget 0 := by
    rw [nil_arrowTarget_zero]
    unfold arrowTarget vertex
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
    rfl
  rw [hsource, htarget]
  rfl

theorem rightZeroRightSuffix_eq
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    compositionRightSuffix e = factorModule (tailDegreeProfile e) 0 ::
      compositionRightSuffix (tailDegreeProfile e) := by
  unfold compositionRightSuffix
  rw [finFamilyList_eq_ofFn, List.ofFn_succ, finFamilyList_eq_ofFn]
  simp only [tailFactorModule]

theorem rightZeroFactorList_eq
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    finFamilyList (factorModule e) =
      factorModule (rightZeroHeadDegreeProfile e) 0 ::
        factorModule (tailDegreeProfile e) 0 ::
          compositionRightSuffix (tailDegreeProfile e) := by
  rw [finFamilyList_factorModule_eq_first_suffix, rightZeroHeadFactor_eq,
    rightZeroRightSuffix_eq]

theorem rightZeroRawContractionFactor_eq
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    rawContractionFactor e 0 =
      zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e) := by
  unfold rawContractionFactor zeroMiddleRightBoundaryModule
  have hsource :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowSource (0 : Fin (k + 1)).castSucc = Y := by
    change ({ length := k + 1, intermediate := intermediate } :
      DrinfeldWord Y Z).arrowSource 0 = Y
    exact arrowSource_zero_eq_source _
  have htarget :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowTarget (0 : Fin (k + 1)).succ =
        (tailWord intermediate).arrowTarget 0 :=
    (tailWord_arrowTarget (X := Y) (Y := Z)
      (intermediate := intermediate) 0).symm
  rw [hsource, htarget]
  rfl

theorem rightZeroRawContractionTargetList_eq
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    finFamilyList
        (recursiveMergedFactor (factorModule e) 0 (rawContractionFactor e 0)) =
      zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
          (tailDegreeProfile e) ::
        compositionRightSuffix (tailDegreeProfile e) := by
  rw [finFamilyList_recursiveMerge_target, rightZeroFactorList_eq,
    rightZeroRawContractionFactor_eq]
  rfl

theorem rightZeroCompositionBoundaryModule_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    compositionBoundaryModule d e =
      compositionBoundaryModule d (rightZeroHeadDegreeProfile e) := by
  unfold compositionBoundaryModule
  have htarget :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowTarget 0 =
        (nil Y (intermediate 0).obj).arrowTarget 0 := by
    rw [nil_arrowTarget_zero]
    unfold arrowTarget vertex
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
    rfl
  rw [htarget]
  rfl

theorem rightZeroCompositionTargetList_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e =
      compositionLeftPrefix d ++
        compositionBoundaryModule d (rightZeroHeadDegreeProfile e) ::
          factorModule (tailDegreeProfile e) 0 ::
            compositionRightSuffix (tailDegreeProfile e) := by
  rw [rightZeroCompositionBoundaryModule_eq, rightZeroRightSuffix_eq]

theorem rightZeroCompositionSourceList_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    finFamilyList (factorModule d) ++ finFamilyList (factorModule e) =
      compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
        factorModule (rightZeroHeadDegreeProfile e) 0 ::
          factorModule (tailDegreeProfile e) 0 ::
            compositionRightSuffix (tailDegreeProfile e) := by
  rw [finFamilyList_factorModule_eq_prefix_last, rightZeroFactorList_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]


theorem rightZeroRawContractionAppendFactor_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    rawContractionFactor (d.append e) (appendRightContractionIndex 0) =
      tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e) := by
  unfold rawContractionFactor tripleCompositionBoundaryModule
  have hboundary : (appendRightContractionIndex (w := w) (0 : Fin (k + 1))).castSucc =
      appendBoundaryArrowIndex w
        ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) :=
    Fin.ext rfl
  have hright : (appendRightContractionIndex (w := w) (0 : Fin (k + 1))).succ =
      appendRightArrowIndex (w := w)
        (v := ({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord Y Z)) 0 := Fin.ext rfl
  rw [hboundary, hright, arrowSource_append_boundary, arrowTarget_append_right,
    tailWord_arrowTarget]
  congr 1
  change appendArrowDegree d e (appendBoundaryArrowIndex w _) +
      appendArrowDegree d e (appendRightArrowIndex (w := w) 0) = _
  rw [appendArrowDegree_boundary, appendArrowDegree_right]
  rfl

theorem rightZeroRawContractionAppendTargetList_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    finFamilyList (recursiveMergedFactor (factorModule (d.append e))
        (appendRightContractionIndex 0)
        (rawContractionFactor (d.append e) (appendRightContractionIndex 0))) =
      compositionLeftPrefix d ++
        tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e) ::
          compositionRightSuffix (tailDegreeProfile e) := by
  let i := appendRightContractionIndex
    (w := w)
    (v := ({ length := k + 1, intermediate := intermediate } :
      DrinfeldWord Y Z)) (0 : Fin (k + 1))
  have hfull := finFamilyList_factorModule_append_boundary d e
  have hprefix : (finFamilyList (factorModule (d.append e))).take i.val =
      compositionLeftPrefix d := by
    change (finFamilyList (factorModule (d.append e))).take w.length = _
    rw [hfull]
    rw [List.take_append_of_le_length]
    · simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
    · simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
  have hsuffix : (finFamilyList (factorModule (d.append e))).drop (i.val + 2) =
      compositionRightSuffix (tailDegreeProfile e) := by
    change (finFamilyList (factorModule (d.append e))).drop (w.length + 2) = _
    rw [hfull]
    rw [← List.drop_drop]
    rw [List.drop_append_of_le_length]
    · have hdrop : (compositionLeftPrefix d).drop w.length = [] := by
        simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
      rw [hdrop, rightZeroRightSuffix_eq e]
      rfl
    · simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
  rw [finFamilyList_recursiveMerge_target, hprefix,
    rightZeroRawContractionAppendFactor_eq, hsuffix]

theorem rightZeroCompositionMergeTensorMap_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap
      ((@AdjacentMergeData.head
          (factorModule d (Fin.last w.length))
          (factorModule (rightZeroHeadDegreeProfile e) 0)
          (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
          (factorModule (tailDegreeProfile e) 0 ::
            compositionRightSuffix (tailDegreeProfile e))
          (compositionBoundaryMap d (rightZeroHeadDegreeProfile e))).prefix
            (compositionLeftPrefix d)).tensorMap := by
  have htarget :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowTarget 0 =
        (nil Y (intermediate 0).obj).arrowTarget 0 := by
    rw [nil_arrowTarget_zero]
    unfold arrowTarget vertex
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
    rfl
  have hsource :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowSource 0 =
        (nil Y (intermediate 0).obj).arrowSource 0 := by
    rw [arrowSource_zero_eq_source, nil_arrowSource_zero]
  have hdegree : e.arrowDegree 0 =
      (rightZeroHeadDegreeProfile e).arrowDegree 0 := rfl
  have hfactor : factorModule e 0 =
      factorModule (rightZeroHeadDegreeProfile e) 0 := by
    unfold factorModule
    rw [hsource, htarget]
    rfl
  have hboundary : compositionBoundaryModule d e =
      compositionBoundaryModule d (rightZeroHeadDegreeProfile e) := by
    unfold compositionBoundaryModule
    rw [htarget]
    rfl
  have hright : compositionRightSuffix e =
      factorModule (tailDegreeProfile e) 0 ::
        compositionRightSuffix (tailDegreeProfile e) := by
    unfold compositionRightSuffix
    rw [finFamilyList_eq_ofFn, List.ofFn_succ]
    rw [finFamilyList_eq_ofFn]
    simp only [tailFactorModule]
  have hmap : HEq (compositionBoundaryMap d e)
      (compositionBoundaryMap d (rightZeroHeadDegreeProfile e)) := by
    unfold compositionBoundaryMap
    apply dgCochainCompTensorOfEq_heq
    · rfl
    · rfl
    · rfl
    · exact htarget
    · rfl
    · rfl
    · rfl
  have hdata := (adjacentMergeAfter_congr
    (f := compositionBoundaryMap d e)
    (g := compositionBoundaryMap d (rightZeroHeadDegreeProfile e))
    rfl rfl hfactor hboundary hright hmap).trans
    (heq_of_eq (adjacentMergeAfter_eq_prefix_head (compositionLeftPrefix d)
      (compositionBoundaryMap d (rightZeroHeadDegreeProfile e))))
  apply AdjacentMergeData.tensorMap_heq
  · rw [hfactor, hright]
  · rw [hboundary, hright]
  · exact hdata

theorem rightZeroRawContractionTensorMap_heq
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (rawContractionAdjacentMergeData e 0).tensorMap
      ((@AdjacentMergeData.head
          (factorModule (rightZeroHeadDegreeProfile e) 0)
          (factorModule (tailDegreeProfile e) 0)
          (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (compositionRightSuffix (tailDegreeProfile e))
          (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))).tensorMap) := by
  have hheadTarget :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowTarget 0 =
        (nil Y (intermediate 0).obj).arrowTarget 0 := by
    rw [nil_arrowTarget_zero]
    unfold arrowTarget vertex
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
    rfl
  have hheadSource :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowSource 0 =
        (nil Y (intermediate 0).obj).arrowSource 0 := by
    rw [arrowSource_zero_eq_source, nil_arrowSource_zero]
  have hfactorZero : factorModule e 0 =
      factorModule (rightZeroHeadDegreeProfile e) 0 := by
    unfold factorModule
    rw [hheadSource, hheadTarget]
    rfl
  have hfactorOne : factorModule e (Fin.succ 0) =
      factorModule (tailDegreeProfile e) 0 := (tailFactorModule e 0).symm
  have hsuffix : finFamilyList (fun q : Fin k ↦ factorModule e q.succ.succ) =
      compositionRightSuffix (tailDegreeProfile e) := by
    unfold compositionRightSuffix
    rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
    simp only [tailFactorModule]
  have hraw : rawContractionFactor e 0 =
      zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e) := by
    unfold rawContractionFactor zeroMiddleRightBoundaryModule
    have hsource :
        ({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord Y Z).arrowSource (0 : Fin (k + 1)).castSucc = Y := by
      change ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowSource 0 = Y
      exact arrowSource_zero_eq_source _
    have htarget :
        ({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord Y Z).arrowTarget (0 : Fin (k + 1)).succ =
          (tailWord intermediate).arrowTarget 0 :=
      (tailWord_arrowTarget (X := Y) (Y := Z)
        (intermediate := intermediate) 0).symm
    rw [hsource, htarget]
    rfl
  have hsource : finFamilyList (factorModule e) =
      factorModule (rightZeroHeadDegreeProfile e) 0 ::
        factorModule (tailDegreeProfile e) 0 ::
          compositionRightSuffix (tailDegreeProfile e) := by
    rw [finFamilyList_eq_ofFn, List.ofFn_succ, List.ofFn_succ]
    rw [hfactorZero, hfactorOne]
    congr 2
    simpa only [finFamilyList_eq_ofFn] using hsuffix
  have htarget : finFamilyList
        (recursiveMergedFactor (factorModule e) 0 (rawContractionFactor e 0)) =
      zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
          (tailDegreeProfile e) ::
        compositionRightSuffix (tailDegreeProfile e) := by
    change rawContractionFactor e 0 ::
        finFamilyList (fun q : Fin k ↦ factorModule e q.succ.succ) = _
    rw [hraw, hsuffix]
  have hmap : HEq (adjacentFactorComposition e 0)
      (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e)) := by
    unfold adjacentFactorComposition zeroMiddleRightBoundaryMap factorModule
    apply dgCochainCompTensorOfEq_heq
    · exact hheadSource
    · exact hheadTarget
    · exact (tailWord_arrowSource (X := Y) (Y := Z)
        (intermediate := intermediate) 0).symm
    · exact (tailWord_arrowTarget (X := Y) (Y := Z)
        (intermediate := intermediate) 0).symm
    · rfl
    · rfl
    · rfl
  apply AdjacentMergeData.tensorMap_heq hsource htarget
  unfold rawContractionAdjacentMergeData
  change HEq (adjacentMergeAfter []
      (ys := finFamilyList (fun q : Fin k ↦ factorModule e q.succ.succ))
      (adjacentFactorComposition e 0))
    (AdjacentMergeData.head
      (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e)))
  exact (adjacentMergeAfter_congr rfl hfactorZero hfactorOne hraw hsuffix hmap).trans
    (heq_of_eq (adjacentMergeAfter_eq_prefix_head []
      (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e))))


theorem rightZeroRawContractionAppendTensorMap_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (rawContractionAdjacentMergeData (d.append e)
        (appendRightContractionIndex (0 : Fin (k + 1)))).tensorMap
      (((@AdjacentMergeData.head
          (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
          (factorModule (tailDegreeProfile e) 0)
          (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (compositionRightSuffix (tailDegreeProfile e))
          (leftAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap) := by
  let i := appendRightContractionIndex
    (w := w)
    (v := ({ length := k + 1, intermediate := intermediate } :
      DrinfeldWord Y Z)) (0 : Fin (k + 1))
  have hi : i.val = w.length := rfl
  have hboundary : i.castSucc = appendBoundaryArrowIndex w
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z) := Fin.ext rfl
  have hright : i.succ = appendRightArrowIndex (w := w)
      (v := ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z)) 0 := Fin.ext rfl
  have hheadTarget :
      ({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord Y Z).arrowTarget 0 =
        (nil Y (intermediate 0).obj).arrowTarget 0 := by
    rw [nil_arrowTarget_zero]
    unfold arrowTarget vertex
    rw [Fin.cases_succ]
    have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
    rw [hzero, Fin.lastCases_castSucc]
    rfl
  have hheadBoundary : compositionBoundaryModule d e =
      compositionBoundaryModule d (rightZeroHeadDegreeProfile e) := by
    unfold compositionBoundaryModule
    rw [hheadTarget]
    rfl
  have hrightSuffix : compositionRightSuffix e =
      factorModule (tailDegreeProfile e) 0 ::
        compositionRightSuffix (tailDegreeProfile e) := by
    unfold compositionRightSuffix
    rw [finFamilyList_eq_ofFn, List.ofFn_succ]
    rw [finFamilyList_eq_ofFn]
    simp only [tailFactorModule]
  have hfull := finFamilyList_factorModule_append_boundary d e
  have hprefix : (finFamilyList (factorModule (d.append e))).take i.val =
      compositionLeftPrefix d := by
    change (finFamilyList (factorModule (d.append e))).take w.length = _
    rw [hfull]
    rw [List.take_append_of_le_length]
    · simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
    · simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
  have hsuffix : (finFamilyList (factorModule (d.append e))).drop (i.val + 2) =
      compositionRightSuffix (tailDegreeProfile e) := by
    change (finFamilyList (factorModule (d.append e))).drop (w.length + 2) = _
    rw [hfull]
    rw [← List.drop_drop]
    rw [List.drop_append_of_le_length]
    · have hdrop : (compositionLeftPrefix d).drop w.length = [] := by
        simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
      rw [hdrop, hrightSuffix]
      rfl
    · simp [compositionLeftPrefix, finFamilyList_eq_ofFn]
  have hleftFactor : factorModule (d.append e) i.castSucc =
      compositionBoundaryModule d (rightZeroHeadDegreeProfile e) := by
    rw [hboundary, factorModule_append_boundary, hheadBoundary]
  have hrightFactor : factorModule (d.append e) i.succ =
      factorModule (tailDegreeProfile e) 0 := by
    rw [hright, factorModule_append_right, tailFactorModule]
  have hraw : rawContractionFactor (d.append e) i =
      tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e) := by
    unfold rawContractionFactor tripleCompositionBoundaryModule
    have hsource : (w.append _).arrowSource i.castSucc =
        w.arrowSource (Fin.last w.length) := by
      rw [hboundary, arrowSource_append_boundary]
    have htarget : (w.append _).arrowTarget i.succ =
        (tailWord (Y := Z) intermediate).arrowTarget 0 := by
      rw [hright, arrowTarget_append_right]
      exact (tailWord_arrowTarget (X := Y) (Y := Z)
        (intermediate := intermediate) 0).symm
    rw [hsource, htarget]
    congr 1
    change appendArrowDegree d e (appendBoundaryArrowIndex w _) +
        appendArrowDegree d e (appendRightArrowIndex (w := w) 0) = _
    rw [appendArrowDegree_boundary, appendArrowDegree_right]
    rfl
  have hmap : HEq (adjacentFactorComposition (d.append e) i)
      (leftAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e)) := by
    unfold adjacentFactorComposition leftAssociatedBoundaryMap
    apply dgCochainCompTensorOfEq_heq
    · rw [hboundary, arrowSource_append_boundary]
    · rw [hboundary, arrowTarget_append_boundary]
      exact hheadTarget
    · rw [hright, arrowSource_append_right, tailWord_arrowSource]
    · rw [hright, arrowTarget_append_right, tailWord_arrowTarget]
    · rw [hboundary]
      change appendArrowDegree d e (appendBoundaryArrowIndex w _) = _
      rw [appendArrowDegree_boundary]
      rfl
    · rw [hright]
      change appendArrowDegree d e (appendRightArrowIndex (w := w) 0) = _
      rw [appendArrowDegree_right]
      rfl
    · rw [hboundary, hright]
      change appendArrowDegree d e (appendBoundaryArrowIndex w _) +
        appendArrowDegree d e (appendRightArrowIndex (w := w) 0) = _
      rw [appendArrowDegree_boundary, appendArrowDegree_right]
      rfl
  have hsource : finFamilyList (factorModule (d.append e)) =
      compositionLeftPrefix d ++
        compositionBoundaryModule d (rightZeroHeadDegreeProfile e) ::
          factorModule (tailDegreeProfile e) 0 ::
            compositionRightSuffix (tailDegreeProfile e) := by
    rw [hfull, hheadBoundary, hrightSuffix]
  have htarget : finFamilyList
        (recursiveMergedFactor (factorModule (d.append e)) i
          (rawContractionFactor (d.append e) i)) =
      compositionLeftPrefix d ++
        tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e) ::
          compositionRightSuffix (tailDegreeProfile e) := by
    rw [finFamilyList_recursiveMerge_target, hprefix, hraw, hsuffix]
  apply AdjacentMergeData.tensorMap_heq hsource htarget
  unfold rawContractionAdjacentMergeData
  change HEq (recursiveAdjacentMergeDataOfFn (factorModule (d.append e)) i
      (rawContractionFactor (d.append e) i)
      (adjacentFactorComposition (d.append e) i)) _
  exact (recursiveAdjacentMergeDataOfFn_eq_after
    (factorModule (d.append e)) i (rawContractionFactor (d.append e) i)
      (adjacentFactorComposition (d.append e) i)).trans
    ((adjacentMergeAfter_congr hprefix hleftFactor hrightFactor hraw hsuffix hmap).trans
      (heq_of_eq (adjacentMergeAfter_eq_prefix_head (compositionLeftPrefix d)
        (leftAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
          (tailDegreeProfile e)))))

theorem rightZeroContractedFactorList_eq
    {Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {m : ℤ}
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    finFamilyList (factorModule (e.contract 0)) =
      zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
          (tailDegreeProfile e) ::
        compositionRightSuffix (tailDegreeProfile e) := by
  exact (rawContractionTargetListEq_right_zero_assembly e 0).trans
    (rightZeroRawContractionTargetList_eq e)

theorem rightZeroContractBoundaryModule_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    compositionBoundaryModule d (e.contract 0) =
      tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e) := by
  let v : DrinfeldWord Y Z :=
    { length := k + 1, intermediate := intermediate }
  have hposition : erasePosition v (0 : Fin (k + 1)) = 0 := Fin.ext rfl
  have htarget : (eraseIntermediate v 0).arrowTarget 0 =
      (tailWord intermediate).arrowTarget 0 :=
    (congrArg (eraseIntermediate v 0).arrowTarget hposition.symm).trans
      ((eraseIntermediate_arrowTarget_at v 0).trans
        (tailWord_arrowTarget (X := Y) (Y := Z)
          (intermediate := intermediate) 0).symm)
  have hdegree : (e.contract 0).arrowDegree 0 =
      e.arrowDegree 0 + (tailDegreeProfile e).arrowDegree 0 :=
    (congrArg (e.contract 0).arrowDegree hposition.symm).trans
      (contract_arrowDegree_at e 0)
  unfold compositionBoundaryModule tripleCompositionBoundaryModule
  rw [htarget, hdegree, Int.add_assoc]
  rfl

theorem rightZeroContractBoundaryMap_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq (compositionBoundaryMap d (e.contract 0))
      (rightAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e)) := by
  let v : DrinfeldWord Y Z :=
    { length := k + 1, intermediate := intermediate }
  have hposition : erasePosition v (0 : Fin (k + 1)) = 0 := Fin.ext rfl
  have hsource : (eraseIntermediate v 0).arrowSource 0 =
      (nil Y (intermediate 0).obj).arrowSource 0 :=
    (congrArg (eraseIntermediate v 0).arrowSource hposition.symm).trans
      ((eraseIntermediate_arrowSource_at v 0).trans (by
        change v.arrowSource 0 = Y
        exact arrowSource_zero_eq_source v))
  have htarget : (eraseIntermediate v 0).arrowTarget 0 =
      (tailWord intermediate).arrowTarget 0 :=
    (congrArg (eraseIntermediate v 0).arrowTarget hposition.symm).trans
      ((eraseIntermediate_arrowTarget_at v 0).trans
        (tailWord_arrowTarget (X := Y) (Y := Z)
          (intermediate := intermediate) 0).symm)
  have hdegree : (e.contract 0).arrowDegree 0 =
      e.arrowDegree 0 + (tailDegreeProfile e).arrowDegree 0 :=
    (congrArg (e.contract 0).arrowDegree hposition.symm).trans
      (contract_arrowDegree_at e 0)
  unfold compositionBoundaryMap rightAssociatedBoundaryMap factorModule
    zeroMiddleRightBoundaryModule tripleCompositionBoundaryModule
  apply dgCochainCompTensorOfEq_heq
  · rfl
  · rfl
  · exact hsource
  · exact htarget
  · rfl
  · exact hdegree
  · exact congrArg (d.arrowDegree (Fin.last w.length) + ·) hdegree |>.trans
      (Int.add_assoc _ _ _).symm


theorem rightZeroContractedCompositionSourceList_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    finFamilyList (factorModule d) ++ finFamilyList (factorModule (e.contract 0)) =
      compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
        zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e) ::
          compositionRightSuffix (tailDegreeProfile e) := by
  rw [finFamilyList_factorModule_eq_prefix_last, rightZeroContractedFactorList_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem rightZeroContractedCompositionTargetList_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    compositionLeftPrefix d ++ compositionBoundaryModule d (e.contract 0) ::
        compositionRightSuffix (e.contract 0) =
      compositionLeftPrefix d ++
        tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e) ::
          compositionRightSuffix (tailDegreeProfile e) := by
  have hcontractCons :
      factorModule (e.contract 0) 0 :: compositionRightSuffix (e.contract 0) =
        zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e) ::
          compositionRightSuffix (tailDegreeProfile e) :=
    (finFamilyList_factorModule_eq_first_suffix (e.contract 0)).symm.trans
      (rightZeroContractedFactorList_eq e)
  rw [rightZeroContractBoundaryModule_eq d e, (List.cons.inj hcontractCons).2]

theorem rightZeroContractCompositionMergeTensorMap_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix d)
        (ys := compositionRightSuffix (e.contract 0))
        (compositionBoundaryMap d (e.contract 0))).tensorMap
      (((@AdjacentMergeData.head
          (factorModule d (Fin.last w.length))
          (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (compositionRightSuffix (tailDegreeProfile e))
          (rightAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap) := by
  have hcontractCons :
      factorModule (e.contract 0) 0 :: compositionRightSuffix (e.contract 0) =
        zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e) ::
          compositionRightSuffix (tailDegreeProfile e) :=
    (finFamilyList_factorModule_eq_first_suffix (e.contract 0)).symm.trans
      (rightZeroContractedFactorList_eq e)
  have hfirst := (List.cons.inj hcontractCons).1
  have hsuffix := (List.cons.inj hcontractCons).2
  have hdata := (adjacentMergeAfter_congr
    (f := compositionBoundaryMap d (e.contract 0))
    (g := rightAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
      (tailDegreeProfile e))
    rfl rfl hfirst (rightZeroContractBoundaryModule_eq d e) hsuffix
      (rightZeroContractBoundaryMap_heq d e)).trans
    (heq_of_eq (adjacentMergeAfter_eq_prefix_head (compositionLeftPrefix d)
      (rightAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e))))
  apply AdjacentMergeData.tensorMap_heq
  · rw [hfirst, hsuffix]
  · rw [rightZeroContractBoundaryModule_eq d e, hsuffix]
  · exact hdata

theorem rightZeroActualRightPair_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (summandCompositionRemainder d e ≫
        (rawContractionAdjacentMergeData (d.append e)
          (appendRightContractionIndex 0)).tensorMap ≫
        eqToHom (congrArg tensorModuleList
          (rawContractionTargetListEq_right_zero_assembly
            (d.append e) (appendRightContractionIndex 0)).symm))
      (((@AdjacentMergeData.head
          (factorModule d (Fin.last w.length))
          (factorModule (rightZeroHeadDegreeProfile e) 0)
          (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
          (factorModule (tailDegreeProfile e) 0 ::
            compositionRightSuffix (tailDegreeProfile e))
          (compositionBoundaryMap d (rightZeroHeadDegreeProfile e))).prefix
            (compositionLeftPrefix d)).tensorMap ≫
        ((@AdjacentMergeData.head
          (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
          (factorModule (tailDegreeProfile e) 0)
          (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (compositionRightSuffix (tailDegreeProfile e))
          (leftAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap) := by
  let p := eqToHom (congrArg tensorModuleList (compositionSourceListEq d e)) ≫
    eqToHom (congrArg tensorModuleList (compositionBoundaryListEq d e))
  let f := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap
  let m₀ := eqToHom (congrArg tensorModuleList (compositionTargetListEq d e))
  let g := (rawContractionAdjacentMergeData (d.append e)
    (appendRightContractionIndex 0)).tensorMap
  let q := eqToHom (congrArg tensorModuleList
    (rawContractionTargetListEq_right_zero_assembly
      (d.append e) (appendRightContractionIndex 0)).symm)
  let F := ((@AdjacentMergeData.head
    (factorModule d (Fin.last w.length))
    (factorModule (rightZeroHeadDegreeProfile e) 0)
    (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
    (factorModule (tailDegreeProfile e) 0 ::
      compositionRightSuffix (tailDegreeProfile e))
    (compositionBoundaryMap d (rightZeroHeadDegreeProfile e))).prefix
      (compositionLeftPrefix d)).tensorMap
  let G := ((@AdjacentMergeData.head
    (compositionBoundaryModule d (rightZeroHeadDegreeProfile e))
    (factorModule (tailDegreeProfile e) 0)
    (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
      (tailDegreeProfile e))
    (compositionRightSuffix (tailDegreeProfile e))
    (leftAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
      (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap
  have hSList := rightZeroCompositionSourceList_eq d e
  have hUList := rightZeroCompositionTargetList_eq d e
  have hVList := rightZeroRawContractionAppendTargetList_eq d e
  have h := transportedPair₂_heq
    (p := p) (f := f) (m := m₀) (g := g) (q₁ := q) (q₂ := 𝟙 _)
    (F := F) (G := G)
    (hS := congrArg tensorModuleList hSList)
    (hA := congrArg tensorModuleList
      ((compositionSourceListEq d e).trans (compositionBoundaryListEq d e)))
    (hB := congrArg tensorModuleList hUList)
    (hC := congrArg tensorModuleList
      ((compositionTargetListEq d e).symm.trans hUList))
    (hD := congrArg tensorModuleList hVList)
    (hE := congrArg tensorModuleList
      ((rawContractionTargetListEq_right_zero_assembly
        (d.append e) (appendRightContractionIndex 0)).trans hVList))
    (hT := congrArg tensorModuleList
      ((rawContractionTargetListEq_right_zero_assembly
        (d.append e) (appendRightContractionIndex 0)).trans hVList))
    (hp := eqToHom_comp_heq_id _ _)
    (hf := rightZeroCompositionMergeTensorMap_heq d e)
    (hm := test_eqToHom_heq_id _)
    (hg := rightZeroRawContractionAppendTensorMap_heq d e)
    (hq₁ := test_eqToHom_heq_id _)
    (hq₂ := HEq.rfl)
  simpa only [p, f, m₀, g, q, F, G, summandCompositionRemainder,
    Category.assoc, Category.comp_id] using h


theorem rightZeroActualLeftPair_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
          ((rawContractionAdjacentMergeData e 0).tensorMap ≫
            eqToHom (congrArg tensorModuleList
              (rawContractionTargetListEq_right_zero_assembly e 0).symm)) ≫
        summandCompositionRemainder d (e.contract 0))
      (((@AdjacentMergeData.tail (factorModule d (Fin.last w.length))
          (factorModule (rightZeroHeadDegreeProfile e) 0 ::
            factorModule (tailDegreeProfile e) 0 ::
              compositionRightSuffix (tailDegreeProfile e))
          (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
              (tailDegreeProfile e) :: compositionRightSuffix (tailDegreeProfile e))
          (@AdjacentMergeData.head
            (factorModule (rightZeroHeadDegreeProfile e) 0)
            (factorModule (tailDegreeProfile e) 0)
            (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
              (tailDegreeProfile e))
            (compositionRightSuffix (tailDegreeProfile e))
            (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
              (tailDegreeProfile e)))).prefix (compositionLeftPrefix d)).tensorMap ≫
        ((@AdjacentMergeData.head
          (factorModule d (Fin.last w.length))
          (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))
          (compositionRightSuffix (tailDegreeProfile e))
          (rightAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap) := by
  let f := tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
    (rawContractionAdjacentMergeData e 0).tensorMap
  let m₀ := tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
      (eqToHom (congrArg tensorModuleList
        (rawContractionTargetListEq_right_zero_assembly e 0).symm)) ≫
    eqToHom (congrArg tensorModuleList (compositionSourceListEq d (e.contract 0))) ≫
    eqToHom (congrArg tensorModuleList (compositionBoundaryListEq d (e.contract 0)))
  let g := (adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix (e.contract 0))
    (compositionBoundaryMap d (e.contract 0))).tensorMap
  let q := eqToHom (congrArg tensorModuleList
    (compositionTargetListEq d (e.contract 0)))
  let F := ((@AdjacentMergeData.tail (factorModule d (Fin.last w.length))
    (factorModule (rightZeroHeadDegreeProfile e) 0 ::
      factorModule (tailDegreeProfile e) 0 :: compositionRightSuffix (tailDegreeProfile e))
    (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e) :: compositionRightSuffix (tailDegreeProfile e))
    (@AdjacentMergeData.head
      (factorModule (rightZeroHeadDegreeProfile e) 0)
      (factorModule (tailDegreeProfile e) 0)
      (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e))
      (compositionRightSuffix (tailDegreeProfile e))
      (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e)))).prefix (compositionLeftPrefix d)).tensorMap
  let G := ((@AdjacentMergeData.head
    (factorModule d (Fin.last w.length))
    (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e) (tailDegreeProfile e))
    (tripleCompositionBoundaryModule d (rightZeroHeadDegreeProfile e)
      (tailDegreeProfile e))
    (compositionRightSuffix (tailDegreeProfile e))
    (rightAssociatedBoundaryMap d (rightZeroHeadDegreeProfile e)
      (tailDegreeProfile e))).prefix (compositionLeftPrefix d)).tensorMap
  have hSList := rightZeroCompositionSourceList_eq d e
  have hUList : finFamilyList (factorModule d) ++
      finFamilyList (recursiveMergedFactor (factorModule e) 0
        (rawContractionFactor e 0)) =
      compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
        zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
            (tailDegreeProfile e) :: compositionRightSuffix (tailDegreeProfile e) := by
    rw [finFamilyList_factorModule_eq_prefix_last,
      rightZeroRawContractionTargetList_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hCList := rightZeroContractedCompositionSourceList_eq d e
  have hVList := rightZeroContractedCompositionTargetList_eq d e
  have hf : HEq f F := by
    dsimp only [f, F]
    apply HEq.trans (tensorModuleListWhiskerLeft_heq_right_succ_core
      (finFamilyList (factorModule d)) (rightZeroFactorList_eq e)
      (rightZeroRawContractionTargetList_eq e)
      (rightZeroRawContractionTensorMap_heq e))
    let hhead := @AdjacentMergeData.head
      (factorModule (rightZeroHeadDegreeProfile e) 0)
      (factorModule (tailDegreeProfile e) 0)
      (zeroMiddleRightBoundaryModule (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e))
      (compositionRightSuffix (tailDegreeProfile e))
      (zeroMiddleRightBoundaryMap (rightZeroHeadDegreeProfile e)
        (tailDegreeProfile e))
    change HEq
      (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
        hhead.tensorMap)
      (((hhead.prefix [factorModule d (Fin.last w.length)]).prefix
        (compositionLeftPrefix d)).tensorMap)
    apply HEq.trans (heq_of_eq
      (AdjacentMergeData.prefix_tensorMap hhead
        (finFamilyList (factorModule d))).symm)
    rw [finFamilyList_factorModule_eq_prefix_last]
    apply AdjacentMergeData.tensorMap_heq
    · exact List.append_assoc _ _ _
    · exact List.append_assoc _ _ _
    · exact (AdjacentMergeData.prefix_prefix_heq hhead
        [factorModule d (Fin.last w.length)] (compositionLeftPrefix d)).symm
  have h := transportedPair₂_heq
    (p := 𝟙 _)
    (f := f) (m := m₀) (g := g) (q₁ := q) (q₂ := 𝟙 _)
    (F := F) (G := G)
    (hS := congrArg tensorModuleList hSList)
    (hA := rfl)
    (hB := congrArg tensorModuleList hUList)
    (hC := congrArg tensorModuleList
      ((compositionBoundaryListEq d (e.contract 0)).symm.trans
        ((compositionSourceListEq d (e.contract 0)).symm.trans hCList)))
    (hD := congrArg tensorModuleList hVList)
    (hE := congrArg tensorModuleList
      ((compositionTargetListEq d (e.contract 0)).symm.trans hVList))
    (hT := congrArg tensorModuleList
      ((compositionTargetListEq d (e.contract 0)).symm.trans hVList))
    (hp := HEq.rfl) (hf := hf)
    (hm := by
      dsimp only [m₀]
      rw [tensorModuleListWhiskerLeft_eqToHom
        (finFamilyList (factorModule d))
        (rawContractionTargetListEq_right_zero_assembly e 0).symm]
      exact eqToHom_comp₃_heq_id _ _ _)
    (hg := rightZeroContractCompositionMergeTensorMap_heq d e)
    (hq₁ := test_eqToHom_heq_id _) (hq₂ := HEq.rfl)
  rw [tensorModuleListWhiskerLeft_comp]
  have htrim : HEq (f ≫ m₀ ≫ g ≫ q) (F ≫ G) := by
    apply HEq.trans ?_ h
    apply heq_of_eq
    rw [Category.comp_id]
    change f ≫ m₀ ≫ g ≫ q = (𝟙 _ ≫ f) ≫ m₀ ≫ g ≫ q
    rw [Category.id_comp]
  simpa [f, m₀, g, q, F, G, summandCompositionRemainder,
    summandModule] using htrim

theorem summandCompositionRemainder_contraction_append_right_zero_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (summandCompositionRemainder d e ≫
        contractionTensorMap (d.append e)
          (appendRightContractionIndex (0 : Fin (k + 1))))
      (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))
          (contractionTensorMap e 0) ≫
        summandCompositionRemainder d (e.contract 0)) := by
  let R := summandCompositionRemainder d e
  let C := contractionTensorMap (d.append e) (appendRightContractionIndex 0)
  let C₀ := (rawContractionAdjacentMergeData (d.append e)
    (appendRightContractionIndex 0)).tensorMap
  let E := contractionTensorMap e 0
  let E₀ := (rawContractionAdjacentMergeData e 0).tensorMap
  let R' := summandCompositionRemainder d (e.contract 0)
  let hAppendTargetList := rawContractionTargetListEq_right_zero_assembly
    (d.append e) (appendRightContractionIndex 0)
  let hAppendTarget := congrArg tensorModuleList hAppendTargetList
  let hETargetList := rawContractionTargetListEq_right_zero_assembly e 0
  let C₁ := C₀ ≫ eqToHom hAppendTarget.symm
  let E₁ := E₀ ≫
    eqToHom (congrArg tensorModuleList hETargetList.symm)
  let W := tensorModuleListWhiskerLeft (finFamilyList (factorModule d)) E
  let W₁ := tensorModuleListWhiskerLeft (finFamilyList (factorModule d)) E₁
  have hC : HEq C C₀ := by
    have hrecursive := contractionTensorMap_recursive_heq
      (d.append e) (appendRightContractionIndex 0)
    exact hrecursive.trans
      (hrecursive.symm.trans (test_contractionTensorMap_raw_heq _ _))
  have hE : HEq E E₀ := by
    have hrecursive := contractionTensorMap_recursive_heq e 0
    exact hrecursive.trans
      (hrecursive.symm.trans (test_contractionTensorMap_raw_heq e 0))
  have hC₁ : C = C₁ := eq_of_heq
    (hC.trans (CategoryTheory.comp_eqToHom_heq C₀ hAppendTarget.symm).symm)
  have hE₁ : E = E₁ := eq_of_heq
    (hE.trans (CategoryTheory.comp_eqToHom_heq E₀
      (congrArg tensorModuleList hETargetList.symm)).symm)
  have hW₁ : W = W₁ := congrArg
    (tensorModuleListWhiskerLeft (finFamilyList (factorModule d))) hE₁
  change HEq (R ≫ C) (W ≫ R')
  rw [hC₁, hW₁]
  have hmiddle := rightZeroNormalizedPairTensorMap_heq d e
  apply transportedPairAssembler_heq (hmiddle := hmiddle)
  · simpa only [R, C₁, C₀, Category.assoc] using
      rightZeroActualRightPair_heq d e
  · simpa only [W₁, E₁, E₀, R', Category.assoc] using
      rightZeroActualLeftPair_heq d e

theorem summandCompositionMap_contraction_append_right_zero_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n m : ℤ} (d : DegreeProfile w n)
    (e : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord Y Z) m) :
    HEq
      (summandCompositionMap d e ≫
        contractionTensorMap (d.append e)
          (appendRightContractionIndex (0 : Fin (k + 1))))
      ((𝟙 (summandModule d) ⊗ₘ contractionTensorMap e 0) ≫
        summandCompositionMap d (e.contract 0)) :=
  summandCompositionMap_contraction_append_right_of_remainder d e 0
    (summandCompositionRemainder_contraction_append_right_zero_heq d e)

theorem summandCompositionMap_contraction_append_right_heq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    HEq
      (summandCompositionMap d e ≫
        contractionTensorMap (d.append e) (appendRightContractionIndex j))
      ((𝟙 (summandModule d) ⊗ₘ contractionTensorMap e j) ≫
        summandCompositionMap d (e.contract j)) := by
  cases v with
  | mk length intermediate =>
      cases length with
      | zero => exact Fin.elim0 j
      | succ k =>
          cases k with
          | zero =>
              have hj : j = 0 := by
                have hjLt : j.val < 1 := j.isLt
                apply Fin.ext
                change j.val = 0
                omega
              subst j
              exact summandCompositionMap_contraction_append_right_zero_heq d e
          | succ k =>
              refine Fin.cases ?_ (fun i ↦ ?_) j
              · exact summandCompositionMap_contraction_append_right_zero_heq d e
              · exact summandCompositionMap_contraction_append_right_succ_heq d e i

theorem internalDifferentialLargeMap_append_boundary_apply
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
    (internalDifferentialLargeMap (d.append e)
        (appendBoundaryArrowIndex w v)).hom
        (largeSummandCompositionValue d e x y) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (rightLeibnizDegreeEq n m))).hom
          (largeSummandCompositionMap d (e.raise 0) x
            (((ModuleCat.uliftFunctor.{1} ℤ).map
              (internalDifferentialTensorMap e 0)).hom y)) +
        (e.arrowDegree 0).negOnePow •
          (eqToHom (congrArg (quotientGradedModule X Z)
            (leftLeibnizDegreeEq n m))).hom
            (largeSummandCompositionMap (d.raise (Fin.last w.length)) e
              (((ModuleCat.uliftFunctor.{1} ℤ).map
                (internalDifferentialTensorMap d (Fin.last w.length))).hom x) y) := by
  rw [transported_boundary_internal_right_apply,
    transported_boundary_internal_left_apply]
  change
    (Limits.Sigma.ι
      (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
      ⟨w.append v, (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
        (ULift.up ((summandCompositionMap d e ≫
          internalDifferentialTensorMap (d.append e)
            (appendBoundaryArrowIndex w v)).hom (x.down ⊗ₜ[ℤ] y.down))) =
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v, (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
          (ULift.up (((𝟙 (summandModule d) ⊗ₘ
              internalDifferentialTensorMap e 0) ≫
            summandCompositionMap d (e.raise 0) ≫
            eqToHom (appendBoundaryRightSummandModuleEq d e)).hom
              (x.down ⊗ₜ[ℤ] y.down))) +
        (e.arrowDegree 0).negOnePow •
          (Limits.Sigma.ι
            (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
            ⟨w.append v,
              (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
                (ULift.up (((internalDifferentialTensorMap d
                    (Fin.last w.length) ⊗ₘ 𝟙 (summandModule e)) ≫
                  summandCompositionMap (d.raise (Fin.last w.length)) e ≫
                  eqToHom (appendBoundaryLeftSummandModuleEq d e)).hom
                    (x.down ⊗ₜ[ℤ] y.down)))
  calc
    _ = (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v,
          (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
          (ULift.up
            ((((𝟙 (summandModule d) ⊗ₘ internalDifferentialTensorMap e 0) ≫
                summandCompositionMap d (e.raise 0) ≫
                eqToHom (appendBoundaryRightSummandModuleEq d e)).hom
                  (x.down ⊗ₜ[ℤ] y.down)) +
              (e.arrowDegree 0).negOnePow •
                (((internalDifferentialTensorMap d (Fin.last w.length) ⊗ₘ
                    𝟙 (summandModule e)) ≫
                  summandCompositionMap (d.raise (Fin.last w.length)) e ≫
                  eqToHom (appendBoundaryLeftSummandModuleEq d e)).hom
                    (x.down ⊗ₜ[ℤ] y.down)))) := by
      apply congrArg (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v,
          (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
      apply congrArg ULift.up
      exact DFunLike.congr_fun
        (congrArg ModuleCat.Hom.hom
          (summandCompositionMap_internalDifferential_append_boundary d e))
        (x.down ⊗ₜ[ℤ] y.down)
    _ = (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v,
          (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
          ((ULift.up (((𝟙 (summandModule d) ⊗ₘ
                internalDifferentialTensorMap e 0) ≫
              summandCompositionMap d (e.raise 0) ≫
              eqToHom (appendBoundaryRightSummandModuleEq d e)).hom
                (x.down ⊗ₜ[ℤ] y.down))) +
            (e.arrowDegree 0).negOnePow •
              (ULift.up (((internalDifferentialTensorMap d
                    (Fin.last w.length) ⊗ₘ 𝟙 (summandModule e)) ≫
                summandCompositionMap (d.raise (Fin.last w.length)) e ≫
                eqToHom (appendBoundaryLeftSummandModuleEq d e)).hom
                  (x.down ⊗ₜ[ℤ] y.down)))) := rfl
    _ = (Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
          ⟨w.append v,
            (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
            (ULift.up (((𝟙 (summandModule d) ⊗ₘ
                internalDifferentialTensorMap e 0) ≫
              summandCompositionMap d (e.raise 0) ≫
              eqToHom (appendBoundaryRightSummandModuleEq d e)).hom
                (x.down ⊗ₜ[ℤ] y.down))) +
          (Limits.Sigma.ι
            (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
            ⟨w.append v,
              (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom
                ((e.arrowDegree 0).negOnePow •
                  (ULift.up (((internalDifferentialTensorMap d
                      (Fin.last w.length) ⊗ₘ 𝟙 (summandModule e)) ≫
                    summandCompositionMap (d.raise (Fin.last w.length)) e ≫
                    eqToHom (appendBoundaryLeftSummandModuleEq d e)).hom
                      (x.down ⊗ₜ[ℤ] y.down)))) :=
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v,
          (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom.map_add _ _
    _ = _ := by
      congr 1
      exact map_zsmul_unit (Limits.Sigma.ι
        (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
        ⟨w.append v,
          (d.append e).raise (appendBoundaryArrowIndex w v)⟩).hom _ _

theorem contractionLargeMap_append_right_apply
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (j : Fin v.length) :
    (contractionLargeMap (d.append e)
        (appendRightContractionIndex (w := w) j)).hom
        (largeSummandCompositionValue d e x y) =
      e.contractionSign j •
        (eqToHom (congrArg (quotientGradedModule X Z)
          (rightLeibnizDegreeEq n m))).hom
          (largeSummandCompositionMap d (e.contract j) x
            (((ModuleCat.uliftFunctor.{1} ℤ).map
              (contractionTensorMap e j)).hom y)) := by
  unfold contractionLargeMap
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [contractionSign_append_right]
  congr 1
  change
    (Limits.Sigma.ι
      (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
      ⟨eraseIntermediate (w.append v) (appendRightContractionIndex j),
        (d.append e).contract (appendRightContractionIndex j)⟩).hom
        (ULift.up ((summandCompositionMap d e ≫
          contractionTensorMap (d.append e)
            (appendRightContractionIndex j)).hom (x.down ⊗ₜ[ℤ] y.down))) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (rightLeibnizDegreeEq n m))).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z (n + (m + 1)) ↦ largeSummandModule s)
          ⟨w.append (eraseIntermediate v j), d.append (e.contract j)⟩).hom
            (ULift.up (((𝟙 (summandModule d) ⊗ₘ contractionTensorMap e j) ≫
              summandCompositionMap d (e.contract j)).hom
                (x.down ⊗ₜ[ℤ] y.down))))
  apply (quotientGradedModule_eqToHom_inclusion_apply
    (rightLeibnizDegreeEq n m)
    (⟨w.append (eraseIntermediate v j), d.append (e.contract j)⟩ :
      GradedSummandIndex X Z (n + (m + 1)))
    (⟨eraseIntermediate (w.append v) (appendRightContractionIndex j),
      (d.append e).contract (appendRightContractionIndex j)⟩ :
        GradedSummandIndex X Z ((n + m) + 1)) ?_ _ _ ?_).symm
  · apply gradedSummandIndex_mk_heq_of_eq (rightLeibnizDegreeEq n m)
      (eraseIntermediate_append_right (w := w) j).symm
    exact (DegreeProfile.contract_append_right_heq d e j).symm
  · apply uliftUp_heq
    have htarget : summandModule (d.append (e.contract j)) =
        summandModule ((d.append e).contract (appendRightContractionIndex j)) :=
      eq_of_heq (summandModule_contract_append_right_heq d e j).symm
    exact moduleCatHom_apply_heq htarget
      (summandCompositionMap_contraction_append_right_heq d e j).symm
      (x.down ⊗ₜ[ℤ] y.down)

theorem contractionLargeMap_append_left_apply
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m))
    (i : Fin w.length) :
    (contractionLargeMap (d.append e)
        (appendLeftContractionIndex (v := v) i)).hom
        (largeSummandCompositionValue d e x y) =
      (d.contractionSign i * (m.negOnePow : ℤ)) •
        (eqToHom (congrArg (quotientGradedModule X Z)
          (leftLeibnizDegreeEq n m))).hom
          (largeSummandCompositionMap (d.contract i) e
            (((ModuleCat.uliftFunctor.{1} ℤ).map
              (contractionTensorMap d i)).hom x) y) := by
  unfold contractionLargeMap
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [contractionSign_append_left]
  congr 1
  change
    (Limits.Sigma.ι
      (fun s : GradedSummandIndex X Z ((n + m) + 1) ↦ largeSummandModule s)
      ⟨eraseIntermediate (w.append v) (appendLeftContractionIndex i),
        (d.append e).contract (appendLeftContractionIndex i)⟩).hom
        (ULift.up ((summandCompositionMap d e ≫
          contractionTensorMap (d.append e)
            (appendLeftContractionIndex i)).hom (x.down ⊗ₜ[ℤ] y.down))) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (leftLeibnizDegreeEq n m))).hom
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Z ((n + 1) + m) ↦ largeSummandModule s)
          ⟨(eraseIntermediate w i).append v, (d.contract i).append e⟩).hom
            (ULift.up (((contractionTensorMap d i ⊗ₘ 𝟙 (summandModule e)) ≫
              summandCompositionMap (d.contract i) e).hom
                (x.down ⊗ₜ[ℤ] y.down))))
  apply (quotientGradedModule_eqToHom_inclusion_apply
    (leftLeibnizDegreeEq n m)
    (⟨(eraseIntermediate w i).append v, (d.contract i).append e⟩ :
      GradedSummandIndex X Z ((n + 1) + m))
    (⟨eraseIntermediate (w.append v) (appendLeftContractionIndex i),
      (d.append e).contract (appendLeftContractionIndex i)⟩ :
        GradedSummandIndex X Z ((n + m) + 1)) ?_ _ _ ?_).symm
  · apply gradedSummandIndex_mk_heq_of_eq (leftLeibnizDegreeEq n m)
      (eraseIntermediate_append_left (v := v) i).symm
    exact (DegreeProfile.contract_append_left_heq d e i).symm
  · apply uliftUp_heq
    have htarget : summandModule ((d.contract i).append e) =
        summandModule ((d.append e).contract (appendLeftContractionIndex i)) :=
      eq_of_heq (summandModule_contract_append_left_heq d e i).symm
    exact moduleCatHom_apply_heq htarget
      (summandCompositionMap_contraction_append_left_heq d e i).symm
      (x.down ⊗ₜ[ℤ] y.down)

theorem largeSummandCompositionMap_leibniz
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (x : largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
    (y : largeSummandModule (⟨v, e⟩ : GradedSummandIndex Y Z m)) :
  (quotientTotalDifferential X Z (n + m)).hom
      (largeSummandCompositionMap d e x y) =
    (eqToHom (congrArg (quotientGradedModule X Z)
        (rightLeibnizDegreeEq n m))).hom
      (quotientCompositionMap X Y Z n (m + 1)
        ((Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
          ⟨w, d⟩).hom x)
        ((internalDifferentialFromSummand e +
          contractionDifferentialFromSummand e).hom y)) +
      m.negOnePow •
        (eqToHom (congrArg (quotientGradedModule X Z)
          (leftLeibnizDegreeEq n m))).hom
          (quotientCompositionMap X Y Z (n + 1) m
            ((internalDifferentialFromSummand d +
              contractionDifferentialFromSummand d).hom x)
            ((Limits.Sigma.ι
              (fun s : GradedSummandIndex Y Z m ↦ largeSummandModule s)
              ⟨v, e⟩).hom y)) := by
  rw [quotientTotalDifferential_largeSummandCompositionMap_partition]
  rw [transported_totalDifferentialComposition_right_sum
    (rightLeibnizDegreeEq n m) d e x y]
  rw [transported_totalDifferentialComposition_left_sum
    (leftLeibnizDegreeEq n m) d e x y]
  simp_rw [internalDifferentialLargeMap_append_left_apply d e x y]
  rw [internalDifferentialLargeMap_append_boundary_apply d e x y]
  simp_rw [internalDifferentialLargeMap_append_right_apply d e x y]
  simp_rw [contractionLargeMap_append_left_apply d e x y]
  simp_rw [contractionLargeMap_append_right_apply d e x y]
  simp_rw [internalSign_append_left d e, internalSign_append_right d e]
  rw [internalBoundaryKoszul_assembly d e]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  have hlast : d.internalSign (Fin.last w.length) = 1 := by
    have hempty : Finset.univ.filter
        (fun j : Fin (w.length + 1) ↦ Fin.last w.length < j) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j _
      exact not_lt_of_ge (Fin.le_last j)
    simp [DegreeProfile.internalSign, DegreeProfile.suffixTotal, hempty]
  rw [hlast]
  simp only [one_zsmul]
  have hswap (a : ℤ) (z : quotientGradedModule X Z ((n + m) + 1)) :
      (a * (m.negOnePow : ℤ)) • z = m.negOnePow • (a • z) := by
    rw [Units.smul_def, ← mul_zsmul, mul_comm]
  simp_rw [hswap]
  simp only [Units.smul_def]
  rw [Finset.sum_zsmul]
  rw [Finset.sum_zsmul]
  simp only [zsmul_add]
  abel


/-- A universe-1 copy of the integer coefficient ring for the large quotient carrier. -/
abbrev QuotientCoefficientRing := ULift.{1} ℤ

attribute [-instance] ULift.semiring

local instance quotientCoefficientCarrierModule (M : ModuleCat.{1} ℤ) :
    Module QuotientCoefficientRing (ULift.{0} M) := by
  infer_instance

attribute [-instance] ULift.module

/-- A large integer module regarded over the universe-matched coefficient ring. -/
abbrev quotientCoefficientModule (M : ModuleCat.{1} ℤ) :
    ModuleCat.{1} QuotientCoefficientRing :=
  ModuleCat.of QuotientCoefficientRing (ULift.{0} M)

/-- Transport an integer-linear map to the universe-matched coefficient modules. -/
def quotientLinearMapChangeScalars {M N : ModuleCat.{1} ℤ} (f : M →ₗ[ℤ] N) :
    quotientCoefficientModule M →ₗ[QuotientCoefficientRing]
      quotientCoefficientModule N where
  toFun x := ULift.up (f x.down)
  map_add' x y := by
    apply ULift.down_injective
    exact f.map_add x.down y.down
  map_smul' r x := by
    apply ULift.down_injective
    exact map_zsmul f r.down x.down

@[simp]
theorem quotientLinearMapChangeScalars_apply_up
    {M N : ModuleCat.{1} ℤ} (f : M →ₗ[ℤ] N) (x : M) :
    quotientLinearMapChangeScalars f (ULift.up x) = ULift.up (f x) :=
  rfl

@[simp]
theorem quotientLinearMapChangeScalars_id (M : ModuleCat.{1} ℤ) :
    quotientLinearMapChangeScalars (LinearMap.id : M →ₗ[ℤ] M) =
      LinearMap.id := by
  ext x
  rfl

theorem quotientLinearMapChangeScalars_comp
    {M N P : ModuleCat.{1} ℤ} (f : M →ₗ[ℤ] N) (g : N →ₗ[ℤ] P) :
    quotientLinearMapChangeScalars (g.comp f) =
      (quotientLinearMapChangeScalars g).comp
        (quotientLinearMapChangeScalars f) := by
  ext x
  rfl

/-- Change large integer modules to the universe-matched coefficient category. -/
def quotientCoefficientChange : ModuleCat.{1} ℤ ⥤
    ModuleCat.{1} QuotientCoefficientRing where
  obj := quotientCoefficientModule
  map f := ModuleCat.ofHom (quotientLinearMapChangeScalars f.hom)
  map_id _ := by
    apply ModuleCat.hom_ext
    rfl
  map_comp _ _ := by
    apply ModuleCat.hom_ext
    rfl

instance quotientCoefficientChangePreservesZeroMorphisms :
    quotientCoefficientChange.PreservesZeroMorphisms where
  map_zero := by
    intro M N
    apply ModuleCat.hom_ext
    rfl

/-- The corrected quotient Hom cochain complex over universe-matched coefficients. -/
def quotientCoefficientCochainComplex (X Y : ComplexCategory) :
    CochainComplex (ModuleCat.{1} QuotientCoefficientRing) ℤ :=
  (quotientCoefficientChange.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (quotientDGMappingCochainComplex X Y)

@[simp]
theorem quotientCoefficientCochainComplex_X (X Y : ComplexCategory) (n : ℤ) :
    (quotientCoefficientCochainComplex X Y).X n =
      quotientCoefficientModule (quotientGradedModule X Y n) :=
  rfl

@[simp]
theorem quotientCoefficientCochainComplex_d_succ
    (X Y : ComplexCategory) (n : ℤ) :
    (quotientCoefficientCochainComplex X Y).d n (n + 1) =
      ModuleCat.ofHom
        (quotientLinearMapChangeScalars (quotientTotalDifferential X Y n).hom) := by
  change quotientCoefficientChange.map
      ((quotientDGMappingCochainComplex X Y).d n (n + 1)) = _
  rw [quotientDGMappingCochainComplex_d_succ]
  rfl

/-- Transport an integer-bilinear map to the universe-matched coefficient modules. -/
def quotientBilinearMapChangeScalars {M N P : ModuleCat.{1} ℤ}
    (f : M →ₗ[ℤ] N →ₗ[ℤ] P) :
    quotientCoefficientModule M →ₗ[QuotientCoefficientRing]
      quotientCoefficientModule N →ₗ[QuotientCoefficientRing]
        quotientCoefficientModule P where
  toFun x :=
    { toFun := fun y ↦ ULift.up (f x.down y.down)
      map_add' := fun y₁ y₂ ↦ by
        apply ULift.down_injective
        exact (f x.down).map_add y₁.down y₂.down
      map_smul' := fun r y ↦ by
        apply ULift.down_injective
        simp [ULift.smul_def] }
  map_add' x₁ x₂ := by
    ext y
    simp [quotientCoefficientCarrierModule]
  map_smul' r x := by
    ext y
    change f (r.down • x.down) y.down = r.down • f x.down y.down
    exact DFunLike.congr_fun (map_zsmul f r.down x.down) y.down

/-- Homogeneous quotient composition as a morphism out of the honest large tensor product. -/
def quotientCompositionTensorMap (X Y Z : ComplexCategory) (n m : ℤ) :
    quotientCoefficientModule (quotientGradedModule X Y n) ⊗
        quotientCoefficientModule (quotientGradedModule Y Z m) ⟶
      quotientCoefficientModule (quotientGradedModule X Z (n + m)) :=
  ModuleCat.ofHom (TensorProduct.lift
    (quotientBilinearMapChangeScalars (quotientCompositionMap X Y Z n m)))

@[simp]
theorem quotientCompositionTensorMap_tmul
    (X Y Z : ComplexCategory) (n m : ℤ)
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    (quotientCompositionTensorMap X Y Z n m).hom
        (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y) =
      ULift.up (quotientCompositionMap X Y Z n m x y) :=
  rfl

theorem quotientCoefficient_eqToHom_apply_up
    {X Y : ComplexCategory} {p q : ℤ} (h : p = q)
    (x : quotientGradedModule X Y p) :
    (eqToHom (congrArg
      (fun k ↦ quotientCoefficientModule (quotientGradedModule X Y k)) h)).hom
        (ULift.up x) =
      ULift.up ((eqToHom (congrArg (quotientGradedModule X Y) h)).hom x) := by
  subst q
  rfl

@[simp]
theorem quotientCoefficient_zsmul_up
    {M : ModuleCat.{1} ℤ} (r : ℤ) (x : M) :
    r • (ULift.up x : quotientCoefficientModule M) = ULift.up (r • x) :=
  rfl

@[simp]
theorem quotientCompositionTensorMap_comp_changeScalars_tmul
    {X Y Z : ComplexCategory} {n m : ℤ} {P : ModuleCat.{1} ℤ}
    (f : quotientGradedModule X Z (n + m) →ₗ[ℤ] P)
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    (quotientCompositionTensorMap X Y Z n m ≫
        ModuleCat.ofHom (quotientLinearMapChangeScalars f)).hom
        (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y) =
      ULift.up (f (quotientCompositionMap X Y Z n m x y)) :=
  rfl

theorem quotientCompositionTensorMap_changeScalars_right_cast_tmul
    {X Y Z : ComplexCategory} {n m k p : ℤ} (h : n + k = p)
    (f : quotientGradedModule Y Z m →ₗ[ℤ] quotientGradedModule Y Z k)
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    ((𝟙 _ ⊗ₘ ModuleCat.ofHom (quotientLinearMapChangeScalars f)) ≫
        quotientCompositionTensorMap X Y Z n k ≫
        eqToHom (congrArg
          (fun q ↦ quotientCoefficientModule (quotientGradedModule X Z q)) h)).hom
        (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y) =
      ULift.up ((eqToHom (congrArg (quotientGradedModule X Z) h)).hom
        (quotientCompositionMap X Y Z n k x (f y))) := by
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  change (eqToHom (congrArg
    (fun q ↦ quotientCoefficientModule (quotientGradedModule X Z q)) h)).hom
      (ULift.up (quotientCompositionMap X Y Z n k x (f y))) = _
  exact quotientCoefficient_eqToHom_apply_up h _


theorem quotientCompositionTensorMap_changeScalars_left_cast_tmul
    {X Y Z : ComplexCategory} {n m k p : ℤ} (h : k + m = p)
    (f : quotientGradedModule X Y n →ₗ[ℤ] quotientGradedModule X Y k)
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    ((ModuleCat.ofHom (quotientLinearMapChangeScalars f) ⊗ₘ 𝟙 _) ≫
        quotientCompositionTensorMap X Y Z k m ≫
        eqToHom (congrArg
          (fun q ↦ quotientCoefficientModule (quotientGradedModule X Z q)) h)).hom
        (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y) =
      ULift.up ((eqToHom (congrArg (quotientGradedModule X Z) h)).hom
        (quotientCompositionMap X Y Z k m (f x) y)) := by
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply]
  change (eqToHom (congrArg
    (fun q ↦ quotientCoefficientModule (quotientGradedModule X Z q)) h)).hom
      (ULift.up (quotientCompositionMap X Y Z k m (f x) y)) = _
  exact quotientCoefficient_eqToHom_apply_up h _

theorem quotientCoefficientTensorMap_ext
    {M N P : ModuleCat.{1} ℤ}
    (f g : quotientCoefficientModule M ⊗ quotientCoefficientModule N ⟶
      quotientCoefficientModule P)
    (h : ∀ (x : M) (y : N),
      f.hom (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y) =
        g.hom (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y)) :
    f = g := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  exact congrArg ULift.down (h x y)

def quotientCoefficientTensorMapDownRightAdd
    {M N P : ModuleCat.{1} ℤ}
    (f : quotientCoefficientModule M ⊗ quotientCoefficientModule N ⟶
      quotientCoefficientModule P) (x : M) :
    N →+ P where
  toFun y := (f.hom
    (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y)).down
  map_zero' := by
    change (f.hom (ULift.up x ⊗ₜ[QuotientCoefficientRing] 0)).down = 0
    rw [TensorProduct.tmul_zero, map_zero]
    rfl
  map_add' y₁ y₂ := by
    change (f.hom (ULift.up x ⊗ₜ[QuotientCoefficientRing]
      (ULift.up y₁ + ULift.up y₂))).down = _
    rw [TensorProduct.tmul_add, map_add]
    rfl

def quotientCoefficientTensorMapDownAdd
    {M N P : ModuleCat.{1} ℤ}
    (f : quotientCoefficientModule M ⊗ quotientCoefficientModule N ⟶
      quotientCoefficientModule P) :
    M →+ (N →ₗ[ℤ] P) where
  toFun x := intLinearMapOfAddHom (quotientCoefficientTensorMapDownRightAdd f x)
  map_zero' := by
    apply LinearMap.ext
    intro y
    change (f.hom (0 ⊗ₜ[QuotientCoefficientRing] ULift.up y)).down = 0
    rw [TensorProduct.zero_tmul, map_zero]
    rfl
  map_add' x₁ x₂ := by
    apply LinearMap.ext
    intro y
    change (f.hom ((ULift.up x₁ + ULift.up x₂) ⊗ₜ[QuotientCoefficientRing]
      ULift.up y)).down = _
    rw [TensorProduct.add_tmul, map_add]
    rfl


def quotientCoefficientTensorMapDown
    {M N P : ModuleCat.{1} ℤ}
    (f : quotientCoefficientModule M ⊗ quotientCoefficientModule N ⟶
      quotientCoefficientModule P) :
    M →ₗ[ℤ] N →ₗ[ℤ] P :=
  intLinearMapOfAddHom (quotientCoefficientTensorMapDownAdd f)

theorem quotientGradedBilinearMap_ext
    {X Y Z : ComplexCategory} {n m : ℤ} {P : ModuleCat.{1} ℤ}
    (f g : quotientGradedModule X Y n →ₗ[ℤ]
      quotientGradedModule Y Z m →ₗ[ℤ] P)
    (h : ∀ (s : GradedSummandIndex X Y n) (t : GradedSummandIndex Y Z m)
      (x : largeSummandModule s) (y : largeSummandModule t),
      f ((Limits.Sigma.ι
          (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x)
          ((Limits.Sigma.ι
            (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u) t).hom y) =
        g ((Limits.Sigma.ι
          (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x)
          ((Limits.Sigma.ι
            (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u) t).hom y)) :
    f = g := by
  have houter : ModuleCat.ofHom f = ModuleCat.ofHom g := by
    apply Limits.Sigma.hom_ext
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change f ((Limits.Sigma.ι
        (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x) =
      g ((Limits.Sigma.ι
        (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x)
    have hinner : ModuleCat.ofHom
        (f ((Limits.Sigma.ι
          (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x)) =
      ModuleCat.ofHom
        (g ((Limits.Sigma.ι
          (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x)) := by
      apply Limits.Sigma.hom_ext
      intro t
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      exact h s t x y
    exact congrArg ModuleCat.Hom.hom hinner
  exact congrArg ModuleCat.Hom.hom houter

theorem quotientCoefficientTensorMap_ext_on_summands
    {X Y Z : ComplexCategory} {n m : ℤ} {P : ModuleCat.{1} ℤ}
    (f g : quotientCoefficientModule (quotientGradedModule X Y n) ⊗
        quotientCoefficientModule (quotientGradedModule Y Z m) ⟶
      quotientCoefficientModule P)
    (h : ∀ (s : GradedSummandIndex X Y n) (t : GradedSummandIndex Y Z m)
      (x : largeSummandModule s) (y : largeSummandModule t),
      f.hom
          (ULift.up ((Limits.Sigma.ι
              (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x)
            ⊗ₜ[QuotientCoefficientRing]
            ULift.up ((Limits.Sigma.ι
              (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u) t).hom y)) =
        g.hom
          (ULift.up ((Limits.Sigma.ι
              (fun u : GradedSummandIndex X Y n ↦ largeSummandModule u) s).hom x)
            ⊗ₜ[QuotientCoefficientRing]
            ULift.up ((Limits.Sigma.ι
              (fun u : GradedSummandIndex Y Z m ↦ largeSummandModule u) t).hom y))) :
    f = g := by
  apply quotientCoefficientTensorMap_ext f g
  intro x y
  apply ULift.down_injective
  have hdown : quotientCoefficientTensorMapDown f =
      quotientCoefficientTensorMapDown g := by
    apply quotientGradedBilinearMap_ext
    intro s t a b
    exact congrArg ULift.down (h s t a b)
  exact DFunLike.congr_fun (DFunLike.congr_fun hdown x) y

end QuotientCoefficient

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
