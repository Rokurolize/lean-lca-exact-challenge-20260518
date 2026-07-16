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

section QuotientCoefficient

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

end QuotientCoefficient

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
