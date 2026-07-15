/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientCompositionMerge

/-! # Composition in the corrected Drinfeld quotient -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

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

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
