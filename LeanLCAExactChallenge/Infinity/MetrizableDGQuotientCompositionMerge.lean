/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientCompositionInfrastructure

/-! # Settled composition in the corrected Drinfeld quotient -/

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
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
