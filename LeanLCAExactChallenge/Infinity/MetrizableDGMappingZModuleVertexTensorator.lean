import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModuleVertexAlexanderWhitney
import LeanLCAExactChallenge.Infinity.AlexanderWhitneyAssociativity

/-!
# The Dold--Kan inverse tensorator in degree zero

This file compares the inverse tensorator induced by normalized Alexander--Whitney with
the tensor product of the canonical degree-zero Dold--Kan projections.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial

theorem normalizedMoore_map_inverseTensorator_comp_counit
    (A B : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (normalizedMooreComplex (ModuleCat ℤ)).map
          (DoldKanMonoidal.inverseTensorator
            DoldKanMonoidal.normalizedMooreOplaxMonoidal A B) ≫
        DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app (A ⊗ B) =
      DoldKanMonoidal.normalizedAlexanderWhitney
          (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj A)
          (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj B) ≫
        HomologicalComplex.tensorHom
          (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A)
          (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B) := by
  let h := DoldKanMonoidal.normalizedMooreOplaxMonoidal
  letI : DoldKanMonoidal.NormalizedMooreOplaxMonoidal := h
  rw [DoldKanMonoidal.inverseTensorator_eq_adjunct h]
  let t := DoldKanMonoidal.normalizedAlexanderWhitney
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj A)
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj B) ≫
    HomologicalComplex.tensorHom
      (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app A)
      (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app B)
  let adj := DoldKanMonoidal.zModuleDoldKanEquivalence.toAdjunction
  change DoldKanMonoidal.zModuleDoldKanEquivalence.functor.map
        (adj.homEquiv _ _ t) ≫ adj.counit.app (A ⊗ B) = t
  exact (adj.homEquiv_counit _ _ (adj.homEquiv _ _ t)).symm.trans
    (Equiv.symm_apply_apply _ t)

theorem inverseTensorator_f_zero
    (A B : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    (DoldKanMonoidal.inverseTensorator
          DoldKanMonoidal.normalizedMooreOplaxMonoidal A B).app (op ⦋0⦌) ≫
        (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv =
      ((zModuleDoldKanInverseZeroIso A).inv ⊗ₘ
          (zModuleDoldKanInverseZeroIso B).inv) ≫
        HomologicalComplex.ιTensorObj A B 0 0 0 rfl := by
  let X := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj A
  let Y := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj B
  let μ := DoldKanMonoidal.inverseTensorator
    DoldKanMonoidal.normalizedMooreOplaxMonoidal A B
  let q := (NormalizedMooreComplex.objX (X ⊗ Y) 0).arrow
  let qAB := (NormalizedMooreComplex.objX
    (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj (A ⊗ B)) 0).arrow
  have hincRaw := HomologicalComplex.congr_hom
    ((inclusionOfMooreComplex (ModuleCat ℤ)).naturality μ) 0
  have hqAB :
      ((inclusionOfMooreComplex (ModuleCat ℤ)).app
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj (A ⊗ B))).f 0 =
        qAB := by
    dsimp only [qAB]
    exact inclusionOfMooreComplexMap_f _ 0
  have hq :
      ((inclusionOfMooreComplex (ModuleCat ℤ)).app (X ⊗ Y)).f 0 = q := by
    dsimp only [q]
    exact inclusionOfMooreComplexMap_f _ 0
  have hinc :
      ((normalizedMooreComplex (ModuleCat ℤ)).map μ).f 0 ≫ qAB =
        q ≫ μ.app (op ⦋0⦌) := by
    rw [← hqAB, ← hq]
    exact hincRaw
  have hzero' :
      qAB ≫ (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv =
        (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app
          (A ⊗ B)).f 0 := by
    change (NormalizedMooreComplex.objX
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj (A ⊗ B)) 0).arrow ≫
      (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv = _
    rw [zModuleDoldKanCounit_f_zero]
  have hchain := HomologicalComplex.congr_hom
    (normalizedMoore_map_inverseTensorator_comp_counit A B) 0
  have hAW := normalizedAlexanderWhitney_comp_counits_f_zero A B
  letI : IsIso q := by
    change IsIso (⊤ : Subobject ((X ⊗ Y).obj (op ⦋0⦌))).arrow
    infer_instance
  letI : Epi q := IsIso.epi_of_iso q
  apply (cancel_epi q).1
  change q ≫
      (μ.app (op ⦋0⦌) ≫ (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv) =
    q ≫ (((zModuleDoldKanInverseZeroIso A).inv ⊗ₘ
      (zModuleDoldKanInverseZeroIso B).inv) ≫
        HomologicalComplex.ιTensorObj A B 0 0 0 rfl)
  have h₁ :
      q ≫ (μ.app (op ⦋0⦌) ≫ (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv) =
        (q ≫ μ.app (op ⦋0⦌)) ≫
          (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv :=
    (Category.assoc _ _ _).symm
  have h₂ :
      (q ≫ μ.app (op ⦋0⦌)) ≫
          (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv =
        (((normalizedMooreComplex (ModuleCat ℤ)).map μ).f 0 ≫ qAB) ≫
          (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv := congrArg
    (fun t => t ≫ (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv) hinc.symm
  have h₃ :
      (((normalizedMooreComplex (ModuleCat ℤ)).map μ).f 0 ≫ qAB) ≫
          (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv =
        ((normalizedMooreComplex (ModuleCat ℤ)).map μ).f 0 ≫
          (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app
            (A ⊗ B)).f 0 :=
    (Category.assoc
      (((normalizedMooreComplex (ModuleCat ℤ)).map μ).f 0) qAB
      (zModuleDoldKanInverseZeroIso (A ⊗ B)).inv).trans
        (congrArg
          (fun t => ((normalizedMooreComplex (ModuleCat ℤ)).map μ).f 0 ≫ t)
          hzero')
  have h₄ :
      q ≫
          ((zModuleDoldKanInverseZeroIso A).inv ⊗ₘ
            (zModuleDoldKanInverseZeroIso B).inv) ≫
          HomologicalComplex.ιTensorObj A B 0 0 0 rfl =
        q ≫ (((zModuleDoldKanInverseZeroIso A).inv ⊗ₘ
          (zModuleDoldKanInverseZeroIso B).inv) ≫
            HomologicalComplex.ιTensorObj A B 0 0 0 rfl) :=
    rfl
  exact h₁.trans (h₂.trans (h₃.trans (hchain.trans (hAW.trans h₄))))

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
