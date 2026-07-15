/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientComplex
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDifferentialCancellation

/-! # Merge and transport infrastructure for corrected Drinfeld quotient composition -/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

theorem dgCochainCompTensorOfEq_tmul_identity_right
    (K L : ComplexCategory) (p : ℤ)
    (x : (dgHomZModuleCochainComplex K L).X p) :
    (dgCochainCompTensorOfEq K L L L rfl
      (show p + 0 = p by omega)).hom
        (x ⊗ₜ[ℤ] identityCochain L) = x := by
  change x.comp (CochainComplex.HomComplex.Cochain.ofHom (𝟙 L.obj))
    (Int.add_zero p) = x
  ext i
  simp

theorem dgCochainCompTensorOfEq_identity_left_tmul
    (K L : ComplexCategory) (p : ℤ)
    (x : (dgHomZModuleCochainComplex K L).X p) :
    (dgCochainCompTensorOfEq K K K L rfl
      (show 0 + p = p by omega)).hom
        (identityCochain K ⊗ₜ[ℤ] x) = x := by
  change (CochainComplex.HomComplex.Cochain.ofHom (𝟙 K.obj)).comp x
    (Int.zero_add p) = x
  ext i
  simp

def identityCochainInclusion (K : ComplexCategory) :
    𝟙_ (ModuleCat.{0} ℤ) ⟶ (dgHomZModuleCochainComplex K K).X 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (identityCochain K))

theorem dgCochainCompTensorOfEq_right_unit
    (K L : ComplexCategory) (p : ℤ) :
    (ρ_ ((dgHomZModuleCochainComplex K L).X p)).inv ≫
        (𝟙 _ ⊗ₘ identityCochainInclusion L) ≫
        dgCochainCompTensorOfEq K L L L rfl
          (show p + 0 = p by omega) =
      𝟙 ((dgHomZModuleCochainComplex K L).X p) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, CategoryTheory.id_apply,
    identityCochainInclusion]
  change (dgCochainCompTensorOfEq K L L L rfl
      (show p + 0 = p by omega)).hom
        (x ⊗ₜ[ℤ] (LinearMap.toSpanSingleton ℤ _
          (identityCochain L)) 1) = x
  rw [LinearMap.toSpanSingleton_apply_one]
  exact dgCochainCompTensorOfEq_tmul_identity_right K L p x

theorem dgCochainCompTensorOfEq_right_unit_of_eq
    (K L L' : ComplexCategory) (h : L = L') (p : ℤ) :
    (ρ_ ((dgHomZModuleCochainComplex K L).X p)).inv ≫
        (𝟙 _ ⊗ₘ identityCochainInclusion L') ≫
        dgCochainCompTensorOfEq K L L' L' h
          (show p + 0 = p by omega) ≫
        eqToHom (congrArg
          (fun T ↦ (dgHomZModuleCochainComplex K T).X p) h.symm) =
      𝟙 ((dgHomZModuleCochainComplex K L).X p) := by
  subst L'
  simpa using dgCochainCompTensorOfEq_right_unit K L p

def dgCochainCompRightUnitTargetEq
    (K L L' : ComplexCategory) (h : L = L') (p : ℤ) :
    (dgHomZModuleCochainComplex K L').X (p + 0) =
      (dgHomZModuleCochainComplex K L).X p := by
  subst L'
  rw [Int.add_zero]

theorem dgCochainCompTensorOfEq_comp_degree_eqToHom
    (K L L' M : ComplexCategory) (hL : L = L')
    {p q r s : ℤ} (h : p + q = r) (k : r = s) :
    dgCochainCompTensorOfEq K L L' M hL h ≫
        eqToHom (congrArg
          (fun t ↦ (dgHomZModuleCochainComplex K M).X t) k) =
      dgCochainCompTensorOfEq K L L' M hL (h.trans k) := by
  subst s
  simp

theorem dgCochainCompTensorOfEq_right_unit_raw
    (K L L' : ComplexCategory) (h : L = L') (p : ℤ) :
    (ρ_ ((dgHomZModuleCochainComplex K L).X p)).inv ≫
        (𝟙 _ ⊗ₘ identityCochainInclusion L') ≫
        dgCochainCompTensorOfEq K L L' L' h
          (show p + 0 = p + 0 by rfl) ≫
        eqToHom (dgCochainCompRightUnitTargetEq K L L' h p) =
      𝟙 ((dgHomZModuleCochainComplex K L).X p) := by
  subst L'
  have hk : dgCochainCompRightUnitTargetEq K L L rfl p =
      congrArg (fun t ↦ (dgHomZModuleCochainComplex K L).X t)
        (Int.add_zero p) := Subsingleton.elim _ _
  rw [hk, dgCochainCompTensorOfEq_comp_degree_eqToHom]
  · convert dgCochainCompTensorOfEq_right_unit K L p using 1
  · exact Int.add_zero p

theorem dgCochainCompTensorOfEq_left_unit
    (K L : ComplexCategory) (p : ℤ) :
    (λ_ ((dgHomZModuleCochainComplex K L).X p)).inv ≫
        (identityCochainInclusion K ⊗ₘ 𝟙 _) ≫
        dgCochainCompTensorOfEq K K K L rfl
          (show 0 + p = p by omega) =
      𝟙 ((dgHomZModuleCochainComplex K L).X p) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, CategoryTheory.id_apply,
    identityCochainInclusion]
  change (dgCochainCompTensorOfEq K K K L rfl
      (show 0 + p = p by omega)).hom
        ((LinearMap.toSpanSingleton ℤ _ (identityCochain K)) 1 ⊗ₜ[ℤ] x) = x
  rw [LinearMap.toSpanSingleton_apply_one]
  exact dgCochainCompTensorOfEq_identity_left_tmul K L p x

theorem dgCochainCompTensorOfEq_left_unit_of_eq
    (K K' L : ComplexCategory) (h : K = K') (p : ℤ) :
    (λ_ ((dgHomZModuleCochainComplex K' L).X p)).inv ≫
        (identityCochainInclusion K ⊗ₘ 𝟙 _) ≫
        dgCochainCompTensorOfEq K K K' L h
          (show 0 + p = p by omega) ≫
        eqToHom (congrArg
          (fun T ↦ (dgHomZModuleCochainComplex T L).X p) h) =
      𝟙 ((dgHomZModuleCochainComplex K' L).X p) := by
  subst K'
  simpa using dgCochainCompTensorOfEq_left_unit K L p

def dgCochainCompLeftUnitTargetEq
    (K K' L : ComplexCategory) (h : K = K') (p : ℤ) :
    (dgHomZModuleCochainComplex K L).X (0 + p) =
      (dgHomZModuleCochainComplex K' L).X p := by
  subst K'
  rw [Int.zero_add]

theorem dgCochainCompTensorOfEq_left_unit_raw
    (K K' L : ComplexCategory) (h : K = K') (p : ℤ) :
    (λ_ ((dgHomZModuleCochainComplex K' L).X p)).inv ≫
        (identityCochainInclusion K ⊗ₘ 𝟙 _) ≫
        dgCochainCompTensorOfEq K K K' L h
          (show 0 + p = 0 + p by rfl) ≫
        eqToHom (dgCochainCompLeftUnitTargetEq K K' L h p) =
      𝟙 ((dgHomZModuleCochainComplex K' L).X p) := by
  subst K'
  have hk : dgCochainCompLeftUnitTargetEq K K L rfl p =
      congrArg (fun t ↦ (dgHomZModuleCochainComplex K L).X t)
        (Int.zero_add p) := Subsingleton.elim _ _
  rw [hk, dgCochainCompTensorOfEq_comp_degree_eqToHom]
  · convert dgCochainCompTensorOfEq_left_unit K L p using 1
  · exact Int.zero_add p

theorem append_nil {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    w.append (nil Y Y) = w := by
  cases w with
  | mk length intermediate =>
      simp only [append, nil, Nat.add_zero, DrinfeldWord.mk.injEq, heq_eq_eq]
      constructor
      · trivial
      funext i
      simpa using (Fin.addCases_left
        (motive := fun _ ↦ CorrectedAcyclicComplexCategory)
        (m := length) (n := 0) (left := intermediate)
        (right := fun i ↦ Fin.elim0 i) i)

theorem nil_append {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    (nil X X).append w = w := by
  cases w with
  | mk length intermediate =>
      simp only [append, nil, Nat.zero_add, DrinfeldWord.mk.injEq]
      constructor
      · trivial
      refine (Fin.heq_fun_iff (Nat.zero_add length)).mpr ?_
      intro i
      simp only [Fin.addCases, not_lt_zero, ↓reduceDIte, Nat.add_zero,
        Fin.subNat_zero, eq_rec_constant]
      apply congrArg intermediate
      apply Fin.ext
      rfl

theorem append_assoc {W X Y Z : ComplexCategory}
    (u : DrinfeldWord W X) (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    (u.append w).append v = u.append (w.append v) := by
  cases u with
  | mk ulength uintermediate =>
    cases w with
    | mk wlength wintermediate =>
      cases v with
      | mk vlength vintermediate =>
        simp only [append, Nat.add_assoc, DrinfeldWord.mk.injEq]
        constructor
        · trivial
        refine (Fin.heq_fun_iff (Nat.add_assoc ulength wlength vlength)).mpr ?_
        intro i
        by_cases hleft : i.val < ulength
        · have houter : i.val < ulength + wlength := by omega
          simp only [Fin.addCases, houter, ↓reduceDIte, Fin.val_castLT,
            hleft, Fin.castLT_mk]
          apply congrArg uintermediate
          apply Fin.ext
          rfl
        · by_cases hmiddle : i.val < ulength + wlength
          · have hshift : i.val - ulength < wlength := by omega
            simp only [Fin.addCases, hmiddle, ↓reduceDIte, Fin.val_castLT,
              hleft, Fin.cast_castLT, eq_rec_constant, Fin.cast_mk,
              Fin.subNat_mk, Fin.natAdd_mk, hshift, Fin.castLT_mk]
            apply congrArg wintermediate
            apply Fin.ext
            rfl
          · have hshift : ¬i.val - ulength < wlength := by omega
            simp only [Fin.addCases, hmiddle, ↓reduceDIte, eq_rec_constant,
              hleft, Fin.cast_mk, Fin.subNat_mk, Fin.natAdd_mk, hshift]
            apply congrArg vintermediate
            apply Fin.ext
            exact (Nat.sub_sub i.val ulength wlength).symm

def DegreeProfile.castTotal {X Y : ComplexCategory} {w : DrinfeldWord X Y}
    {n m : ℤ} (h : n = m) (d : DegreeProfile w n) : DegreeProfile w m := by
  subst h
  exact d

@[simp]
theorem DegreeProfile.castTotal_arrowDegree
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (h : n = m) (d : DegreeProfile w n) (i : Fin (w.length + 1)) :
    (d.castTotal h).arrowDegree i = d.arrowDegree i := by
  subst h
  rfl

def DegreeProfile.transport {X Y : ComplexCategory} {w v : DrinfeldWord X Y}
    {n m : ℤ} (hw : w = v) (hn : n = m) (d : DegreeProfile w n) :
    DegreeProfile v m := by
  subst hw
  subst hn
  exact d

@[simp]
theorem DegreeProfile.transport_arrowDegree
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n m : ℤ}
    (hw : w = v) (hn : n = m) (d : DegreeProfile w n)
    (i : Fin (v.length + 1)) :
    (d.transport hw hn).arrowDegree i =
      d.arrowDegree
        (Fin.cast (congrArg (fun q : DrinfeldWord X Y ↦ q.length + 1) hw).symm i) := by
  subst hw
  subst hn
  rfl

def appendArrowDegree
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Fin ((w.append v).length + 1) → ℤ :=
  fun q ↦
    Fin.addCases
      (fun i : Fin w.length ↦ d.arrowDegree i.castSucc)
      (Fin.cases
        (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
        (fun j : Fin v.length ↦ e.arrowDegree j.succ))
      (Fin.cast (by simp [append]; omega) q)

def DegreeProfile.append
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    DegreeProfile (w.append v) (n + m) where
  arrowDegree := appendArrowDegree d e
  totalDegree := by
    have hsum :
        (∑ q, appendArrowDegree d e q) =
          ∑ q : Fin (w.length + (v.length + 1)),
            Fin.addCases
              (fun i : Fin w.length ↦ d.arrowDegree i.castSucc)
              (Fin.cases
                (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
                (fun j : Fin v.length ↦ e.arrowDegree j.succ)) q := by
      apply Fintype.sum_equiv
        (finCongr (by simp [Nat.add_assoc]))
      intro q
      rfl
    rw [hsum, Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    have hd := d.totalDegree
    have he := e.totalDegree
    rw [Fin.sum_univ_castSucc] at hd
    rw [Fin.sum_univ_succ] at he
    simp only [append_length]
    omega

def degreeBoundaryMerge : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | [x], y :: ys => (x + y) :: ys
  | x :: x' :: xs, y :: ys =>
      x :: degreeBoundaryMerge (x' :: xs) (y :: ys)

theorem degreeBoundaryMerge_ne_nil
    (xs ys : List ℤ) (hxs : xs ≠ []) (hys : ys ≠ []) :
    degreeBoundaryMerge xs ys ≠ [] := by
  cases xs with
  | nil => exact False.elim (hxs rfl)
  | cons x xs =>
      cases xs with
      | nil =>
          cases ys with
          | nil => exact False.elim (hys rfl)
          | cons y ys => simp [degreeBoundaryMerge]
      | cons x' xs =>
          cases ys with
          | nil => exact False.elim (hys rfl)
          | cons y ys => simp [degreeBoundaryMerge]

theorem degreeBoundaryMerge_assoc
    (xs ys zs : List ℤ) (hxs : xs ≠ []) (hys : ys ≠ []) (hzs : zs ≠ []) :
    degreeBoundaryMerge (degreeBoundaryMerge xs ys) zs =
      degreeBoundaryMerge xs (degreeBoundaryMerge ys zs) := by
  induction xs with
  | nil => exact False.elim (hxs rfl)
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases ys with
          | nil => exact False.elim (hys rfl)
          | cons y ys =>
              cases ys with
              | nil =>
                  cases zs with
                  | nil => exact False.elim (hzs rfl)
                  | cons z zs =>
                      simp [degreeBoundaryMerge, Int.add_assoc]
              | cons y' ys =>
                  cases zs with
                  | nil => exact False.elim (hzs rfl)
                  | cons z zs =>
                      simp [degreeBoundaryMerge]
      | cons x' xs =>
          cases ys with
          | nil => exact False.elim (hys rfl)
          | cons y ys =>
              cases zs with
              | nil => exact False.elim (hzs rfl)
              | cons z zs =>
                  have hmerge := degreeBoundaryMerge_ne_nil
                    (x' :: xs) (y :: ys) (by simp) (by simp)
                  cases h : degreeBoundaryMerge (x' :: xs) (y :: ys) with
                  | nil => exact False.elim (hmerge h)
                  | cons a as =>
                      have hright := degreeBoundaryMerge_ne_nil
                        (y :: ys) (z :: zs) (by simp) (by simp)
                      cases hr : degreeBoundaryMerge (y :: ys) (z :: zs) with
                      | nil => exact False.elim (hright hr)
                      | cons b bs =>
                          simp only [degreeBoundaryMerge, h]
                          exact congrArg (List.cons x) (by simpa [h, hr] using ih (by simp))

theorem degreeBoundaryMerge_cons_of_ne_nil
    (x : ℤ) (xs : List ℤ) (hxs : xs ≠ []) (y : ℤ) (ys : List ℤ) :
    degreeBoundaryMerge (x :: xs) (y :: ys) =
      x :: degreeBoundaryMerge xs (y :: ys) := by
  cases xs with
  | nil => exact False.elim (hxs rfl)
  | cons x' xs => rfl

theorem degreeBoundaryMerge_ofFn
    (k l : ℕ) (f : Fin (k + 1) → ℤ) (g : Fin (l + 1) → ℤ) :
    degreeBoundaryMerge (List.ofFn f) (List.ofFn g) =
      List.ofFn (fun i : Fin k ↦ f i.castSucc) ++
        (f (Fin.last k) + g 0) :: List.ofFn (fun j : Fin l ↦ g j.succ) := by
  induction k with
  | zero => simp [List.ofFn_succ, degreeBoundaryMerge]
  | succ k ih =>
      rw [List.ofFn_succ (f := f), List.ofFn_succ (f := g),
        degreeBoundaryMerge_cons_of_ne_nil]
      · conv_rhs => rw [List.ofFn_succ]
        apply congrArg (List.cons (f 0))
        rw [← List.ofFn_succ (f := g)]
        have hprefix :
            (fun i : Fin k ↦ f i.succ.castSucc) =
              (fun i : Fin k ↦ f i.castSucc.succ) := by
          funext i
          apply congrArg f
          apply Fin.ext
          rfl
        have hlast : (Fin.last k).succ = Fin.last (k + 1) := by
          apply Fin.ext
          rfl
        rw [hprefix, ← hlast]
        exact ih (fun i : Fin (k + 1) ↦ f i.succ)
      · simp

def tensorModuleListAppendIso :
    (Ms Ns : List (ModuleCat.{0} ℤ)) →
      tensorModuleList Ms ⊗ tensorModuleList Ns ≅ tensorModuleList (Ms ++ Ns)
  | [], Ns => λ_ (tensorModuleList Ns)
  | M :: Ms, Ns =>
      α_ M (tensorModuleList Ms) (tensorModuleList Ns) ≪≫
        MonoidalCategory.tensorIso (Iso.refl M) (tensorModuleListAppendIso Ms Ns)

theorem tensor_obj_eqToHom
    (M : ModuleCat.{0} ℤ) {N P : ModuleCat.{0} ℤ} (h : N = P) :
    eqToHom (congrArg (fun Q ↦ M ⊗ Q) h) = 𝟙 M ⊗ₘ eqToHom h := by
  subst P
  exact (MonoidalCategory.id_tensorHom_id M N).symm

theorem tensorModuleListAppendIso_assoc
    (Ms Ns Ps : List (ModuleCat.{0} ℤ)) :
    (α_ (tensorModuleList Ms) (tensorModuleList Ns)
          (tensorModuleList Ps)).inv ≫
        ((tensorModuleListAppendIso Ms Ns).hom ⊗ₘ
          𝟙 (tensorModuleList Ps)) ≫
        (tensorModuleListAppendIso (Ms ++ Ns) Ps).hom ≫
        eqToHom (congrArg tensorModuleList (List.append_assoc Ms Ns Ps)) =
      (𝟙 (tensorModuleList Ms) ⊗ₘ
          (tensorModuleListAppendIso Ns Ps).hom) ≫
        (tensorModuleListAppendIso Ms (Ns ++ Ps)).hom := by
  induction Ms with
  | nil =>
      dsimp [tensorModuleListAppendIso, tensorModuleList, tensorModuleListOver]
      monoidal
  | cons M Ms ih =>
      let a : tensorModuleList Ms ⊗ tensorModuleList Ns ⟶
          tensorModuleList (Ms ++ Ns) :=
        (tensorModuleListAppendIso Ms Ns).hom
      let b : tensorModuleList (Ms ++ Ns) ⊗ tensorModuleList Ps ⟶
          tensorModuleList ((Ms ++ Ns) ++ Ps) :=
        (tensorModuleListAppendIso (Ms ++ Ns) Ps).hom
      let c : tensorModuleList Ns ⊗ tensorModuleList Ps ⟶
          tensorModuleList (Ns ++ Ps) :=
        (tensorModuleListAppendIso Ns Ps).hom
      let q : tensorModuleList Ms ⊗ tensorModuleList (Ns ++ Ps) ⟶
          tensorModuleList (Ms ++ (Ns ++ Ps)) :=
        (tensorModuleListAppendIso Ms (Ns ++ Ps)).hom
      let t : tensorModuleList ((Ms ++ Ns) ++ Ps) ⟶
          tensorModuleList (Ms ++ (Ns ++ Ps)) :=
        eqToHom (congrArg tensorModuleList (List.append_assoc Ms Ns Ps))
      have htransport : eqToHom (congrArg tensorModuleList
          (List.append_assoc (M :: Ms) Ns Ps)) =
          𝟙 M ⊗ₘ t := by
        change eqToHom (congrArg (fun Q : ModuleCat.{0} ℤ ↦ M ⊗ Q)
            (congrArg tensorModuleList (List.append_assoc Ms Ns Ps))) = _
        simpa only [t] using tensor_obj_eqToHom M
          (congrArg tensorModuleList (List.append_assoc Ms Ns Ps))
      change
        (α_ (tensorModuleList Ms) (tensorModuleList Ns)
              (tensorModuleList Ps)).inv ≫
            (a ⊗ₘ 𝟙 (tensorModuleList Ps)) ≫ b ≫ t =
          (𝟙 (tensorModuleList Ms) ⊗ₘ c) ≫ q at ih
      dsimp [tensorModuleListAppendIso, tensorModuleList, tensorModuleListOver]
      erw [htransport]
      simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
      change
        (α_ (M ⊗ tensorModuleList Ms) (tensorModuleList Ns)
              (tensorModuleList Ps)).inv ≫
            (((α_ M (tensorModuleList Ms) (tensorModuleList Ns)).hom ≫
                (𝟙 M ⊗ₘ a)) ⊗ₘ 𝟙 (tensorModuleList Ps)) ≫
            (α_ M (tensorModuleList (Ms ++ Ns))
              (tensorModuleList Ps)).hom ≫
            (𝟙 M ⊗ₘ b) ≫ (𝟙 M ⊗ₘ t) =
          (𝟙 (M ⊗ tensorModuleList Ms) ⊗ₘ c) ≫
            (α_ M (tensorModuleList Ms)
              (tensorModuleList (Ns ++ Ps))).hom ≫
            (𝟙 M ⊗ₘ q)
      calc
        _ = (α_ M (tensorModuleList Ms)
              (tensorModuleList Ns ⊗ tensorModuleList Ps)).hom ≫
            (𝟙 M ⊗ₘ
              ((α_ (tensorModuleList Ms) (tensorModuleList Ns)
                    (tensorModuleList Ps)).inv ≫
                (a ⊗ₘ 𝟙 (tensorModuleList Ps)) ≫ b ≫ t)) := by
            dsimp [tensorModuleList, tensorModuleListOver]
            monoidal
        _ = (α_ M (tensorModuleList Ms)
              (tensorModuleList Ns ⊗ tensorModuleList Ps)).hom ≫
            (𝟙 M ⊗ₘ
              ((𝟙 (tensorModuleList Ms) ⊗ₘ c) ≫ q)) := by rw [ih]
        _ = _ := by
          dsimp [tensorModuleList, tensorModuleListOver]
          monoidal

theorem tensorModuleListAppendIso_assoc_inv_transport
    (Ms Ns Ps : List (ModuleCat.{0} ℤ)) :
    (α_ (tensorModuleList Ms) (tensorModuleList Ns)
          (tensorModuleList Ps)).inv ≫
        ((tensorModuleListAppendIso Ms Ns).hom ⊗ₘ
          𝟙 (tensorModuleList Ps)) ≫
        (tensorModuleListAppendIso (Ms ++ Ns) Ps).hom =
      (𝟙 (tensorModuleList Ms) ⊗ₘ
          (tensorModuleListAppendIso Ns Ps).hom) ≫
        (tensorModuleListAppendIso Ms (Ns ++ Ps)).hom ≫
        eqToHom (congrArg tensorModuleList
          (List.append_assoc Ms Ns Ps).symm) := by
  apply (cancel_mono (eqToHom (congrArg tensorModuleList
    (List.append_assoc Ms Ns Ps)))).mp
  simp only [Category.assoc, eqToHom_trans]
  rw [tensorModuleListAppendIso_assoc]
  simp

theorem tensorModuleListAppendIso_eqToHom
    {Ms Ms' Ns Ns' : List (ModuleCat.{0} ℤ)}
    (hM : Ms = Ms') (hN : Ns = Ns') :
    (eqToHom (congrArg tensorModuleList hM) ⊗ₘ
        eqToHom (congrArg tensorModuleList hN)) ≫
      (tensorModuleListAppendIso Ms' Ns').hom =
    (tensorModuleListAppendIso Ms Ns).hom ≫
      eqToHom (congrArg tensorModuleList
        (congrArg₂ List.append hM hN)) := by
  subst Ms'
  subst Ns'
  simp

def tensorModuleListWhiskerRight
    {Ms Ns : List (ModuleCat.{0} ℤ)} (Ps : List (ModuleCat.{0} ℤ))
    (f : tensorModuleList Ms ⟶ tensorModuleList Ns) :
    tensorModuleList (Ms ++ Ps) ⟶ tensorModuleList (Ns ++ Ps) :=
  (tensorModuleListAppendIso Ms Ps).inv ≫
    (f ⊗ₘ 𝟙 (tensorModuleList Ps)) ≫
    (tensorModuleListAppendIso Ns Ps).hom

def tensorModuleListWhiskerLeft
    (Ps : List (ModuleCat.{0} ℤ)) {Ms Ns : List (ModuleCat.{0} ℤ)}
    (f : tensorModuleList Ms ⟶ tensorModuleList Ns) :
    tensorModuleList (Ps ++ Ms) ⟶ tensorModuleList (Ps ++ Ns) :=
  (tensorModuleListAppendIso Ps Ms).inv ≫
    (𝟙 (tensorModuleList Ps) ⊗ₘ f) ≫
    (tensorModuleListAppendIso Ps Ns).hom

@[reassoc]
theorem tensorModuleListAppendIso_whiskerRight
    {Ms Ns : List (ModuleCat.{0} ℤ)} (Ps : List (ModuleCat.{0} ℤ))
    (f : tensorModuleList Ms ⟶ tensorModuleList Ns) :
    (f ⊗ₘ 𝟙 (tensorModuleList Ps)) ≫
        (tensorModuleListAppendIso Ns Ps).hom =
      (tensorModuleListAppendIso Ms Ps).hom ≫
        tensorModuleListWhiskerRight Ps f := by
  simp [tensorModuleListWhiskerRight]

@[reassoc]
theorem tensorModuleListAppendIso_whiskerLeft
    (Ps : List (ModuleCat.{0} ℤ)) {Ms Ns : List (ModuleCat.{0} ℤ)}
    (f : tensorModuleList Ms ⟶ tensorModuleList Ns) :
    (𝟙 (tensorModuleList Ps) ⊗ₘ f) ≫
        (tensorModuleListAppendIso Ps Ns).hom =
      (tensorModuleListAppendIso Ps Ms).hom ≫
        tensorModuleListWhiskerLeft Ps f := by
  simp [tensorModuleListWhiskerLeft]

theorem tensorModuleListWhiskerRight_comp
    {Ms Ns Ps : List (ModuleCat.{0} ℤ)}
    (Qs : List (ModuleCat.{0} ℤ))
    (f : tensorModuleList Ms ⟶ tensorModuleList Ns)
    (g : tensorModuleList Ns ⟶ tensorModuleList Ps) :
    tensorModuleListWhiskerRight Qs (f ≫ g) =
      tensorModuleListWhiskerRight Qs f ≫
        tensorModuleListWhiskerRight Qs g := by
  simp [tensorModuleListWhiskerRight, Category.assoc]

theorem tensorModuleListWhiskerLeft_comp
    (Qs : List (ModuleCat.{0} ℤ))
    {Ms Ns Ps : List (ModuleCat.{0} ℤ)}
    (f : tensorModuleList Ms ⟶ tensorModuleList Ns)
    (g : tensorModuleList Ns ⟶ tensorModuleList Ps) :
    tensorModuleListWhiskerLeft Qs (f ≫ g) =
      tensorModuleListWhiskerLeft Qs f ≫
        tensorModuleListWhiskerLeft Qs g := by
  simp [tensorModuleListWhiskerLeft, Category.assoc]

theorem tensorModuleListWhiskerRight_eqToHom
    {Ms Ns : List (ModuleCat.{0} ℤ)} (Ps : List (ModuleCat.{0} ℤ))
    (h : Ms = Ns) :
    tensorModuleListWhiskerRight Ps
        (eqToHom (congrArg tensorModuleList h)) =
      eqToHom (congrArg tensorModuleList
        (congrArg₂ List.append h (rfl : Ps = Ps))) := by
  subst Ns
  simp [tensorModuleListWhiskerRight]

theorem tensorModuleListWhiskerLeft_eqToHom
    (Ps : List (ModuleCat.{0} ℤ)) {Ms Ns : List (ModuleCat.{0} ℤ)}
    (h : Ms = Ns) :
    tensorModuleListWhiskerLeft Ps
        (eqToHom (congrArg tensorModuleList h)) =
      eqToHom (congrArg tensorModuleList
        (congrArg₂ List.append (rfl : Ps = Ps) h)) := by
  subst Ns
  simp [tensorModuleListWhiskerLeft]

def adjacentMergeAfter : (xs : List (ModuleCat.{0} ℤ)) →
    {M N P : ModuleCat.{0} ℤ} → {ys : List (ModuleCat.{0} ℤ)} →
    Quiver.Hom (M ⊗ N) P →
      AdjacentMergeData (xs ++ M :: N :: ys) (xs ++ P :: ys)
  | [], _, _, _, _, f => .head f
  | _ :: xs, M, N, P, ys, f =>
      .tail (adjacentMergeAfter xs (M := M) (N := N) (P := P)
        (ys := ys) f)

def AdjacentMergeData.prefix : (xs : List (ModuleCat.{0} ℤ)) →
    {source target : List (ModuleCat.{0} ℤ)} →
      AdjacentMergeData source target →
        AdjacentMergeData (xs ++ source) (xs ++ target)
  | [], _, _, f => f
  | _ :: xs, _, _, f => .tail (f.prefix xs)

def AdjacentMergeData.suffix :
    {source target : List (ModuleCat.{0} ℤ)} →
      AdjacentMergeData source target →
      (Ps : List (ModuleCat.{0} ℤ)) →
        AdjacentMergeData (source ++ Ps) (target ++ Ps)
  | _, _, @AdjacentMergeData.head M N P Ms f, Ps =>
      @AdjacentMergeData.head M N P (Ms ++ Ps) f
  | _, _, @AdjacentMergeData.tail M Ms Ns f, Ps =>
      @AdjacentMergeData.tail M (Ms ++ Ps) (Ns ++ Ps) (f.suffix Ps)

theorem AdjacentMergeData.suffix_tensorMap_naturality
    {source target : List (ModuleCat.{0} ℤ)}
    (f : AdjacentMergeData source target) (Ps : List (ModuleCat.{0} ℤ)) :
    (tensorModuleListAppendIso source Ps).hom ≫ (f.suffix Ps).tensorMap =
      (f.tensorMap ⊗ₘ 𝟙 (tensorModuleList Ps)) ≫
        (tensorModuleListAppendIso target Ps).hom := by
  induction f with
  | @head M N P Ms f =>
      dsimp [AdjacentMergeData.suffix, AdjacentMergeData.tensorMap,
        tensorModuleListAppendIso]
      dsimp only [tensorModuleList, tensorModuleListOver]
      let t := (tensorModuleListAppendIso Ms Ps).hom
      change (α_ M (N ⊗ tensorModuleList Ms) (tensorModuleList Ps)).hom ≫
          (𝟙 M ⊗ₘ ((α_ N (tensorModuleList Ms)
            (tensorModuleList Ps)).hom ≫ (𝟙 N ⊗ₘ t))) ≫
          (α_ M N (tensorModuleList (Ms ++ Ps))).inv ≫
          (f ⊗ₘ 𝟙 (tensorModuleList (Ms ++ Ps))) =
        (((α_ M N (tensorModuleList Ms)).inv ≫
            (f ⊗ₘ 𝟙 (tensorModuleList Ms))) ⊗ₘ
              𝟙 (tensorModuleList Ps)) ≫
          (α_ P (tensorModuleList Ms) (tensorModuleList Ps)).hom ≫
          (𝟙 P ⊗ₘ t)
      simp only [MonoidalCategory.id_tensorHom,
        MonoidalCategory.whiskerLeft_comp,
        MonoidalCategory.tensorHom_id, Category.assoc,
        MonoidalCategory.comp_whiskerRight]
      rw [MonoidalCategory.associator_inv_naturality_right_assoc]
      rw [MonoidalCategory.whisker_exchange]
      have hcoherence :
          (α_ M (N ⊗ tensorModuleList Ms)
                (tensorModuleList Ps)).hom ≫
              M ◁ (α_ N (tensorModuleList Ms)
                (tensorModuleList Ps)).hom ≫
              (α_ M N (tensorModuleList Ms ⊗
                tensorModuleList Ps)).inv =
            (α_ M N (tensorModuleList Ms)).inv ▷
                tensorModuleList Ps ≫
              (α_ (M ⊗ N) (tensorModuleList Ms)
                (tensorModuleList Ps)).hom := by
        monoidal
      slice_lhs 1 3 => rw [hcoherence]
      simp only [Category.assoc]
      rw [← MonoidalCategory.associator_naturality_left_assoc]
  | @tail M Ms Ns f ih =>
      dsimp [AdjacentMergeData.suffix, AdjacentMergeData.tensorMap,
        tensorModuleListAppendIso]
      dsimp only [tensorModuleList, tensorModuleListOver]
      simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
        Iso.refl_hom, Category.assoc]
      slice_lhs 2 3 =>
        rw [← MonoidalCategory.id_tensor_comp, ih,
          MonoidalCategory.id_tensor_comp]
      monoidal

theorem AdjacentMergeData.suffix_tensorMap
    {source target : List (ModuleCat.{0} ℤ)}
    (f : AdjacentMergeData source target) (Ps : List (ModuleCat.{0} ℤ)) :
    (f.suffix Ps).tensorMap =
      tensorModuleListWhiskerRight Ps f.tensorMap := by
  apply (cancel_epi (tensorModuleListAppendIso source Ps).hom).mp
  rw [f.suffix_tensorMap_naturality]
  simp [tensorModuleListWhiskerRight]

theorem AdjacentMergeData.prefix_tensorMap_naturality
    {source target : List (ModuleCat.{0} ℤ)}
    (f : AdjacentMergeData source target) (Ps : List (ModuleCat.{0} ℤ)) :
    (tensorModuleListAppendIso Ps source).hom ≫ (f.prefix Ps).tensorMap =
      (𝟙 (tensorModuleList Ps) ⊗ₘ f.tensorMap) ≫
        (tensorModuleListAppendIso Ps target).hom := by
  induction Ps with
  | nil =>
      dsimp [AdjacentMergeData.prefix, tensorModuleListAppendIso]
      change (λ_ (tensorModuleList source)).hom ≫ f.tensorMap =
        (𝟙_ (ModuleCat.{0} ℤ) ◁ f.tensorMap) ≫
          (λ_ (tensorModuleList target)).hom
      exact (MonoidalCategory.leftUnitor_naturality f.tensorMap).symm
  | cons P Ps ih =>
      dsimp [AdjacentMergeData.prefix, AdjacentMergeData.tensorMap,
        tensorModuleListAppendIso]
      dsimp only [tensorModuleList, tensorModuleListOver]
      simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
        Iso.refl_hom, Category.assoc]
      slice_lhs 2 3 =>
        rw [← MonoidalCategory.id_tensor_comp, ih,
          MonoidalCategory.id_tensor_comp]
      monoidal

theorem AdjacentMergeData.prefix_tensorMap
    {source target : List (ModuleCat.{0} ℤ)}
    (f : AdjacentMergeData source target) (Ps : List (ModuleCat.{0} ℤ)) :
    (f.prefix Ps).tensorMap = tensorModuleListWhiskerLeft Ps f.tensorMap := by
  apply (cancel_epi (tensorModuleListAppendIso Ps source).hom).mp
  rw [f.prefix_tensorMap_naturality]
  simp [tensorModuleListWhiskerLeft]

theorem eqToHom_comp_heq_id
    {A B C : ModuleCat.{0} ℤ} (hAB : A = B) (hBC : B = C) :
    HEq (eqToHom hAB ≫ eqToHom hBC) (𝟙 A) := by
  subst B
  subst C
  rfl

theorem eqToHom_comp₃_heq_id
    {A B C D : ModuleCat.{0} ℤ}
    (hAB : A = B) (hBC : B = C) (hCD : C = D) :
    HEq (eqToHom hAB ≫ eqToHom hBC ≫ eqToHom hCD) (𝟙 A) := by
  subst B
  subst C
  subst D
  rfl

theorem transportedPair_heq
    {S A B C D T U V : ModuleCat.{0} ℤ}
    (hA : S = A) (hB : B = U) (hC : C = U)
    (hD : D = V) (hT : T = V)
    (p : S ⟶ A) (f : A ⟶ B) (m : B ⟶ C)
    (g : C ⟶ D) (q : D ⟶ T) (F : S ⟶ U) (G : U ⟶ V)
    (hp : HEq p (𝟙 S)) (hf : HEq f F) (hm : HEq m (𝟙 B))
    (hg : HEq g G) (hq : HEq q (𝟙 V)) :
    HEq (p ≫ f ≫ m ≫ g ≫ q) (F ≫ G) := by
  subst A
  subst B
  subst C
  subst D
  subst T
  have ep : p = 𝟙 S := eq_of_heq hp
  have ef : f = F := eq_of_heq hf
  have em : m = 𝟙 U := eq_of_heq hm
  have eg : g = G := eq_of_heq hg
  have eq : q = 𝟙 V := eq_of_heq hq
  rw [ep, ef, em, eg, eq]
  simp

theorem transportedPair₂_heq
    {S A B C D E T R U V : ModuleCat.{0} ℤ}
    (hS : S = R) (hA : S = A) (hB : B = U) (hC : C = U)
    (hD : D = V) (hE : E = V) (hT : T = V)
    (p : S ⟶ A) (f : A ⟶ B) (m : B ⟶ C)
    (g : C ⟶ D) (q₁ : D ⟶ E) (q₂ : E ⟶ T)
    (F : R ⟶ U) (G : U ⟶ V)
    (hp : HEq p (𝟙 S)) (hf : HEq f F) (hm : HEq m (𝟙 B))
    (hg : HEq g G) (hq₁ : HEq q₁ (𝟙 D))
    (hq₂ : HEq q₂ (𝟙 E)) :
    HEq (p ≫ f ≫ m ≫ g ≫ q₁ ≫ q₂) (F ≫ G) := by
  subst R
  subst A
  subst B
  subst C
  subst D
  subst E
  subst T
  have ep : p = 𝟙 S := eq_of_heq hp
  have ef : f = F := eq_of_heq hf
  have em : m = 𝟙 U := eq_of_heq hm
  have eg : g = G := eq_of_heq hg
  have eq₁ : q₁ = 𝟙 V := eq_of_heq hq₁
  have eq₂ : q₂ = 𝟙 V := eq_of_heq hq₂
  rw [ep, ef, em, eg, eq₁, eq₂]
  simp

theorem transportedPairAssembler_heq
    {S T U V A B C D E F : ModuleCat.{0} ℤ}
    {left : S ⟶ T} {right : U ⟶ V}
    {f₁ : A ⟶ B} {g₁ : B ⟶ C}
    {f₂ : D ⟶ E} {g₂ : E ⟶ F}
    (hleft : HEq left (f₁ ≫ g₁))
    (hmiddle : HEq (f₁ ≫ g₁) (f₂ ≫ g₂))
    (hright : HEq right (f₂ ≫ g₂)) :
    HEq left right :=
  hleft.trans (hmiddle.trans hright.symm)

theorem AdjacentMergePairCoherence.prefix
    {source middle₁ middle₂ target : List (ModuleCat.{0} ℤ)}
    {f₁ : AdjacentMergeData source middle₁}
    {g₁ : AdjacentMergeData middle₁ target}
    {f₂ : AdjacentMergeData source middle₂}
    {g₂ : AdjacentMergeData middle₂ target}
    (h : AdjacentMergePairCoherence f₁ g₁ f₂ g₂) :
    (xs : List (ModuleCat.{0} ℤ)) →
      AdjacentMergePairCoherence
        (f₁.prefix xs) (g₁.prefix xs) (f₂.prefix xs) (g₂.prefix xs)
  | [] => h
  | _ :: xs => .tail (h.prefix xs)

theorem AdjacentMergePairHCoherence.prefix
    {source middle₁ middle₂ target₁ target₂ : List (ModuleCat.{0} ℤ)}
    {f₁ : AdjacentMergeData source middle₁}
    {g₁ : AdjacentMergeData middle₁ target₁}
    {f₂ : AdjacentMergeData source middle₂}
    {g₂ : AdjacentMergeData middle₂ target₂}
    (h : AdjacentMergePairHCoherence f₁ g₁ f₂ g₂) :
    (xs : List (ModuleCat.{0} ℤ)) →
      AdjacentMergePairHCoherence
        (f₁.prefix xs) (g₁.prefix xs) (f₂.prefix xs) (g₂.prefix xs)
  | [] => h
  | _ :: xs => .tail (h.prefix xs)

theorem adjacentMergeAfter_eq_prefix_head
    (xs : List (ModuleCat.{0} ℤ))
    {M N P : ModuleCat.{0} ℤ} {ys : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) P) :
    adjacentMergeAfter xs (ys := ys) f =
      (AdjacentMergeData.head f).prefix xs := by
  induction xs with
  | nil => rfl
  | cons Q xs ih =>
      change AdjacentMergeData.tail (adjacentMergeAfter xs (ys := ys) f) =
        AdjacentMergeData.tail ((AdjacentMergeData.head f).prefix xs)
      rw [ih]

theorem adjacentMergeData_tail_heq
    {M M' : ModuleCat.{0} ℤ} (hM : M = M')
    {source target source' target' : List (ModuleCat.{0} ℤ)}
    {f : AdjacentMergeData source target}
    {g : AdjacentMergeData source' target'}
    (hsource : source = source') (htarget : target = target')
    (h : HEq f g) :
    HEq (@AdjacentMergeData.tail M source target f)
      (@AdjacentMergeData.tail M' source' target' g) := by
  subst M'
  subst source'
  subst target'
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

theorem AdjacentMergeData.tensorMap_heq
    {source target source' target' : List (ModuleCat.{0} ℤ)}
    (hsource : source = source') (htarget : target = target')
    {f : AdjacentMergeData source target}
    {g : AdjacentMergeData source' target'} (h : HEq f g) :
    HEq f.tensorMap g.tensorMap := by
  subst source'
  subst target'
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

theorem adjacentMergeAfter_congr
    {xs xs' : List (ModuleCat.{0} ℤ)} (hxs : xs = xs')
    {M N P M' N' P' : ModuleCat.{0} ℤ}
    (hM : M = M') (hN : N = N') (hP : P = P')
    {ys ys' : List (ModuleCat.{0} ℤ)} (hys : ys = ys')
    {f : Quiver.Hom (M ⊗ N) P} {g : Quiver.Hom (M' ⊗ N') P'}
    (h : HEq f g) :
    HEq (adjacentMergeAfter xs (ys := ys) f)
      (adjacentMergeAfter xs' (ys := ys') g) := by
  subst xs'
  subst M'
  subst N'
  subst P'
  subst ys'
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

theorem adjacentMergeAfter_prefix_heq
    (xs Ps : List (ModuleCat.{0} ℤ))
    {M N P : ModuleCat.{0} ℤ} {ys : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) P) :
    HEq ((adjacentMergeAfter xs (ys := ys) f).prefix Ps)
      (adjacentMergeAfter (Ps ++ xs) (ys := ys) f) := by
  induction Ps with
  | nil => rfl
  | cons Q Ps ih =>
      apply adjacentMergeData_tail_heq rfl
      · exact (List.append_assoc Ps xs (M :: N :: ys)).symm
      · exact (List.append_assoc Ps xs (P :: ys)).symm
      · exact ih

theorem adjacentMergeAfter_suffix_heq
    (xs : List (ModuleCat.{0} ℤ))
    {M N P : ModuleCat.{0} ℤ} {ys : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) P) (Ps : List (ModuleCat.{0} ℤ)) :
    HEq ((adjacentMergeAfter xs (ys := ys) f).suffix Ps)
      (adjacentMergeAfter xs (ys := ys ++ Ps) f) := by
  induction xs with
  | nil => rfl
  | cons Q xs ih =>
      apply adjacentMergeData_tail_heq rfl
      · exact List.append_assoc xs (M :: N :: ys) Ps
      · exact List.append_assoc xs (P :: ys) Ps
      · exact ih

theorem AdjacentMergeData.prefix_prefix_heq
    {source target : List (ModuleCat.{0} ℤ)}
    (f : AdjacentMergeData source target)
    (xs ys : List (ModuleCat.{0} ℤ)) :
    HEq ((f.prefix xs).prefix ys) (f.prefix (ys ++ xs)) := by
  induction ys with
  | nil => rfl
  | cons M ys ih =>
      apply adjacentMergeData_tail_heq rfl
      · exact (List.append_assoc ys xs source).symm
      · exact (List.append_assoc ys xs target).symm
      · exact ih

@[simp]
theorem adjacentMergeAfter_nil
    {M N P : ModuleCat.{0} ℤ} {ys : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) P) :
    adjacentMergeAfter [] (ys := ys) f = AdjacentMergeData.head f :=
  rfl

@[simp]
theorem adjacentMergeAfter_cons
    (Q : ModuleCat.{0} ℤ) (xs : List (ModuleCat.{0} ℤ))
    {M N P : ModuleCat.{0} ℤ} {ys : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) P) :
    adjacentMergeAfter (Q :: xs) (ys := ys) f =
      AdjacentMergeData.tail (adjacentMergeAfter xs (ys := ys) f) :=
  rfl

theorem adjacentMergeAfter_pair_assoc
    (xs : List (ModuleCat.{0} ℤ))
    {M N P MN NP Q : ModuleCat.{0} ℤ}
    {zs : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) MN) (g : Quiver.Hom (MN ⊗ P) Q)
    (h : Quiver.Hom (N ⊗ P) NP) (k : Quiver.Hom (M ⊗ NP) Q)
    (hassoc : (α_ M N P).inv ≫ (f ⊗ₘ 𝟙 P) ≫ g =
      (𝟙 M ⊗ₘ h) ≫ k) :
    AdjacentMergePairHCoherence
      ((@AdjacentMergeData.head M N MN (P :: zs) f).prefix xs)
      ((@AdjacentMergeData.head MN P Q zs g).prefix xs)
      ((@AdjacentMergeData.tail M (N :: P :: zs) (NP :: zs)
        (@AdjacentMergeData.head N P NP zs h)).prefix xs)
      ((@AdjacentMergeData.head M NP Q zs k).prefix xs) :=
  (AdjacentMergePairHCoherence.assoc f g h k hassoc).prefix xs

theorem adjacentMergeAfter_pair_head_tail
    (xs ms : List (ModuleCat.{0} ℤ))
    {M N P A B Q : ModuleCat.{0} ℤ}
    {zs : List (ModuleCat.{0} ℤ)}
    (f : Quiver.Hom (M ⊗ N) P) (g : Quiver.Hom (A ⊗ B) Q) :
    AdjacentMergePairHCoherence
      ((@AdjacentMergeData.head M N P (ms ++ A :: B :: zs) f).prefix xs)
      ((@AdjacentMergeData.tail P (ms ++ A :: B :: zs)
        (ms ++ Q :: zs) (adjacentMergeAfter ms (ys := zs) g)).prefix xs)
      ((@AdjacentMergeData.tail M (N :: ms ++ A :: B :: zs)
        (N :: ms ++ Q :: zs)
        (@AdjacentMergeData.tail N (ms ++ A :: B :: zs)
          (ms ++ Q :: zs) (adjacentMergeAfter ms (ys := zs) g))).prefix xs)
      ((@AdjacentMergeData.head M N P (ms ++ Q :: zs) f).prefix xs) :=
  (AdjacentMergePairHCoherence.head_tail f
    (adjacentMergeAfter ms (ys := zs) g)).prefix xs

def tensorMapDataId : (xs : List (ModuleCat.{0} ℤ)) → TensorMapData xs xs
  | [] => .nil
  | M :: xs => .cons (𝟙 M) (tensorMapDataId xs)

@[simp]
theorem tensorMapDataId_tensorMap : (xs : List (ModuleCat.{0} ℤ)) →
    (tensorMapDataId xs).tensorMap = 𝟙 (tensorModuleList xs)
  | [] => rfl
  | M :: xs => by
      change 𝟙 M ⊗ₘ (tensorMapDataId xs).tensorMap =
        𝟙 (M ⊗ tensorModuleList xs)
      rw [tensorMapDataId_tensorMap]
      exact MonoidalCategory.id_tensorHom_id M (tensorModuleList xs)

def tensorMapDataReplaceAfter :
    (xs : List (ModuleCat.{0} ℤ)) → {P Q : ModuleCat.{0} ℤ} →
      Quiver.Hom P Q → (ys : List (ModuleCat.{0} ℤ)) →
      TensorMapData (xs ++ P :: ys) (xs ++ Q :: ys)
  | [], _, _, c, ys => .cons c (tensorMapDataId ys)
  | M :: xs, P, Q, c, ys =>
      .cons (𝟙 M) (tensorMapDataReplaceAfter xs (P := P) (Q := Q) c ys)

@[simp]
theorem tensorMapDataReplaceAfter_id_tensorMap
    (xs : List (ModuleCat.{0} ℤ)) (P : ModuleCat.{0} ℤ)
    (ys : List (ModuleCat.{0} ℤ)) :
    (tensorMapDataReplaceAfter xs (𝟙 P) ys).tensorMap =
      𝟙 (tensorModuleList (xs ++ P :: ys)) := by
  induction xs with
  | nil =>
      change 𝟙 P ⊗ₘ (tensorMapDataId ys).tensorMap =
        𝟙 (P ⊗ tensorModuleList ys)
      rw [tensorMapDataId_tensorMap]
      exact MonoidalCategory.id_tensorHom_id P (tensorModuleList ys)
  | cons M xs ih =>
      change 𝟙 M ⊗ₘ
          (tensorMapDataReplaceAfter xs (𝟙 P) ys).tensorMap =
        𝟙 (M ⊗ tensorModuleList (xs ++ P :: ys))
      rw [ih]
      exact MonoidalCategory.id_tensorHom_id M
        (tensorModuleList (xs ++ P :: ys))

theorem tensorMapDataReplaceAfter_eqToHom
    (xs : List (ModuleCat.{0} ℤ)) {P Q : ModuleCat.{0} ℤ}
    (h : P = Q) (ys : List (ModuleCat.{0} ℤ)) :
    (tensorMapDataReplaceAfter xs (eqToHom h) ys).tensorMap =
      eqToHom (congrArg tensorModuleList
        (congrArg (fun T ↦ xs ++ T :: ys) h)) := by
  cases h
  exact tensorMapDataReplaceAfter_id_tensorMap xs P ys

def adjacentMergeAfterNaturalityPost
    (xs : List (ModuleCat.{0} ℤ))
    {M N P Q : ModuleCat.{0} ℤ}
    (f : Quiver.Hom (M ⊗ N) P) (c : Quiver.Hom P Q)
    (ys : List (ModuleCat.{0} ℤ)) :
    AdjacentMergeNaturality
      (adjacentMergeAfter xs (ys := ys) f)
      (adjacentMergeAfter xs (ys := ys) (f ≫ c))
      (tensorMapDataId (xs ++ M :: N :: ys))
      (tensorMapDataReplaceAfter xs c ys) := by
  induction xs with
  | nil =>
      exact .head f (f ≫ c) (𝟙 M) (𝟙 N) c
        (tensorMapDataId ys) (by simp)
  | cons R xs ih => exact .tail (𝟙 R) ih

@[reassoc]
theorem adjacentMergeAfter_tensorMap_post
    (xs : List (ModuleCat.{0} ℤ))
    {M N P Q : ModuleCat.{0} ℤ}
    (f : Quiver.Hom (M ⊗ N) P) (c : Quiver.Hom P Q)
    (ys : List (ModuleCat.{0} ℤ)) :
    (adjacentMergeAfter xs (ys := ys) f).tensorMap ≫
        (tensorMapDataReplaceAfter xs c ys).tensorMap =
      (adjacentMergeAfter xs (ys := ys) (f ≫ c)).tensorMap := by
  have h := (adjacentMergeAfterNaturalityPost xs f c ys).tensorMap_comm
  rw [tensorMapDataId_tensorMap, Category.id_comp] at h
  exact h.symm

def appendSingletonPairEq {α : Type*} (xs : List α) (M N : α) :
    (xs ++ [M]) ++ [N] = xs ++ [M, N] := by
  induction xs with
  | nil => rfl
  | cons Q xs ih => exact congrArg (Q :: ·) ih

def appendBoundaryListsEq {α : Type*} (xs : List α) (M N : α)
    (ys : List α) :
    (xs ++ [M]) ++ N :: ys = xs ++ M :: N :: ys := by
  induction xs with
  | nil => rfl
  | cons Q xs ih => exact congrArg (Q :: ·) ih

theorem appendSingletonTailEq {α : Type*} (xs : List α) (M : α) (ys : List α) :
    xs ++ M :: ys = (xs ++ [M]) ++ ys := by
  induction xs with
  | nil => rfl
  | cons Q xs ih => exact congrArg (Q :: ·) ih

theorem appendPairTailEq {α : Type*} (xs : List α) (M N : α) (ys : List α) :
    xs ++ M :: N :: ys = (xs ++ [M, N]) ++ ys := by
  induction xs with
  | nil => rfl
  | cons Q xs ih => exact congrArg (Q :: ·) ih

theorem appendBoundaryListsEq_nil {α : Type*} (xs : List α) (M N : α) :
    appendBoundaryListsEq xs M N [] = appendSingletonPairEq xs M N :=
  Subsingleton.elim _ _

@[simp]
theorem tensorModuleList_eqToHom_cons
    (Q : ModuleCat.{0} ℤ) {xs ys : List (ModuleCat.{0} ℤ)} (h : xs = ys) :
    eqToHom (congrArg tensorModuleList (congrArg (Q :: ·) h)) =
      𝟙 Q ⊗ₘ eqToHom (congrArg tensorModuleList h) := by
  subst h
  change 𝟙 (Q ⊗ tensorModuleList xs) =
    𝟙 Q ⊗ₘ 𝟙 (tensorModuleList xs)
  exact (MonoidalCategory.id_tensorHom_id Q (tensorModuleList xs)).symm

@[simp]
theorem appendSingletonPair_eqToHom_cons
    (Q : ModuleCat.{0} ℤ) (xs : List (ModuleCat.{0} ℤ))
    (M N : ModuleCat.{0} ℤ) :
    eqToHom (congrArg tensorModuleList
      (appendSingletonPairEq (Q :: xs) M N)) =
      𝟙 Q ⊗ₘ eqToHom (congrArg tensorModuleList
        (appendSingletonPairEq xs M N)) := by
  change eqToHom (congrArg tensorModuleList
      (congrArg (Q :: ·) (appendSingletonPairEq xs M N))) = _
  exact tensorModuleList_eqToHom_cons Q (appendSingletonPairEq xs M N)

theorem adjacentMergeAfter_tensorMap_right_unit
    (xs : List (ModuleCat.{0} ℤ)) {M N : ModuleCat.{0} ℤ}
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ N) (f : M ⊗ N ⟶ M)
    (hunit : (ρ_ M).inv ≫ (𝟙 M ⊗ₘ u) ≫ f = 𝟙 M) :
    (ρ_ (tensorModuleList (xs ++ [M]))).inv ≫
        (𝟙 (tensorModuleList (xs ++ [M])) ⊗ₘ (u ≫ (ρ_ N).inv)) ≫
        (tensorModuleListAppendIso (xs ++ [M]) [N]).hom ≫
        eqToHom (congrArg tensorModuleList (appendSingletonPairEq xs M N)) ≫
        (adjacentMergeAfter xs (ys := []) f).tensorMap =
      𝟙 (tensorModuleList (xs ++ [M])) := by
  induction xs with
  | nil =>
      dsimp only [List.nil_append, List.cons_append, List.append_nil,
        tensorModuleList, tensorModuleListOver, tensorModuleListAppendIso,
        adjacentMergeAfter, appendSingletonPairEq, AdjacentMergeData.tensorMap]
      change (ρ_ (M ⊗ 𝟙_ (ModuleCat.{0} ℤ))).inv ≫
          (𝟙 (M ⊗ 𝟙_ (ModuleCat.{0} ℤ)) ⊗ₘ (u ≫ (ρ_ N).inv)) ≫
          (α_ M (𝟙_ (ModuleCat.{0} ℤ)) (N ⊗ 𝟙_ (ModuleCat.{0} ℤ))).hom ≫
          (𝟙 M ⊗ₘ (λ_ (N ⊗ 𝟙_ (ModuleCat.{0} ℤ))).hom) ≫
          (α_ M N (𝟙_ (ModuleCat.{0} ℤ))).inv ≫
          (f ⊗ₘ 𝟙 (𝟙_ (ModuleCat.{0} ℤ))) =
        𝟙 (M ⊗ 𝟙_ (ModuleCat.{0} ℤ))
      calc
        _ = ((ρ_ M).inv ≫ (𝟙 M ⊗ₘ u) ≫ f) ⊗ₘ
            𝟙 (𝟙_ (ModuleCat.{0} ℤ)) := by monoidal
        _ = 𝟙 M ⊗ₘ 𝟙 (𝟙_ (ModuleCat.{0} ℤ)) := by rw [hunit]
        _ = _ := MonoidalCategory.id_tensorHom_id M (𝟙_ (ModuleCat.{0} ℤ))
  | cons Q xs ih =>
      rw [appendSingletonPair_eqToHom_cons]
      dsimp only [List.cons_append, tensorModuleList, tensorModuleListOver,
        tensorModuleListAppendIso, adjacentMergeAfter,
        AdjacentMergeData.tensorMap]
      let A := tensorModuleList (xs ++ [M])
      let r : 𝟙_ (ModuleCat.{0} ℤ) ⟶ N ⊗ 𝟙_ (ModuleCat.{0} ℤ) :=
        u ≫ (ρ_ N).inv
      let a : A ⊗ (N ⊗ 𝟙_ (ModuleCat.{0} ℤ)) ⟶
          tensorModuleList ((xs ++ [M]) ++ [N]) :=
        (tensorModuleListAppendIso (xs ++ [M]) [N]).hom
      let e : tensorModuleList ((xs ++ [M]) ++ [N]) ⟶
          tensorModuleList (xs ++ [M, N]) :=
        eqToHom (congrArg tensorModuleList (appendSingletonPairEq xs M N))
      let g : tensorModuleList (xs ++ [M, N]) ⟶
          tensorModuleList (xs ++ [M]) :=
        (adjacentMergeAfter xs (ys := []) f).tensorMap
      change (ρ_ (Q ⊗ A)).inv ≫ (𝟙 (Q ⊗ A) ⊗ₘ r) ≫
          (α_ Q A (N ⊗ 𝟙_ (ModuleCat.{0} ℤ))).hom ≫
          (𝟙 Q ⊗ₘ a) ≫ (𝟙 Q ⊗ₘ e) ≫ (𝟙 Q ⊗ₘ g) =
        𝟙 (Q ⊗ A)
      calc
        _ = 𝟙 Q ⊗ₘ ((ρ_ A).inv ≫ (𝟙 A ⊗ₘ r) ≫ a ≫ e ≫ g) := by
          monoidal
        _ = 𝟙 Q ⊗ₘ 𝟙 (tensorModuleList (xs ++ [M])) := by rw [ih]
        _ = _ := MonoidalCategory.id_tensorHom_id Q
          (tensorModuleList (xs ++ [M]))

theorem adjacentMergeAfter_tensorMap_left_unit
    {M N : ModuleCat.{0} ℤ} (ys : List (ModuleCat.{0} ℤ))
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ M) (f : M ⊗ N ⟶ N)
    (hunit : (λ_ N).inv ≫ (u ⊗ₘ 𝟙 N) ≫ f = 𝟙 N) :
    (λ_ (tensorModuleList (N :: ys))).inv ≫
        ((u ≫ (ρ_ M).inv) ⊗ₘ 𝟙 (tensorModuleList (N :: ys))) ≫
        (tensorModuleListAppendIso [M] (N :: ys)).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq [] M N ys)) ≫
        (adjacentMergeAfter [] (ys := ys) f).tensorMap =
      𝟙 (tensorModuleList (N :: ys)) := by
  dsimp only [List.nil_append, List.cons_append, List.append_nil,
    tensorModuleList, tensorModuleListOver, tensorModuleListAppendIso,
    appendBoundaryListsEq, adjacentMergeAfter, AdjacentMergeData.tensorMap]
  change (λ_ (N ⊗ tensorModuleList ys)).inv ≫
      ((u ≫ (ρ_ M).inv) ⊗ₘ 𝟙 (N ⊗ tensorModuleList ys)) ≫
      (MonoidalCategoryStruct.associator M (𝟙_ (ModuleCat.{0} ℤ))
        (N ⊗ tensorModuleList ys)).hom ≫
      (𝟙 M ⊗ₘ (λ_ (N ⊗ tensorModuleList ys)).hom) ≫
      (MonoidalCategoryStruct.associator M N (tensorModuleList ys)).inv ≫
      (f ⊗ₘ 𝟙 (tensorModuleList ys)) =
    𝟙 (N ⊗ tensorModuleList ys)
  calc
    _ = ((λ_ N).inv ≫ (u ⊗ₘ 𝟙 N) ≫ f) ⊗ₘ
        𝟙 (tensorModuleList ys) := by monoidal
    _ = 𝟙 N ⊗ₘ 𝟙 (tensorModuleList ys) := by rw [hunit]
    _ = _ := MonoidalCategory.id_tensorHom_id N (tensorModuleList ys)

def compositionSourceFactor
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Fin (((w.length + 1) + v.length) + 1) → ModuleCat.{0} ℤ :=
  fun q ↦ Fin.addCases (factorModule d) (factorModule e)
    (Fin.cast (by omega) q)

def compositionBoundaryIndex
    {X Y Z : ComplexCategory} (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    Fin ((w.length + 1) + v.length) :=
  ⟨w.length, by omega⟩

theorem finFamilyList_compositionSourceFactor
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    finFamilyList (compositionSourceFactor d e) =
      finFamilyList (factorModule d) ++ finFamilyList (factorModule e) := by
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn,
    finFamilyList_eq_ofFn, ← List.ofFn_fin_append]
  let h : ((w.length + 1) + v.length) + 1 =
      (w.length + 1) + (v.length + 1) := by omega
  calc
    List.ofFn (compositionSourceFactor d e) =
        List.ofFn (fun q : Fin ((w.length + 1) + (v.length + 1)) ↦
          compositionSourceFactor d e (Fin.cast h.symm q)) :=
      List.ofFn_congr h (compositionSourceFactor d e)
    _ = List.ofFn (Fin.append (factorModule d) (factorModule e)) := by
      congr 1

def compositionLeftPrefix
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) : List (ModuleCat.{0} ℤ) :=
  finFamilyList (fun i : Fin w.length ↦ factorModule d i.castSucc)

def compositionRightSuffix
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) : List (ModuleCat.{0} ℤ) :=
  finFamilyList (fun i : Fin w.length ↦ factorModule d i.succ)

@[simp]
theorem compositionRightSuffix_nilDegreeProfile
    (X Y : ComplexCategory) (n : ℤ) :
    compositionRightSuffix (nilDegreeProfile X Y n) = [] := by
  rfl

theorem appendBoundaryListsEq_right_nil_eqToHom
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    eqToHom (congrArg tensorModuleList
        (appendBoundaryListsEq (compositionLeftPrefix d)
          (factorModule d (Fin.last w.length))
          (factorModule (nilDegreeProfile Y Y 0) 0)
          (compositionRightSuffix (nilDegreeProfile Y Y 0)))) =
      eqToHom (congrArg tensorModuleList
        (appendSingletonPairEq (compositionLeftPrefix d)
          (factorModule d (Fin.last w.length))
          (factorModule (nilDegreeProfile Y Y 0) 0))) := by
  change eqToHom (congrArg tensorModuleList
      (appendBoundaryListsEq (compositionLeftPrefix d)
        (factorModule d (Fin.last w.length))
        (factorModule (nilDegreeProfile Y Y 0) 0) [])) = _
  congr 1

theorem finFamilyList_factorModule_eq_prefix_last
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    finFamilyList (factorModule d) =
      compositionLeftPrefix d ++ [factorModule d (Fin.last w.length)] := by
  rw [finFamilyList_eq_ofFn, compositionLeftPrefix, finFamilyList_eq_ofFn]
  exact List.ofFn_succ_last

theorem finFamilyList_factorModule_eq_first_suffix
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    finFamilyList (factorModule d) =
      factorModule d 0 :: compositionRightSuffix d := by
  rfl

theorem finFamilyList_compositionSourceFactor_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    finFamilyList (compositionSourceFactor d e) =
      compositionLeftPrefix d ++
        factorModule d (Fin.last w.length) :: factorModule e 0 ::
          compositionRightSuffix e := by
  rw [finFamilyList_compositionSourceFactor,
    finFamilyList_factorModule_eq_prefix_last,
    finFamilyList_factorModule_eq_first_suffix]
  simp only [List.append_assoc, List.singleton_append]

theorem finFamilyList_factorModule_pair_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    finFamilyList (factorModule d) ++ finFamilyList (factorModule e) =
      compositionLeftPrefix d ++
        factorModule d (Fin.last w.length) :: factorModule e 0 ::
          compositionRightSuffix e := by
  rw [finFamilyList_factorModule_eq_prefix_last,
    finFamilyList_factorModule_eq_first_suffix]
  simp only [List.append_assoc, List.singleton_append]

def compositionSourceLeftIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin (w.length + 1)) : Fin (((w.length + 1) + v.length) + 1) :=
  ⟨i.val, by omega⟩

def compositionSourceRightIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin (v.length + 1)) : Fin (((w.length + 1) + v.length) + 1) :=
  ⟨w.length + 1 + j.val, by omega⟩

@[simp]
theorem compositionSourceFactor_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin (w.length + 1)) :
    compositionSourceFactor d e (compositionSourceLeftIndex i) =
      factorModule d i := by
  unfold compositionSourceFactor
  have hindex : Fin.cast (by omega) (compositionSourceLeftIndex (v := v) i) =
      Fin.castAdd (v.length + 1) i := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.addCases_left]

@[simp]
theorem compositionSourceFactor_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin (v.length + 1)) :
    compositionSourceFactor d e (compositionSourceRightIndex j) =
      factorModule e j := by
  unfold compositionSourceFactor
  have hindex : Fin.cast (by omega) (compositionSourceRightIndex (w := w) j) =
      Fin.natAdd (w.length + 1) j := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.addCases_right]

def compositionBoundaryModule
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex
      (w.arrowSource (Fin.last w.length)) (v.arrowTarget 0)).X
    (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)

def compositionBoundaryFactorMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom
      (compositionSourceFactor d e (compositionBoundaryIndex w v).castSucc ⊗
        compositionSourceFactor d e (compositionBoundaryIndex w v).succ)
      (compositionBoundaryModule d e) := by
  have hmiddle :
      w.arrowTarget (Fin.last w.length) = v.arrowSource 0 := by
    change w.vertex (Fin.last w.length).succ = v.vertex (Fin.castSucc 0)
    calc
      _ = w.vertex (Fin.last (w.length + 1)) := by congr 1
      _ = Y := vertex_last w
      _ = v.vertex 0 := rfl
      _ = _ := by congr 1
  have hleft :
      (compositionBoundaryIndex w v).castSucc =
        compositionSourceLeftIndex (v := v) (Fin.last w.length) := by
    apply Fin.ext
    rfl
  have hright :
      (compositionBoundaryIndex w v).succ =
        compositionSourceRightIndex (w := w) (0 : Fin (v.length + 1)) := by
    apply Fin.ext
    rfl
  rw [hleft, hright]
  simp only [compositionSourceFactor_left, compositionSourceFactor_right]
  exact
    dgCochainCompTensorOfEq
      (w.arrowSource (Fin.last w.length))
      (w.arrowTarget (Fin.last w.length))
      (v.arrowSource 0) (v.arrowTarget 0) hmiddle rfl

def compositionBoundaryMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    factorModule d (Fin.last w.length) ⊗ factorModule e 0 ⟶
      compositionBoundaryModule d e := by
  have hmiddle : w.arrowTarget (Fin.last w.length) = v.arrowSource 0 := by
    change w.vertex (Fin.last w.length).succ = v.vertex (Fin.castSucc 0)
    calc
      _ = w.vertex (Fin.last (w.length + 1)) := by congr 1
      _ = Y := vertex_last w
      _ = v.vertex 0 := rfl
      _ = _ := by congr 1
  exact dgCochainCompTensorOfEq
    (w.arrowSource (Fin.last w.length))
    (w.arrowTarget (Fin.last w.length))
    (v.arrowSource 0) (v.arrowTarget 0) hmiddle rfl

theorem factorModule_nilDegreeProfile
    (K L : ComplexCategory) (p : ℤ) :
    factorModule (nilDegreeProfile K L p) 0 =
      (dgHomZModuleCochainComplex K L).X p := by
  rfl

@[simp]
theorem nil_arrowSource_zero (K L : ComplexCategory) :
    (nil K L).arrowSource 0 = K := by
  rfl

@[simp]
theorem nil_arrowTarget_zero (K L : ComplexCategory) :
    (nil K L).arrowTarget 0 = L := by
  rfl

theorem arrowTarget_last_eq_target
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    w.arrowTarget (Fin.last w.length) = Y := by
  change w.vertex (Fin.last w.length).succ = Y
  rw [show (Fin.last w.length).succ =
    Fin.last (w.length + 1) by ext; rfl]
  exact vertex_last w

theorem arrowSource_zero_eq_source
    {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    w.arrowSource 0 = X := by
  rfl

theorem compositionBoundaryMap_right_nil
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    compositionBoundaryMap d (nilDegreeProfile Y Y 0) =
      dgCochainCompTensorOfEq
        (w.arrowSource (Fin.last w.length))
        (w.arrowTarget (Fin.last w.length)) Y Y
        (arrowTarget_last_eq_target w)
        (show d.arrowDegree (Fin.last w.length) + 0 =
          d.arrowDegree (Fin.last w.length) + 0 by rfl) := by
  rfl

theorem compositionBoundaryMap_left_nil
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    compositionBoundaryMap (nilDegreeProfile X X 0) d =
      dgCochainCompTensorOfEq X X (w.arrowSource 0) (w.arrowTarget 0)
        (arrowSource_zero_eq_source w)
        (show 0 + d.arrowDegree 0 = 0 + d.arrowDegree 0 by rfl) := by
  rfl

theorem compositionBoundaryModule_right_nil
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    compositionBoundaryModule d (nilDegreeProfile Y Y 0) =
      factorModule d (Fin.last w.length) := by
  unfold compositionBoundaryModule factorModule
  congr 2
  · change (nil Y Y).arrowTarget 0 = w.arrowTarget (Fin.last w.length)
    calc
      _ = Y := by rfl
      _ = _ := by
        change Y = w.vertex (Fin.last w.length).succ
        rw [show (Fin.last w.length).succ =
          Fin.last (w.length + 1) by ext; rfl]
        exact (vertex_last w).symm
  · simp [nilDegreeProfile]

theorem compositionBoundaryModule_left_nil
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    compositionBoundaryModule (nilDegreeProfile X X 0) d =
      factorModule d 0 := by
  unfold compositionBoundaryModule factorModule
  congr 2
  simp [nilDegreeProfile]

def rightUnitCompositionBoundaryMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    factorModule d (Fin.last w.length) ⊗
        factorModule (nilDegreeProfile Y Y 0) 0 ⟶
      factorModule d (Fin.last w.length) :=
  compositionBoundaryMap d (nilDegreeProfile Y Y 0) ≫
    eqToHom (compositionBoundaryModule_right_nil d)

def leftUnitCompositionBoundaryMap
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    factorModule (nilDegreeProfile X X 0) 0 ⊗ factorModule d 0 ⟶
      factorModule d 0 :=
  compositionBoundaryMap (nilDegreeProfile X X 0) d ≫
    eqToHom (compositionBoundaryModule_left_nil d)

theorem rightUnitCompositionBoundaryMap_unit
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (ρ_ (factorModule d (Fin.last w.length))).inv ≫
        (𝟙 _ ⊗ₘ identityCochainInclusion Y) ≫
        rightUnitCompositionBoundaryMap d =
      𝟙 (factorModule d (Fin.last w.length)) := by
  unfold rightUnitCompositionBoundaryMap
  rw [compositionBoundaryMap_right_nil]
  have hk : compositionBoundaryModule_right_nil d =
      dgCochainCompRightUnitTargetEq
        (w.arrowSource (Fin.last w.length))
        (w.arrowTarget (Fin.last w.length)) Y
        (arrowTarget_last_eq_target w)
        (d.arrowDegree (Fin.last w.length)) := Subsingleton.elim _ _
  rw [hk]
  exact dgCochainCompTensorOfEq_right_unit_raw
      (w.arrowSource (Fin.last w.length))
      (w.arrowTarget (Fin.last w.length)) Y
      (arrowTarget_last_eq_target w)
      (d.arrowDegree (Fin.last w.length))

theorem leftUnitCompositionBoundaryMap_unit
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (λ_ (factorModule d 0)).inv ≫
        (identityCochainInclusion X ⊗ₘ 𝟙 _) ≫
        leftUnitCompositionBoundaryMap d = 𝟙 (factorModule d 0) := by
  unfold leftUnitCompositionBoundaryMap
  rw [compositionBoundaryMap_left_nil]
  have hk : compositionBoundaryModule_left_nil d =
      dgCochainCompLeftUnitTargetEq X (w.arrowSource 0)
        (w.arrowTarget 0) (arrowSource_zero_eq_source w)
        (d.arrowDegree 0) := Subsingleton.elim _ _
  rw [hk]
  exact dgCochainCompTensorOfEq_left_unit_raw X (w.arrowSource 0)
    (w.arrowTarget 0) (arrowSource_zero_eq_source w) (d.arrowDegree 0)

@[reassoc]
theorem compositionBoundaryMap_right_nil_tensorMap_post
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (adjacentMergeAfter (compositionLeftPrefix d) (ys := [])
        (compositionBoundaryMap d (nilDegreeProfile Y Y 0))).tensorMap ≫
        (tensorMapDataReplaceAfter (compositionLeftPrefix d)
          (eqToHom (compositionBoundaryModule_right_nil d)) []).tensorMap =
      (adjacentMergeAfter (compositionLeftPrefix d) (ys := [])
        (rightUnitCompositionBoundaryMap d)).tensorMap := by
  unfold rightUnitCompositionBoundaryMap
  exact adjacentMergeAfter_tensorMap_post
    (compositionLeftPrefix d)
    (compositionBoundaryMap d (nilDegreeProfile Y Y 0))
    (eqToHom (compositionBoundaryModule_right_nil d)) []

@[reassoc]
theorem compositionBoundaryMap_left_nil_tensorMap_post
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (adjacentMergeAfter [] (ys := compositionRightSuffix d)
        (compositionBoundaryMap (nilDegreeProfile X X 0) d)).tensorMap ≫
        (tensorMapDataReplaceAfter []
          (eqToHom (compositionBoundaryModule_left_nil d))
          (compositionRightSuffix d)).tensorMap =
      (adjacentMergeAfter [] (ys := compositionRightSuffix d)
        (leftUnitCompositionBoundaryMap d)).tensorMap := by
  unfold leftUnitCompositionBoundaryMap
  exact adjacentMergeAfter_tensorMap_post []
    (compositionBoundaryMap (nilDegreeProfile X X 0) d)
    (eqToHom (compositionBoundaryModule_left_nil d))
    (compositionRightSuffix d)

theorem normalizedSummandRightUnit
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (ρ_ (tensorModuleList
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
          (rightUnitCompositionBoundaryMap d)).tensorMap =
      𝟙 (tensorModuleList
        (compositionLeftPrefix d ++
          [factorModule d (Fin.last w.length)])) :=
  adjacentMergeAfter_tensorMap_right_unit
    (compositionLeftPrefix d)
    (identityCochainInclusion Y)
    (rightUnitCompositionBoundaryMap d)
    (rightUnitCompositionBoundaryMap_unit d)

theorem normalizedSummandLeftUnit
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (λ_ (tensorModuleList
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
          (leftUnitCompositionBoundaryMap d)).tensorMap =
      𝟙 (tensorModuleList
        (factorModule d 0 :: compositionRightSuffix d)) :=
  adjacentMergeAfter_tensorMap_left_unit
    (compositionRightSuffix d)
    (identityCochainInclusion X)
    (leftUnitCompositionBoundaryMap d)
    (leftUnitCompositionBoundaryMap_unit d)

def summandModuleTransportEq
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n m : ℤ}
    (hw : w = v) (hn : n = m) (d : DegreeProfile w n) :
    summandModule d = summandModule (d.transport hw hn) := by
  subst hw
  subst hn
  rfl

def summandModuleTransportIso
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n m : ℤ}
    (hw : w = v) (hn : n = m) (d : DegreeProfile w n) :
    summandModule d ≅ summandModule (d.transport hw hn) :=
  eqToIso (summandModuleTransportEq hw hn d)

def summandLastFactorIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule d ≅ tensorModuleList
      (compositionLeftPrefix d ++
        [factorModule d (Fin.last w.length)]) :=
  eqToIso (congrArg tensorModuleList
    (finFamilyList_factorModule_eq_prefix_last d))

def summandFirstFactorIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule d ≅ tensorModuleList
      (factorModule d 0 :: compositionRightSuffix d) :=
  eqToIso (congrArg tensorModuleList
    (finFamilyList_factorModule_eq_first_suffix d))

def nilIdentitySummandMap (K : ComplexCategory) :
    𝟙_ (ModuleCat.{0} ℤ) ⟶ summandModule (nilDegreeProfile K K 0) :=
  identityCochainInclusion K ≫
    (ρ_ (factorModule (nilDegreeProfile K K 0) 0)).inv ≫
    (summandFirstFactorIso (nilDegreeProfile K K 0)).inv

theorem nilIdentitySummandMap_comp_firstFactorIso
    (K : ComplexCategory) :
    nilIdentitySummandMap K ≫
        (summandFirstFactorIso (nilDegreeProfile K K 0)).hom =
      identityCochainInclusion K ≫
        (ρ_ (factorModule (nilDegreeProfile K K 0) 0)).inv := by
  unfold nilIdentitySummandMap
  slice_lhs 3 4 =>
    exact (summandFirstFactorIso (nilDegreeProfile K K 0)).inv_hom_id
  exact Category.comp_id
    (identityCochainInclusion K ≫
      (ρ_ (factorModule (nilDegreeProfile K K 0) 0)).inv)

theorem nilFirstFactorIso_inv_comp_lastFactorIso_hom
    (K : ComplexCategory) :
    (summandFirstFactorIso (nilDegreeProfile K K 0)).inv ≫
        (summandLastFactorIso (nilDegreeProfile K K 0)).hom =
      𝟙 (tensorModuleList
        [factorModule (nilDegreeProfile K K 0) 0]) := by
  unfold summandFirstFactorIso summandLastFactorIso
  simp only [eqToIso.inv, eqToIso.hom, eqToHom_trans]
  congr 1

theorem nilIdentitySummandMap_comp_lastFactorIso
    (K : ComplexCategory) :
    nilIdentitySummandMap K ≫
        (summandLastFactorIso (nilDegreeProfile K K 0)).hom =
      identityCochainInclusion K ≫
        (ρ_ (factorModule (nilDegreeProfile K K 0) 0)).inv := by
  unfold nilIdentitySummandMap
  slice_lhs 3 4 =>
    exact nilFirstFactorIso_inv_comp_lastFactorIso_hom K
  exact Category.comp_id
    (identityCochainInclusion K ≫
      (ρ_ (factorModule (nilDegreeProfile K K 0) 0)).inv)

theorem nilFirstFactorIso_inv_comp_nilSummandIsoOriginal
    (K : ComplexCategory) :
    (summandFirstFactorIso (nilDegreeProfile K K 0)).inv ≫
        (nilSummandIsoOriginal K K (nilDegreeProfile K K 0)).hom =
      (ρ_ (factorModule (nilDegreeProfile K K 0) 0)).hom := by
  unfold summandFirstFactorIso nilSummandIsoOriginal
  simp only [Iso.trans_hom, eqToIso.inv, eqToIso.hom]
  congr 1

theorem nilIdentitySummandMap_comp_nilSummandIsoOriginal
    (K : ComplexCategory) :
    nilIdentitySummandMap K ≫
        (nilSummandIsoOriginal K K (nilDegreeProfile K K 0)).hom =
      identityCochainInclusion K := by
  unfold nilIdentitySummandMap
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    exact nilFirstFactorIso_inv_comp_nilSummandIsoOriginal K
  simp

theorem identityCochainInclusion_comp_nilSummandIsoOriginal_inv
    (K : ComplexCategory) :
    identityCochainInclusion K ≫
        (nilSummandIsoOriginal K K (nilDegreeProfile K K 0)).inv =
      nilIdentitySummandMap K := by
  rw [← nilIdentitySummandMap_comp_nilSummandIsoOriginal]
  simp

@[reassoc]
theorem summandRightUnitSource_decompose
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (ρ_ (summandModule d)).inv ≫
        (𝟙 _ ⊗ₘ nilIdentitySummandMap Y) ≫
        ((summandLastFactorIso d).hom ⊗ₘ
          (summandFirstFactorIso (nilDegreeProfile Y Y 0)).hom) =
      (summandLastFactorIso d).hom ≫
        (ρ_ (tensorModuleList
          (compositionLeftPrefix d ++
            [factorModule d (Fin.last w.length)]))).inv ≫
        (𝟙 _ ⊗ₘ (identityCochainInclusion Y ≫
          (ρ_ (factorModule (nilDegreeProfile Y Y 0) 0)).inv)) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp, nilIdentitySummandMap_comp_firstFactorIso]
  let r : 𝟙_ (ModuleCat.{0} ℤ) ⟶
      factorModule (nilDegreeProfile Y Y 0) 0 ⊗
        𝟙_ (ModuleCat.{0} ℤ) :=
    identityCochainInclusion Y ≫
      (ρ_ (factorModule (nilDegreeProfile Y Y 0) 0)).inv
  calc
    _ = (ρ_ (summandModule d)).inv ≫
        (((summandLastFactorIso d).hom ⊗ₘ
          𝟙 (tensorUnit (ModuleCat.{0} ℤ))) ≫
        (𝟙 _ ⊗ₘ r)) := by
      change (ρ_ (summandModule d)).inv ≫
          ((summandLastFactorIso d).hom ⊗ₘ r) = _
      congr 1
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    _ = ((summandLastFactorIso d).hom ≫
        (ρ_ (tensorModuleList
          (compositionLeftPrefix d ++
            [factorModule d (Fin.last w.length)]))).inv) ≫
        (𝟙 _ ⊗ₘ r) := by
      rw [Category.assoc]
      slice_lhs 1 2 =>
        rw [MonoidalCategory.tensorHom_id]
        exact (MonoidalCategory.rightUnitor_inv_naturality
          (summandLastFactorIso d).hom).symm
      exact Category.assoc _ _ _
    _ = _ := Category.assoc _ _ _

@[reassoc]
theorem summandLeftUnitSource_decompose
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (λ_ (summandModule d)).inv ≫
        (nilIdentitySummandMap X ⊗ₘ 𝟙 _) ≫
        ((summandLastFactorIso (nilDegreeProfile X X 0)).hom ⊗ₘ
          (summandFirstFactorIso d).hom) =
      (summandFirstFactorIso d).hom ≫
        (λ_ (tensorModuleList
          (factorModule d 0 :: compositionRightSuffix d))).inv ≫
        ((identityCochainInclusion X ≫
          (ρ_ (factorModule (nilDegreeProfile X X 0) 0)).inv) ⊗ₘ 𝟙 _) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    nilIdentitySummandMap_comp_lastFactorIso, Category.id_comp]
  let l : 𝟙_ (ModuleCat.{0} ℤ) ⟶
      factorModule (nilDegreeProfile X X 0) 0 ⊗
        𝟙_ (ModuleCat.{0} ℤ) :=
    identityCochainInclusion X ≫
      (ρ_ (factorModule (nilDegreeProfile X X 0) 0)).inv
  calc
    _ = (λ_ (summandModule d)).inv ≫
        ((𝟙 (tensorUnit (ModuleCat.{0} ℤ)) ⊗ₘ
          (summandFirstFactorIso d).hom) ≫
        (l ⊗ₘ 𝟙 _)) := by
      change (λ_ (summandModule d)).inv ≫
          (l ⊗ₘ (summandFirstFactorIso d).hom) = _
      congr 1
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    _ = ((summandFirstFactorIso d).hom ≫
        (λ_ (tensorModuleList
          (factorModule d 0 :: compositionRightSuffix d))).inv) ≫
        (l ⊗ₘ 𝟙 _) := by
      rw [Category.assoc]
      slice_lhs 1 2 =>
        rw [MonoidalCategory.id_tensorHom]
        exact (MonoidalCategory.leftUnitor_inv_naturality
          (summandFirstFactorIso d).hom).symm
      exact Category.assoc _ _ _
    _ = _ := Category.assoc _ _ _

def appendLeftArrowIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin w.length) : Fin ((w.append v).length + 1) :=
  ⟨i.val, by simp; omega⟩

def appendBoundaryArrowIndex
    {X Y Z : ComplexCategory} (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    Fin ((w.append v).length + 1) :=
  ⟨w.length, by simp⟩

def appendRightArrowIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin v.length) : Fin ((w.append v).length + 1) :=
  ⟨w.length + 1 + j.val, by simp; omega⟩

def appendLeftVertexIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin (w.length + 1)) : Fin ((w.append v).length + 2) :=
  ⟨i.val, by simp; omega⟩

def appendRightVertexIndex
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin (v.length + 1)) : Fin ((w.append v).length + 2) :=
  ⟨w.length + 1 + j.val, by simp; omega⟩

theorem vertex_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin (w.length + 1)) :
    (w.append v).vertex (appendLeftVertexIndex i) = w.vertex i.castSucc := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      have hleft : appendLeftVertexIndex (v := v) i.succ =
          ((Fin.castAdd v.length i).castSucc).succ := by
        apply Fin.ext
        rfl
      have hright : i.succ.castSucc = i.castSucc.succ := by
        apply Fin.ext
        rfl
      rw [hleft, hright]
      dsimp only [append]
      unfold vertex
      rw [Fin.cases_succ, Fin.cases_succ,
        Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      simp [object]

theorem vertex_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin (v.length + 1)) :
    (w.append v).vertex (appendRightVertexIndex j) = v.vertex j.succ := by
  cases j using Fin.lastCases with
  | last =>
      have hleft : appendRightVertexIndex (w := w) (v := v) (Fin.last v.length) =
          Fin.last ((w.append v).length + 1) := by
        apply Fin.ext
        change w.length + 1 + v.length = w.length + v.length + 1
        omega
      have hright : (Fin.last v.length).succ = Fin.last (v.length + 1) := by
        apply Fin.ext
        rfl
      rw [hleft, hright, vertex_last, vertex_last]
  | cast j =>
      have hleft : appendRightVertexIndex (w := w) (v := v) j.castSucc =
          ((Fin.natAdd w.length j).castSucc).succ := by
        apply Fin.ext
        change w.length + 1 + j.val = (w.length + j.val) + 1
        omega
      rw [hleft]
      dsimp only [append]
      unfold vertex
      rw [Fin.cases_succ, Fin.cases_succ,
        Fin.lastCases_castSucc, Fin.lastCases_castSucc]
      simp [object]

theorem arrowSource_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin w.length) :
    (w.append v).arrowSource (appendLeftArrowIndex i) =
      w.arrowSource i.castSucc := by
  unfold arrowSource
  have hindex : (appendLeftArrowIndex (v := v) i).castSucc =
      appendLeftVertexIndex i.castSucc := by
    apply Fin.ext
    rfl
  rw [hindex, vertex_append_left]

theorem arrowTarget_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (i : Fin w.length) :
    (w.append v).arrowTarget (appendLeftArrowIndex i) =
      w.arrowTarget i.castSucc := by
  unfold arrowTarget
  have hindex : (appendLeftArrowIndex (v := v) i).succ =
      appendLeftVertexIndex i.succ := by
    apply Fin.ext
    rfl
  have htarget : i.succ.castSucc = i.castSucc.succ := by
    apply Fin.ext
    rfl
  rw [hindex, vertex_append_left, htarget]

theorem appendArrowDegree_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    appendArrowDegree d e (appendLeftArrowIndex i) =
      d.arrowDegree i.castSucc := by
  unfold appendArrowDegree
  have hindex : Fin.cast
      (show (w.append v).length + 1 = w.length + (v.length + 1) by
        simp [Nat.add_assoc]) (appendLeftArrowIndex i) =
      Fin.castAdd (v.length + 1) i := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.addCases_left]

theorem arrowSource_append_boundary
    {X Y Z : ComplexCategory} (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    (w.append v).arrowSource (appendBoundaryArrowIndex w v) =
      w.arrowSource (Fin.last w.length) := by
  unfold arrowSource
  have hindex : (appendBoundaryArrowIndex w v).castSucc =
      appendLeftVertexIndex (Fin.last w.length) := by
    apply Fin.ext
    rfl
  rw [hindex, vertex_append_left]

theorem arrowTarget_append_boundary
    {X Y Z : ComplexCategory} (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    (w.append v).arrowTarget (appendBoundaryArrowIndex w v) =
      v.arrowTarget 0 := by
  unfold arrowTarget
  have hindex : (appendBoundaryArrowIndex w v).succ =
      appendRightVertexIndex (0 : Fin (v.length + 1)) := by
    apply Fin.ext
    rfl
  rw [hindex, vertex_append_right]

theorem appendArrowDegree_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    appendArrowDegree d e (appendBoundaryArrowIndex w v) =
      d.arrowDegree (Fin.last w.length) + e.arrowDegree 0 := by
  unfold appendArrowDegree
  have hindex : Fin.cast (by simp [Nat.add_assoc]) (appendBoundaryArrowIndex w v) =
      Fin.natAdd w.length (0 : Fin (v.length + 1)) := by
    apply Fin.ext
    rfl
  rw [hindex, Fin.addCases_right, Fin.cases_zero]

theorem arrowSource_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin v.length) :
    (w.append v).arrowSource (appendRightArrowIndex j) =
      v.arrowSource j.succ := by
  unfold arrowSource
  have hindex : (appendRightArrowIndex (w := w) j).castSucc =
      appendRightVertexIndex j.castSucc := by
    apply Fin.ext
    rfl
  have hsource : j.castSucc.succ = j.succ.castSucc := by
    apply Fin.ext
    rfl
  rw [hindex, vertex_append_right, hsource]

theorem arrowTarget_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    (j : Fin v.length) :
    (w.append v).arrowTarget (appendRightArrowIndex j) =
      v.arrowTarget j.succ := by
  unfold arrowTarget
  have hindex : (appendRightArrowIndex (w := w) j).succ =
      appendRightVertexIndex j.succ := by
    apply Fin.ext
    change w.length + 1 + j.val + 1 = w.length + 1 + (j.val + 1)
    omega
  rw [hindex, vertex_append_right]

theorem appendArrowDegree_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    appendArrowDegree d e (appendRightArrowIndex j) =
      e.arrowDegree j.succ := by
  unfold appendArrowDegree
  have hindex : Fin.cast
      (show (w.append v).length + 1 = w.length + (v.length + 1) by
        simp [Nat.add_assoc]) (appendRightArrowIndex j) =
      Fin.natAdd w.length j.succ := by
    apply Fin.ext
    change w.length + 1 + j.val = w.length + (j.val + 1)
    omega
  rw [hindex, Fin.addCases_right, Fin.cases_succ]

def DegreeProfile.degreeList
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) : List ℤ :=
  finFamilyList d.arrowDegree

theorem DegreeProfile.degreeList_ne_nil
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) : d.degreeList ≠ [] := by
  rw [DegreeProfile.degreeList, finFamilyList_eq_ofFn]
  simp

theorem DegreeProfile.degreeList_transport
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n m : ℤ}
    (hw : w = v) (hn : n = m) (d : DegreeProfile w n) :
    (d.transport hw hn).degreeList = d.degreeList := by
  subst hw
  subst hn
  rfl

theorem DegreeProfile.degreeList_append
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (d.append e).degreeList = degreeBoundaryMerge d.degreeList e.degreeList := by
  rw [DegreeProfile.degreeList, DegreeProfile.degreeList,
    DegreeProfile.degreeList, finFamilyList_eq_ofFn, finFamilyList_eq_ofFn,
    finFamilyList_eq_ofFn, degreeBoundaryMerge_ofFn]
  let h : (w.append v).length + 1 = w.length + (v.length + 1) := by
    simp [Nat.add_assoc]
  calc
    List.ofFn (d.append e).arrowDegree =
        List.ofFn (fun q : Fin (w.length + (v.length + 1)) ↦
          (d.append e).arrowDegree (Fin.cast h.symm q)) :=
      List.ofFn_congr h (d.append e).arrowDegree
    _ = List.ofFn (Fin.append
        (fun i : Fin w.length ↦ d.arrowDegree i.castSucc)
        (Fin.cases (d.arrowDegree (Fin.last w.length) + e.arrowDegree 0)
          (fun j : Fin v.length ↦ e.arrowDegree j.succ))) := by
      rfl
    _ = _ := by
      rw [List.ofFn_fin_append, List.ofFn_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]

theorem DegreeProfile.eq_of_degreeList_eq
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    {d e : DegreeProfile w n} (h : d.degreeList = e.degreeList) : d = e := by
  apply DegreeProfile.ext
  apply List.ofFn_injective
  rw [DegreeProfile.degreeList, DegreeProfile.degreeList,
    finFamilyList_eq_ofFn, finFamilyList_eq_ofFn] at h
  exact h

theorem DegreeProfile.append_assoc_transport
    {W X Y Z : ComplexCategory}
    {u : DrinfeldWord W X} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {p q r : ℤ} (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    ((a.append d).append e).transport (append_assoc u w v)
        (Int.add_assoc p q r) =
      a.append (d.append e) := by
  apply DegreeProfile.eq_of_degreeList_eq
  calc
    (((a.append d).append e).transport (append_assoc u w v)
        (Int.add_assoc p q r)).degreeList =
        ((a.append d).append e).degreeList :=
      DegreeProfile.degreeList_transport (append_assoc u w v)
        (Int.add_assoc p q r) ((a.append d).append e)
    _ = degreeBoundaryMerge
          (degreeBoundaryMerge a.degreeList d.degreeList) e.degreeList := by
      rw [DegreeProfile.degreeList_append, DegreeProfile.degreeList_append]
    _ = degreeBoundaryMerge a.degreeList
          (degreeBoundaryMerge d.degreeList e.degreeList) :=
      degreeBoundaryMerge_assoc a.degreeList d.degreeList e.degreeList
        a.degreeList_ne_nil d.degreeList_ne_nil e.degreeList_ne_nil
    _ = (a.append (d.append e)).degreeList := by
      rw [DegreeProfile.degreeList_append, DegreeProfile.degreeList_append]

def summandAssocIso
    {W X Y Z : ComplexCategory}
    {u : DrinfeldWord W X} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {p q r : ℤ} (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    summandModule ((a.append d).append e) ≅
      summandModule (a.append (d.append e)) :=
  summandModuleTransportIso (append_assoc u w v) (Int.add_assoc p q r)
      ((a.append d).append e) ≪≫
    eqToIso (congrArg summandModule
      (DegreeProfile.append_assoc_transport a d e))

def summandAssocModuleEq
    {W X Y Z : ComplexCategory}
    {u : DrinfeldWord W X} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {p q r : ℤ} (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    summandModule ((a.append d).append e) =
      summandModule (a.append (d.append e)) :=
  (summandModuleTransportEq (append_assoc u w v) (Int.add_assoc p q r)
    ((a.append d).append e)).trans
      (congrArg summandModule (DegreeProfile.append_assoc_transport a d e))

theorem summandAssocIso_hom_heq_id
    {W X Y Z : ComplexCategory}
    {u : DrinfeldWord W X} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {p q r : ℤ} (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    HEq (summandAssocIso a d e).hom
      (𝟙 (summandModule ((a.append d).append e))) := by
  unfold summandAssocIso summandModuleTransportIso
  simp only [Iso.trans_hom, eqToIso.hom]
  exact eqToHom_comp_heq_id _ _

theorem DegreeProfile.append_nil_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    (d.append (nilDegreeProfile Y Y 0)).transport
      (append_nil w) (Int.add_zero n) = d := by
  apply DegreeProfile.ext
  funext i
  rw [DegreeProfile.transport_arrowDegree]
  induction i using Fin.lastCases with
  | last =>
      have hindex :
          Fin.cast
              (congrArg (fun q : DrinfeldWord X Y ↦ q.length + 1)
                (append_nil w)).symm
              (Fin.last w.length) =
            appendBoundaryArrowIndex w (nil Y Y) := by
        apply Fin.ext
        rfl
      rw [hindex]
      change appendArrowDegree d (nilDegreeProfile Y Y 0)
        (appendBoundaryArrowIndex w (nil Y Y)) = _
      rw [appendArrowDegree_boundary]
      simp [nilDegreeProfile]
  | cast i =>
      have hindex :
          Fin.cast
              (congrArg (fun q : DrinfeldWord X Y ↦ q.length + 1)
                (append_nil w)).symm i.castSucc =
            appendLeftArrowIndex (v := nil Y Y) i := by
        apply Fin.ext
        rfl
      rw [hindex]
      change appendArrowDegree d (nilDegreeProfile Y Y 0)
        (appendLeftArrowIndex (v := nil Y Y) i) = _
      rw [appendArrowDegree_left]

def summandRightUnitIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule (d.append (nilDegreeProfile Y Y 0)) ≅
      summandModule d :=
  summandModuleTransportIso (append_nil w) (Int.add_zero n)
      (d.append (nilDegreeProfile Y Y 0)) ≪≫
    eqToIso (congrArg summandModule (DegreeProfile.append_nil_transport d))

theorem DegreeProfile.nil_append_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    ((nilDegreeProfile X X 0).append d).transport
      (nil_append w) (Int.zero_add n) = d := by
  apply DegreeProfile.ext
  funext i
  rw [DegreeProfile.transport_arrowDegree]
  induction i using Fin.cases with
  | zero =>
      have hindex :
          Fin.cast
              (congrArg (fun q : DrinfeldWord X Y ↦ q.length + 1)
                (nil_append w)).symm 0 =
            appendBoundaryArrowIndex (nil X X) w := by
        apply Fin.ext
        rfl
      rw [hindex]
      change appendArrowDegree (nilDegreeProfile X X 0) d
        (appendBoundaryArrowIndex (nil X X) w) = _
      rw [appendArrowDegree_boundary]
      simp [nilDegreeProfile]
  | succ i =>
      have hindex :
          Fin.cast
              (congrArg (fun q : DrinfeldWord X Y ↦ q.length + 1)
                (nil_append w)).symm i.succ =
            appendRightArrowIndex (w := nil X X) i := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_succ, appendRightArrowIndex,
          Fin.val_mk, nil]
        omega
      rw [hindex]
      change appendArrowDegree (nilDegreeProfile X X 0) d
        (appendRightArrowIndex (w := nil X X) i) = _
      rw [appendArrowDegree_right]

def summandLeftUnitIso
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    summandModule ((nilDegreeProfile X X 0).append d) ≅
      summandModule d :=
  summandModuleTransportIso (nil_append w) (Int.zero_add n)
      ((nilDegreeProfile X X 0).append d) ≪≫
    eqToIso (congrArg summandModule (DegreeProfile.nil_append_transport d))

def GradedSummandIndex.castTotal {X Y : ComplexCategory} {n m : ℤ}
    (h : n = m) (s : GradedSummandIndex X Y n) : GradedSummandIndex X Y m := by
  subst h
  exact s

theorem GradedSummandIndex.castTotal_sigma
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n m : ℤ}
    (h : n = m) (d : DegreeProfile w n) :
    GradedSummandIndex.castTotal h
        (⟨w, d⟩ : GradedSummandIndex X Y n) =
      (⟨w, d.castTotal h⟩ : GradedSummandIndex X Y m) := by
  subst h
  rfl

theorem DegreeProfile.transport_eq_castTotal_castWord
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n m : ℤ}
    (hw : w = v) (hn : n = m) (d : DegreeProfile w n) :
    d.transport hw hn = (d.castTotal hn).castWord hw := by
  subst hw
  subst hn
  rfl

theorem DegreeProfile.cast_eq_castWord
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) :
    cast (congrArg (fun q : DrinfeldWord X Y ↦ DegreeProfile q n) h) d =
      d.castWord h := by
  subst h
  rfl

theorem gradedSummandIndex_append_assoc
    {W X Y Z : ComplexCategory}
    {u : DrinfeldWord W X} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {p q r : ℤ} (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    GradedSummandIndex.castTotal (Int.add_assoc p q r)
        (⟨(u.append w).append v, (a.append d).append e⟩ :
          GradedSummandIndex W Z ((p + q) + r)) =
      (⟨u.append (w.append v), a.append (d.append e)⟩ :
        GradedSummandIndex W Z (p + (q + r))) := by
  rw [GradedSummandIndex.castTotal_sigma]
  apply Sigma.ext (append_assoc u w v)
  let raw := ((a.append d).append e).castTotal (Int.add_assoc p q r)
  have hp : raw.castWord (append_assoc u w v) =
      a.append (d.append e) := by
    rw [← DegreeProfile.transport_eq_castTotal_castWord]
    exact DegreeProfile.append_assoc_transport a d e
  have hhp : raw.castWord (append_assoc u w v) ≍
      a.append (d.append e) := heq_of_eq hp
  let hty := congrArg
    (fun t : DrinfeldWord W Z ↦ DegreeProfile t (p + (q + r)))
      (append_assoc u w v)
  apply (cast_heq_iff_heq hty raw (a.append (d.append e))).mp
  rw [DegreeProfile.cast_eq_castWord]
  exact hhp

theorem gradedSummandIndex_append_nil
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    GradedSummandIndex.castTotal (Int.add_zero n)
        (⟨w.append (nil Y Y), d.append (nilDegreeProfile Y Y 0)⟩ :
          GradedSummandIndex X Y (n + 0)) =
      (⟨w, d⟩ : GradedSummandIndex X Y n) := by
  rw [GradedSummandIndex.castTotal_sigma]
  apply Sigma.ext (append_nil w)
  let raw := (d.append (nilDegreeProfile Y Y 0)).castTotal (Int.add_zero n)
  have hp : raw.castWord (append_nil w) = d := by
    rw [← DegreeProfile.transport_eq_castTotal_castWord]
    exact DegreeProfile.append_nil_transport d
  have hhp : raw.castWord (append_nil w) ≍ d := heq_of_eq hp
  let hty := congrArg
    (fun q : DrinfeldWord X Y ↦ DegreeProfile q n) (append_nil w)
  apply (cast_heq_iff_heq hty raw d).mp
  rw [DegreeProfile.cast_eq_castWord]
  exact hhp

theorem gradedSummandIndex_nil_append
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    GradedSummandIndex.castTotal (Int.zero_add n)
        (⟨(nil X X).append w, (nilDegreeProfile X X 0).append d⟩ :
          GradedSummandIndex X Y (0 + n)) =
      (⟨w, d⟩ : GradedSummandIndex X Y n) := by
  rw [GradedSummandIndex.castTotal_sigma]
  apply Sigma.ext (nil_append w)
  let raw := ((nilDegreeProfile X X 0).append d).castTotal (Int.zero_add n)
  have hp : raw.castWord (nil_append w) = d := by
    rw [← DegreeProfile.transport_eq_castTotal_castWord]
    exact DegreeProfile.nil_append_transport d
  have hhp : raw.castWord (nil_append w) ≍ d := heq_of_eq hp
  let hty := congrArg
    (fun q : DrinfeldWord X Y ↦ DegreeProfile q n) (nil_append w)
  apply (cast_heq_iff_heq hty raw d).mp
  rw [DegreeProfile.cast_eq_castWord]
  exact hhp

def largeSummandModuleCastTotalEq
    {X Y : ComplexCategory} {n m : ℤ} (h : n = m)
    (s : GradedSummandIndex X Y n) :
    largeSummandModule s =
      largeSummandModule (GradedSummandIndex.castTotal h s) := by
  subst m
  rfl

@[reassoc]
theorem quotientGradedModule_eqToHom_ι
    {X Y : ComplexCategory} {n m : ℤ} (h : n = m)
    (s : GradedSummandIndex X Y n) :
    Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s ≫
        eqToHom (congrArg (quotientGradedModule X Y) h) =
      eqToHom (largeSummandModuleCastTotalEq h s) ≫
        Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y m ↦ largeSummandModule t)
          (GradedSummandIndex.castTotal h s) := by
  subst m
  simp [GradedSummandIndex.castTotal]

@[reassoc]
theorem quotientGradedModule_eqToHom_ι_of_eq
    {X Y : ComplexCategory} {n m : ℤ} (h : n = m)
    (s : GradedSummandIndex X Y n) (t : GradedSummandIndex X Y m)
    (k : GradedSummandIndex.castTotal h s = t) :
    Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) s ≫
        eqToHom (congrArg (quotientGradedModule X Y) h) =
      eqToHom (largeSummandModuleCastTotalEq h s) ≫
        eqToHom (congrArg largeSummandModule k) ≫
        Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y m ↦ largeSummandModule q) t := by
  rw [quotientGradedModule_eqToHom_ι]
  slice_rhs 2 3 =>
    exact Limits.Sigma.eqToHom_comp_ι
      (fun q : GradedSummandIndex X Y m ↦ largeSummandModule q) k

theorem largeSummandAssocTransport
    {W X Y Z : ComplexCategory}
    {u : DrinfeldWord W X} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {p q r : ℤ} (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    eqToHom (largeSummandModuleCastTotalEq (Int.add_assoc p q r)
          (⟨(u.append w).append v, (a.append d).append e⟩ :
            GradedSummandIndex W Z ((p + q) + r))) ≫
        eqToHom (congrArg largeSummandModule
          (gradedSummandIndex_append_assoc a d e)) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (summandAssocIso a d e).hom := by
  simp only [summandAssocIso, summandModuleTransportIso,
    Iso.trans_hom, eqToIso.hom, eqToHom_map, eqToHom_trans]

theorem largeSummandRightUnitTransport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    eqToHom (largeSummandModuleCastTotalEq (Int.add_zero n)
          (⟨w.append (nil Y Y), d.append (nilDegreeProfile Y Y 0)⟩ :
            GradedSummandIndex X Y (n + 0))) ≫
        eqToHom (congrArg largeSummandModule
          (gradedSummandIndex_append_nil d)) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (summandRightUnitIso d).hom := by
  simp only [summandRightUnitIso, summandModuleTransportIso,
    Iso.trans_hom, eqToIso.hom, eqToHom_map, eqToHom_trans]

theorem largeSummandLeftUnitTransport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    eqToHom (largeSummandModuleCastTotalEq (Int.zero_add n)
          (⟨(nil X X).append w, (nilDegreeProfile X X 0).append d⟩ :
            GradedSummandIndex X Y (0 + n))) ≫
        eqToHom (congrArg largeSummandModule
          (gradedSummandIndex_nil_append d)) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (summandLeftUnitIso d).hom := by
  simp only [summandLeftUnitIso, summandModuleTransportIso,
    Iso.trans_hom, eqToIso.hom, eqToHom_map, eqToHom_trans]

@[reassoc]
theorem largeSummandAssocInclusion_transport
    {W X Y Z : ComplexCategory}
    {u : DrinfeldWord W X} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {p q r : ℤ} (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    Limits.Sigma.ι
          (fun t : GradedSummandIndex W Z ((p + q) + r) ↦
            largeSummandModule t)
          ⟨(u.append w).append v, (a.append d).append e⟩ ≫
        eqToHom (congrArg (quotientGradedModule W Z)
          (Int.add_assoc p q r)) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (summandAssocIso a d e).hom ≫
        Limits.Sigma.ι
          (fun t : GradedSummandIndex W Z (p + (q + r)) ↦
            largeSummandModule t)
          ⟨u.append (w.append v), a.append (d.append e)⟩ := by
  calc
    _ = eqToHom (largeSummandModuleCastTotalEq (Int.add_assoc p q r)
          (⟨(u.append w).append v, (a.append d).append e⟩ :
            GradedSummandIndex W Z ((p + q) + r))) ≫
        eqToHom (congrArg largeSummandModule
          (gradedSummandIndex_append_assoc a d e)) ≫
        Limits.Sigma.ι
          (fun t : GradedSummandIndex W Z (p + (q + r)) ↦
            largeSummandModule t)
          ⟨u.append (w.append v), a.append (d.append e)⟩ :=
      quotientGradedModule_eqToHom_ι_of_eq (Int.add_assoc p q r)
        (⟨(u.append w).append v, (a.append d).append e⟩ :
          GradedSummandIndex W Z ((p + q) + r))
        (⟨u.append (w.append v), a.append (d.append e)⟩ :
          GradedSummandIndex W Z (p + (q + r)))
        (gradedSummandIndex_append_assoc a d e)
    _ = _ := by
      rw [← Category.assoc, largeSummandAssocTransport]

@[reassoc]
theorem largeSummandRightUnitInclusion_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y (n + 0) ↦ largeSummandModule q)
          ⟨w.append (nil Y Y), d.append (nilDegreeProfile Y Y 0)⟩ ≫
        eqToHom (congrArg (quotientGradedModule X Y) (Int.add_zero n)) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (summandRightUnitIso d).hom ≫
        Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩ := by
  calc
    _ = eqToHom (largeSummandModuleCastTotalEq (Int.add_zero n)
          (⟨w.append (nil Y Y), d.append (nilDegreeProfile Y Y 0)⟩ :
            GradedSummandIndex X Y (n + 0))) ≫
        eqToHom (congrArg largeSummandModule
          (gradedSummandIndex_append_nil d)) ≫
        Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩ :=
      quotientGradedModule_eqToHom_ι_of_eq (Int.add_zero n)
        (⟨w.append (nil Y Y), d.append (nilDegreeProfile Y Y 0)⟩ :
          GradedSummandIndex X Y (n + 0))
        (⟨w, d⟩ : GradedSummandIndex X Y n)
        (gradedSummandIndex_append_nil d)
    _ = _ := by
      rw [← Category.assoc, largeSummandRightUnitTransport]

@[reassoc]
theorem largeSummandLeftUnitInclusion_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y (0 + n) ↦ largeSummandModule q)
          ⟨(nil X X).append w, (nilDegreeProfile X X 0).append d⟩ ≫
        eqToHom (congrArg (quotientGradedModule X Y) (Int.zero_add n)) =
      (ModuleCat.uliftFunctor.{1} ℤ).map (summandLeftUnitIso d).hom ≫
        Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩ := by
  calc
    _ = eqToHom (largeSummandModuleCastTotalEq (Int.zero_add n)
          (⟨(nil X X).append w, (nilDegreeProfile X X 0).append d⟩ :
            GradedSummandIndex X Y (0 + n))) ≫
        eqToHom (congrArg largeSummandModule
          (gradedSummandIndex_nil_append d)) ≫
        Limits.Sigma.ι
          (fun q : GradedSummandIndex X Y n ↦ largeSummandModule q) ⟨w, d⟩ :=
      quotientGradedModule_eqToHom_ι_of_eq (Int.zero_add n)
        (⟨(nil X X).append w, (nilDegreeProfile X X 0).append d⟩ :
          GradedSummandIndex X Y (0 + n))
        (⟨w, d⟩ : GradedSummandIndex X Y n)
        (gradedSummandIndex_nil_append d)
    _ = _ := by
      rw [← Category.assoc, largeSummandLeftUnitTransport]

theorem factorModule_append_left
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (i : Fin w.length) :
    factorModule (d.append e) (appendLeftArrowIndex i) =
      factorModule d i.castSucc := by
  unfold factorModule
  change (dgHomZModuleCochainComplex
      ((w.append v).arrowSource (appendLeftArrowIndex i))
      ((w.append v).arrowTarget (appendLeftArrowIndex i))).X
        (appendArrowDegree d e (appendLeftArrowIndex i)) = _
  rw [arrowSource_append_left, arrowTarget_append_left,
    appendArrowDegree_left]

theorem factorModule_append_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    factorModule (d.append e) (appendBoundaryArrowIndex w v) =
      compositionBoundaryModule d e := by
  unfold factorModule compositionBoundaryModule
  change (dgHomZModuleCochainComplex
      ((w.append v).arrowSource (appendBoundaryArrowIndex w v))
      ((w.append v).arrowTarget (appendBoundaryArrowIndex w v))).X
        (appendArrowDegree d e (appendBoundaryArrowIndex w v)) = _
  rw [arrowSource_append_boundary, arrowTarget_append_boundary,
    appendArrowDegree_boundary]

theorem factorModule_append_right
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (j : Fin v.length) :
    factorModule (d.append e) (appendRightArrowIndex j) =
      factorModule e j.succ := by
  unfold factorModule
  change (dgHomZModuleCochainComplex
      ((w.append v).arrowSource (appendRightArrowIndex j))
      ((w.append v).arrowTarget (appendRightArrowIndex j))).X
        (appendArrowDegree d e (appendRightArrowIndex j)) = _
  rw [arrowSource_append_right, arrowTarget_append_right,
    appendArrowDegree_right]

theorem factorModule_append_last_of_right_nil
    {W X Y : ComplexCategory} {u : DrinfeldWord W X}
    {p q : ℤ} (a : DegreeProfile u p)
    (d : DegreeProfile (nil X Y) q) :
    factorModule (a.append d) (Fin.last (u.append (nil X Y)).length) =
      compositionBoundaryModule a d := by
  have hindex : Fin.last (u.append (nil X Y)).length =
      appendBoundaryArrowIndex u (nil X Y) := by
    apply Fin.ext
    change u.length + 0 = u.length
    omega
  rw [hindex, factorModule_append_boundary]

theorem factorModule_append_first_of_left_nil
    {W X Y : ComplexCategory} {v : DrinfeldWord X Y}
    {p q : ℤ} (a : DegreeProfile (nil W X) p)
    (d : DegreeProfile v q) :
    factorModule (a.append d) 0 = compositionBoundaryModule a d := by
  have hindex : (0 : Fin (((nil W X).append v).length + 1)) =
      appendBoundaryArrowIndex (nil W X) v := by
    apply Fin.ext
    rfl
  rw [hindex, factorModule_append_boundary]

theorem factorModule_append_last_of_right_succ
    {W X Y : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {p q : ℤ} (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q) :
    factorModule (a.append d)
        (Fin.last (u.append
          ({ length := k + 1, intermediate := intermediate } :
            DrinfeldWord X Y)).length) =
      factorModule d (Fin.last k).succ := by
  have hindex : Fin.last (u.append
        ({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y)).length =
      appendRightArrowIndex (w := u) (Fin.last k) := by
    apply Fin.ext
    change u.length + (k + 1) = u.length + 1 + k
    omega
  rw [hindex, factorModule_append_right]

theorem factorModule_append_first_of_left_succ
    {W X Y : ComplexCategory} {v : DrinfeldWord X Y} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {p q : ℤ}
    (a : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord W X) p)
    (d : DegreeProfile v q) :
    factorModule (a.append d) 0 = factorModule a 0 := by
  have hindex : (0 : Fin ((({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord W X).append v).length + 1)) =
      appendLeftArrowIndex (v := v) (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  rw [hindex, factorModule_append_left]
  simp only [Fin.castSucc_zero]

theorem compositionBoundaryModule_assoc_of_middle_nil
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    compositionBoundaryModule (a.append d) e =
      compositionBoundaryModule a (d.append e) := by
  unfold compositionBoundaryModule
  have hleft : Fin.last (u.append (nil X Y)).length =
      appendBoundaryArrowIndex u (nil X Y) := by
    apply Fin.ext
    change u.length + 0 = u.length
    omega
  have hright : (0 : Fin (((nil X Y).append v).length + 1)) =
      appendBoundaryArrowIndex (nil X Y) v := by
    apply Fin.ext
    rfl
  rw [hleft, arrowSource_append_boundary, hright,
    arrowTarget_append_boundary]
  change (dgHomZModuleCochainComplex
      (u.arrowSource (Fin.last u.length)) (v.arrowTarget 0)).X
        (appendArrowDegree a d (appendBoundaryArrowIndex u (nil X Y)) +
          e.arrowDegree 0) =
    (dgHomZModuleCochainComplex
      (u.arrowSource (Fin.last u.length)) (v.arrowTarget 0)).X
        (a.arrowDegree (Fin.last u.length) +
          appendArrowDegree d e (appendBoundaryArrowIndex (nil X Y) v))
  rw [appendArrowDegree_boundary, appendArrowDegree_boundary]
  rw [Fin.eq_zero (Fin.last (nil X Y).length)]
  rw [Int.add_assoc]
  rfl

def tripleCompositionBoundaryModule
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) : ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex
      (u.arrowSource (Fin.last u.length)) (v.arrowTarget 0)).X
    ((a.arrowDegree (Fin.last u.length) + d.arrowDegree 0) +
      e.arrowDegree 0)

def zeroMiddleRightBoundaryModule
    {X Y Z : ComplexCategory} {v : DrinfeldWord Y Z} {q r : ℤ}
    (d : DegreeProfile (nil X Y) q) (e : DegreeProfile v r) :
    ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex ((nil X Y).arrowSource 0)
      (v.arrowTarget 0)).X (d.arrowDegree 0 + e.arrowDegree 0)

def zeroMiddleRightBoundaryMap
    {X Y Z : ComplexCategory} {v : DrinfeldWord Y Z} {q r : ℤ}
    (d : DegreeProfile (nil X Y) q) (e : DegreeProfile v r) :
    factorModule d 0 ⊗ factorModule e 0 ⟶
      zeroMiddleRightBoundaryModule d e := by
  have hmiddle : (nil X Y).arrowTarget 0 = v.arrowSource 0 := by
    change Y = v.arrowSource 0
    exact (arrowSource_zero_eq_source v).symm
  exact dgCochainCompTensorOfEq ((nil X Y).arrowSource 0)
    ((nil X Y).arrowTarget 0) (v.arrowSource 0) (v.arrowTarget 0)
    hmiddle rfl

theorem zeroMiddleRightBoundaryModule_eq
    {X Y Z : ComplexCategory} {v : DrinfeldWord Y Z} {q r : ℤ}
    (d : DegreeProfile (nil X Y) q) (e : DegreeProfile v r) :
    zeroMiddleRightBoundaryModule d e = compositionBoundaryModule d e := by
  unfold zeroMiddleRightBoundaryModule compositionBoundaryModule
  have hi : Fin.last (nil X Y).length = 0 := Fin.eq_zero _
  rw [hi]

theorem zeroMiddleRightBoundaryMap_heq
    {X Y Z : ComplexCategory} {v : DrinfeldWord Y Z} {q r : ℤ}
    (d : DegreeProfile (nil X Y) q) (e : DegreeProfile v r) :
    HEq (zeroMiddleRightBoundaryMap d e) (compositionBoundaryMap d e) := by
  unfold zeroMiddleRightBoundaryMap compositionBoundaryMap
  have hi : Fin.last (nil X Y).length = 0 := Fin.eq_zero _
  apply dgCochainCompTensorOfEq_heq
  · exact congrArg (nil X Y).arrowSource hi.symm
  · exact congrArg (nil X Y).arrowTarget hi.symm
  · rfl
  · rfl
  · exact congrArg d.arrowDegree hi.symm
  · rfl
  · exact congrArg (fun t ↦ t + e.arrowDegree 0)
      (congrArg d.arrowDegree hi.symm)

def leftAssociatedBoundaryMap
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    compositionBoundaryModule a d ⊗ factorModule e 0 ⟶
      tripleCompositionBoundaryModule a d e := by
  have hmiddle : (nil X Y).arrowTarget 0 = v.arrowSource 0 := by
    change Y = v.arrowSource 0
    exact (arrowSource_zero_eq_source v).symm
  exact dgCochainCompTensorOfEq
    (u.arrowSource (Fin.last u.length)) ((nil X Y).arrowTarget 0)
      (v.arrowSource 0) (v.arrowTarget 0) hmiddle rfl

def rightAssociatedBoundaryMap
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    factorModule a (Fin.last u.length) ⊗ zeroMiddleRightBoundaryModule d e ⟶
      tripleCompositionBoundaryModule a d e := by
  have hmiddle : u.arrowTarget (Fin.last u.length) =
      (nil X Y).arrowSource 0 := by
    change u.arrowTarget (Fin.last u.length) = X
    exact arrowTarget_last_eq_target u
  exact dgCochainCompTensorOfEq
    (u.arrowSource (Fin.last u.length))
      (u.arrowTarget (Fin.last u.length)) ((nil X Y).arrowSource 0)
      (v.arrowTarget 0) hmiddle (by
        exact (Int.add_assoc _ _ _).symm)

theorem normalizedBoundaryMaps_assoc
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    (α_ (factorModule a (Fin.last u.length)) (factorModule d 0)
          (factorModule e 0)).inv ≫
        (compositionBoundaryMap a d ⊗ₘ 𝟙 (factorModule e 0)) ≫
        leftAssociatedBoundaryMap a d e =
      (𝟙 (factorModule a (Fin.last u.length)) ⊗ₘ
          zeroMiddleRightBoundaryMap d e) ≫
        rightAssociatedBoundaryMap a d e := by
  simpa only [factorModule, compositionBoundaryModule,
    tripleCompositionBoundaryModule, zeroMiddleRightBoundaryModule,
    zeroMiddleRightBoundaryMap, compositionBoundaryMap,
    leftAssociatedBoundaryMap, rightAssociatedBoundaryMap] using
    dgCochainCompTensorOfEq_assoc
      (u.arrowSource (Fin.last u.length))
      (u.arrowTarget (Fin.last u.length)) ((nil X Y).arrowSource 0)
      ((nil X Y).arrowTarget 0) (v.arrowSource 0) (v.arrowTarget 0)
      (by
        change u.arrowTarget (Fin.last u.length) = X
        exact arrowTarget_last_eq_target u)
      (by
        change Y = v.arrowSource 0
        exact (arrowSource_zero_eq_source v).symm)
      (a.arrowDegree (Fin.last u.length)) (d.arrowDegree 0)
      (e.arrowDegree 0)

theorem tripleCompositionBoundaryModule_eq_left
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    tripleCompositionBoundaryModule a d e =
      compositionBoundaryModule (a.append d) e := by
  unfold tripleCompositionBoundaryModule compositionBoundaryModule
  have hindex : Fin.last (u.append (nil X Y)).length =
      appendBoundaryArrowIndex u (nil X Y) := by
    apply Fin.ext
    change u.length + 0 = u.length
    omega
  rw [hindex, arrowSource_append_boundary]
  change (dgHomZModuleCochainComplex
      (u.arrowSource (Fin.last u.length)) (v.arrowTarget 0)).X
        ((a.arrowDegree (Fin.last u.length) + d.arrowDegree 0) +
          e.arrowDegree 0) =
    (dgHomZModuleCochainComplex
      (u.arrowSource (Fin.last u.length)) (v.arrowTarget 0)).X
        (appendArrowDegree a d (appendBoundaryArrowIndex u (nil X Y)) +
          e.arrowDegree 0)
  rw [appendArrowDegree_boundary]

theorem tripleCompositionBoundaryModule_eq_right
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    tripleCompositionBoundaryModule a d e =
      compositionBoundaryModule a (d.append e) :=
  (tripleCompositionBoundaryModule_eq_left a d e).trans
    (compositionBoundaryModule_assoc_of_middle_nil a d e)

theorem leftAssociatedBoundaryMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq (leftAssociatedBoundaryMap a d e)
      (compositionBoundaryMap (a.append d) e) := by
  unfold leftAssociatedBoundaryMap compositionBoundaryMap
  have hi : Fin.last (u.append (nil X Y)).length =
      appendBoundaryArrowIndex u (nil X Y) := by
    apply Fin.ext
    change u.length + 0 = u.length
    omega
  have hsource : u.arrowSource (Fin.last u.length) =
      (u.append (nil X Y)).arrowSource
        (Fin.last (u.append (nil X Y)).length) := by
    rw [hi, arrowSource_append_boundary]
  have htarget : (nil X Y).arrowTarget 0 =
      (u.append (nil X Y)).arrowTarget
        (Fin.last (u.append (nil X Y)).length) := by
    rw [hi, arrowTarget_append_boundary]
  have hdegree : a.arrowDegree (Fin.last u.length) + d.arrowDegree 0 =
      (a.append d).arrowDegree
        (Fin.last (u.append (nil X Y)).length) := by
    rw [hi]
    change a.arrowDegree (Fin.last u.length) + d.arrowDegree 0 =
      appendArrowDegree a d (appendBoundaryArrowIndex u (nil X Y))
    rw [appendArrowDegree_boundary]
  apply dgCochainCompTensorOfEq_heq
  · exact hsource
  · exact htarget
  · rfl
  · rfl
  · exact hdegree
  · rfl
  · exact congrArg (fun t ↦ t + e.arrowDegree 0) hdegree

theorem rightAssociatedBoundaryMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq (rightAssociatedBoundaryMap a d e)
      (compositionBoundaryMap a (d.append e)) := by
  unfold rightAssociatedBoundaryMap compositionBoundaryMap
  have hi : (0 : Fin (((nil X Y).append v).length + 1)) =
      appendBoundaryArrowIndex (nil X Y) v := by
    apply Fin.ext
    rfl
  have hsource : (nil X Y).arrowSource 0 =
      ((nil X Y).append v).arrowSource 0 := by
    rw [hi, arrowSource_append_boundary]
    congr 1
  have htarget : v.arrowTarget 0 =
      ((nil X Y).append v).arrowTarget 0 := by
    rw [hi, arrowTarget_append_boundary]
  have hdegree : d.arrowDegree 0 + e.arrowDegree 0 =
      (d.append e).arrowDegree 0 := by
    rw [hi]
    change d.arrowDegree 0 + e.arrowDegree 0 =
      appendArrowDegree d e (appendBoundaryArrowIndex (nil X Y) v)
    rw [appendArrowDegree_boundary]
    congr 2
  apply dgCochainCompTensorOfEq_heq
  · rfl
  · rfl
  · exact hsource
  · exact htarget
  · rfl
  · exact hdegree
  · calc
      (a.arrowDegree (Fin.last u.length) + d.arrowDegree 0) +
          e.arrowDegree 0 =
        a.arrowDegree (Fin.last u.length) +
          (d.arrowDegree 0 + e.arrowDegree 0) := Int.add_assoc _ _ _
      _ = a.arrowDegree (Fin.last u.length) +
          (d.append e).arrowDegree 0 := congrArg
            (fun t ↦ a.arrowDegree (Fin.last u.length) + t) hdegree

theorem normalizedBoundaryPairCoherence
    (xs zs : List (ModuleCat.{0} ℤ))
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    AdjacentMergePairHCoherence
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d) (factorModule e 0 :: zs)
        (compositionBoundaryMap a d)).prefix xs)
      ((@AdjacentMergeData.head
        (compositionBoundaryModule a d) (factorModule e 0)
        (tripleCompositionBoundaryModule a d e) zs
        (leftAssociatedBoundaryMap a d e)).prefix xs)
      ((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: factorModule e 0 :: zs)
        (zeroMiddleRightBoundaryModule d e :: zs)
        (@AdjacentMergeData.head (factorModule d 0) (factorModule e 0)
          (zeroMiddleRightBoundaryModule d e) zs
          (zeroMiddleRightBoundaryMap d e))).prefix xs)
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length))
        (zeroMiddleRightBoundaryModule d e)
        (tripleCompositionBoundaryModule a d e) zs
        (rightAssociatedBoundaryMap a d e)).prefix xs) :=
  adjacentMergeAfter_pair_assoc xs (compositionBoundaryMap a d)
    (leftAssociatedBoundaryMap a d e) (zeroMiddleRightBoundaryMap d e)
    (rightAssociatedBoundaryMap a d e)
    (normalizedBoundaryMaps_assoc a d e)

theorem normalizedBoundaryPairTensorMap_eq
    (xs zs : List (ModuleCat.{0} ℤ))
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d) (factorModule e 0 :: zs)
        (compositionBoundaryMap a d)).prefix xs).tensorMap ≫
      ((@AdjacentMergeData.head
        (compositionBoundaryModule a d) (factorModule e 0)
        (tripleCompositionBoundaryModule a d e) zs
        (leftAssociatedBoundaryMap a d e)).prefix xs).tensorMap =
    ((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: factorModule e 0 :: zs)
        (zeroMiddleRightBoundaryModule d e :: zs)
        (@AdjacentMergeData.head (factorModule d 0) (factorModule e 0)
          (zeroMiddleRightBoundaryModule d e) zs
          (zeroMiddleRightBoundaryMap d e))).prefix xs).tensorMap ≫
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length))
        (zeroMiddleRightBoundaryModule d e)
        (tripleCompositionBoundaryModule a d e) zs
        (rightAssociatedBoundaryMap a d e)).prefix xs).tensorMap := by
  exact eq_of_heq
    (normalizedBoundaryPairCoherence xs zs a d e).tensorMap_heq

def compositionMiddleFactors
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {q : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q) :
    List (ModuleCat.{0} ℤ) :=
  finFamilyList (fun i : Fin k ↦ factorModule d i.succ.castSucc)

theorem compositionLeftPrefix_succ_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {q : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q) :
    compositionLeftPrefix d = factorModule d 0 :: compositionMiddleFactors d := by
  rw [compositionLeftPrefix, compositionMiddleFactors,
    finFamilyList_eq_ofFn, finFamilyList_eq_ofFn, List.ofFn_succ]
  congr 2

theorem compositionRightSuffix_succ_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory} {q : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q) :
    compositionRightSuffix d =
      compositionMiddleFactors d ++ [factorModule d (Fin.last (k + 1))] := by
  rw [compositionRightSuffix, compositionMiddleFactors,
    finFamilyList_eq_ofFn, finFamilyList_eq_ofFn, List.ofFn_succ_last]
  congr 1

theorem compositionBoundaryMap_append_left_succ_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq (compositionBoundaryMap (a.append d) e)
      (compositionBoundaryMap d e) := by
  unfold compositionBoundaryMap
  have hi : Fin.last (u.append
        ({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y)).length =
      appendRightArrowIndex (w := u) (Fin.last k) := by
    apply Fin.ext
    change u.length + (k + 1) = u.length + 1 + k
    omega
  apply dgCochainCompTensorOfEq_heq
  · rw [hi, arrowSource_append_right]
    rfl
  · rw [hi, arrowTarget_append_right]
    rfl
  · rfl
  · rfl
  · rw [hi]
    change appendArrowDegree a d (appendRightArrowIndex (Fin.last k)) = _
    rw [appendArrowDegree_right]
    rfl
  · rfl
  · rw [hi]
    change appendArrowDegree a d (appendRightArrowIndex (Fin.last k)) +
      e.arrowDegree 0 = _
    rw [appendArrowDegree_right]
    rfl

theorem compositionBoundaryMap_append_right_succ_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq (compositionBoundaryMap a (d.append e))
      (compositionBoundaryMap a d) := by
  unfold compositionBoundaryMap
  have hi : (0 : Fin ((({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).append v).length + 1)) =
      appendLeftArrowIndex (v := v) (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  apply dgCochainCompTensorOfEq_heq
  · rfl
  · rfl
  · rw [hi, arrowSource_append_left]
    congr 1
  · rw [hi, arrowTarget_append_left]
    congr 1
  · rfl
  · rw [hi]
    change appendArrowDegree d e (appendLeftArrowIndex 0) = _
    rw [appendArrowDegree_left]
    congr 1
  · rw [hi]
    change a.arrowDegree (Fin.last u.length) +
      appendArrowDegree d e (appendLeftArrowIndex 0) = _
    rw [appendArrowDegree_left]
    congr 2

theorem compositionBoundaryModule_append_left_succ_eq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    compositionBoundaryModule (a.append d) e = compositionBoundaryModule d e := by
  unfold compositionBoundaryModule
  have hi : Fin.last (u.append
        ({ length := k + 1, intermediate := intermediate } :
          DrinfeldWord X Y)).length =
      appendRightArrowIndex (w := u) (Fin.last k) := by
    apply Fin.ext
    change u.length + (k + 1) = u.length + 1 + k
    omega
  rw [hi, arrowSource_append_right]
  change (dgHomZModuleCochainComplex
      (({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).arrowSource (Fin.last k).succ)
      (v.arrowTarget 0)).X
        (appendArrowDegree a d (appendRightArrowIndex (Fin.last k)) +
          e.arrowDegree 0) = _
  rw [appendArrowDegree_right]
  rfl

theorem compositionBoundaryModule_append_right_succ_eq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    compositionBoundaryModule a (d.append e) = compositionBoundaryModule a d := by
  unfold compositionBoundaryModule
  have hi : (0 : Fin ((({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).append v).length + 1)) =
      appendLeftArrowIndex (v := v) (0 : Fin (k + 1)) := by
    apply Fin.ext
    rfl
  rw [hi, arrowTarget_append_left]
  change (dgHomZModuleCochainComplex (u.arrowSource (Fin.last u.length))
      (({ length := k + 1, intermediate := intermediate } :
        DrinfeldWord X Y).arrowTarget 0)).X
        (a.arrowDegree (Fin.last u.length) +
          appendArrowDegree d e (appendLeftArrowIndex 0)) = _
  rw [appendArrowDegree_left]
  rfl

theorem positiveMiddleBoundaryPairCoherence
    (xs zs : List (ModuleCat.{0} ℤ))
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    AdjacentMergePairHCoherence
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
        (compositionBoundaryMap a d)).prefix xs)
      ((@AdjacentMergeData.tail (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e :: zs)
        (adjacentMergeAfter (compositionMiddleFactors d) (ys := zs)
          (compositionBoundaryMap d e))).prefix xs)
      ((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
        (factorModule d 0 :: compositionMiddleFactors d ++
          compositionBoundaryModule d e :: zs)
        (@AdjacentMergeData.tail (factorModule d 0)
          (compositionMiddleFactors d ++
            factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
          (compositionMiddleFactors d ++ compositionBoundaryModule d e :: zs)
          (adjacentMergeAfter (compositionMiddleFactors d) (ys := zs)
            (compositionBoundaryMap d e)))).prefix xs)
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e :: zs)
        (compositionBoundaryMap a d)).prefix xs) :=
  adjacentMergeAfter_pair_head_tail xs (compositionMiddleFactors d)
    (compositionBoundaryMap a d) (compositionBoundaryMap d e)

theorem positiveMiddleBoundaryPairTensorMap_eq
    (xs zs : List (ModuleCat.{0} ℤ))
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    (((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
        (compositionBoundaryMap a d)).prefix xs).tensorMap ≫
      ((@AdjacentMergeData.tail (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e :: zs)
        (adjacentMergeAfter (compositionMiddleFactors d) (ys := zs)
          (compositionBoundaryMap d e))).prefix xs).tensorMap) =
    (((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
        (factorModule d 0 :: compositionMiddleFactors d ++
          compositionBoundaryModule d e :: zs)
        (@AdjacentMergeData.tail (factorModule d 0)
          (compositionMiddleFactors d ++
            factorModule d (Fin.last (k + 1)) :: factorModule e 0 :: zs)
          (compositionMiddleFactors d ++ compositionBoundaryModule d e :: zs)
          (adjacentMergeAfter (compositionMiddleFactors d) (ys := zs)
            (compositionBoundaryMap d e)))).prefix xs).tensorMap ≫
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e :: zs)
        (compositionBoundaryMap a d)).prefix xs).tensorMap) := by
  exact eq_of_heq
    (positiveMiddleBoundaryPairCoherence xs zs a d e).tensorMap_heq

theorem finFamilyList_factorModule_append_boundary
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    finFamilyList (factorModule (d.append e)) =
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e := by
  rw [finFamilyList_eq_ofFn, compositionLeftPrefix, compositionRightSuffix,
    finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
  let h : (w.append v).length + 1 = w.length + (v.length + 1) := by
    simp [Nat.add_assoc]
  calc
    List.ofFn (factorModule (d.append e)) =
        List.ofFn (fun q : Fin (w.length + (v.length + 1)) ↦
          factorModule (d.append e) (Fin.cast h.symm q)) :=
      List.ofFn_congr h (factorModule (d.append e))
    _ = List.ofFn (Fin.append
        (fun i : Fin w.length ↦ factorModule d i.castSucc)
        (Fin.cases (compositionBoundaryModule d e)
          (fun j : Fin v.length ↦ factorModule e j.succ))) := by
      congr 1
      funext q
      refine Fin.addCases ?_ ?_ q
      · intro i
        have hi : Fin.cast h.symm (Fin.castAdd (v.length + 1) i) =
            appendLeftArrowIndex (v := v) i := by
          apply Fin.ext
          rfl
        rw [hi, factorModule_append_left]
        simp only [Fin.append_left]
      · intro j
        induction j using Fin.cases with
        | zero =>
            have hj : Fin.cast h.symm (Fin.natAdd w.length 0) =
                appendBoundaryArrowIndex w v := by
              apply Fin.ext
              rfl
            rw [hj, factorModule_append_boundary]
            simp only [Fin.append_right, Fin.cases_zero]
        | succ j =>
            have hj : Fin.cast h.symm (Fin.natAdd w.length j.succ) =
                appendRightArrowIndex (w := w) j := by
              apply Fin.ext
              simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ,
                appendRightArrowIndex, Fin.val_mk]
              omega
            rw [hj, factorModule_append_right]
            simp only [Fin.append_right, Fin.cases_succ]
    _ = _ := by
      rw [List.ofFn_fin_append, List.ofFn_succ]
      rfl

theorem compositionLeftPrefix_append_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionLeftPrefix (d.append e) =
      (compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e).dropLast := by
  calc
    compositionLeftPrefix (d.append e) =
        (finFamilyList (factorModule (d.append e))).dropLast := by
      rw [finFamilyList_factorModule_eq_prefix_last]
      simp
    _ = _ := congrArg List.dropLast (finFamilyList_factorModule_append_boundary d e)

theorem compositionRightSuffix_append_eq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionRightSuffix (d.append e) =
      (compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e).tail := by
  calc
    compositionRightSuffix (d.append e) =
        (finFamilyList (factorModule (d.append e))).tail := by
      rw [finFamilyList_factorModule_eq_first_suffix]
      rfl
    _ = _ := congrArg List.tail (finFamilyList_factorModule_append_boundary d e)

@[simp]
theorem compositionLeftPrefix_nil
    {X Y : ComplexCategory} {q : ℤ} (d : DegreeProfile (nil X Y) q) :
    compositionLeftPrefix d = [] := by
  rw [compositionLeftPrefix, finFamilyList_eq_ofFn]
  rfl

@[simp]
theorem compositionRightSuffix_nil
    {X Y : ComplexCategory} {q : ℤ} (d : DegreeProfile (nil X Y) q) :
    compositionRightSuffix d = [] := by
  rw [compositionRightSuffix, finFamilyList_eq_ofFn]
  rfl

theorem compositionLeftPrefix_append_zero_eq
    {W X Y : ComplexCategory} {u : DrinfeldWord W X} {p q : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q) :
    compositionLeftPrefix (a.append d) = compositionLeftPrefix a := by
  rw [compositionLeftPrefix_append_eq, compositionRightSuffix_nil,
    List.dropLast_concat]

theorem compositionRightSuffix_zero_append_eq
    {X Y Z : ComplexCategory} {v : DrinfeldWord Y Z} {q r : ℤ}
    (d : DegreeProfile (nil X Y) q) (e : DegreeProfile v r) :
    compositionRightSuffix (d.append e) = compositionRightSuffix e := by
  rw [compositionRightSuffix_append_eq, compositionLeftPrefix_nil]
  simp only [List.nil_append, List.tail_cons]

theorem compositionLeftPrefix_append_succ_eq
    {W X Y : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {p q : ℤ} (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q) :
    compositionLeftPrefix (a.append d) =
      compositionLeftPrefix a ++ compositionBoundaryModule a d ::
        compositionMiddleFactors d := by
  rw [compositionLeftPrefix_append_eq, compositionRightSuffix_succ_eq]
  rw [List.dropLast_append_cons,
    List.dropLast_cons_of_ne_nil (by simp), List.dropLast_concat]

theorem compositionRightSuffix_succ_append_eq
    {X Y Z : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {q r : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    compositionRightSuffix (d.append e) =
      compositionMiddleFactors d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e := by
  rw [compositionRightSuffix_append_eq, compositionLeftPrefix_succ_eq]
  rfl

theorem zeroLeftFirstMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((adjacentMergeAfter (compositionLeftPrefix a)
          (ys := compositionRightSuffix d)
          (compositionBoundaryMap a d)).suffix
        (finFamilyList (factorModule e)))
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (factorModule e 0 :: compositionRightSuffix e)
        (compositionBoundaryMap a d)).prefix (compositionLeftPrefix a)) := by
  apply HEq.trans (adjacentMergeAfter_suffix_heq
    (compositionLeftPrefix a) (compositionBoundaryMap a d)
    (finFamilyList (factorModule e)))
  have hys : compositionRightSuffix d ++ finFamilyList (factorModule e) =
      factorModule e 0 :: compositionRightSuffix e := by
    rw [compositionRightSuffix_nil, List.nil_append,
      finFamilyList_factorModule_eq_first_suffix]
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap a d) (g := compositionBoundaryMap a d)
    rfl rfl rfl rfl hys HEq.rfl)
  exact heq_of_eq (adjacentMergeAfter_eq_prefix_head
    (compositionLeftPrefix a) (compositionBoundaryMap a d))

theorem zeroRightFirstMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e)).prefix
        (finFamilyList (factorModule a)))
      ((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: factorModule e 0 :: compositionRightSuffix e)
        (zeroMiddleRightBoundaryModule d e :: compositionRightSuffix e)
        (@AdjacentMergeData.head (factorModule d 0) (factorModule e 0)
          (zeroMiddleRightBoundaryModule d e) (compositionRightSuffix e)
          (zeroMiddleRightBoundaryMap d e))).prefix
        (compositionLeftPrefix a)) := by
  apply HEq.trans (adjacentMergeAfter_prefix_heq
    (compositionLeftPrefix d) (finFamilyList (factorModule a))
    (compositionBoundaryMap d e))
  have hxs : finFamilyList (factorModule a) ++ compositionLeftPrefix d =
      compositionLeftPrefix a ++ [factorModule a (Fin.last u.length)] := by
    rw [compositionLeftPrefix_nil, List.append_nil,
      finFamilyList_factorModule_eq_prefix_last]
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap d e) (g := zeroMiddleRightBoundaryMap d e)
    hxs rfl rfl (zeroMiddleRightBoundaryModule_eq d e).symm rfl
    (zeroMiddleRightBoundaryMap_heq d e).symm)
  apply HEq.trans (heq_of_eq (adjacentMergeAfter_eq_prefix_head
    (compositionLeftPrefix a ++ [factorModule a (Fin.last u.length)])
    (zeroMiddleRightBoundaryMap d e)))
  exact (AdjacentMergeData.prefix_prefix_heq
    (@AdjacentMergeData.head (factorModule d 0) (factorModule e 0)
      (zeroMiddleRightBoundaryModule d e) (compositionRightSuffix e)
      (zeroMiddleRightBoundaryMap d e))
    [factorModule a (Fin.last u.length)] (compositionLeftPrefix a)).symm

theorem zeroLeftSecondMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix (a.append d))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (a.append d) e))
      ((@AdjacentMergeData.head
        (compositionBoundaryModule a d) (factorModule e 0)
        (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
        (leftAssociatedBoundaryMap a d e)).prefix (compositionLeftPrefix a)) := by
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap (a.append d) e)
    (g := leftAssociatedBoundaryMap a d e)
    (compositionLeftPrefix_append_zero_eq a d)
    (factorModule_append_last_of_right_nil a d) rfl
    (tripleCompositionBoundaryModule_eq_left a d e).symm rfl
    (leftAssociatedBoundaryMap_heq a d e).symm)
  exact heq_of_eq (adjacentMergeAfter_eq_prefix_head
    (compositionLeftPrefix a) (leftAssociatedBoundaryMap a d e))

theorem zeroRightSecondMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix a)
        (ys := compositionRightSuffix (d.append e))
        (compositionBoundaryMap a (d.append e)))
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length))
        (zeroMiddleRightBoundaryModule d e)
        (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
        (rightAssociatedBoundaryMap a d e)).prefix (compositionLeftPrefix a)) := by
  have hmiddle : factorModule (d.append e) 0 =
      zeroMiddleRightBoundaryModule d e :=
    (factorModule_append_first_of_left_nil d e).trans
      (zeroMiddleRightBoundaryModule_eq d e).symm
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap a (d.append e))
    (g := rightAssociatedBoundaryMap a d e)
    rfl rfl hmiddle (tripleCompositionBoundaryModule_eq_right a d e).symm
    (compositionRightSuffix_zero_append_eq d e)
    (rightAssociatedBoundaryMap_heq a d e).symm)
  exact heq_of_eq (adjacentMergeAfter_eq_prefix_head
    (compositionLeftPrefix a) (rightAssociatedBoundaryMap a d e))

theorem zeroLeftFirstMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((adjacentMergeAfter (compositionLeftPrefix a)
          (ys := compositionRightSuffix d)
          (compositionBoundaryMap a d)).suffix
        (finFamilyList (factorModule e))).tensorMap
      (((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (factorModule e 0 :: compositionRightSuffix e)
        (compositionBoundaryMap a d)).prefix
          (compositionLeftPrefix a)).tensorMap) := by
  apply AdjacentMergeData.tensorMap_heq
  · simp only [compositionRightSuffix_nil]
    rw [finFamilyList_factorModule_eq_first_suffix]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · simp only [compositionRightSuffix_nil]
    rw [finFamilyList_factorModule_eq_first_suffix]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · exact zeroLeftFirstMergeData_heq a d e

theorem zeroRightFirstMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e)).prefix
        (finFamilyList (factorModule a))).tensorMap
      (((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: factorModule e 0 :: compositionRightSuffix e)
        (zeroMiddleRightBoundaryModule d e :: compositionRightSuffix e)
        (@AdjacentMergeData.head (factorModule d 0) (factorModule e 0)
          (zeroMiddleRightBoundaryModule d e) (compositionRightSuffix e)
          (zeroMiddleRightBoundaryMap d e))).prefix
      (compositionLeftPrefix a)).tensorMap) := by
  have hlast : factorModule d (Fin.last (nil X Y).length) = factorModule d 0 := by
    congr 1
  apply AdjacentMergeData.tensorMap_heq
  · simp only [compositionLeftPrefix_nil]
    rw [finFamilyList_factorModule_eq_prefix_last]
    simp only [List.append_assoc, List.cons_append, List.nil_append, hlast]
  · simp only [compositionLeftPrefix_nil]
    rw [finFamilyList_factorModule_eq_prefix_last,
      zeroMiddleRightBoundaryModule_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · exact zeroRightFirstMergeData_heq a d e

theorem zeroLeftSecondMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix (a.append d))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (a.append d) e)).tensorMap
      (((@AdjacentMergeData.head
        (compositionBoundaryModule a d) (factorModule e 0)
        (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
        (leftAssociatedBoundaryMap a d e)).prefix
          (compositionLeftPrefix a)).tensorMap) := by
  apply AdjacentMergeData.tensorMap_heq
  · rw [compositionLeftPrefix_append_zero_eq,
      factorModule_append_last_of_right_nil]
  · rw [compositionLeftPrefix_append_zero_eq,
      ← tripleCompositionBoundaryModule_eq_left]
  · exact zeroLeftSecondMergeData_heq a d e

theorem zeroRightSecondMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix a)
        (ys := compositionRightSuffix (d.append e))
        (compositionBoundaryMap a (d.append e))).tensorMap
      (((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length))
        (zeroMiddleRightBoundaryModule d e)
        (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
        (rightAssociatedBoundaryMap a d e)).prefix
          (compositionLeftPrefix a)).tensorMap) := by
  apply AdjacentMergeData.tensorMap_heq
  · rw [compositionRightSuffix_zero_append_eq,
      factorModule_append_first_of_left_nil,
      ← zeroMiddleRightBoundaryModule_eq]
  · rw [compositionRightSuffix_zero_append_eq,
      ← tripleCompositionBoundaryModule_eq_right]
  · exact zeroRightSecondMergeData_heq a d e

theorem positiveLeftFirstMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((adjacentMergeAfter (compositionLeftPrefix a)
          (ys := compositionRightSuffix d)
          (compositionBoundaryMap a d)).suffix
        (finFamilyList (factorModule e)))
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (compositionBoundaryMap a d)).prefix (compositionLeftPrefix a)) := by
  apply HEq.trans (adjacentMergeAfter_suffix_heq
    (compositionLeftPrefix a) (compositionBoundaryMap a d)
    (finFamilyList (factorModule e)))
  have hys : compositionRightSuffix d ++ finFamilyList (factorModule e) =
      compositionMiddleFactors d ++
        factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
          compositionRightSuffix e := by
    rw [compositionRightSuffix_succ_eq,
      finFamilyList_factorModule_eq_first_suffix]
    exact (appendSingletonTailEq (compositionMiddleFactors d)
      (factorModule d (Fin.last (k + 1)))
      (factorModule e 0 :: compositionRightSuffix e)).symm
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap a d) (g := compositionBoundaryMap a d)
    rfl rfl rfl rfl hys HEq.rfl)
  exact heq_of_eq (adjacentMergeAfter_eq_prefix_head
    (compositionLeftPrefix a) (compositionBoundaryMap a d))

theorem positiveLeftSecondMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix (a.append d))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (a.append d) e))
      ((@AdjacentMergeData.tail (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e)
        (adjacentMergeAfter (compositionMiddleFactors d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e))).prefix (compositionLeftPrefix a)) := by
  let f := adjacentMergeAfter (compositionMiddleFactors d)
    (ys := compositionRightSuffix e) (compositionBoundaryMap d e)
  have hp : compositionLeftPrefix (a.append d) =
      (compositionLeftPrefix a ++ [compositionBoundaryModule a d]) ++
        compositionMiddleFactors d :=
    (compositionLeftPrefix_append_succ_eq a d).trans
      (appendSingletonTailEq (compositionLeftPrefix a)
        (compositionBoundaryModule a d) (compositionMiddleFactors d))
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap (a.append d) e)
    (g := compositionBoundaryMap d e) hp
    (factorModule_append_last_of_right_succ a d) rfl
    (compositionBoundaryModule_append_left_succ_eq a d e)
    rfl (compositionBoundaryMap_append_left_succ_heq a d e))
  apply HEq.trans (adjacentMergeAfter_prefix_heq
    (compositionMiddleFactors d)
    (compositionLeftPrefix a ++ [compositionBoundaryModule a d])
    (compositionBoundaryMap d e)).symm
  exact (AdjacentMergeData.prefix_prefix_heq f
    [compositionBoundaryModule a d] (compositionLeftPrefix a)).symm

theorem positiveLeftFirstMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (((adjacentMergeAfter (compositionLeftPrefix a)
          (ys := compositionRightSuffix d)
          (compositionBoundaryMap a d)).suffix
        (finFamilyList (factorModule e))).tensorMap)
      (((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (compositionBoundaryMap a d)).prefix
          (compositionLeftPrefix a)).tensorMap) := by
  apply AdjacentMergeData.tensorMap_heq
  · rw [compositionRightSuffix_succ_eq,
      finFamilyList_factorModule_eq_first_suffix]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [compositionRightSuffix_succ_eq,
      finFamilyList_factorModule_eq_first_suffix]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · exact positiveLeftFirstMergeData_heq a d e

theorem positiveLeftSecondMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix (a.append d))
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap (a.append d) e)).tensorMap
      (((@AdjacentMergeData.tail (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e)
        (adjacentMergeAfter (compositionMiddleFactors d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e))).prefix
            (compositionLeftPrefix a)).tensorMap) := by
  have hlast : (Fin.last k).succ = Fin.last (k + 1) := rfl
  apply AdjacentMergeData.tensorMap_heq
  · rw [compositionLeftPrefix_append_succ_eq,
      factorModule_append_last_of_right_succ, hlast]
    simp only [List.append_assoc, List.cons_append]
  · rw [compositionLeftPrefix_append_succ_eq,
      compositionBoundaryModule_append_left_succ_eq]
    simp only [List.append_assoc, List.cons_append]
  · exact positiveLeftSecondMergeData_heq a d e

theorem positiveRightFirstMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e)).prefix
        (finFamilyList (factorModule a)))
      ((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (factorModule d 0 :: compositionMiddleFactors d ++
          compositionBoundaryModule d e :: compositionRightSuffix e)
        (@AdjacentMergeData.tail (factorModule d 0)
          (compositionMiddleFactors d ++
            factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
              compositionRightSuffix e)
          (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
            compositionRightSuffix e)
          (adjacentMergeAfter (compositionMiddleFactors d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)))).prefix
              (compositionLeftPrefix a)) := by
  let f := adjacentMergeAfter (compositionMiddleFactors d)
    (ys := compositionRightSuffix e) (compositionBoundaryMap d e)
  let P := (compositionLeftPrefix a ++ [factorModule a (Fin.last u.length)]) ++
    [factorModule d 0]
  apply HEq.trans (adjacentMergeAfter_prefix_heq
    (compositionLeftPrefix d) (finFamilyList (factorModule a))
    (compositionBoundaryMap d e))
  have hxs : finFamilyList (factorModule a) ++ compositionLeftPrefix d =
      P ++ compositionMiddleFactors d := by
    rw [finFamilyList_factorModule_eq_prefix_last,
      compositionLeftPrefix_succ_eq]
    exact appendSingletonTailEq
      (compositionLeftPrefix a ++ [factorModule a (Fin.last u.length)])
      (factorModule d 0) (compositionMiddleFactors d)
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap d e) (g := compositionBoundaryMap d e)
    hxs rfl rfl rfl rfl HEq.rfl)
  apply HEq.trans (adjacentMergeAfter_prefix_heq
    (compositionMiddleFactors d) P (compositionBoundaryMap d e)).symm
  have hraw := (AdjacentMergeData.prefix_prefix_heq
    (f.prefix [factorModule d 0]) [factorModule a (Fin.last u.length)]
      (compositionLeftPrefix a)).trans
    (AdjacentMergeData.prefix_prefix_heq f [factorModule d 0]
      (compositionLeftPrefix a ++ [factorModule a (Fin.last u.length)]))
  exact hraw.symm

theorem positiveRightSecondMergeData_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix a)
        (ys := compositionRightSuffix (d.append e))
        (compositionBoundaryMap a (d.append e)))
      ((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e)
        (compositionBoundaryMap a d)).prefix (compositionLeftPrefix a)) := by
  apply HEq.trans (adjacentMergeAfter_congr
    (f := compositionBoundaryMap a (d.append e))
    (g := compositionBoundaryMap a d) rfl rfl
    (factorModule_append_first_of_left_succ d e)
    (compositionBoundaryModule_append_right_succ_eq a d e)
    (compositionRightSuffix_succ_append_eq d e)
    (compositionBoundaryMap_append_right_succ_heq a d e))
  exact heq_of_eq (adjacentMergeAfter_eq_prefix_head
    (compositionLeftPrefix a) (compositionBoundaryMap a d))

theorem positiveRightFirstMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (((adjacentMergeAfter (compositionLeftPrefix d)
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap d e)).prefix
        (finFamilyList (factorModule a))).tensorMap)
      (((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (factorModule d 0 :: compositionMiddleFactors d ++
          compositionBoundaryModule d e :: compositionRightSuffix e)
        (@AdjacentMergeData.tail (factorModule d 0)
          (compositionMiddleFactors d ++
            factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
              compositionRightSuffix e)
          (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
            compositionRightSuffix e)
          (adjacentMergeAfter (compositionMiddleFactors d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)))).prefix
              (compositionLeftPrefix a)).tensorMap) := by
  apply AdjacentMergeData.tensorMap_heq
  · rw [finFamilyList_factorModule_eq_prefix_last,
      compositionLeftPrefix_succ_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · rw [finFamilyList_factorModule_eq_prefix_last,
      compositionLeftPrefix_succ_eq]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · exact positiveRightFirstMergeData_heq a d e

theorem positiveRightSecondMergeTensorMap_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      (adjacentMergeAfter (compositionLeftPrefix a)
        (ys := compositionRightSuffix (d.append e))
        (compositionBoundaryMap a (d.append e))).tensorMap
      (((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
          compositionRightSuffix e)
        (compositionBoundaryMap a d)).prefix
          (compositionLeftPrefix a)).tensorMap) := by
  apply AdjacentMergeData.tensorMap_heq
  · rw [factorModule_append_first_of_left_succ,
      compositionRightSuffix_succ_append_eq]
  · rw [compositionBoundaryModule_append_right_succ_eq,
      compositionRightSuffix_succ_append_eq]
  · exact positiveRightSecondMergeData_heq a d e

@[reassoc]
theorem summandRightUnitTarget_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_append_boundary d
          (nilDegreeProfile Y Y 0)).symm) ≫
        (summandRightUnitIso d).hom =
      (tensorMapDataReplaceAfter (compositionLeftPrefix d)
          (eqToHom (compositionBoundaryModule_right_nil d)) []).tensorMap ≫
        (summandLastFactorIso d).inv := by
  rw [tensorMapDataReplaceAfter_eqToHom]
  simp only [summandRightUnitIso, summandLastFactorIso,
    summandModuleTransportIso, Iso.trans_hom, eqToIso.hom,
    eqToIso.inv, eqToHom_trans]
  congr 1

@[reassoc]
theorem summandLeftUnitTarget_transport
    {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) :
    eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_append_boundary
          (nilDegreeProfile X X 0) d).symm) ≫
        (summandLeftUnitIso d).hom =
      (tensorMapDataReplaceAfter []
          (eqToHom (compositionBoundaryModule_left_nil d))
          (compositionRightSuffix d)).tensorMap ≫
        (summandFirstFactorIso d).inv := by
  rw [tensorMapDataReplaceAfter_eqToHom]
  simp only [summandLeftUnitIso, summandFirstFactorIso,
    summandModuleTransportIso, Iso.trans_hom, eqToIso.hom,
    eqToIso.inv, eqToHom_trans]
  congr 1

def compositionMergedFactor
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Fin ((w.length + 1) + v.length) → ModuleCat.{0} ℤ :=
  recursiveMergedFactor (compositionSourceFactor d e)
    (compositionBoundaryIndex w v) (compositionBoundaryModule d e)

def compositionTargetFactor
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Fin ((w.length + 1) + v.length) → ModuleCat.{0} ℤ :=
  fun q ↦ factorModule (d.append e)
    (Fin.cast (by rw [append_length]; omega) q)

theorem compositionMergedFactor_eq_target
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionMergedFactor d e = compositionTargetFactor d e := by
  unfold compositionMergedFactor compositionTargetFactor
  rw [recursiveMergedFactor_eq_mergedFactor]
  funext q
  by_cases hlt : q < compositionBoundaryIndex w v
  · let i : Fin w.length := ⟨q.val, by
      have hi := (compositionBoundaryIndex w v).isLt
      change q.val < w.length at hlt
      exact hlt⟩
    have hsource : q.castSucc =
        compositionSourceLeftIndex (w := w) (v := v) i.castSucc := by
      apply Fin.ext
      rfl
    have htarget : Fin.cast (by rw [append_length]; omega) q =
        appendLeftArrowIndex (w := w) (v := v) i := by
      apply Fin.ext
      rfl
    rw [mergedFactor, if_pos hlt, hsource]
    simp only [compositionSourceFactor_left]
    rw [htarget, factorModule_append_left]
  · by_cases heq : q = compositionBoundaryIndex w v
    · subst q
      rw [mergedFactor, if_neg hlt, if_pos rfl]
      have htarget : Fin.cast (by rw [append_length]; omega)
          (compositionBoundaryIndex w v) = appendBoundaryArrowIndex w v := by
        apply Fin.ext
        rfl
      rw [htarget, factorModule_append_boundary]
    · have hgt : w.length < q.val := by
        have hle : w.length ≤ q.val := by
          change ¬q.val < w.length at hlt
          omega
        have hne : w.length ≠ q.val := by
          intro h
          apply heq
          apply Fin.ext
          exact h.symm
        omega
      let j : Fin v.length := ⟨q.val - w.length - 1, by
        have hq := q.isLt
        change q.val < (w.length + 1) + v.length at hq
        omega⟩
      have hsource : q.succ =
          compositionSourceRightIndex (w := w) (v := v) j.succ := by
        apply Fin.ext
        change q.val + 1 = w.length + 1 + (q.val - w.length - 1 + 1)
        omega
      have htarget : Fin.cast (by rw [append_length]; omega) q =
          appendRightArrowIndex (w := w) (v := v) j := by
        apply Fin.ext
        change q.val = w.length + 1 + (q.val - w.length - 1)
        omega
      rw [mergedFactor, if_neg hlt, if_neg heq, hsource]
      simp only [compositionSourceFactor_right]
      rw [htarget, factorModule_append_right]

theorem finFamilyList_compositionTargetFactor
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    finFamilyList (compositionTargetFactor d e) =
      finFamilyList (factorModule (d.append e)) := by
  rw [finFamilyList_eq_ofFn, finFamilyList_eq_ofFn]
  let h : (w.length + 1) + v.length = (w.append v).length + 1 := by
    rw [append_length]
    omega
  calc
    List.ofFn (compositionTargetFactor d e) =
        List.ofFn (fun q : Fin ((w.append v).length + 1) ↦
          compositionTargetFactor d e (Fin.cast h.symm q)) :=
      List.ofFn_congr h (compositionTargetFactor d e)
    _ = List.ofFn (factorModule (d.append e)) := by
      congr 1

def compositionMergeData
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    AdjacentMergeData (finFamilyList (compositionSourceFactor d e))
      (finFamilyList (compositionMergedFactor d e)) := by
  have hs := finFamilyList_compositionSourceFactor_boundary d e
  have ht : finFamilyList (compositionMergedFactor d e) =
      compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e := by
    rw [congrArg finFamilyList (compositionMergedFactor_eq_target d e),
      finFamilyList_compositionTargetFactor,
      finFamilyList_factorModule_append_boundary]
  rw [hs, ht]
  exact adjacentMergeAfter (compositionLeftPrefix d)
    (ys := compositionRightSuffix e) (compositionBoundaryMap d e)

theorem finFamilyList_compositionMergedFactor
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    finFamilyList (compositionMergedFactor d e) =
      finFamilyList (factorModule (d.append e)) := by
  rw [congrArg finFamilyList (compositionMergedFactor_eq_target d e),
    finFamilyList_compositionTargetFactor]

def compositionSourceListEq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    finFamilyList (factorModule d) ++ finFamilyList (factorModule e) =
      (compositionLeftPrefix d ++ [factorModule d (Fin.last w.length)]) ++
        factorModule e 0 :: compositionRightSuffix e :=
  congrArg₂ List.append (finFamilyList_factorModule_eq_prefix_last d)
    (finFamilyList_factorModule_eq_first_suffix e)

def compositionBoundaryListEq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    (compositionLeftPrefix d ++ [factorModule d (Fin.last w.length)]) ++
        factorModule e 0 :: compositionRightSuffix e =
      compositionLeftPrefix d ++ factorModule d (Fin.last w.length) ::
        factorModule e 0 :: compositionRightSuffix e :=
  appendBoundaryListsEq (compositionLeftPrefix d)
    (factorModule d (Fin.last w.length)) (factorModule e 0)
    (compositionRightSuffix e)

def compositionTargetListEq
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    compositionLeftPrefix d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e =
      finFamilyList (factorModule (d.append e)) :=
  (finFamilyList_factorModule_append_boundary d e).symm

theorem zeroLeftTransportedPair_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((eqToHom (congrArg tensorModuleList
            (List.append_assoc (finFamilyList (factorModule a))
              (finFamilyList (factorModule d))
              (finFamilyList (factorModule e))).symm) ≫
          eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append (compositionSourceListEq a d) rfl)) ≫
          eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append (compositionBoundaryListEq a d) rfl))) ≫
        ((adjacentMergeAfter (compositionLeftPrefix a)
            (ys := compositionRightSuffix d)
            (compositionBoundaryMap a d)).suffix
          (finFamilyList (factorModule e))).tensorMap ≫
        (eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append (compositionTargetListEq a d) rfl)) ≫
          eqToHom (congrArg tensorModuleList
            (compositionSourceListEq (a.append d) e)) ≫
          eqToHom (congrArg tensorModuleList
            (compositionBoundaryListEq (a.append d) e))) ≫
        (adjacentMergeAfter (compositionLeftPrefix (a.append d))
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap (a.append d) e)).tensorMap ≫
        (eqToHom (congrArg tensorModuleList
            (compositionTargetListEq (a.append d) e)) ≫
          (summandAssocIso a d e).hom))
      (((@AdjacentMergeData.head
          (factorModule a (Fin.last u.length)) (factorModule d 0)
          (compositionBoundaryModule a d)
          (factorModule e 0 :: compositionRightSuffix e)
          (compositionBoundaryMap a d)).prefix
            (compositionLeftPrefix a)).tensorMap ≫
        ((@AdjacentMergeData.head
          (compositionBoundaryModule a d) (factorModule e 0)
          (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
            (leftAssociatedBoundaryMap a d e)).prefix
            (compositionLeftPrefix a)).tensorMap) := by
  let pL := eqToHom (congrArg tensorModuleList
      (List.append_assoc (finFamilyList (factorModule a))
        (finFamilyList (factorModule d))
        (finFamilyList (factorModule e))).symm) ≫
    eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append (compositionSourceListEq a d) rfl)) ≫
    eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append (compositionBoundaryListEq a d) rfl))
  let fL := ((adjacentMergeAfter (compositionLeftPrefix a)
      (ys := compositionRightSuffix d)
      (compositionBoundaryMap a d)).suffix
    (finFamilyList (factorModule e))).tensorMap
  let mL := eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append (compositionTargetListEq a d) rfl)) ≫
    eqToHom (congrArg tensorModuleList
      (compositionSourceListEq (a.append d) e)) ≫
    eqToHom (congrArg tensorModuleList
      (compositionBoundaryListEq (a.append d) e))
  let gL := (adjacentMergeAfter (compositionLeftPrefix (a.append d))
    (ys := compositionRightSuffix e)
    (compositionBoundaryMap (a.append d) e)).tensorMap
  let q₁L := eqToHom (congrArg tensorModuleList
    (compositionTargetListEq (a.append d) e))
  let q₂L := (summandAssocIso a d e).hom
  let FL := ((@AdjacentMergeData.head
    (factorModule a (Fin.last u.length)) (factorModule d 0)
    (compositionBoundaryModule a d)
    (factorModule e 0 :: compositionRightSuffix e)
    (compositionBoundaryMap a d)).prefix (compositionLeftPrefix a)).tensorMap
  let GL := ((@AdjacentMergeData.head
    (compositionBoundaryModule a d) (factorModule e 0)
    (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
    (leftAssociatedBoundaryMap a d e)).prefix
      (compositionLeftPrefix a)).tensorMap
  have h := transportedPair₂_heq
    (p := pL) (f := fL) (m := mL) (g := gL)
    (q₁ := q₁L) (q₂ := q₂L) (F := FL) (G := GL)
    (hS := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_first_suffix d,
        compositionRightSuffix_nil,
        finFamilyList_factorModule_eq_first_suffix e]
      exact appendBoundaryListsEq (compositionLeftPrefix a)
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (factorModule e 0 :: compositionRightSuffix e))
    (hA := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_first_suffix d,
        compositionRightSuffix_nil,
        finFamilyList_factorModule_eq_first_suffix e]
      exact (appendBoundaryListsEq (compositionLeftPrefix a)
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (factorModule e 0 :: compositionRightSuffix e)).trans
          (appendPairTailEq (compositionLeftPrefix a)
            (factorModule a (Fin.last u.length)) (factorModule d 0)
            (factorModule e 0 :: compositionRightSuffix e)))
    (hB := by
      apply congrArg tensorModuleList
      rw [compositionRightSuffix_nil,
        finFamilyList_factorModule_eq_first_suffix e]
      exact (appendSingletonTailEq (compositionLeftPrefix a)
        (compositionBoundaryModule a d)
        (factorModule e 0 :: compositionRightSuffix e)).symm)
    (hC := by
      apply congrArg tensorModuleList
      rw [compositionLeftPrefix_append_zero_eq,
        factorModule_append_last_of_right_nil])
    (hD := by
      apply congrArg tensorModuleList
      rw [compositionTargetListEq, finFamilyList_factorModule_append_boundary,
        compositionLeftPrefix_append_zero_eq,
        ← tripleCompositionBoundaryModule_eq_left])
    (hE := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_append_boundary,
        compositionLeftPrefix_append_zero_eq,
        ← tripleCompositionBoundaryModule_eq_left])
    (hT := (summandAssocModuleEq a d e).symm.trans
      (congrArg tensorModuleList (by
        rw [finFamilyList_factorModule_append_boundary,
          compositionLeftPrefix_append_zero_eq,
          ← tripleCompositionBoundaryModule_eq_left])))
    (hp := eqToHom_comp₃_heq_id _ _ _)
    (hf := zeroLeftFirstMergeTensorMap_heq a d e)
    (hm := eqToHom_comp₃_heq_id _ _ _)
    (hg := zeroLeftSecondMergeTensorMap_heq a d e)
    (hq₁ := test_eqToHom_heq_id _)
    (hq₂ := summandAssocIso_hom_heq_id a d e)
  simpa only [pL, fL, mL, gL, q₁L, q₂L, FL, GL, Category.assoc] using h

theorem zeroRightTransportedPair_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append
              (rfl : finFamilyList (factorModule a) = _) (compositionSourceListEq d e))) ≫
          eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append
              (rfl : finFamilyList (factorModule a) = _) (compositionBoundaryListEq d e)))) ≫
        ((adjacentMergeAfter (compositionLeftPrefix d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)).prefix
          (finFamilyList (factorModule a))).tensorMap ≫
        (eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append
              (rfl : finFamilyList (factorModule a) = _) (compositionTargetListEq d e))) ≫
          eqToHom (congrArg tensorModuleList
            (compositionSourceListEq a (d.append e))) ≫
          eqToHom (congrArg tensorModuleList
            (compositionBoundaryListEq a (d.append e)))) ≫
        (adjacentMergeAfter (compositionLeftPrefix a)
          (ys := compositionRightSuffix (d.append e))
          (compositionBoundaryMap a (d.append e))).tensorMap ≫
        eqToHom (congrArg tensorModuleList
          (compositionTargetListEq a (d.append e))))
      (((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
          (factorModule d 0 :: factorModule e 0 :: compositionRightSuffix e)
          (zeroMiddleRightBoundaryModule d e :: compositionRightSuffix e)
          (@AdjacentMergeData.head (factorModule d 0) (factorModule e 0)
            (zeroMiddleRightBoundaryModule d e) (compositionRightSuffix e)
            (zeroMiddleRightBoundaryMap d e))).prefix
            (compositionLeftPrefix a)).tensorMap ≫
        ((@AdjacentMergeData.head
          (factorModule a (Fin.last u.length))
          (zeroMiddleRightBoundaryModule d e)
          (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
          (rightAssociatedBoundaryMap a d e)).prefix
            (compositionLeftPrefix a)).tensorMap) := by
  let pR := eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append
        (rfl : finFamilyList (factorModule a) = _) (compositionSourceListEq d e))) ≫
    eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append
        (rfl : finFamilyList (factorModule a) = _) (compositionBoundaryListEq d e)))
  let fR := ((adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix e)
      (compositionBoundaryMap d e)).prefix
    (finFamilyList (factorModule a))).tensorMap
  let mR := eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append
        (rfl : finFamilyList (factorModule a) = _) (compositionTargetListEq d e))) ≫
    eqToHom (congrArg tensorModuleList
      (compositionSourceListEq a (d.append e))) ≫
    eqToHom (congrArg tensorModuleList
      (compositionBoundaryListEq a (d.append e)))
  let gR := (adjacentMergeAfter (compositionLeftPrefix a)
    (ys := compositionRightSuffix (d.append e))
    (compositionBoundaryMap a (d.append e))).tensorMap
  let qR := eqToHom (congrArg tensorModuleList
    (compositionTargetListEq a (d.append e)))
  let FR := ((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
    (factorModule d 0 :: factorModule e 0 :: compositionRightSuffix e)
    (zeroMiddleRightBoundaryModule d e :: compositionRightSuffix e)
    (@AdjacentMergeData.head (factorModule d 0) (factorModule e 0)
      (zeroMiddleRightBoundaryModule d e) (compositionRightSuffix e)
      (zeroMiddleRightBoundaryMap d e))).prefix
        (compositionLeftPrefix a)).tensorMap
  let GR := ((@AdjacentMergeData.head
    (factorModule a (Fin.last u.length))
    (zeroMiddleRightBoundaryModule d e)
    (tripleCompositionBoundaryModule a d e) (compositionRightSuffix e)
    (rightAssociatedBoundaryMap a d e)).prefix
      (compositionLeftPrefix a)).tensorMap
  have hlast : factorModule d (Fin.last (nil X Y).length) = factorModule d 0 := by
    congr 1
  have h := transportedPair₂_heq
    (p := pR) (f := fR) (m := mR) (g := gR)
    (q₁ := qR) (q₂ := 𝟙 _) (F := FR) (G := GR)
    (hS := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_first_suffix d,
        compositionRightSuffix_nil,
        finFamilyList_factorModule_eq_first_suffix e]
      exact appendBoundaryListsEq (compositionLeftPrefix a)
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (factorModule e 0 :: compositionRightSuffix e))
    (hA := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_prefix_last d,
        compositionLeftPrefix_nil, hlast,
        finFamilyList_factorModule_eq_first_suffix e]
      rfl)
    (hB := by
      apply congrArg tensorModuleList
      rw [compositionLeftPrefix_nil,
        finFamilyList_factorModule_eq_prefix_last a,
        ← zeroMiddleRightBoundaryModule_eq]
      exact (appendSingletonTailEq (compositionLeftPrefix a)
        (factorModule a (Fin.last u.length))
        (zeroMiddleRightBoundaryModule d e :: compositionRightSuffix e)).symm)
    (hC := by
      apply congrArg tensorModuleList
      rw [factorModule_append_first_of_left_nil,
        compositionRightSuffix_zero_append_eq,
        ← zeroMiddleRightBoundaryModule_eq])
    (hD := by
      apply congrArg tensorModuleList
      rw [compositionRightSuffix_zero_append_eq,
        ← tripleCompositionBoundaryModule_eq_right])
    (hE := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_append_boundary,
        compositionRightSuffix_zero_append_eq,
        ← tripleCompositionBoundaryModule_eq_right])
    (hT := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_append_boundary,
        compositionRightSuffix_zero_append_eq,
        ← tripleCompositionBoundaryModule_eq_right])
    (hp := eqToHom_comp_heq_id _ _)
    (hf := zeroRightFirstMergeTensorMap_heq a d e)
    (hm := eqToHom_comp₃_heq_id _ _ _)
    (hg := zeroRightSecondMergeTensorMap_heq a d e)
    (hq₁ := test_eqToHom_heq_id _)
    (hq₂ := HEq.rfl)
  simpa only [pR, fR, mR, gR, qR, FR, GR, Category.assoc, Category.comp_id] using h

theorem positiveLeftTransportedPair_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((eqToHom (congrArg tensorModuleList
            (List.append_assoc (finFamilyList (factorModule a))
              (finFamilyList (factorModule d))
              (finFamilyList (factorModule e))).symm) ≫
          eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append (compositionSourceListEq a d) rfl)) ≫
          eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append (compositionBoundaryListEq a d) rfl))) ≫
        ((adjacentMergeAfter (compositionLeftPrefix a)
            (ys := compositionRightSuffix d)
            (compositionBoundaryMap a d)).suffix
          (finFamilyList (factorModule e))).tensorMap ≫
        (eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append (compositionTargetListEq a d) rfl)) ≫
          eqToHom (congrArg tensorModuleList
            (compositionSourceListEq (a.append d) e)) ≫
          eqToHom (congrArg tensorModuleList
            (compositionBoundaryListEq (a.append d) e))) ≫
        (adjacentMergeAfter (compositionLeftPrefix (a.append d))
          (ys := compositionRightSuffix e)
          (compositionBoundaryMap (a.append d) e)).tensorMap ≫
        (eqToHom (congrArg tensorModuleList
            (compositionTargetListEq (a.append d) e)) ≫
          (summandAssocIso a d e).hom))
      (((@AdjacentMergeData.head
        (factorModule a (Fin.last u.length)) (factorModule d 0)
        (compositionBoundaryModule a d)
        (compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (compositionBoundaryMap a d)).prefix
          (compositionLeftPrefix a)).tensorMap ≫
        ((@AdjacentMergeData.tail (compositionBoundaryModule a d)
          (compositionMiddleFactors d ++
            factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
              compositionRightSuffix e)
          (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
            compositionRightSuffix e)
          (adjacentMergeAfter (compositionMiddleFactors d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e))).prefix
              (compositionLeftPrefix a)).tensorMap) := by
  let pL := eqToHom (congrArg tensorModuleList
      (List.append_assoc (finFamilyList (factorModule a))
        (finFamilyList (factorModule d))
        (finFamilyList (factorModule e))).symm) ≫
    eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append (compositionSourceListEq a d) rfl)) ≫
    eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append (compositionBoundaryListEq a d) rfl))
  let fL := ((adjacentMergeAfter (compositionLeftPrefix a)
      (ys := compositionRightSuffix d)
      (compositionBoundaryMap a d)).suffix
    (finFamilyList (factorModule e))).tensorMap
  let mL := eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append (compositionTargetListEq a d) rfl)) ≫
    eqToHom (congrArg tensorModuleList
      (compositionSourceListEq (a.append d) e)) ≫
    eqToHom (congrArg tensorModuleList
      (compositionBoundaryListEq (a.append d) e))
  let gL := (adjacentMergeAfter (compositionLeftPrefix (a.append d))
    (ys := compositionRightSuffix e)
    (compositionBoundaryMap (a.append d) e)).tensorMap
  let q₁L := eqToHom (congrArg tensorModuleList
    (compositionTargetListEq (a.append d) e))
  let q₂L := (summandAssocIso a d e).hom
  let FL := ((@AdjacentMergeData.head
    (factorModule a (Fin.last u.length)) (factorModule d 0)
    (compositionBoundaryModule a d)
    (compositionMiddleFactors d ++
      factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
        compositionRightSuffix e)
    (compositionBoundaryMap a d)).prefix (compositionLeftPrefix a)).tensorMap
  let GL := ((@AdjacentMergeData.tail (compositionBoundaryModule a d)
    (compositionMiddleFactors d ++
      factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
        compositionRightSuffix e)
    (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
      compositionRightSuffix e)
    (adjacentMergeAfter (compositionMiddleFactors d)
      (ys := compositionRightSuffix e)
      (compositionBoundaryMap d e))).prefix (compositionLeftPrefix a)).tensorMap
  have hlast : (Fin.last k).succ = Fin.last (k + 1) := rfl
  have h := transportedPair₂_heq
    (p := pL) (f := fL) (m := mL) (g := gL)
    (q₁ := q₁L) (q₂ := q₂L) (F := FL) (G := GL)
    (hS := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_first_suffix d,
        compositionRightSuffix_succ_eq,
        finFamilyList_factorModule_eq_first_suffix e]
      simp only [List.append_assoc, List.cons_append, List.nil_append])
    (hA := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_first_suffix d,
        compositionRightSuffix_succ_eq,
        finFamilyList_factorModule_eq_first_suffix e]
      simp [List.append_assoc])
    (hB := by
      apply congrArg tensorModuleList
      rw [compositionRightSuffix_succ_eq,
        finFamilyList_factorModule_eq_first_suffix e]
      simp only [List.append_assoc, List.cons_append, List.nil_append])
    (hC := by
      apply congrArg tensorModuleList
      rw [compositionLeftPrefix_append_succ_eq,
        factorModule_append_last_of_right_succ, hlast]
      simp only [List.append_assoc, List.cons_append])
    (hD := by
      apply congrArg tensorModuleList
      rw [compositionLeftPrefix_append_succ_eq,
        compositionBoundaryModule_append_left_succ_eq]
      simp only [List.append_assoc, List.cons_append])
    (hE := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_append_boundary,
        compositionLeftPrefix_append_succ_eq,
        compositionBoundaryModule_append_left_succ_eq]
      simp only [List.append_assoc, List.cons_append])
    (hT := (summandAssocModuleEq a d e).symm.trans
      (congrArg tensorModuleList (by
        rw [finFamilyList_factorModule_append_boundary,
          compositionLeftPrefix_append_succ_eq,
          compositionBoundaryModule_append_left_succ_eq]
        simp only [List.append_assoc, List.cons_append])))
    (hp := eqToHom_comp₃_heq_id _ _ _)
    (hf := positiveLeftFirstMergeTensorMap_heq a d e)
    (hm := eqToHom_comp₃_heq_id _ _ _)
    (hg := positiveLeftSecondMergeTensorMap_heq a d e)
    (hq₁ := test_eqToHom_heq_id _)
    (hq₂ := summandAssocIso_hom_heq_id a d e)
  simpa only [pL, fL, mL, gL, q₁L, q₂L, FL, GL, Category.assoc] using h

theorem positiveRightTransportedPair_heq
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    HEq
      ((eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append
              (rfl : finFamilyList (factorModule a) = _)
              (compositionSourceListEq d e))) ≫
          eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append
              (rfl : finFamilyList (factorModule a) = _)
              (compositionBoundaryListEq d e)))) ≫
        ((adjacentMergeAfter (compositionLeftPrefix d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)).prefix
          (finFamilyList (factorModule a))).tensorMap ≫
        (eqToHom (congrArg tensorModuleList
            (congrArg₂ List.append
              (rfl : finFamilyList (factorModule a) = _)
              (compositionTargetListEq d e))) ≫
          eqToHom (congrArg tensorModuleList
            (compositionSourceListEq a (d.append e))) ≫
          eqToHom (congrArg tensorModuleList
            (compositionBoundaryListEq a (d.append e)))) ≫
        (adjacentMergeAfter (compositionLeftPrefix a)
          (ys := compositionRightSuffix (d.append e))
          (compositionBoundaryMap a (d.append e))).tensorMap ≫
        eqToHom (congrArg tensorModuleList
          (compositionTargetListEq a (d.append e))))
      (((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
        (factorModule d 0 :: compositionMiddleFactors d ++
          factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
            compositionRightSuffix e)
        (factorModule d 0 :: compositionMiddleFactors d ++
          compositionBoundaryModule d e :: compositionRightSuffix e)
        (@AdjacentMergeData.tail (factorModule d 0)
          (compositionMiddleFactors d ++
            factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
              compositionRightSuffix e)
          (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
            compositionRightSuffix e)
          (adjacentMergeAfter (compositionMiddleFactors d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)))).prefix
              (compositionLeftPrefix a)).tensorMap ≫
        ((@AdjacentMergeData.head
          (factorModule a (Fin.last u.length)) (factorModule d 0)
          (compositionBoundaryModule a d)
          (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
            compositionRightSuffix e)
          (compositionBoundaryMap a d)).prefix
            (compositionLeftPrefix a)).tensorMap) := by
  let pR := eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append
        (rfl : finFamilyList (factorModule a) = _)
        (compositionSourceListEq d e))) ≫
    eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append
        (rfl : finFamilyList (factorModule a) = _)
        (compositionBoundaryListEq d e)))
  let fR := ((adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix e)
      (compositionBoundaryMap d e)).prefix
    (finFamilyList (factorModule a))).tensorMap
  let mR := eqToHom (congrArg tensorModuleList
      (congrArg₂ List.append
        (rfl : finFamilyList (factorModule a) = _)
        (compositionTargetListEq d e))) ≫
    eqToHom (congrArg tensorModuleList
      (compositionSourceListEq a (d.append e))) ≫
    eqToHom (congrArg tensorModuleList
      (compositionBoundaryListEq a (d.append e)))
  let gR := (adjacentMergeAfter (compositionLeftPrefix a)
    (ys := compositionRightSuffix (d.append e))
    (compositionBoundaryMap a (d.append e))).tensorMap
  let qR := eqToHom (congrArg tensorModuleList
    (compositionTargetListEq a (d.append e)))
  let FR := ((@AdjacentMergeData.tail (factorModule a (Fin.last u.length))
    (factorModule d 0 :: compositionMiddleFactors d ++
      factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
        compositionRightSuffix e)
    (factorModule d 0 :: compositionMiddleFactors d ++
      compositionBoundaryModule d e :: compositionRightSuffix e)
    (@AdjacentMergeData.tail (factorModule d 0)
      (compositionMiddleFactors d ++
        factorModule d (Fin.last (k + 1)) :: factorModule e 0 ::
          compositionRightSuffix e)
      (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
        compositionRightSuffix e)
      (adjacentMergeAfter (compositionMiddleFactors d)
        (ys := compositionRightSuffix e)
        (compositionBoundaryMap d e)))).prefix
          (compositionLeftPrefix a)).tensorMap
  let GR := ((@AdjacentMergeData.head
    (factorModule a (Fin.last u.length)) (factorModule d 0)
    (compositionBoundaryModule a d)
    (compositionMiddleFactors d ++ compositionBoundaryModule d e ::
      compositionRightSuffix e)
    (compositionBoundaryMap a d)).prefix (compositionLeftPrefix a)).tensorMap
  have h := transportedPair₂_heq
    (p := pR) (f := fR) (m := mR) (g := gR)
    (q₁ := qR) (q₂ := 𝟙 _) (F := FR) (G := GR)
    (hS := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_first_suffix d,
        compositionRightSuffix_succ_eq,
        finFamilyList_factorModule_eq_first_suffix e]
      simp [List.append_assoc])
    (hA := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        finFamilyList_factorModule_eq_first_suffix e]
      apply congrArg
        ((compositionLeftPrefix a ++ [factorModule a (Fin.last u.length)]) ++ ·)
      rw [finFamilyList_factorModule_eq_prefix_last]
      exact (appendSingletonTailEq (compositionLeftPrefix d)
        (factorModule d (Fin.last (k + 1)))
        (factorModule e 0 :: compositionRightSuffix e)).symm)
    (hB := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_eq_prefix_last a,
        compositionLeftPrefix_succ_eq]
      simp [List.append_assoc])
    (hC := by
      apply congrArg tensorModuleList
      rw [factorModule_append_first_of_left_succ,
        compositionRightSuffix_succ_append_eq]
      simp)
    (hD := by
      apply congrArg tensorModuleList
      rw [compositionBoundaryModule_append_right_succ_eq,
        compositionRightSuffix_succ_append_eq])
    (hE := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_append_boundary,
        compositionBoundaryModule_append_right_succ_eq,
        compositionRightSuffix_succ_append_eq])
    (hT := by
      apply congrArg tensorModuleList
      rw [finFamilyList_factorModule_append_boundary,
        compositionBoundaryModule_append_right_succ_eq,
        compositionRightSuffix_succ_append_eq])
    (hp := eqToHom_comp_heq_id _ _)
    (hf := positiveRightFirstMergeTensorMap_heq a d e)
    (hm := eqToHom_comp₃_heq_id _ _ _)
    (hg := positiveRightSecondMergeTensorMap_heq a d e)
    (hq₁ := test_eqToHom_heq_id _)
    (hq₂ := HEq.rfl)
  simpa only [pR, fR, mR, gR, qR, FR, GR, Category.assoc, Category.comp_id] using h

def normalizedSummandCompositionMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom (summandModule d ⊗ summandModule e)
      (summandModule (d.append e)) :=
  (tensorModuleListAppendIso (finFamilyList (factorModule d))
      (finFamilyList (factorModule e))).hom ≫
    eqToHom (congrArg tensorModuleList (compositionSourceListEq d e)) ≫
    eqToHom (congrArg tensorModuleList (compositionBoundaryListEq d e)) ≫
    (adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap ≫
    eqToHom (congrArg tensorModuleList (compositionTargetListEq d e))

def summandCompositionRemainder
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    tensorModuleList
        (finFamilyList (factorModule d) ++ finFamilyList (factorModule e)) ⟶
      summandModule (d.append e) :=
  eqToHom (congrArg tensorModuleList (compositionSourceListEq d e)) ≫
    eqToHom (congrArg tensorModuleList (compositionBoundaryListEq d e)) ≫
    (adjacentMergeAfter (compositionLeftPrefix d)
      (ys := compositionRightSuffix e) (compositionBoundaryMap d e)).tensorMap ≫
    eqToHom (congrArg tensorModuleList (compositionTargetListEq d e))

theorem summandCompositionRemainder_whiskerRight
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m)
    (Ps : List (ModuleCat.{0} ℤ)) :
    tensorModuleListWhiskerRight Ps (summandCompositionRemainder d e) =
      eqToHom (congrArg tensorModuleList
          (congrArg₂ List.append (compositionSourceListEq d e)
            (rfl : Ps = Ps))) ≫
        eqToHom (congrArg tensorModuleList
          (congrArg₂ List.append (compositionBoundaryListEq d e)
            (rfl : Ps = Ps))) ≫
        tensorModuleListWhiskerRight Ps
          (adjacentMergeAfter (compositionLeftPrefix d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)).tensorMap ≫
        eqToHom (congrArg tensorModuleList
          (congrArg₂ List.append (compositionTargetListEq d e)
            (rfl : Ps = Ps))) := by
  unfold summandCompositionRemainder
  simp only [tensorModuleListWhiskerRight_comp]
  rw [tensorModuleListWhiskerRight_eqToHom Ps (compositionSourceListEq d e),
    tensorModuleListWhiskerRight_eqToHom Ps (compositionBoundaryListEq d e),
    tensorModuleListWhiskerRight_eqToHom Ps (compositionTargetListEq d e)]

theorem summandCompositionRemainder_whiskerLeft
    (Ps : List (ModuleCat.{0} ℤ))
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    tensorModuleListWhiskerLeft Ps (summandCompositionRemainder d e) =
      eqToHom (congrArg tensorModuleList
          (congrArg₂ List.append (rfl : Ps = Ps)
            (compositionSourceListEq d e))) ≫
        eqToHom (congrArg tensorModuleList
          (congrArg₂ List.append (rfl : Ps = Ps)
            (compositionBoundaryListEq d e))) ≫
        tensorModuleListWhiskerLeft Ps
          (adjacentMergeAfter (compositionLeftPrefix d)
            (ys := compositionRightSuffix e)
            (compositionBoundaryMap d e)).tensorMap ≫
        eqToHom (congrArg tensorModuleList
          (congrArg₂ List.append (rfl : Ps = Ps)
            (compositionTargetListEq d e))) := by
  unfold summandCompositionRemainder
  simp only [tensorModuleListWhiskerLeft_comp]
  rw [tensorModuleListWhiskerLeft_eqToHom Ps (compositionSourceListEq d e),
    tensorModuleListWhiskerLeft_eqToHom Ps (compositionBoundaryListEq d e),
    tensorModuleListWhiskerLeft_eqToHom Ps (compositionTargetListEq d e)]

theorem summandCompositionRemainder_assoc_of_middle_nil
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile (nil X Y) q)
    (e : DegreeProfile v r) :
    eqToHom (congrArg tensorModuleList
        (List.append_assoc (finFamilyList (factorModule a))
          (finFamilyList (factorModule d))
          (finFamilyList (factorModule e))).symm) ≫
      tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (summandCompositionRemainder a d) ≫
      summandCompositionRemainder (a.append d) e ≫
      (summandAssocIso a d e).hom =
    tensorModuleListWhiskerLeft (finFamilyList (factorModule a))
        (summandCompositionRemainder d e) ≫
      summandCompositionRemainder a (d.append e) := by
  rw [summandCompositionRemainder_whiskerRight,
    summandCompositionRemainder_whiskerLeft]
  rw [← AdjacentMergeData.suffix_tensorMap,
    ← AdjacentMergeData.prefix_tensorMap]
  apply eq_of_heq
  exact transportedPairAssembler_heq
    (zeroLeftTransportedPair_heq a d e)
    (heq_of_eq (normalizedBoundaryPairTensorMap_eq
      (compositionLeftPrefix a) (compositionRightSuffix e) a d e))
    (zeroRightTransportedPair_heq a d e)

theorem summandCompositionRemainder_assoc_of_middle_succ
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p)
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) q)
    (e : DegreeProfile v r) :
    eqToHom (congrArg tensorModuleList
        (List.append_assoc (finFamilyList (factorModule a))
          (finFamilyList (factorModule d))
          (finFamilyList (factorModule e))).symm) ≫
      tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (summandCompositionRemainder a d) ≫
      summandCompositionRemainder (a.append d) e ≫
      (summandAssocIso a d e).hom =
    tensorModuleListWhiskerLeft (finFamilyList (factorModule a))
        (summandCompositionRemainder d e) ≫
      summandCompositionRemainder a (d.append e) := by
  rw [summandCompositionRemainder_whiskerRight,
    summandCompositionRemainder_whiskerLeft]
  rw [← AdjacentMergeData.suffix_tensorMap,
    ← AdjacentMergeData.prefix_tensorMap]
  apply eq_of_heq
  exact transportedPairAssembler_heq
    (positiveLeftTransportedPair_heq a d e)
    (heq_of_eq (positiveMiddleBoundaryPairTensorMap_eq
      (compositionLeftPrefix a) (compositionRightSuffix e) a d e))
    (positiveRightTransportedPair_heq a d e)

theorem summandCompositionRemainder_assoc
    {W X Y Z : ComplexCategory} {u : DrinfeldWord W X}
    {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z} {p q r : ℤ}
    (a : DegreeProfile u p) (d : DegreeProfile w q)
    (e : DegreeProfile v r) :
    eqToHom (congrArg tensorModuleList
        (List.append_assoc (finFamilyList (factorModule a))
          (finFamilyList (factorModule d))
          (finFamilyList (factorModule e))).symm) ≫
      tensorModuleListWhiskerRight (finFamilyList (factorModule e))
        (summandCompositionRemainder a d) ≫
      summandCompositionRemainder (a.append d) e ≫
      (summandAssocIso a d e).hom =
    tensorModuleListWhiskerLeft (finFamilyList (factorModule a))
        (summandCompositionRemainder d e) ≫
      summandCompositionRemainder a (d.append e) := by
  rcases w with ⟨_ | k, intermediate⟩
  · have hi : intermediate = (nil X Y).intermediate := Subsingleton.elim _ _
    subst intermediate
    exact summandCompositionRemainder_assoc_of_middle_nil a d e
  · exact summandCompositionRemainder_assoc_of_middle_succ a d e

theorem normalizedSummandCompositionMap_eq_append_remainder
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    normalizedSummandCompositionMap d e =
      (tensorModuleListAppendIso (finFamilyList (factorModule d))
        (finFamilyList (factorModule e))).hom ≫
        summandCompositionRemainder d e := by
  rfl

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
