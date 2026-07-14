import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientComplex
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDifferentialCancellation

/-! # Composition in the corrected Drinfeld quotient -/

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

def tensorModuleListAppendIso :
    (Ms Ns : List (ModuleCat.{0} ℤ)) →
      tensorModuleList Ms ⊗ tensorModuleList Ns ≅ tensorModuleList (Ms ++ Ns)
  | [], Ns => λ_ (tensorModuleList Ns)
  | M :: Ms, Ns =>
      α_ M (tensorModuleList Ms) (tensorModuleList Ns) ≪≫
        MonoidalCategory.tensorIso (Iso.refl M) (tensorModuleListAppendIso Ms Ns)

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
      (finFamilyList (compositionMergedFactor d e)) :=
  recursiveAdjacentMergeDataOfFn (compositionSourceFactor d e)
    (compositionBoundaryIndex w v) (compositionBoundaryModule d e)
    (compositionBoundaryFactorMap d e)

def summandCompositionMap
    {X Y Z : ComplexCategory} {w : DrinfeldWord X Y} {v : DrinfeldWord Y Z}
    {n m : ℤ} (d : DegreeProfile w n) (e : DegreeProfile v m) :
    Quiver.Hom (summandModule d ⊗ summandModule e)
      (summandModule (d.append e)) :=
  (tensorModuleListAppendIso
      (finFamilyList (factorModule d)) (finFamilyList (factorModule e))).hom ≫
    eqToHom (congrArg tensorModuleList
      (finFamilyList_compositionSourceFactor d e).symm) ≫
    (compositionMergeData d e).tensorMap ≫
    eqToHom (congrArg tensorModuleList
      (congrArg finFamilyList (compositionMergedFactor_eq_target d e))) ≫
    eqToHom (congrArg tensorModuleList
      (finFamilyList_compositionTargetFactor d e))

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

def quotientIdentityElement (K : ComplexCategory) : quotientGradedModule K K 0 :=
  (originalHomInclusion K K 0).hom (ULift.up (identityCochain K))

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
