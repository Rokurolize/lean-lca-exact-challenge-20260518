/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientLocalizationComparison
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDGCategory

/-! # Linear evaluation of corrected Drinfeld words

A DG-enriched functor out of the coefficient-changed original category, together with a chosen
contracting element on every corrected acyclic object, evaluates each homogeneous Drinfeld word
in the target DG-enriched category. This module contains only the linear word-evaluation core;
cochain-map compatibility and the extension universal property are proved separately.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

/-- The degree-zero element selected by the enriched identity of a DG-enriched target. -/
def targetDGIdentityElement
    {D : Type*} [EnrichedCategory QuotientDGCochain D] (X : D) :
    (X ⟶[QuotientDGCochain] X).X 0 :=
  (eId QuotientDGCochain X).f 0
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)

/-- An original DG functor together with contracting elements for all corrected acyclic objects. -/
structure AnnihilatingEnrichedFunctorData
    (D : Type*) [EnrichedCategory QuotientDGCochain D] where
  functor : EnrichedFunctor QuotientDGCochain OriginalCoefficientDGCategory D
  contraction : ∀ A : CorrectedAcyclicComplexCategory,
    (functor.obj (Opposite.op A.obj) ⟶[QuotientDGCochain]
      functor.obj (Opposite.op A.obj)).X (-1)
  contraction_d : ∀ A : CorrectedAcyclicComplexCategory,
    ((functor.obj (Opposite.op A.obj) ⟶[QuotientDGCochain]
      functor.obj (Opposite.op A.obj)).d (-1) 0) (contraction A) =
        targetDGIdentityElement (functor.obj (Opposite.op A.obj))

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

/-- Target object corresponding to an actual bounded complex. -/
abbrev obj (X : ComplexCategory) : D := E.functor.obj (Opposite.op X)

/-- Target Hom corresponding to an actual arrow direction `X ⟶ Y`. -/
abbrev hom (X Y : ComplexCategory) : QuotientDGCochain :=
  E.obj Y ⟶[QuotientDGCochain] E.obj X

/-- Differential of one homogeneous tensor summand in the target coefficient category. -/
theorem tensorInclusion_comp_d
    (A B : QuotientDGCochain) (q p : ℤ) :
    HomologicalComplex.ιTensorObj A B q p (q + p) rfl ≫
        (A ⊗ B).d (q + p) ((q + p) + 1) =
      ((A.d q (q + 1) ⊗ₘ 𝟙 (B.X p)) ≫
        HomologicalComplex.ιTensorObj A B (q + 1) p ((q + p) + 1) (by omega)) +
      q.negOnePow •
        ((𝟙 (A.X q) ⊗ₘ B.d p (p + 1)) ≫
          HomologicalComplex.ιTensorObj A B q (p + 1) ((q + p) + 1) (by omega)) := by
  change HomologicalComplex.ιTensorObj A B q p (q + p) rfl ≫
      (HomologicalComplex.tensorObj A B).d (q + p) ((q + p) + 1) = _
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
    (show (ComplexShape.up ℤ).Rel q (q + 1) by rfl)
    p ((q + p) + 1) (by change (q + 1) + p = (q + p) + 1; omega)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q
    (show (ComplexShape.up ℤ).Rel p (p + 1) by rfl)
    ((q + p) + 1) (by change q + (p + 1) = (q + p) + 1; omega)]
  have hε₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (q, p) = 1 := rfl
  have hε₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (q, p) = q.negOnePow := rfl
  simp only [hε₁, hε₂, one_smul]
  rfl

/-- Compose homogeneous target elements in actual bounded-complex arrow order. -/
def composeElement
    (X Y Z : ComplexCategory) (p q n : ℤ) (h : q + p = n)
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    (E.hom X Z).X n :=
  ((HomologicalComplex.ιTensorObj (E.hom Y Z) (E.hom X Y) q p n h ≫
      (eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)).f n).hom)
    (y ⊗ₜ[QuotientCoefficientRing] x)

/-- The target enriched composition satisfies the homogeneous cochain Leibniz rule. -/
theorem composeElement_d
    (X Y Z : ComplexCategory) (p q : ℤ)
    (x : (E.hom X Y).X p) (y : (E.hom Y Z).X q) :
    ((E.hom X Z).d (q + p) ((q + p) + 1))
        (E.composeElement X Y Z p q (q + p) rfl x y) =
      E.composeElement X Y Z p (q + 1) ((q + p) + 1) (by omega)
        x (((E.hom Y Z).d q (q + 1)) y) +
      q.negOnePow •
        E.composeElement X Y Z (p + 1) q ((q + p) + 1) (by omega)
          (((E.hom X Y).d p (p + 1)) x) y := by
  let A := E.hom Y Z
  let B := E.hom X Y
  let C := E.hom X Z
  let μ := eComp QuotientDGCochain (E.obj Z) (E.obj Y) (E.obj X)
  let ι := HomologicalComplex.ιTensorObj A B q p (q + p) rfl
  have hcomm := ConcreteCategory.congr_hom (μ.comm (q + p) ((q + p) + 1))
    (ι.hom (y ⊗ₜ[QuotientCoefficientRing] x))
  have htensor := ConcreteCategory.congr_hom (tensorInclusion_comp_d A B q p)
    (y ⊗ₜ[QuotientCoefficientRing] x)
  simp only [ModuleCat.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.hom_smul, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at htensor hcomm
  change (C.d (q + p) ((q + p) + 1)).hom
      ((μ.f (q + p)).hom (ι.hom (y ⊗ₜ[QuotientCoefficientRing] x))) = _
  calc
    _ = (μ.f ((q + p) + 1)).hom
        (((A ⊗ B).d (q + p) ((q + p) + 1)).hom
          (ι.hom (y ⊗ₜ[QuotientCoefficientRing] x))) := hcomm
    _ = (μ.f ((q + p) + 1)).hom
        ((HomologicalComplex.ιTensorObj A B (q + 1) p ((q + p) + 1) (by omega)).hom
            (((A.d q (q + 1)).hom y) ⊗ₜ[QuotientCoefficientRing] x) +
          q.negOnePow •
            (HomologicalComplex.ιTensorObj A B q (p + 1) ((q + p) + 1) (by omega)).hom
              (y ⊗ₜ[QuotientCoefficientRing] ((B.d p (p + 1)).hom x))) :=
      congrArg (fun z ↦ (μ.f ((q + p) + 1)).hom z) htensor
    _ = _ := by
      simp only [map_add, Units.smul_def, map_zsmul]
      rfl

/-- Composition is integer-linear in the later actual arrow. -/
def composeSecondMap
    (X Y Z : ComplexCategory) (p q n : ℤ) (h : q + p = n)
    (x : (E.hom X Y).X p) :
    (E.hom Y Z).X q →ₗ[ℤ] (E.hom X Z).X n :=
  ({ toFun := fun y ↦ E.composeElement X Y Z p q n h x y
     map_zero' := by
       unfold composeElement
       simp
     map_add' := by
       intro y₁ y₂
       unfold composeElement
       simp [TensorProduct.add_tmul] } :
    (E.hom Y Z).X q →+ (E.hom X Z).X n).toIntLinearMap

/-- Composition is integer-linear in the earlier actual arrow. -/
def composeFirstMap
    (X Y Z : ComplexCategory) (p q n : ℤ) (h : q + p = n)
    (y : (E.hom Y Z).X q) :
    (E.hom X Y).X p →ₗ[ℤ] (E.hom X Z).X n :=
  ({ toFun := fun x ↦ E.composeElement X Y Z p q n h x y
     map_zero' := by
       unfold composeElement
       simp
     map_add' := by
       intro x₁ x₂
       unfold composeElement
       simp [TensorProduct.tmul_add] } :
    (E.hom X Y).X p →+ (E.hom X Z).X n).toIntLinearMap

/-- The image of one ordinary Hom-cochain factor, viewed as an integer-linear map. -/
def factorMap
    (X Y : ComplexCategory) (p : ℤ) :
    (dgHomZModuleCochainComplex X Y).X p →ₗ[ℤ] (E.hom X Y).X p where
  toFun x :=
    (E.functor.map (Opposite.op Y) (Opposite.op X)).f p
      (ULift.up (ULift.up x))
  map_add' x y := by
    change (E.functor.map (Opposite.op Y) (Opposite.op X)).f p
        (ULift.up (ULift.up x) + ULift.up (ULift.up y)) =
      (E.functor.map (Opposite.op Y) (Opposite.op X)).f p
          (ULift.up (ULift.up x)) +
        (E.functor.map (Opposite.op Y) (Opposite.op X)).f p
          (ULift.up (ULift.up y))
    exact map_add _ _ _
  map_smul' r x := by
    change (E.functor.map (Opposite.op Y) (Opposite.op X)).f p
        (r • ULift.up (ULift.up x)) =
      r • (E.functor.map (Opposite.op Y) (Opposite.op X)).f p
        (ULift.up (ULift.up x))
    exact ((E.functor.map (Opposite.op Y) (Opposite.op X)).f p).hom.toAddMonoidHom.map_zsmul
      r (ULift.up (ULift.up x))

/-- The degree carried by the tail of a positive-length word. -/
def tailDegree
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) : ℤ :=
  n - d.arrowDegree 0 + 1

/-- The list of tail factors agrees with the successor-indexed original factor list. -/
theorem finFamilyList_factorModule_tail
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    finFamilyList (fun i : Fin (k + 1) ↦ factorModule d i.succ) =
      finFamilyList (factorModule (tailDegreeProfile d)) := by
  exact congrArg finFamilyList (funext fun i ↦ (tailFactorModule d i).symm)

/-- A positive-length word summand is its first factor tensored with its tail summand. -/
theorem summandModule_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    summandModule d = factorModule d 0 ⊗ summandModule (tailDegreeProfile d) := by
  change factorModule d 0 ⊗
      tensorModuleList (finFamilyList (fun i : Fin (k + 1) ↦ factorModule d i.succ)) =
    factorModule d 0 ⊗ tensorModuleList (finFamilyList (factorModule (tailDegreeProfile d)))
  rw [finFamilyList_factorModule_tail d]

/-- The first factor of a positive word has the expected endpoint objects. -/
theorem factorModule_zero_succ
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 =
      (dgHomZModuleCochainComplex X (intermediate 0).obj).X (d.arrowDegree 0) := by
  unfold factorModule arrowSource arrowTarget vertex object
  change (dgHomZModuleCochainComplex X
      (Fin.lastCases Y (fun i : Fin (k + 1) ↦ (intermediate i).obj) 0)).X
        (d.arrowDegree 0) = _
  have hzero : (0 : Fin (k + 2)) = (0 : Fin (k + 1)).castSucc := rfl
  rw [hzero, Fin.lastCases_castSucc]

/-- The tail degree plus the contracted first-factor degree is the total word degree. -/
theorem tailDegree_add_head_sub_one
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tailDegree d + (d.arrowDegree 0 - 1) = n := by
  unfold tailDegree
  omega

/-- Map the first ordinary factor into the target enrichment. -/
def firstFactorMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 →ₗ[ℤ]
      (E.hom X (intermediate 0).obj).X (d.arrowDegree 0) :=
  (E.factorMap X (intermediate 0).obj (d.arrowDegree 0)).comp
    (eqToHom (factorModule_zero_succ d)).hom

/-- Compose the first ordinary factor with the chosen contraction. -/
def firstContractionMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 →ₗ[ℤ]
      (E.hom X (intermediate 0).obj).X (d.arrowDegree 0 - 1) :=
  (E.composeFirstMap X (intermediate 0).obj (intermediate 0).obj
      (d.arrowDegree 0) (-1) (d.arrowDegree 0 - 1) (by omega)
      (E.contraction (intermediate 0))).comp
    (E.firstFactorMap d)

/-- Bilinear evaluation of a positive word from its first factor and evaluated tail. -/
def evaluateSuccBilinear
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (tailEval : summandModule (tailDegreeProfile d) →ₗ[ℤ]
      (E.hom (intermediate 0).obj Y).X (tailDegree d)) :
    factorModule d 0 →ₗ[ℤ]
      summandModule (tailDegreeProfile d) →ₗ[ℤ] (E.hom X Y).X n := by
  let hdeg := tailDegree_add_head_sub_one d
  refine LinearMap.mk₂ ℤ
    (fun x t ↦ E.composeElement X (intermediate 0).obj Y
      (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
      (E.firstContractionMap d x) (tailEval t)) ?_ ?_ ?_ ?_
  · intro x₁ x₂ t
    calc
      E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (E.firstContractionMap d (x₁ + x₂)) (tailEval t) =
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (E.firstContractionMap d x₁ + E.firstContractionMap d x₂) (tailEval t) := by
            rw [map_add]
      _ = _ := (E.composeFirstMap X (intermediate 0).obj Y
        (d.arrowDegree 0 - 1) (tailDegree d) n hdeg (tailEval t)).map_add _ _
  · intro r x t
    calc
      E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (E.firstContractionMap d (r • x)) (tailEval t) =
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (r • E.firstContractionMap d x) (tailEval t) := by
            rw [map_smul]
      _ = _ := (E.composeFirstMap X (intermediate 0).obj Y
        (d.arrowDegree 0 - 1) (tailDegree d) n hdeg (tailEval t)).map_smul r _
  · intro x t₁ t₂
    calc
      E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (E.firstContractionMap d x) (tailEval (t₁ + t₂)) =
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (E.firstContractionMap d x) (tailEval t₁ + tailEval t₂) := by
            rw [map_add]
      _ = _ := (E.composeSecondMap X (intermediate 0).obj Y
        (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
        (E.firstContractionMap d x)).map_add _ _
  · intro r x t
    calc
      E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (E.firstContractionMap d x) (tailEval (r • t)) =
        E.composeElement X (intermediate 0).obj Y
          (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
          (E.firstContractionMap d x) (r • tailEval t) := by
            rw [map_smul]
      _ = _ := (E.composeSecondMap X (intermediate 0).obj Y
        (d.arrowDegree 0 - 1) (tailDegree d) n hdeg
        (E.firstContractionMap d x)).map_smul r _

/-- Evaluate a positive word after recursively evaluating its tail. -/
def evaluateSucc
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (tailEval : summandModule (tailDegreeProfile d) →ₗ[ℤ]
      (E.hom (intermediate 0).obj Y).X (tailDegree d)) :
    summandModule d →ₗ[ℤ] (E.hom X Y).X n :=
  (TensorProduct.lift (E.evaluateSuccBilinear d tailEval)).comp
    (eqToHom (summandModule_succ d)).hom

/-- A length-zero word with any compatible profile evaluates by the original enriched functor. -/
def evaluateNilProfile
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    summandModule d →ₗ[ℤ] (E.hom X Y).X n :=
  (E.factorMap X Y n).comp (nilSummandIsoOriginal X Y d).hom.hom

/-- Length-zero words with the canonical profile evaluate by the original enriched functor. -/
def evaluateNil
    (X Y : ComplexCategory) (n : ℤ) :
    summandModule (nilDegreeProfile X Y n) →ₗ[ℤ] (E.hom X Y).X n :=
  E.evaluateNilProfile X Y (nilDegreeProfile X Y n)

/-- Every degree profile on the zero-length word is the canonical profile. -/
theorem degreeProfile_nil_eq
    {X Y : ComplexCategory} {n : ℤ}
    (d : DegreeProfile (nil X Y) n) : d = nilDegreeProfile X Y n := by
  apply DegreeProfile.ext
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  change d.arrowDegree 0 = n
  have hd := d.totalDegree
  simpa [nil] using hd

/-- Evaluate words of a specified length by structural recursion on that length. -/
noncomputable def evaluateWordOfLength
    {X Y : ComplexCategory} :
    (k : ℕ) →
    (intermediate : Fin k → CorrectedAcyclicComplexCategory) →
    {n : ℤ} →
    (d : DegreeProfile
      ({ length := k, intermediate := intermediate } : DrinfeldWord X Y) n) →
    summandModule d →ₗ[ℤ] (E.hom X Y).X n
  | 0, intermediate, n, d => by
      let w : DrinfeldWord X Y := { length := 0, intermediate := intermediate }
      have hw : w = nil X Y := eq_nil_of_length_eq_zero w rfl
      let d0 := d.castWord hw
      exact (E.evaluateNilProfile X Y d0).comp (summandModuleCastWordIso hw d).hom.hom
  | k + 1, intermediate, n, d =>
      E.evaluateSucc d
        (evaluateWordOfLength k
          (fun i ↦ intermediate i.succ) (tailDegreeProfile d))

/-- Evaluate an arbitrary homogeneous corrected Drinfeld word. -/
noncomputable def evaluateWord
    {X Y : ComplexCategory} {n : ℤ}
    (w : DrinfeldWord X Y) (d : DegreeProfile w n) :
    summandModule d →ₗ[ℤ] (E.hom X Y).X n := by
  cases w with
  | mk k intermediate =>
      exact evaluateWordOfLength (E := E) k intermediate d

end AnnihilatingEnrichedFunctorData

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
