/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedCoefficientUniqueness
import Mathlib.CategoryTheory.Enriched.Basic

/-! # Unit-graded transformations for the corrected Drinfeld quotient

The ambient cochain category is monoidal but is not currently bundled as braided.  The tensor
unit nevertheless has its canonical half-braiding, so it is an object of the Drinfeld center.
Transformations graded by this center object are the strict enriched natural transformations
needed by the quotient universal property.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped MonoidalCategory

/-- The canonical central tensor unit of the quotient cochain category. -/
noncomputable abbrev QuotientDGCentralUnit : Center QuotientDGCochain :=
  𝟙_ (Center QuotientDGCochain)

/-- A strict unit-graded enriched natural transformation. -/
abbrev QuotientDGUnitGradedNatTrans
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    (F G : EnrichedFunctor QuotientDGCochain C D) :=
  GradedNatTrans QuotientDGCentralUnit F G

/-- The degree-zero element represented by one component of a unit-graded transformation. -/
def quotientDGUnitGradedNatTransElement
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G) (X : C) :
    (F.obj X ⟶[QuotientDGCochain] G.obj X).X 0 :=
  (α.app X).f 0
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)

/-- Homogeneous enriched composition in an arbitrary quotient-DG-enriched target. -/
def quotientDGComposeElement
    {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (X Y Z : D) (p q n : ℤ) (h : p + q = n)
    (x : (X ⟶[QuotientDGCochain] Y).X p)
    (y : (Y ⟶[QuotientDGCochain] Z).X q) :
    (X ⟶[QuotientDGCochain] Z).X n :=
  ((HomologicalComplex.ιTensorObj
      (X ⟶[QuotientDGCochain] Y)
      (Y ⟶[QuotientDGCochain] Z) p q n h ≫
    (eComp QuotientDGCochain X Y Z).f n).hom)
    (x ⊗ₜ[QuotientCoefficientRing] y)

@[reassoc]
theorem quotientDGTensorInclusion_comp_tensorHom
    {K₁ K₂ L₁ L₂ : QuotientDGCochain}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    {p q n : ℤ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫
        HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

/-- The enriched identity is a left unit for homogeneous target composition. -/
theorem quotientDGComposeElement_identity_left
    {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (X Y : D) (p : ℤ)
    (x : (X ⟶[QuotientDGCochain] Y).X p) :
    quotientDGComposeElement X X Y 0 p p (by omega)
      (targetDGIdentityElement X) x = x := by
  let B := X ⟶[QuotientDGCochain] Y
  let μ := eComp QuotientDGCochain X X Y
  let η := eId QuotientDGCochain X
  let idB : B ⟶ B := 𝟙 B
  have hunit := congrArg (fun f : B ⟶ B ↦ f.f p)
    (e_id_comp QuotientDGCochain X Y)
  have happ := ConcreteCategory.congr_hom hunit x
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at happ
  change (((HomologicalComplex.leftUnitor' B).inv p ≫ _) ≫ _) x = x at happ
  rw [HomologicalComplex.leftUnitor'_inv] at happ
  have hwhisker :
      (η ▷ B).f p = (HomologicalComplex.tensorHom η idB).f p := rfl
  rw [hwhisker] at happ
  simp only [Category.assoc, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply] at happ
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  have hι := GradedObject.Monoidal.ι_tensorHom η.f idB.f
    0 p p (by omega)
  have hιapp := ConcreteCategory.congr_hom hι
    (e.inv.hom (1 : QuotientCoefficientRing) ⊗ₜ[QuotientCoefficientRing] x)
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hιapp
  have hμ := congrArg (fun z ↦ μ.f p z) hιapp
  have hright := hμ.symm.trans happ
  change quotientDGComposeElement X X Y 0 p p (by omega)
      (targetDGIdentityElement X) x = x at hright
  exact hright

/-- The enriched identity is a right unit for homogeneous target composition. -/
theorem quotientDGComposeElement_identity_right
    {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (X Y : D) (p : ℤ)
    (x : (X ⟶[QuotientDGCochain] Y).X p) :
    quotientDGComposeElement X Y Y p 0 p (by omega)
      x (targetDGIdentityElement Y) = x := by
  let B := X ⟶[QuotientDGCochain] Y
  let μ := eComp QuotientDGCochain X Y Y
  let η := eId QuotientDGCochain Y
  let idB : B ⟶ B := 𝟙 B
  have hunit := congrArg (fun f : B ⟶ B ↦ f.f p)
    (e_comp_id QuotientDGCochain X Y)
  have happ := ConcreteCategory.congr_hom hunit x
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at happ
  change (((HomologicalComplex.rightUnitor' B).inv p ≫ _) ≫ _) x = x at happ
  rw [HomologicalComplex.rightUnitor'_inv] at happ
  have hwhisker :
      (B ◁ η).f p = (HomologicalComplex.tensorHom idB η).f p := rfl
  rw [hwhisker] at happ
  simp only [Category.assoc, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply] at happ
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  have hι := GradedObject.Monoidal.ι_tensorHom idB.f η.f
    p 0 p (by omega)
  have hιapp := ConcreteCategory.congr_hom hι
    (x ⊗ₜ[QuotientCoefficientRing]
      e.inv.hom (1 : QuotientCoefficientRing))
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hιapp
  have hμ := congrArg (fun z ↦ μ.f p z) hιapp
  have hright := hμ.symm.trans happ
  change quotientDGComposeElement X Y Y p 0 p (by omega)
      x (targetDGIdentityElement Y) = x at hright
  exact hright

/-- Homogeneous enriched target composition is associative. -/
theorem quotientDGComposeElement_assoc
    {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (X Y Z W : D) (p q r : ℤ)
    (x : (X ⟶[QuotientDGCochain] Y).X p)
    (y : (Y ⟶[QuotientDGCochain] Z).X q)
    (z : (Z ⟶[QuotientDGCochain] W).X r) :
    quotientDGComposeElement X Z W (p + q) r (p + q + r) rfl
        (quotientDGComposeElement X Y Z p q (p + q) rfl x y) z =
      quotientDGComposeElement X Y W p (q + r) (p + q + r) (by omega) x
        (quotientDGComposeElement Y Z W q r (q + r) rfl y z) := by
  let A := X ⟶[QuotientDGCochain] Y
  let B := Y ⟶[QuotientDGCochain] Z
  let C := Z ⟶[QuotientDGCochain] W
  let AB := X ⟶[QuotientDGCochain] Z
  let BC := Y ⟶[QuotientDGCochain] W
  let T := X ⟶[QuotientDGCochain] W
  let μAB := eComp QuotientDGCochain X Y Z
  let μBC := eComp QuotientDGCochain Y Z W
  let μL := eComp QuotientDGCochain X Z W
  let μR := eComp QuotientDGCochain X Y W
  let total := p + q + r
  have hassoc := congrArg (fun f : A ⊗ B ⊗ C ⟶ T ↦ f.f total)
    (e_assoc QuotientDGCochain X Y Z W)
  have hpre := congrArg
    (fun f ↦ GradedObject.Monoidal.ιTensorObj₃ A.X B.X C.X
      p q r total (by omega) ≫ f) hassoc
  simp only [HomologicalComplex.comp_f] at hpre
  have hassociator :
      (α_ A B C).inv.f total =
        (GradedObject.Monoidal.associator A.X B.X C.X).inv total := rfl
  rw [hassociator,
    GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc] at hpre
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq A.X B.X C.X
      p q r total (by omega) (p + q) rfl,
    GradedObject.Monoidal.ιTensorObj₃_eq A.X B.X C.X
      p q r total (by omega) (q + r) rfl] at hpre
  have hwr : (μAB ▷ C).f total =
      (HomologicalComplex.tensorHom μAB (𝟙 C)).f total := rfl
  have hwl : (A ◁ μBC).f total =
      (HomologicalComplex.tensorHom (𝟙 A) μBC).f total := rfl
  rw [hwr, hwl] at hpre
  have houterL :
      GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj A.X B.X) C.X
            (p + q) r total (by omega) ≫
          (HomologicalComplex.tensorHom μAB (𝟙 C)).f total =
        (μAB.f (p + q) ⊗ₘ 𝟙 (C.X r)) ≫
          GradedObject.Monoidal.ιTensorObj AB.X C.X
            (p + q) r total (by omega) := by
    change HomologicalComplex.ιTensorObj (A ⊗ B) C
        (p + q) r total (by omega) ≫
      (HomologicalComplex.tensorHom μAB (𝟙 C)).f total = _
    exact quotientDGTensorInclusion_comp_tensorHom μAB (𝟙 C)
      (show (p + q) + r = total by omega)
  have houterR :
      GradedObject.Monoidal.ιTensorObj A.X
            (GradedObject.Monoidal.tensorObj B.X C.X)
            p (q + r) total (by omega) ≫
          (HomologicalComplex.tensorHom (𝟙 A) μBC).f total =
        (𝟙 (A.X p) ⊗ₘ μBC.f (q + r)) ≫
          GradedObject.Monoidal.ιTensorObj A.X BC.X
            p (q + r) total (by omega) := by
    change HomologicalComplex.ιTensorObj A (B ⊗ C)
        p (q + r) total (by omega) ≫
      (HomologicalComplex.tensorHom (𝟙 A) μBC).f total = _
    exact quotientDGTensorInclusion_comp_tensorHom (𝟙 A) μBC
      (show p + (q + r) = total by omega)
  simp only [Category.assoc] at hpre
  have hleftRaw := congrArg
    (fun t ↦
      (α_ (A.X p) (B.X q) (C.X r)).inv ≫
        (GradedObject.Monoidal.ιTensorObj A.X B.X
          p q (p + q) rfl ▷ C.X r) ≫
        t ≫ μL.f total)
    houterL
  have hrightRaw := congrArg
    (fun t ↦
      (A.X p ◁ GradedObject.Monoidal.ιTensorObj B.X C.X
        q r (q + r) rfl) ≫
        t ≫ μR.f total)
    houterR
  simp only [Category.assoc] at hleftRaw hrightRaw
  have hnorm := hleftRaw.symm.trans (hpre.trans hrightRaw)
  let v : ↑(A.X p ⊗ B.X q ⊗ C.X r) :=
    x ⊗ₜ[QuotientCoefficientRing]
      (y ⊗ₜ[QuotientCoefficientRing] z)
  have happ := ConcreteCategory.congr_hom hnorm v
  dsimp only [v] at happ
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.associator_inv_apply] at happ
  rw [ModuleCat.MonoidalCategory.whiskerRight_apply] at happ
  have hleft :
      quotientDGComposeElement X Z W (p + q) r total rfl
          (quotientDGComposeElement X Y Z p q (p + q) rfl x y) z =
        (ConcreteCategory.hom (μL.f total))
          ((ConcreteCategory.hom (GradedObject.Monoidal.ιTensorObj AB.X C.X
            (p + q) r total (by omega)))
            ((ConcreteCategory.hom (μAB.f (p + q) ⊗ₘ 𝟙 (C.X r)))
              ((ConcreteCategory.hom (GradedObject.Monoidal.ιTensorObj A.X B.X
                p q (p + q) rfl)) (x ⊗ₜ[QuotientCoefficientRing] y)
                ⊗ₜ[QuotientCoefficientRing] z))) := by
    unfold quotientDGComposeElement
    rw [ModuleCat.MonoidalCategory.tensorHom_tmul]
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply]
    dsimp [μL, μAB, AB, A, B, C, total]
    rfl
  have hright :
      (ConcreteCategory.hom (μR.f total))
          ((ConcreteCategory.hom (GradedObject.Monoidal.ιTensorObj A.X BC.X
            p (q + r) total (by omega)))
            ((ConcreteCategory.hom (𝟙 (A.X p) ⊗ₘ μBC.f (q + r)))
              ((ConcreteCategory.hom (A.X p ◁
                GradedObject.Monoidal.ιTensorObj B.X C.X q r (q + r) rfl))
                (x ⊗ₜ[QuotientCoefficientRing]
                  (y ⊗ₜ[QuotientCoefficientRing] z))))) =
        quotientDGComposeElement X Y W p (q + r) total (by omega) x
          (quotientDGComposeElement Y Z W q r (q + r) rfl y z) := by
    unfold quotientDGComposeElement
    rw [ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul]
    simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply]
    dsimp [μR, μBC, BC, A, B, C, total]
    rfl
  exact hleft.trans (happ.trans hright)

/-- Homogeneous enriched composition remains associative after replacing the displayed
degree sums by propositionally equal indices. -/
theorem quotientDGComposeElement_assoc_of_degree_eq
    {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (X Y Z W : D) {p q r s t n : ℤ}
    (hpq : p + q = s) (hsr : s + r = n)
    (hqr : q + r = t) (hpt : p + t = n)
    (x : (X ⟶[QuotientDGCochain] Y).X p)
    (y : (Y ⟶[QuotientDGCochain] Z).X q)
    (z : (Z ⟶[QuotientDGCochain] W).X r) :
    quotientDGComposeElement X Z W s r n hsr
        (quotientDGComposeElement X Y Z p q s hpq x y) z =
      quotientDGComposeElement X Y W p t n hpt x
        (quotientDGComposeElement Y Z W q r t hqr y z) := by
  subst s
  subst t
  have hn : n = p + q + r := by omega
  subst n
  exact quotientDGComposeElement_assoc X Y Z W p q r x y z

/-- Move a source Hom map through the canonical tensor-unit half-braiding before applying
the left factor of enriched composition. -/
theorem quotientDGCentralNaturalityLeft
    {A B P Q R : QuotientDGCochain}
    (j : A ⟶ B) (f : B ⟶ P)
    (a : 𝟙_ QuotientDGCochain ⟶ Q)
    (μ : P ⊗ Q ⟶ R) :
    ((λ_ A).hom ≫ (ρ_ A).inv) ≫ ((j ≫ f) ⊗ₘ a) ≫ μ =
      (𝟙_ QuotientDGCochain ◁ j) ≫
        ((λ_ B).hom ≫ (ρ_ B).inv) ≫ (f ⊗ₘ a) ≫ μ := by
  have hj := HalfBraiding.naturality
    (𝟙_ (Center QuotientDGCochain)).2 j
  change (𝟙_ QuotientDGCochain ◁ j) ≫
      ((λ_ B).hom ≫ (ρ_ B).inv) =
    ((λ_ A).hom ≫ (ρ_ A).inv) ≫
      (j ▷ 𝟙_ QuotientDGCochain) at hj
  have hj' := congrArg
    (fun z ↦ z ≫ (f ▷ 𝟙_ QuotientDGCochain) ≫ (P ◁ a) ≫ μ) hj.symm
  calc
    _ = (((λ_ A).hom ≫ (ρ_ A).inv) ≫
        (j ▷ 𝟙_ QuotientDGCochain)) ≫
        (f ▷ 𝟙_ QuotientDGCochain) ≫ (P ◁ a) ≫ μ := by
      simp only [MonoidalCategory.tensorHom_def, Category.assoc,
        MonoidalCategory.comp_whiskerRight]
    _ = ((𝟙_ QuotientDGCochain ◁ j) ≫
        ((λ_ B).hom ≫ (ρ_ B).inv)) ≫
        (f ▷ 𝟙_ QuotientDGCochain) ≫ (P ◁ a) ≫ μ := by
      simpa only [Category.assoc] using hj'
    _ = _ := by
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]

/-- Move a source Hom map through a tensor-unit component before applying the right factor
of enriched composition. -/
theorem quotientDGCentralNaturalityRight
    {A B P Q R : QuotientDGCochain}
    (a : 𝟙_ QuotientDGCochain ⟶ P)
    (j : A ⟶ B) (g : B ⟶ Q)
    (μ : P ⊗ Q ⟶ R) :
    (𝟙_ QuotientDGCochain ◁ j) ≫ (a ⊗ₘ g) ≫ μ =
      (a ⊗ₘ (j ≫ g)) ≫ μ := by
  have hwe := MonoidalCategory.whisker_exchange a j
  have hwe' := congrArg (fun z ↦ z ≫ (P ◁ g) ≫ μ) hwe
  simp only [MonoidalCategory.tensorHom_def, Category.assoc,
    MonoidalCategory.whiskerLeft_comp]
  simpa only [Category.assoc] using hwe'

/-- Precompose a unit-graded enriched transformation by an enriched functor. -/
noncomputable def quotientDGUnitGradedNatTransPrecomp
    {C B D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain B]
    [EnrichedCategory QuotientDGCochain D]
    (J : EnrichedFunctor QuotientDGCochain C B)
    {F G : EnrichedFunctor QuotientDGCochain B D}
    (α : QuotientDGUnitGradedNatTrans F G) :
    QuotientDGUnitGradedNatTrans
      (EnrichedFunctor.comp QuotientDGCochain J F)
      (EnrichedFunctor.comp QuotientDGCochain J G) where
  app X := α.app (J.obj X)
  naturality X Y := by
    let I := 𝟙_ QuotientDGCochain
    let A := X ⟶[QuotientDGCochain] Y
    let B' := J.obj X ⟶[QuotientDGCochain] J.obj Y
    let j := J.map X Y
    let pre : I ⊗ A ⟶ I ⊗ B' := 𝟙 I ⊗ₘ j
    have hα := α.naturality (J.obj X) (J.obj Y)
    rw [Center.tensorUnit_β] at hα ⊢
    simp only [Iso.trans_hom, Iso.symm_hom,
      EnrichedFunctor.comp_map] at hα ⊢
    have hpre := congrArg (fun z ↦ pre ≫ z) hα
    change ((λ_ A).hom ≫ (ρ_ A).inv) ≫
        ((j ≫ F.map (J.obj X) (J.obj Y)) ⊗ₘ α.app (J.obj Y)) ≫
        eComp QuotientDGCochain (F.obj (J.obj X))
          (F.obj (J.obj Y)) (G.obj (J.obj Y)) =
      (α.app (J.obj X) ⊗ₘ
        (j ≫ G.map (J.obj X) (J.obj Y))) ≫
        eComp QuotientDGCochain (F.obj (J.obj X))
          (G.obj (J.obj X)) (G.obj (J.obj Y))
    calc
      _ = pre ≫ ((λ_ B').hom ≫ (ρ_ B').inv) ≫
          (F.map (J.obj X) (J.obj Y) ⊗ₘ α.app (J.obj Y)) ≫
          eComp QuotientDGCochain (F.obj (J.obj X))
            (F.obj (J.obj Y)) (G.obj (J.obj Y)) := by
        exact quotientDGCentralNaturalityLeft j
          (F.map (J.obj X) (J.obj Y)) (α.app (J.obj Y))
          (eComp QuotientDGCochain (F.obj (J.obj X))
            (F.obj (J.obj Y)) (G.obj (J.obj Y)))
      _ = pre ≫
          (α.app (J.obj X) ⊗ₘ G.map (J.obj X) (J.obj Y)) ≫
          eComp QuotientDGCochain (F.obj (J.obj X))
            (G.obj (J.obj X)) (G.obj (J.obj Y)) := hpre
      _ = _ := by
        exact quotientDGCentralNaturalityRight (α.app (J.obj X)) j
          (G.map (J.obj X) (J.obj Y))
          (eComp QuotientDGCochain (F.obj (J.obj X))
            (G.obj (J.obj X)) (G.obj (J.obj Y)))

/-- The identity unit-graded enriched natural transformation. -/
noncomputable def quotientDGUnitGradedNatTransId
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    (F : EnrichedFunctor QuotientDGCochain C D) :
    QuotientDGUnitGradedNatTrans F F where
  app X := eId QuotientDGCochain (F.obj X)
  naturality X Y := by
    change ((𝟙_ (Center QuotientDGCochain)).2.β
        (X ⟶[QuotientDGCochain] Y)).hom ≫
        (F.map X Y ⊗ₘ eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain _ _ _ =
      (eId QuotientDGCochain (F.obj X) ⊗ₘ F.map X Y) ≫
        eComp QuotientDGCochain _ _ _
    rw [Center.tensorUnit_β]
    simp only [Iso.trans_hom, Iso.symm_hom]
    change ((λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫
        (ρ_ (X ⟶[QuotientDGCochain] Y)).inv) ≫
        (F.map X Y ⊗ₘ eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain _ _ _ =
      (eId QuotientDGCochain (F.obj X) ⊗ₘ F.map X Y) ≫
        eComp QuotientDGCochain _ _ _
    have hid :
        (eId QuotientDGCochain (F.obj X) ▷
            (F.obj X ⟶[QuotientDGCochain] F.obj Y)) ≫
            eComp QuotientDGCochain (F.obj X) (F.obj X) (F.obj Y) =
          (λ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).hom := by
      rw [← cancel_epi (λ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv]
      simp only [e_id_comp, Iso.inv_hom_id]
    have hcomp :
        (ρ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y) =
        𝟙 (F.obj X ⟶[QuotientDGCochain] F.obj Y) :=
      e_comp_id QuotientDGCochain (F.obj X) (F.obj Y)
    calc
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫
          (ρ_ (X ⟶[QuotientDGCochain] Y)).inv ≫
          (F.map X Y ▷ 𝟙_ QuotientDGCochain) ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y) := by
            rw [MonoidalCategory.tensorHom_def]
            simp only [Category.assoc]
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫ F.map X Y ≫
          (ρ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y) := by
            rw [← MonoidalCategory.rightUnitor_inv_naturality_assoc]
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫ F.map X Y ≫
          ((ρ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).inv ≫
          ((F.obj X ⟶[QuotientDGCochain] F.obj Y) ◁
            eId QuotientDGCochain (F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (F.obj Y)) := by
            rfl
      _ = (λ_ (X ⟶[QuotientDGCochain] Y)).hom ≫ F.map X Y := by
            rw [hcomp, Category.comp_id]
      _ = (𝟙_ QuotientDGCochain ◁ F.map X Y) ≫
          (λ_ (F.obj X ⟶[QuotientDGCochain] F.obj Y)).hom := by
            exact (MonoidalCategory.leftUnitor_naturality (F.map X Y)).symm
      _ = (𝟙_ QuotientDGCochain ◁ F.map X Y) ≫
          (eId QuotientDGCochain (F.obj X) ▷
            (F.obj X ⟶[QuotientDGCochain] F.obj Y)) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj X) (F.obj Y) := by
            rw [hid]
      _ = (eId QuotientDGCochain (F.obj X) ⊗ₘ F.map X Y) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj X) (F.obj Y) := by
            rw [MonoidalCategory.tensorHom_def']
            simp only [Category.assoc]

@[simp]
theorem quotientDGUnitGradedNatTransId_element
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    (F : EnrichedFunctor QuotientDGCochain C D) (X : C) :
    quotientDGUnitGradedNatTransElement
        (quotientDGUnitGradedNatTransId F) X =
      targetDGIdentityElement (F.obj X) :=
  rfl

/-- Thread two uses of the tensor unit around an arbitrary unit-graded component. -/
theorem quotientDGUnitThread
    {A U B : QuotientDGCochain}
    (t : (𝟙_ QuotientDGCochain) ⊗ A ⟶ U)
    (b : 𝟙_ QuotientDGCochain ⟶ B) :
    (((λ_ (𝟙_ QuotientDGCochain)).inv ⊗ₘ 𝟙 A) ≫
        (α_ (𝟙_ QuotientDGCochain) (𝟙_ QuotientDGCochain) A).hom) ≫
      (𝟙 (𝟙_ QuotientDGCochain) ⊗ₘ t) ≫
      ((λ_ U).hom ≫ (ρ_ U).inv) ≫
      (𝟙 U ⊗ₘ b) =
    ((λ_ A).hom ≫ (ρ_ A).inv) ≫
      (𝟙 A ⊗ₘ (λ_ (𝟙_ QuotientDGCochain)).inv) ≫
      (α_ A (𝟙_ QuotientDGCochain) (𝟙_ QuotientDGCochain)).inv ≫
      (((ρ_ A).hom ≫ (λ_ A).inv) ▷ (𝟙_ QuotientDGCochain)) ≫
      (t ⊗ₘ b) := by
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  monoidal

/-- Attach a unit-graded component after an arbitrary binary morphism. -/
theorem quotientDGPostcomposeUnitComponent
    {P Q U B : QuotientDGCochain}
    (m : P ⊗ Q ⟶ U) (b : 𝟙_ QuotientDGCochain ⟶ B) :
    (P ◁ (ρ_ Q).inv) ≫
      (P ◁ (Q ◁ b)) ≫
      (α_ P Q B).inv ≫
      (m ▷ B) =
    m ≫ (ρ_ U).inv ≫ (U ◁ b) := by
  have hcoh :
      (P ◁ (ρ_ Q).inv) ≫
          (P ◁ (Q ◁ b)) ≫
          (α_ P Q B).inv =
        (ρ_ (P ⊗ Q)).inv ≫ ((P ⊗ Q) ◁ b) := by
    monoidal
  have hcoh' := congrArg (fun t ↦ t ≫ (m ▷ B)) hcoh
  have hwe := MonoidalCategory.whisker_exchange m b
  have hwe' := congrArg (fun t ↦ (ρ_ (P ⊗ Q)).inv ≫ t) hwe
  calc
    _ = (ρ_ (P ⊗ Q)).inv ≫ ((P ⊗ Q) ◁ b) ≫ (m ▷ B) := by
      simpa only [Category.assoc] using hcoh'
    _ = (ρ_ (P ⊗ Q)).inv ≫
        (m ▷ (𝟙_ QuotientDGCochain)) ≫ (U ◁ b) := by
      simpa only [Category.assoc] using hwe'
    _ = m ≫ (ρ_ U).inv ≫ (U ◁ b) := by
      rw [← Category.assoc, ← MonoidalCategory.rightUnitor_inv_naturality]
      rfl

/-- Move an arbitrary rightmost map through a binary composition. -/
theorem quotientDGWhiskerRightThroughComposition
    {P Q U A B : QuotientDGCochain}
    (m : P ⊗ Q ⟶ U) (f : A ⟶ B) :
    (P ◁ (Q ◁ f)) ≫ (α_ P Q B).inv ≫ (m ▷ B) =
      (α_ P Q A).inv ≫ (m ▷ A) ≫ (U ◁ f) := by
  have hassoc :
      (P ◁ (Q ◁ f)) ≫ (α_ P Q B).inv =
        (α_ P Q A).inv ≫ ((P ⊗ Q) ◁ f) := by
    simpa only [MonoidalCategory.tensorHom_def, Category.id_comp,
      Category.comp_id, MonoidalCategory.id_whiskerRight,
      MonoidalCategory.whiskerLeft_id] using
      (MonoidalCategory.associator_inv_naturality
        (𝟙 P) (𝟙 Q) f)
  have hassoc' := congrArg (fun t ↦ t ≫ (m ▷ B)) hassoc
  have hwe := MonoidalCategory.whisker_exchange m f
  have hwe' := congrArg (fun t ↦ (α_ P Q A).inv ≫ t) hwe
  calc
    _ = (α_ P Q A).inv ≫ ((P ⊗ Q) ◁ f) ≫ (m ▷ B) := by
      simpa only [Category.assoc] using hassoc'
    _ = (α_ P Q A).inv ≫ (m ▷ A) ≫ (U ◁ f) := by
      simpa only [Category.assoc] using hwe'

/-- Normalize a map followed by two unit-graded components to left-associated composition. -/
theorem quotientDGMapThenUnitPairLeftAssociated
    {A P Q U B V : QuotientDGCochain}
    (f : A ⟶ P)
    (a : 𝟙_ QuotientDGCochain ⟶ Q)
    (b : 𝟙_ QuotientDGCochain ⟶ B)
    (m : P ⊗ Q ⟶ U) (n : U ⊗ B ⟶ V) :
    let I := 𝟙_ QuotientDGCochain
    let δ : I ⟶ I ⊗ I := (λ_ I).inv
    let s : ∀ T : QuotientDGCochain, I ⊗ T ⟶ T ⊗ I :=
      fun T ↦ (λ_ T).hom ≫ (ρ_ T).inv
    let ha : I ⊗ A ⟶ U := s A ≫ (f ⊗ₘ a) ≫ m
    let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
      (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
    let p : I ⊗ A ⟶ P ⊗ (Q ⊗ B) :=
      s A ≫ (𝟙 A ⊗ₘ δ) ≫ (f ⊗ₘ (a ⊗ₘ b))
    p ≫ (α_ P Q B).inv ≫ (m ▷ B) ≫ n =
      pre ≫ (𝟙 I ⊗ₘ ha) ≫ s U ≫ (𝟙 U ⊗ₘ b) ≫ n := by
  dsimp
  let I := 𝟙_ QuotientDGCochain
  let δ : I ⟶ I ⊗ I := (λ_ I).inv
  let s (T : QuotientDGCochain) : I ⊗ T ⟶ T ⊗ I :=
    (λ_ T).hom ≫ (ρ_ T).inv
  let t : I ⊗ A ⟶ P ⊗ Q := s A ≫ (f ⊗ₘ a)
  let ha : I ⊗ A ⟶ U := t ≫ m
  let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
    (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
  let out : I ⊗ A ⟶ V :=
    pre ≫ (𝟙 I ⊗ₘ ha) ≫ s U ≫ (𝟙 U ⊗ₘ b) ≫ n
  let k : I ⊗ A ⟶ P ⊗ Q :=
    s A ≫ (𝟙 A ⊗ₘ δ) ≫ (α_ A I I).inv ≫
      (((ρ_ A).hom ≫ (λ_ A).inv) ▷ I) ≫
      (t ⊗ₘ 𝟙 I) ≫ (ρ_ (P ⊗ Q)).hom
  have hpost := quotientDGPostcomposeUnitComponent m b
  have hpost' := congrArg (fun z ↦ k ≫ z ≫ n) hpost
  have hthread := quotientDGUnitThread ha b
  have hthread' := congrArg (fun z ↦ z ≫ n) hthread
  have hout : out =
      s A ≫ (𝟙 A ⊗ₘ δ) ≫ (α_ A I I).inv ≫
      (((ρ_ A).hom ≫ (λ_ A).inv) ▷ I) ≫ (ha ⊗ₘ b) ≫ n := by
    simpa only [out, pre, s, δ, I, Category.assoc] using hthread'
  change (s A ≫ (𝟙 A ⊗ₘ δ) ≫ (f ⊗ₘ (a ⊗ₘ b))) ≫
      (α_ P Q B).inv ≫ (m ▷ B) ≫ n = out
  rw [hout]
  calc
    _ = k ≫ ((P ◁ (ρ_ Q).inv) ≫ (P ◁ (Q ◁ b)) ≫
        (α_ P Q B).inv ≫ (m ▷ B)) ≫ n := by
      dsimp [k, t, s, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal
    _ = k ≫ (m ≫ (ρ_ U).inv ≫ (U ◁ b)) ≫ n := by
      simpa only [Category.assoc] using hpost'
    _ = s A ≫ (𝟙 A ⊗ₘ δ) ≫ (α_ A I I).inv ≫
      (((ρ_ A).hom ≫ (λ_ A).inv) ▷ I) ≫ (ha ⊗ₘ b) ≫ n := by
      dsimp [k, ha, t, s, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal

/-- Normalize a map followed by two unit components using an associativity square. -/
theorem quotientDGMapThenUnitPair
    {A P Q U B R V : QuotientDGCochain}
    (f : A ⟶ P)
    (a : 𝟙_ QuotientDGCochain ⟶ Q)
    (b : 𝟙_ QuotientDGCochain ⟶ B)
    (m : P ⊗ Q ⟶ U) (q : Q ⊗ B ⟶ R)
    (n : U ⊗ B ⟶ V) (r : P ⊗ R ⟶ V)
    (hassoc :
      (α_ P Q B).inv ≫ (m ▷ B) ≫ n = (P ◁ q) ≫ r) :
    let I := 𝟙_ QuotientDGCochain
    let δ : I ⟶ I ⊗ I := (λ_ I).inv
    let s : ∀ T : QuotientDGCochain, I ⊗ T ⟶ T ⊗ I :=
      fun T ↦ (λ_ T).hom ≫ (ρ_ T).inv
    let ha : I ⊗ A ⟶ U := s A ≫ (f ⊗ₘ a) ≫ m
    let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
      (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
    s A ≫ (f ⊗ₘ (δ ≫ (a ⊗ₘ b) ≫ q)) ≫ r =
      pre ≫ (𝟙 I ⊗ₘ ha) ≫ s U ≫ (𝟙 U ⊗ₘ b) ≫ n := by
  dsimp
  let I := 𝟙_ QuotientDGCochain
  let δ : I ⟶ I ⊗ I := (λ_ I).inv
  let s (T : QuotientDGCochain) : I ⊗ T ⟶ T ⊗ I :=
    (λ_ T).hom ≫ (ρ_ T).inv
  let ha : I ⊗ A ⟶ U := s A ≫ (f ⊗ₘ a) ≫ m
  let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
    (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
  let p : I ⊗ A ⟶ P ⊗ (Q ⊗ B) :=
    s A ≫ (𝟙 A ⊗ₘ δ) ≫ (f ⊗ₘ (a ⊗ₘ b))
  have hleft := quotientDGMapThenUnitPairLeftAssociated f a b m n
  calc
    _ = p ≫ (P ◁ q) ≫ r := by
      dsimp [p, s, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal
    _ = p ≫ (α_ P Q B).inv ≫ (m ▷ B) ≫ n := by
      have h := congrArg (fun z ↦ p ≫ z) hassoc.symm
      simpa only [Category.assoc] using h
    _ = pre ≫ (𝟙 I ⊗ₘ ha) ≫ s U ≫ (𝟙 U ⊗ₘ b) ≫ n := by
      simpa only [p, pre, ha, s, δ, I] using hleft

/-- Move a unit component, an ordinary Hom map, and a second component across associativity. -/
theorem quotientDGUnitPairAcrossMap
    {A P Q U B R V : QuotientDGCochain}
    (a : 𝟙_ QuotientDGCochain ⟶ P)
    (f : A ⟶ Q)
    (b : 𝟙_ QuotientDGCochain ⟶ B)
    (m : P ⊗ Q ⟶ U) (q : Q ⊗ B ⟶ R)
    (n : U ⊗ B ⟶ V) (r : P ⊗ R ⟶ V)
    (hassoc :
      (α_ P Q B).inv ≫ (m ▷ B) ≫ n = (P ◁ q) ≫ r) :
    let I := 𝟙_ QuotientDGCochain
    let δ : I ⟶ I ⊗ I := (λ_ I).inv
    let s : ∀ T : QuotientDGCochain, I ⊗ T ⟶ T ⊗ I :=
      fun T ↦ (λ_ T).hom ≫ (ρ_ T).inv
    let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
      (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
    let ha : I ⊗ A ⟶ U := (a ⊗ₘ f) ≫ m
    let hb : I ⊗ A ⟶ R := s A ≫ (f ⊗ₘ b) ≫ q
    pre ≫ (𝟙 I ⊗ₘ ha) ≫ s U ≫ (𝟙 U ⊗ₘ b) ≫ n =
      pre ≫ (a ⊗ₘ hb) ≫ r := by
  dsimp
  let I := 𝟙_ QuotientDGCochain
  let δ : I ⟶ I ⊗ I := (λ_ I).inv
  let s (T : QuotientDGCochain) : I ⊗ T ⟶ T ⊗ I :=
    (λ_ T).hom ≫ (ρ_ T).inv
  let ha : I ⊗ A ⟶ U := (a ⊗ₘ f) ≫ m
  let hb : I ⊗ A ⟶ R := s A ≫ (f ⊗ₘ b) ≫ q
  let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
    (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
  let lhs : I ⊗ A ⟶ V :=
    pre ≫ (𝟙 I ⊗ₘ ha) ≫ s U ≫ (𝟙 U ⊗ₘ b) ≫ n
  let rhs : I ⊗ A ⟶ V := pre ≫ (a ⊗ₘ hb) ≫ r
  have hthread := quotientDGUnitThread ha b
  have hthread' := congrArg (fun z ↦ z ≫ n) hthread
  have hlhs : lhs =
      s A ≫ (𝟙 A ⊗ₘ δ) ≫ (α_ A I I).inv ≫
      (((ρ_ A).hom ≫ (λ_ A).inv) ▷ I) ≫ (ha ⊗ₘ b) ≫ n := by
    simpa only [lhs, pre, s, δ, I, Category.assoc] using hthread'
  change lhs = rhs
  rw [hlhs]
  let k : I ⊗ A ⟶ P ⊗ Q :=
    s A ≫ (𝟙 A ⊗ₘ δ) ≫ (α_ A I I).inv ≫
      (((ρ_ A).hom ≫ (λ_ A).inv) ▷ I) ≫
      ((a ⊗ₘ f) ⊗ₘ 𝟙 I) ≫ (ρ_ (P ⊗ Q)).hom
  let p : I ⊗ A ⟶ P ⊗ (Q ⊗ B) :=
    pre ≫ (a ⊗ₘ (s A ≫ (f ⊗ₘ b)))
  have hpost := quotientDGPostcomposeUnitComponent m b
  have hpost' := congrArg (fun z ↦ k ≫ z ≫ n) hpost
  calc
    _ = k ≫ (m ≫ (ρ_ U).inv ≫ (U ◁ b)) ≫ n := by
      dsimp [k, ha, s, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal
    _ = k ≫ ((P ◁ (ρ_ Q).inv) ≫ (P ◁ (Q ◁ b)) ≫
        (α_ P Q B).inv ≫ (m ▷ B)) ≫ n := by
      simpa only [Category.assoc] using hpost'.symm
    _ = p ≫ (α_ P Q B).inv ≫ (m ▷ B) ≫ n := by
      dsimp [k, p, pre, s, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal
    _ = p ≫ (P ◁ q) ≫ r := by
      have h := congrArg (fun z ↦ p ≫ z) hassoc
      simpa only [Category.assoc] using h
    _ = rhs := by
      dsimp [rhs, pre, hb, p, s, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal

/-- Normalize two unit components followed by an arbitrary rightmost map. -/
theorem quotientDGUnitPairThenMap
    {A P Q U B R V : QuotientDGCochain}
    (a : 𝟙_ QuotientDGCochain ⟶ P)
    (b : 𝟙_ QuotientDGCochain ⟶ Q)
    (f : A ⟶ B)
    (m : P ⊗ Q ⟶ U) (q : Q ⊗ B ⟶ R)
    (n : U ⊗ B ⟶ V) (r : P ⊗ R ⟶ V)
    (hassoc :
      (α_ P Q B).inv ≫ (m ▷ B) ≫ n = (P ◁ q) ≫ r) :
    (((λ_ (𝟙_ QuotientDGCochain)).inv ⊗ₘ 𝟙 A) ≫
        (α_ (𝟙_ QuotientDGCochain) (𝟙_ QuotientDGCochain) A).hom) ≫
      (a ⊗ₘ ((b ⊗ₘ f) ≫ q)) ≫ r =
    (((λ_ (𝟙_ QuotientDGCochain)).inv ≫ (a ⊗ₘ b) ≫ m) ⊗ₘ f) ≫ n := by
  let I := 𝟙_ QuotientDGCochain
  let δ : I ⟶ I ⊗ I := (λ_ I).inv
  let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
    (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
  let p0 : I ⊗ A ⟶ P ⊗ (Q ⊗ A) :=
    pre ≫ (a ⊗ₘ (b ⊗ₘ 𝟙 A))
  have hright := quotientDGWhiskerRightThroughComposition m f
  have hright' := congrArg (fun z ↦ p0 ≫ z ≫ n) hright
  change pre ≫ (a ⊗ₘ ((b ⊗ₘ f) ≫ q)) ≫ r =
    (((δ ≫ (a ⊗ₘ b) ≫ m) ⊗ₘ f) ≫ n)
  calc
    _ = p0 ≫ (P ◁ (Q ◁ f)) ≫ (P ◁ q) ≫ r := by
      dsimp [p0, pre, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal
    _ = p0 ≫ (P ◁ (Q ◁ f)) ≫
        (α_ P Q B).inv ≫ (m ▷ B) ≫ n := by
      have h := congrArg
        (fun z : P ⊗ (Q ⊗ B) ⟶ V ↦ (P ◁ (Q ◁ f)) ≫ z)
        hassoc.symm
      have h' := congrArg (fun z ↦ p0 ≫ z) h
      simpa only [Category.assoc] using h'
    _ = p0 ≫ (α_ P Q A).inv ≫ (m ▷ A) ≫ (U ◁ f) ≫ n := by
      simpa only [Category.assoc] using hright'
    _ = ((δ ≫ (a ⊗ₘ b) ≫ m) ⊗ₘ f) ≫ n := by
      dsimp [p0, pre, δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal

/-- Vertical composition of strict unit-graded enriched natural transformations. -/
noncomputable def quotientDGUnitGradedNatTransComp
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G H : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G)
    (β : QuotientDGUnitGradedNatTrans G H) :
    QuotientDGUnitGradedNatTrans F H where
  app X := (λ_ (𝟙_ QuotientDGCochain)).inv ≫
    (α.app X ⊗ₘ β.app X) ≫
      eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj X)
  naturality X Y := by
    let I := 𝟙_ QuotientDGCochain
    let A := X ⟶[QuotientDGCochain] Y
    let δ : I ⟶ I ⊗ I := (λ_ I).inv
    let s (T : QuotientDGCochain) : I ⊗ T ⟶ T ⊗ I :=
      (λ_ T).hom ≫ (ρ_ T).inv
    let pre : I ⊗ A ⟶ I ⊗ (I ⊗ A) :=
      (δ ⊗ₘ 𝟙 A) ≫ (α_ I I A).hom
    let haL : I ⊗ A ⟶ (F.obj X ⟶[QuotientDGCochain] G.obj Y) :=
      s A ≫ (F.map X Y ⊗ₘ α.app Y) ≫
        eComp QuotientDGCochain (F.obj X) (F.obj Y) (G.obj Y)
    let haR : I ⊗ A ⟶ (F.obj X ⟶[QuotientDGCochain] G.obj Y) :=
      (α.app X ⊗ₘ G.map X Y) ≫
        eComp QuotientDGCochain (F.obj X) (G.obj X) (G.obj Y)
    let hbL : I ⊗ A ⟶ (G.obj X ⟶[QuotientDGCochain] H.obj Y) :=
      s A ≫ (G.map X Y ⊗ₘ β.app Y) ≫
        eComp QuotientDGCochain (G.obj X) (G.obj Y) (H.obj Y)
    let hbR : I ⊗ A ⟶ (G.obj X ⟶[QuotientDGCochain] H.obj Y) :=
      (β.app X ⊗ₘ H.map X Y) ≫
        eComp QuotientDGCochain (G.obj X) (H.obj X) (H.obj Y)
    let n1 : I ⊗ A ⟶ (F.obj X ⟶[QuotientDGCochain] H.obj Y) :=
      pre ≫ (𝟙 I ⊗ₘ haL) ≫
        s (F.obj X ⟶[QuotientDGCochain] G.obj Y) ≫
        (𝟙 (F.obj X ⟶[QuotientDGCochain] G.obj Y) ⊗ₘ β.app Y) ≫
        eComp QuotientDGCochain (F.obj X) (G.obj Y) (H.obj Y)
    let n2 : I ⊗ A ⟶ (F.obj X ⟶[QuotientDGCochain] H.obj Y) :=
      pre ≫ (𝟙 I ⊗ₘ haR) ≫
        s (F.obj X ⟶[QuotientDGCochain] G.obj Y) ≫
        (𝟙 (F.obj X ⟶[QuotientDGCochain] G.obj Y) ⊗ₘ β.app Y) ≫
        eComp QuotientDGCochain (F.obj X) (G.obj Y) (H.obj Y)
    let n3 : I ⊗ A ⟶ (F.obj X ⟶[QuotientDGCochain] H.obj Y) :=
      pre ≫ (α.app X ⊗ₘ hbL) ≫
        eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj Y)
    let n4 : I ⊗ A ⟶ (F.obj X ⟶[QuotientDGCochain] H.obj Y) :=
      pre ≫ (α.app X ⊗ₘ hbR) ≫
        eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj Y)
    have h1 := quotientDGMapThenUnitPair
      (F.map X Y) (α.app Y) (β.app Y)
      (eComp QuotientDGCochain (F.obj X) (F.obj Y) (G.obj Y))
      (eComp QuotientDGCochain (F.obj Y) (G.obj Y) (H.obj Y))
      (eComp QuotientDGCochain (F.obj X) (G.obj Y) (H.obj Y))
      (eComp QuotientDGCochain (F.obj X) (F.obj Y) (H.obj Y))
      (e_assoc QuotientDGCochain (F.obj X) (F.obj Y) (G.obj Y) (H.obj Y))
    have h1' :
        s A ≫ (F.map X Y ⊗ₘ
          (δ ≫ (α.app Y ⊗ₘ β.app Y) ≫
            eComp QuotientDGCochain (F.obj Y) (G.obj Y) (H.obj Y))) ≫
          eComp QuotientDGCochain (F.obj X) (F.obj Y) (H.obj Y) = n1 := by
      simpa only [n1, haL, pre, s, δ, I, A] using h1
    have hα : haL = haR := by
      exact α.naturality X Y
    have h12 : n1 = n2 := by
      exact congrArg
        (fun t ↦ pre ≫ (𝟙 I ⊗ₘ t) ≫
          s (F.obj X ⟶[QuotientDGCochain] G.obj Y) ≫
          (𝟙 (F.obj X ⟶[QuotientDGCochain] G.obj Y) ⊗ₘ β.app Y) ≫
          eComp QuotientDGCochain (F.obj X) (G.obj Y) (H.obj Y)) hα
    have h23 : n2 = n3 := by
      simpa only [n2, n3, haR, hbL, pre, s, δ, I, A] using
        (quotientDGUnitPairAcrossMap
          (α.app X) (G.map X Y) (β.app Y)
          (eComp QuotientDGCochain (F.obj X) (G.obj X) (G.obj Y))
          (eComp QuotientDGCochain (G.obj X) (G.obj Y) (H.obj Y))
          (eComp QuotientDGCochain (F.obj X) (G.obj Y) (H.obj Y))
          (eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj Y))
          (e_assoc QuotientDGCochain (F.obj X) (G.obj X) (G.obj Y) (H.obj Y)))
    have hβ : hbL = hbR := by
      exact β.naturality X Y
    have h34 : n3 = n4 := by
      exact congrArg
        (fun t ↦ pre ≫ (α.app X ⊗ₘ t) ≫
          eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj Y)) hβ
    have h4 : n4 =
        (((δ ≫ (α.app X ⊗ₘ β.app X) ≫
          eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj X)) ⊗ₘ
            H.map X Y) ≫
          eComp QuotientDGCochain (F.obj X) (H.obj X) (H.obj Y)) := by
      simpa only [n4, hbR, pre, δ, I, A] using
        (quotientDGUnitPairThenMap
          (α.app X) (β.app X) (H.map X Y)
          (eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj X))
          (eComp QuotientDGCochain (G.obj X) (H.obj X) (H.obj Y))
          (eComp QuotientDGCochain (F.obj X) (H.obj X) (H.obj Y))
          (eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj Y))
          (e_assoc QuotientDGCochain (F.obj X) (G.obj X) (H.obj X) (H.obj Y)))
    rw [Center.tensorUnit_β]
    simp only [Iso.trans_hom, Iso.symm_hom]
    change s A ≫ (F.map X Y ⊗ₘ
        (δ ≫ (α.app Y ⊗ₘ β.app Y) ≫
          eComp QuotientDGCochain (F.obj Y) (G.obj Y) (H.obj Y))) ≫
        eComp QuotientDGCochain (F.obj X) (F.obj Y) (H.obj Y) =
      ((δ ≫ (α.app X ⊗ₘ β.app X) ≫
        eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj X)) ⊗ₘ
          H.map X Y) ≫
        eComp QuotientDGCochain (F.obj X) (H.obj X) (H.obj Y)
    exact h1'.trans (h12.trans (h23.trans (h34.trans h4)))

/-- The degree-zero component of vertical composition is homogeneous enriched composition
of the two component elements. -/
theorem quotientDGUnitGradedNatTransComp_element
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G H : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G)
    (β : QuotientDGUnitGradedNatTrans G H) (X : C) :
    quotientDGUnitGradedNatTransElement
        (quotientDGUnitGradedNatTransComp α β) X =
      quotientDGComposeElement (F.obj X) (G.obj X) (H.obj X)
        0 0 0 (by omega)
        (quotientDGUnitGradedNatTransElement α X)
        (quotientDGUnitGradedNatTransElement β X) := by
  unfold quotientDGUnitGradedNatTransElement
  change (((HomologicalComplex.leftUnitor'
      (𝟙_ QuotientDGCochain)).inv 0 ≫ _) ≫ _) _ = _
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [Category.assoc, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  let u := e.inv.hom (1 : QuotientCoefficientRing)
  have hι := GradedObject.Monoidal.ι_tensorHom
    (α.app X).f (β.app X).f 0 0 0 (by omega)
  have hιapp := ConcreteCategory.congr_hom hι
    (u ⊗ₜ[QuotientCoefficientRing] u)
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] at hιapp
  have hμ := congrArg
    (fun z ↦ ((eComp QuotientDGCochain
      (F.obj X) (G.obj X) (H.obj X)).f 0).hom z) hιapp
  unfold quotientDGComposeElement
  exact hμ

/-- Two tensor-unit components, normalized with the second component first. -/
theorem quotientDGUnitPairLeft
    {A B : QuotientDGCochain}
    (a : 𝟙_ QuotientDGCochain ⟶ A)
    (b : 𝟙_ QuotientDGCochain ⟶ B) :
    (λ_ (𝟙_ QuotientDGCochain)).inv ≫ (a ⊗ₘ b) =
      b ≫ (λ_ B).inv ≫ (a ▷ B) := by
  calc
    _ = (λ_ (𝟙_ QuotientDGCochain)).inv ≫
        (a ▷ (𝟙_ QuotientDGCochain)) ≫ (A ◁ b) := by
      rw [MonoidalCategory.tensorHom_def]
    _ = (λ_ (𝟙_ QuotientDGCochain)).inv ≫
        ((𝟙_ QuotientDGCochain) ◁ b) ≫ (a ▷ B) := by
      rw [MonoidalCategory.whisker_exchange]
    _ = (b ≫ (λ_ B).inv) ≫ (a ▷ B) := by
      have h := congrArg (fun z ↦ z ≫ (a ▷ B))
        (MonoidalCategory.leftUnitor_inv_naturality b).symm
      simpa only [Category.assoc] using h
    _ = b ≫ (λ_ B).inv ≫ (a ▷ B) := by rfl

/-- Two tensor-unit components, normalized with the first component first. -/
theorem quotientDGUnitPairRight
    {A B : QuotientDGCochain}
    (a : 𝟙_ QuotientDGCochain ⟶ A)
    (b : 𝟙_ QuotientDGCochain ⟶ B) :
    (λ_ (𝟙_ QuotientDGCochain)).inv ≫ (a ⊗ₘ b) =
      a ≫ (ρ_ A).inv ≫ (A ◁ b) := by
  simp only [MonoidalCategory.tensorHom_def]
  monoidal

/-- A morphism from the quotient DG tensor unit is determined by its degree-zero value on
the canonical generator. -/
theorem quotientDGUnitHom_ext
    {K : QuotientDGCochain}
    {f g : 𝟙_ QuotientDGCochain ⟶ K}
    (h : f.f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1) =
      g.f 0
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv.hom 1)) :
    f = g := by
  apply HomologicalComplex.from_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  let r : QuotientCoefficientRing := e.hom.hom x
  have hx : e.inv.hom r = x := by
    exact ConcreteCategory.congr_hom e.inv_hom_id x
  have hr : e.inv.hom r = r • e.inv.hom (1 : QuotientCoefficientRing) := by
    calc
      e.inv.hom r = e.inv.hom (r • (1 : QuotientCoefficientRing)) := by
        rw [smul_eq_mul, mul_one]
      _ = r • e.inv.hom (1 : QuotientCoefficientRing) := by
        exact e.inv.hom.map_smul r 1
  rw [← hx, hr]
  letI : SMul QuotientCoefficientRing (K.X 0) :=
    (Module.toDistribMulAction
      (R := QuotientCoefficientRing) (M := K.X 0)).toSMul
  let v := e.inv.hom (1 : QuotientCoefficientRing)
  calc
    (f.f 0).hom (r • v) = r • (f.f 0).hom v := by
      exact (f.f 0).hom.map_smul r v
    _ = r • (g.f 0).hom v := by
      exact congrArg (r • ·) h
    _ = (g.f 0).hom (r • v) := by
      exact ((g.f 0).hom.map_smul r v).symm

/-- Associativity of three tensor-unit components with respect to compatible binary
composition maps. -/
theorem quotientDGUnitComp_assoc
    {P Q U B R V : QuotientDGCochain}
    (a : 𝟙_ QuotientDGCochain ⟶ P)
    (b : 𝟙_ QuotientDGCochain ⟶ Q)
    (c : 𝟙_ QuotientDGCochain ⟶ B)
    (m : P ⊗ Q ⟶ U) (q : Q ⊗ B ⟶ R)
    (n : U ⊗ B ⟶ V) (r : P ⊗ R ⟶ V)
    (hassoc : (α_ P Q B).inv ≫ (m ▷ B) ≫ n = (P ◁ q) ≫ r) :
    (λ_ (𝟙_ QuotientDGCochain)).inv ≫
      (((λ_ (𝟙_ QuotientDGCochain)).inv ≫ (a ⊗ₘ b) ≫ m) ⊗ₘ c) ≫ n =
    (λ_ (𝟙_ QuotientDGCochain)).inv ≫
      (a ⊗ₘ ((λ_ (𝟙_ QuotientDGCochain)).inv ≫ (b ⊗ₘ c) ≫ q)) ≫ r := by
  let I := 𝟙_ QuotientDGCochain
  let δ : I ⟶ I ⊗ I := (λ_ I).inv
  have hbase := quotientDGUnitPairThenMap a b c m q n r hassoc
  have hpre := congrArg (fun z ↦ δ ≫ z) hbase
  calc
    _ = δ ≫ (((δ ≫ (a ⊗ₘ b) ≫ m) ⊗ₘ c) ≫ n) := by rfl
    _ = δ ≫
        ((((δ ⊗ₘ 𝟙 I) ≫ (α_ I I I).hom) ≫
          (a ⊗ₘ ((b ⊗ₘ c) ≫ q)) ≫ r)) := by
      simpa only [I, δ] using hpre.symm
    _ = δ ≫ (a ⊗ₘ (δ ≫ (b ⊗ₘ c) ≫ q)) ≫ r := by
      dsimp [δ, I]
      simp only [MonoidalCategory.tensorHom_def, Category.assoc]
      monoidal

/-- Left unit law for vertical composition of unit-graded enriched transformations. -/
theorem quotientDGUnitGradedNatTrans_id_comp
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G) :
    quotientDGUnitGradedNatTransComp
        (quotientDGUnitGradedNatTransId F) α = α := by
  apply GradedNatTrans.ext
  funext X
  let H := F.obj X ⟶[QuotientDGCochain] G.obj X
  let η := eId QuotientDGCochain (F.obj X)
  let μ := eComp QuotientDGCochain (F.obj X) (F.obj X) (G.obj X)
  change (λ_ (𝟙_ QuotientDGCochain)).inv ≫
      (η ⊗ₘ α.app X) ≫ μ = α.app X
  have hp := congrArg (fun z ↦ z ≫ μ)
    (quotientDGUnitPairLeft η (α.app X))
  have hu := congrArg (fun z : H ⟶ H ↦ α.app X ≫ z)
    (e_id_comp QuotientDGCochain (F.obj X) (G.obj X))
  calc
    _ = α.app X ≫ (λ_ H).inv ≫ (η ▷ H) ≫ μ := by
      simpa only [Category.assoc] using hp
    _ = α.app X := by
      simpa only [H, η, μ, Category.assoc, Category.comp_id] using hu

/-- Right unit law for vertical composition of unit-graded enriched transformations. -/
theorem quotientDGUnitGradedNatTrans_comp_id
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G) :
    quotientDGUnitGradedNatTransComp α
        (quotientDGUnitGradedNatTransId G) = α := by
  apply GradedNatTrans.ext
  funext X
  let H := F.obj X ⟶[QuotientDGCochain] G.obj X
  let η := eId QuotientDGCochain (G.obj X)
  let μ := eComp QuotientDGCochain (F.obj X) (G.obj X) (G.obj X)
  change (λ_ (𝟙_ QuotientDGCochain)).inv ≫
      (α.app X ⊗ₘ η) ≫ μ = α.app X
  have hp := congrArg (fun z ↦ z ≫ μ)
    (quotientDGUnitPairRight (α.app X) η)
  have hu := congrArg (fun z : H ⟶ H ↦ α.app X ≫ z)
    (e_comp_id QuotientDGCochain (F.obj X) (G.obj X))
  calc
    _ = α.app X ≫ (ρ_ H).inv ≫ (H ◁ η) ≫ μ := by
      simpa only [Category.assoc] using hp
    _ = α.app X := by
      simpa only [H, η, μ, Category.assoc, Category.comp_id] using hu

/-- Associativity law for vertical composition of unit-graded enriched transformations. -/
theorem quotientDGUnitGradedNatTrans_assoc
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F G H K : EnrichedFunctor QuotientDGCochain C D}
    (α : QuotientDGUnitGradedNatTrans F G)
    (β : QuotientDGUnitGradedNatTrans G H)
    (γ : QuotientDGUnitGradedNatTrans H K) :
    quotientDGUnitGradedNatTransComp
        (quotientDGUnitGradedNatTransComp α β) γ =
      quotientDGUnitGradedNatTransComp α
        (quotientDGUnitGradedNatTransComp β γ) := by
  apply GradedNatTrans.ext
  funext X
  exact quotientDGUnitComp_assoc
    (α.app X) (β.app X) (γ.app X)
    (eComp QuotientDGCochain (F.obj X) (G.obj X) (H.obj X))
    (eComp QuotientDGCochain (G.obj X) (H.obj X) (K.obj X))
    (eComp QuotientDGCochain (F.obj X) (H.obj X) (K.obj X))
    (eComp QuotientDGCochain (F.obj X) (G.obj X) (K.obj X))
    (e_assoc QuotientDGCochain (F.obj X) (G.obj X) (H.obj X) (K.obj X))

/-- Transport a unit-graded enriched transformation along equalities of its source and
target enriched functors. -/
noncomputable def quotientDGUnitGradedNatTransTransport
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F F' G G' : EnrichedFunctor QuotientDGCochain C D}
    (hF : F = F') (hG : G = G')
    (α : QuotientDGUnitGradedNatTrans F G) :
    QuotientDGUnitGradedNatTrans F' G' := by
  subst F'
  subst G'
  exact α

/-- Transport does not change the component family, up to heterogeneous equality. -/
theorem quotientDGUnitGradedNatTransTransport_app_heq
    {C D : Type*}
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D]
    {F F' G G' : EnrichedFunctor QuotientDGCochain C D}
    (hF : F = F') (hG : G = G')
    (α : QuotientDGUnitGradedNatTrans F G) (X : C) :
    HEq ((quotientDGUnitGradedNatTransTransport hF hG α).app X)
      (α.app X) := by
  cases hF
  cases hG
  rfl

/-- Enriched functors equipped with strict unit-graded transformations as morphisms. -/
def QuotientDGEnrichedFunctorCategory
    (C D : Type*)
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D] :=
  EnrichedFunctor QuotientDGCochain C D

noncomputable instance
    (C D : Type*)
    [EnrichedCategory QuotientDGCochain C]
    [EnrichedCategory QuotientDGCochain D] :
    Category (QuotientDGEnrichedFunctorCategory C D) where
  Hom F G := QuotientDGUnitGradedNatTrans F G
  id F := quotientDGUnitGradedNatTransId F
  comp α β := quotientDGUnitGradedNatTransComp α β
  id_comp α := quotientDGUnitGradedNatTrans_id_comp α
  comp_id α := quotientDGUnitGradedNatTrans_comp_id α
  assoc α β γ := quotientDGUnitGradedNatTrans_assoc α β γ

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
