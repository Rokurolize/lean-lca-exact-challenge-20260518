/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Derived.Bounded

/-!
Reusable binary mapping-cone/biproduct comparison.

This module packages the explicit component maps between
`CochainComplex.mappingCone (biprod.map f₁ f₂)` and
`CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂` as a cochain-complex
isomorphism.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MappingConeBiprodComparison

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

variable {K₁ K₂ L₁ L₂ : CochainComplex C ℤ}
variable (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)

noncomputable abbrev coneBiprodMap : CochainComplex C ℤ :=
  CochainComplex.mappingCone (biprod.map f₁ f₂)

noncomputable abbrev biprodCone : CochainComplex C ℤ :=
  CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂

noncomputable def coneBiprodMapToLeftComponent (n : ℤ) :
    (coneBiprodMap f₁ f₂).X n ⟶ (CochainComplex.mappingCone f₁).X n :=
  (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl ≫
      (biprod.fst : K₁ ⊞ K₂ ⟶ K₁).f (n + 1) ≫
        (CochainComplex.mappingCone.inl f₁).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v n n (add_zero n) ≫
      (biprod.fst : L₁ ⊞ L₂ ⟶ L₁).f n ≫
        (CochainComplex.mappingCone.inr f₁).f n

noncomputable def coneBiprodMapToRightComponent (n : ℤ) :
    (coneBiprodMap f₁ f₂).X n ⟶ (CochainComplex.mappingCone f₂).X n :=
  (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl ≫
      (biprod.snd : K₁ ⊞ K₂ ⟶ K₂).f (n + 1) ≫
        (CochainComplex.mappingCone.inl f₂).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v n n (add_zero n) ≫
      (biprod.snd : L₁ ⊞ L₂ ⟶ L₂).f n ≫
        (CochainComplex.mappingCone.inr f₂).f n

noncomputable def coneBiprodMapToBiprodConeX (n : ℤ) :
    (coneBiprodMap f₁ f₂).X n ⟶ (biprodCone f₁ f₂).X n :=
  biprod.lift
      (coneBiprodMapToLeftComponent f₁ f₂ n)
      (coneBiprodMapToRightComponent f₁ f₂ n) ≫
    (HomologicalComplex.biprodXIso
      (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).inv

noncomputable def leftComponentToConeBiprodMap (n : ℤ) :
    (CochainComplex.mappingCone f₁).X n ⟶ (coneBiprodMap f₁ f₂).X n :=
  (CochainComplex.mappingCone.fst f₁).1.v n (n + 1) rfl ≫
      (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 1) ≫
        (CochainComplex.mappingCone.inl (biprod.map f₁ f₂)).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd f₁).v n n (add_zero n) ≫
      (biprod.inl : L₁ ⟶ L₁ ⊞ L₂).f n ≫
        (CochainComplex.mappingCone.inr (biprod.map f₁ f₂)).f n

noncomputable def rightComponentToConeBiprodMap (n : ℤ) :
    (CochainComplex.mappingCone f₂).X n ⟶ (coneBiprodMap f₁ f₂).X n :=
  (CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫
      (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 1) ≫
        (CochainComplex.mappingCone.inl (biprod.map f₁ f₂)).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd f₂).v n n (add_zero n) ≫
      (biprod.inr : L₂ ⟶ L₁ ⊞ L₂).f n ≫
        (CochainComplex.mappingCone.inr (biprod.map f₁ f₂)).f n

noncomputable def biprodConeToConeBiprodMapX (n : ℤ) :
    (biprodCone f₁ f₂).X n ⟶ (coneBiprodMap f₁ f₂).X n :=
  (HomologicalComplex.biprodXIso
      (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).hom ≫
    biprod.desc
      (leftComponentToConeBiprodMap f₁ f₂ n)
      (rightComponentToConeBiprodMap f₁ f₂ n)

theorem biprod_total_f_comp {A : C} {K L : CochainComplex C ℤ} (n : ℤ)
    (g : (K ⊞ L).X n ⟶ A) :
    ((biprod.fst : K ⊞ L ⟶ K).f n ≫ (biprod.inl : K ⟶ K ⊞ L).f n) ≫ g +
      ((biprod.snd : K ⊞ L ⟶ L).f n ≫ (biprod.inr : L ⟶ K ⊞ L).f n) ≫ g = g := by
  rw [← Preadditive.add_comp, HomologicalComplex.biprod_total_f, Category.id_comp]

theorem comp_biprod_total_f {A : C} {K L : CochainComplex C ℤ} (n : ℤ)
    (g : A ⟶ (K ⊞ L).X n) :
    g ≫ ((biprod.fst : K ⊞ L ⟶ K).f n ≫ (biprod.inl : K ⟶ K ⊞ L).f n) +
      g ≫ ((biprod.snd : K ⊞ L ⟶ L).f n ≫ (biprod.inr : L ⟶ K ⊞ L).f n) = g := by
  rw [← Preadditive.comp_add, HomologicalComplex.biprod_total_f, Category.comp_id]

theorem coneBiprodMap_component_roundtrip (n : ℤ) :
    coneBiprodMapToLeftComponent f₁ f₂ n ≫ leftComponentToConeBiprodMap f₁ f₂ n +
      coneBiprodMapToRightComponent f₁ f₂ n ≫ rightComponentToConeBiprodMap f₁ f₂ n = 𝟙 _ := by
  apply CochainComplex.mappingCone.ext_from (biprod.map f₁ f₂) (n + 1) n rfl
  · simp [coneBiprodMapToLeftComponent, coneBiprodMapToRightComponent,
      leftComponentToConeBiprodMap, rightComponentToConeBiprodMap,
      Preadditive.add_comp, Category.assoc]
    simpa [Category.assoc] using
      biprod_total_f_comp (n + 1)
        ((CochainComplex.mappingCone.inl (biprod.map f₁ f₂)).v (n + 1) n (by omega))
  · simp [coneBiprodMapToLeftComponent, coneBiprodMapToRightComponent,
      leftComponentToConeBiprodMap, rightComponentToConeBiprodMap,
      Preadditive.add_comp, Category.assoc]
    simpa [Category.assoc] using
      biprod_total_f_comp n ((CochainComplex.mappingCone.inr (biprod.map f₁ f₂)).f n)

theorem coneBiprodMapToBiprodConeX_comp_biprodConeToConeBiprodMapX (n : ℤ) :
    coneBiprodMapToBiprodConeX f₁ f₂ n ≫ biprodConeToConeBiprodMapX f₁ f₂ n = 𝟙 _ := by
  simp [coneBiprodMapToBiprodConeX, biprodConeToConeBiprodMapX,
    coneBiprodMap_component_roundtrip]

theorem leftComponentToConeBiprodMap_comp_coneBiprodMapToLeftComponent (n : ℤ) :
    leftComponentToConeBiprodMap f₁ f₂ n ≫ coneBiprodMapToLeftComponent f₁ f₂ n = 𝟙 _ := by
  apply CochainComplex.mappingCone.ext_to f₁ n (n + 1) rfl
  · simp [leftComponentToConeBiprodMap, coneBiprodMapToLeftComponent, Category.assoc]
  · simp [leftComponentToConeBiprodMap, coneBiprodMapToLeftComponent, Category.assoc]

theorem leftComponentToConeBiprodMap_comp_coneBiprodMapToRightComponent (n : ℤ) :
    leftComponentToConeBiprodMap f₁ f₂ n ≫ coneBiprodMapToRightComponent f₁ f₂ n = 0 := by
  apply CochainComplex.mappingCone.ext_to f₂ n (n + 1) rfl
  · simp [leftComponentToConeBiprodMap, coneBiprodMapToRightComponent, Category.assoc]
  · simp [leftComponentToConeBiprodMap, coneBiprodMapToRightComponent, Category.assoc]

theorem rightComponentToConeBiprodMap_comp_coneBiprodMapToLeftComponent (n : ℤ) :
    rightComponentToConeBiprodMap f₁ f₂ n ≫ coneBiprodMapToLeftComponent f₁ f₂ n = 0 := by
  apply CochainComplex.mappingCone.ext_to f₁ n (n + 1) rfl
  · simp [rightComponentToConeBiprodMap, coneBiprodMapToLeftComponent, Category.assoc]
  · simp [rightComponentToConeBiprodMap, coneBiprodMapToLeftComponent, Category.assoc]

theorem rightComponentToConeBiprodMap_comp_coneBiprodMapToRightComponent (n : ℤ) :
    rightComponentToConeBiprodMap f₁ f₂ n ≫ coneBiprodMapToRightComponent f₁ f₂ n = 𝟙 _ := by
  apply CochainComplex.mappingCone.ext_to f₂ n (n + 1) rfl
  · simp [rightComponentToConeBiprodMap, coneBiprodMapToRightComponent, Category.assoc]
  · simp [rightComponentToConeBiprodMap, coneBiprodMapToRightComponent, Category.assoc]

theorem biprodConeToConeBiprodMapX_auxiliary_comp (n : ℤ) :
    biprod.desc (leftComponentToConeBiprodMap f₁ f₂ n) (rightComponentToConeBiprodMap f₁ f₂ n) ≫
      biprod.lift (coneBiprodMapToLeftComponent f₁ f₂ n) (coneBiprodMapToRightComponent f₁ f₂ n) =
        𝟙 _ := by
  ext <;>
    simp [leftComponentToConeBiprodMap_comp_coneBiprodMapToLeftComponent,
      leftComponentToConeBiprodMap_comp_coneBiprodMapToRightComponent,
      rightComponentToConeBiprodMap_comp_coneBiprodMapToLeftComponent,
      rightComponentToConeBiprodMap_comp_coneBiprodMapToRightComponent,
      Category.assoc]

theorem biprodConeToConeBiprodMapX_comp_coneBiprodMapToBiprodConeX (n : ℤ) :
    biprodConeToConeBiprodMapX f₁ f₂ n ≫ coneBiprodMapToBiprodConeX f₁ f₂ n = 𝟙 _ := by
  rw [show biprodConeToConeBiprodMapX f₁ f₂ n ≫ coneBiprodMapToBiprodConeX f₁ f₂ n =
      (HomologicalComplex.biprodXIso
          (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).hom ≫
        (biprod.desc (leftComponentToConeBiprodMap f₁ f₂ n)
            (rightComponentToConeBiprodMap f₁ f₂ n) ≫
          biprod.lift (coneBiprodMapToLeftComponent f₁ f₂ n)
            (coneBiprodMapToRightComponent f₁ f₂ n)) ≫
        (HomologicalComplex.biprodXIso
          (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).inv by
    simp [coneBiprodMapToBiprodConeX, biprodConeToConeBiprodMapX, Category.assoc]]
  rw [biprodConeToConeBiprodMapX_auxiliary_comp]
  simp

theorem biprodMap_fst_f (n : ℤ) :
    (biprod.map f₁ f₂).f n ≫ (biprod.fst : L₁ ⊞ L₂ ⟶ L₁).f n =
      (biprod.fst : K₁ ⊞ K₂ ⟶ K₁).f n ≫ f₁.f n := by
  rw [← HomologicalComplex.comp_f, biprod.map_fst, HomologicalComplex.comp_f]

theorem biprodMap_snd_f (n : ℤ) :
    (biprod.map f₁ f₂).f n ≫ (biprod.snd : L₁ ⊞ L₂ ⟶ L₂).f n =
      (biprod.snd : K₁ ⊞ K₂ ⟶ K₂).f n ≫ f₂.f n := by
  rw [← HomologicalComplex.comp_f, biprod.map_snd, HomologicalComplex.comp_f]

def forwardDifferentialSquare (n : ℤ) : Prop :=
  coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1) =
    (coneBiprodMap f₁ f₂).d n (n + 1) ≫ coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)

def forwardDifferentialSquareLeftProjection (n : ℤ) : Prop :=
  (coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1)) ≫
      (biprod.fst :
        CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂ ⟶
          CochainComplex.mappingCone f₁).f (n + 1) =
    ((coneBiprodMap f₁ f₂).d n (n + 1) ≫
      coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) ≫
        (biprod.fst :
          CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂ ⟶
            CochainComplex.mappingCone f₁).f (n + 1)

def forwardDifferentialSquareRightProjection (n : ℤ) : Prop :=
  (coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1)) ≫
      (biprod.snd :
        CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂ ⟶
          CochainComplex.mappingCone f₂).f (n + 1) =
    ((coneBiprodMap f₁ f₂).d n (n + 1) ≫
      coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) ≫
        (biprod.snd :
          CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂ ⟶
            CochainComplex.mappingCone f₂).f (n + 1)

theorem forwardDifferentialSquare_reduction_iff (n : ℤ) :
    forwardDifferentialSquare f₁ f₂ n ↔
      forwardDifferentialSquareLeftProjection f₁ f₂ n ∧
        forwardDifferentialSquareRightProjection f₁ f₂ n := by
  constructor
  · intro h
    constructor
    · dsimp [forwardDifferentialSquareLeftProjection, forwardDifferentialSquare] at h ⊢
      rw [h]
    · dsimp [forwardDifferentialSquareRightProjection, forwardDifferentialSquare] at h ⊢
      rw [h]
  · rintro ⟨hleft, hright⟩
    dsimp [forwardDifferentialSquareLeftProjection, forwardDifferentialSquareRightProjection,
      forwardDifferentialSquare] at hleft hright ⊢
    apply HomologicalComplex.biprodX_ext_to
    · simpa [Category.assoc] using hleft
    · simpa [Category.assoc] using hright

theorem biprod_inr_f_comp_biprodConeToConeBiprodMapX (n : ℤ) :
    (biprod.inr :
        CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
      biprodConeToConeBiprodMapX f₁ f₂ n =
        rightComponentToConeBiprodMap f₁ f₂ n := by
  rw [show (biprod.inr :
        CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n =
      biprod.inr ≫
        (HomologicalComplex.biprodXIso
          (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).inv by
    rw [HomologicalComplex.inr_biprodXIso_inv]]
  simp only [biprodConeToConeBiprodMapX, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  simp

theorem biprod_inl_f_comp_biprodConeToConeBiprodMapX (n : ℤ) :
    (biprod.inl :
        CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).f n ≫
      biprodConeToConeBiprodMapX f₁ f₂ n =
        leftComponentToConeBiprodMap f₁ f₂ n := by
  rw [show (biprod.inl :
        CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).f n =
      biprod.inl ≫
        (HomologicalComplex.biprodXIso
          (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).inv by
    rw [HomologicalComplex.inl_biprodXIso_inv]]
  simp only [biprodConeToConeBiprodMapX, Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  simp

def leftComponentDifferentialSquare (n : ℤ) : Prop :=
  leftComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) =
    (CochainComplex.mappingCone f₁).d n (n + 1) ≫
      leftComponentToConeBiprodMap f₁ f₂ (n + 1)

def leftComponentDifferentialSquareFstEquation (n : ℤ) : Prop :=
  (leftComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
      (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
        (by omega) =
    ((CochainComplex.mappingCone f₁).d n (n + 1) ≫
      leftComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
          (by omega)

def leftComponentDifferentialSquareSndEquation (n : ℤ) : Prop :=
  (leftComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
      (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v (n + 1) (n + 1)
        (add_zero (n + 1)) =
    ((CochainComplex.mappingCone f₁).d n (n + 1) ≫
      leftComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v (n + 1) (n + 1)
          (add_zero (n + 1))

theorem leftComponentToConeBiprodMap_fst (n : ℤ) :
    leftComponentToConeBiprodMap f₁ f₂ n ≫
      (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl =
        (CochainComplex.mappingCone.fst f₁).1.v n (n + 1) rfl ≫
          (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 1) := by
  simp [leftComponentToConeBiprodMap, Category.assoc]

theorem leftComponentToConeBiprodMap_fst_of_eq (n j : ℤ) (h : n + 1 = j) :
    leftComponentToConeBiprodMap f₁ f₂ n ≫
      (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n j h =
        (CochainComplex.mappingCone.fst f₁).1.v n j h ≫
          (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f j := by
  subst j
  simpa using leftComponentToConeBiprodMap_fst f₁ f₂ n

theorem leftComponentToConeBiprodMap_snd (n : ℤ) :
    leftComponentToConeBiprodMap f₁ f₂ n ≫
      (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v n n (add_zero n) =
        (CochainComplex.mappingCone.snd f₁).v n n (add_zero n) ≫
          (biprod.inl : L₁ ⟶ L₁ ⊞ L₂).f n := by
  simp [leftComponentToConeBiprodMap, Category.assoc]

theorem biprodMap_inl_f (n : ℤ) :
    (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f n ≫ (biprod.map f₁ f₂).f n =
      f₁.f n ≫ (biprod.inl : L₁ ⟶ L₁ ⊞ L₂).f n := by
  rw [← HomologicalComplex.comp_f, biprod.inl_map, HomologicalComplex.comp_f]

theorem biprodCone_d_left_component (n : ℤ) :
    (biprod.inl : L₁ ⟶ L₁ ⊞ L₂).f n ≫ (L₁ ⊞ L₂).d n (n + 1) =
      L₁.d n (n + 1) ≫ (biprod.inl : L₁ ⟶ L₁ ⊞ L₂).f (n + 1) := by
  exact (biprod.inl : L₁ ⟶ L₁ ⊞ L₂).comm n (n + 1)

theorem biprodCone_d_left_source_component (n : ℤ) :
    (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f n ≫ (K₁ ⊞ K₂).d n (n + 1) =
      K₁.d n (n + 1) ≫ (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 1) := by
  exact (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).comm n (n + 1)

theorem leftComponentDifferentialSquareFstEquation_proof (n : ℤ) :
    leftComponentDifferentialSquareFstEquation f₁ f₂ n := by
  dsimp [leftComponentDifferentialSquareFstEquation]
  calc
    (leftComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
        (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
          (by omega) =
      leftComponentToConeBiprodMap f₁ f₂ n ≫
        ((coneBiprodMap f₁ f₂).d n (n + 1) ≫
          (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
            (by omega)) := by
        rw [Category.assoc]
    _ = leftComponentToConeBiprodMap f₁ f₂ n ≫
        (-(CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl ≫
          (K₁ ⊞ K₂).d (n + 1) (n + 2)) := by
        rw [CochainComplex.mappingCone.d_fst_v (biprod.map f₁ f₂) n (n + 1) (n + 2) rfl (by omega)]
    _ = -((leftComponentToConeBiprodMap f₁ f₂ n ≫
          (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl) ≫
        (K₁ ⊞ K₂).d (n + 1) (n + 2)) := by
        simp [Category.assoc]
    _ = -(((CochainComplex.mappingCone.fst f₁).1.v n (n + 1) rfl ≫
          (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 1)) ≫
        (K₁ ⊞ K₂).d (n + 1) (n + 2)) := by
        rw [leftComponentToConeBiprodMap_fst]
    _ = -(((CochainComplex.mappingCone.fst f₁).1.v n (n + 1) rfl ≫
          K₁.d (n + 1) (n + 2)) ≫
        (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 2)) := by
        have hsrc :
            ((CochainComplex.mappingCone.fst f₁).1.v n (n + 1) rfl ≫
                (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 1)) ≫
              (K₁ ⊞ K₂).d (n + 1) (n + 2) =
                ((CochainComplex.mappingCone.fst f₁).1.v n (n + 1) rfl ≫
                  K₁.d (n + 1) (n + 2)) ≫
                    (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 2) := by
          simp [Category.assoc]
        simp [hsrc]
    _ = ((CochainComplex.mappingCone f₁).d n (n + 1) ≫
          (CochainComplex.mappingCone.fst f₁).1.v (n + 1) (n + 2) (by omega)) ≫
        (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 2) := by
        rw [CochainComplex.mappingCone.d_fst_v f₁ n (n + 1) (n + 2) rfl (by omega)]
        simp [Category.assoc]
    _ = ((CochainComplex.mappingCone f₁).d n (n + 1) ≫
          leftComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
          (by omega) := by
        symm
        rw [Category.assoc, leftComponentToConeBiprodMap_fst_of_eq]
        rw [Category.assoc]

theorem leftComponentDifferentialSquareSndEquation_proof (n : ℤ) :
    leftComponentDifferentialSquareSndEquation f₁ f₂ n := by
  dsimp [leftComponentDifferentialSquareSndEquation]
  rw [Category.assoc]
  rw [CochainComplex.mappingCone.d_snd_v (biprod.map f₁ f₂) n (n + 1) rfl]
  rw [Preadditive.comp_add]
  rw [← Category.assoc, leftComponentToConeBiprodMap_fst]
  rw [← Category.assoc, leftComponentToConeBiprodMap_snd]
  rw [Category.assoc, biprodMap_inl_f]
  rw [Category.assoc, biprodCone_d_left_component]
  rw [← Category.assoc]
  rw [← Category.assoc]
  rw [← Preadditive.add_comp]
  rw [← CochainComplex.mappingCone.d_snd_v f₁ n (n + 1) rfl]
  rw [Category.assoc]
  rw [Category.assoc]
  rw [leftComponentToConeBiprodMap_snd]

theorem leftComponentDifferentialSquare_ext_to_iff (n : ℤ) :
    leftComponentDifferentialSquare f₁ f₂ n ↔
      leftComponentDifferentialSquareFstEquation f₁ f₂ n ∧
        leftComponentDifferentialSquareSndEquation f₁ f₂ n := by
  constructor
  · intro h
    constructor
    · dsimp [leftComponentDifferentialSquareFstEquation,
        leftComponentDifferentialSquare] at h ⊢
      rw [h]
    · dsimp [leftComponentDifferentialSquareSndEquation,
        leftComponentDifferentialSquare] at h ⊢
      rw [h]
  · rintro ⟨hfst, hsnd⟩
    dsimp [leftComponentDifferentialSquareFstEquation,
      leftComponentDifferentialSquareSndEquation, leftComponentDifferentialSquare] at hfst hsnd ⊢
    apply CochainComplex.mappingCone.ext_to (biprod.map f₁ f₂) (n + 1) (n + 2) (by omega)
    · simpa [Category.assoc] using hfst
    · simpa [Category.assoc] using hsnd

theorem leftComponentDifferentialSquare_proof (n : ℤ) :
    leftComponentDifferentialSquare f₁ f₂ n :=
  (leftComponentDifferentialSquare_ext_to_iff f₁ f₂ n).2
    ⟨leftComponentDifferentialSquareFstEquation_proof f₁ f₂ n,
      leftComponentDifferentialSquareSndEquation_proof f₁ f₂ n⟩

def rightComponentDifferentialSquare (n : ℤ) : Prop :=
  rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) =
    (CochainComplex.mappingCone f₂).d n (n + 1) ≫
      rightComponentToConeBiprodMap f₁ f₂ (n + 1)

def rightComponentDifferentialSquareFstEquation (n : ℤ) : Prop :=
  (rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
      (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
        (by omega) =
    ((CochainComplex.mappingCone f₂).d n (n + 1) ≫
      rightComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
          (by omega)

def rightComponentDifferentialSquareSndEquation (n : ℤ) : Prop :=
  (rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
      (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v (n + 1) (n + 1)
        (add_zero (n + 1)) =
    ((CochainComplex.mappingCone f₂).d n (n + 1) ≫
      rightComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v (n + 1) (n + 1)
          (add_zero (n + 1))

theorem rightComponentToConeBiprodMap_fst (n : ℤ) :
    rightComponentToConeBiprodMap f₁ f₂ n ≫
      (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl =
        (CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫
          (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 1) := by
  simp [rightComponentToConeBiprodMap, Category.assoc]

theorem rightComponentToConeBiprodMap_fst_of_eq (n j : ℤ) (h : n + 1 = j) :
    rightComponentToConeBiprodMap f₁ f₂ n ≫
      (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n j h =
        (CochainComplex.mappingCone.fst f₂).1.v n j h ≫
          (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f j := by
  subst j
  simpa using rightComponentToConeBiprodMap_fst f₁ f₂ n

theorem rightComponentToConeBiprodMap_snd (n : ℤ) :
    rightComponentToConeBiprodMap f₁ f₂ n ≫
      (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v n n (add_zero n) =
        (CochainComplex.mappingCone.snd f₂).v n n (add_zero n) ≫
          (biprod.inr : L₂ ⟶ L₁ ⊞ L₂).f n := by
  simp [rightComponentToConeBiprodMap, Category.assoc]

theorem biprodMap_inr_f (n : ℤ) :
    (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f n ≫ (biprod.map f₁ f₂).f n =
      f₂.f n ≫ (biprod.inr : L₂ ⟶ L₁ ⊞ L₂).f n := by
  rw [← HomologicalComplex.comp_f, biprod.inr_map, HomologicalComplex.comp_f]

theorem biprodCone_d_right_component (n : ℤ) :
    (biprod.inr : L₂ ⟶ L₁ ⊞ L₂).f n ≫ (L₁ ⊞ L₂).d n (n + 1) =
      L₂.d n (n + 1) ≫ (biprod.inr : L₂ ⟶ L₁ ⊞ L₂).f (n + 1) := by
  exact (biprod.inr : L₂ ⟶ L₁ ⊞ L₂).comm n (n + 1)

theorem biprodCone_d_right_source_component (n : ℤ) :
    (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f n ≫ (K₁ ⊞ K₂).d n (n + 1) =
      K₂.d n (n + 1) ≫ (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 1) := by
  exact (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).comm n (n + 1)

theorem rightComponentDifferentialSquareFstEquation_proof (n : ℤ) :
    rightComponentDifferentialSquareFstEquation f₁ f₂ n := by
  dsimp [rightComponentDifferentialSquareFstEquation]
  calc
    (rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
        (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
          (by omega) =
      rightComponentToConeBiprodMap f₁ f₂ n ≫
        ((coneBiprodMap f₁ f₂).d n (n + 1) ≫
          (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
            (by omega)) := by
        rw [Category.assoc]
    _ = rightComponentToConeBiprodMap f₁ f₂ n ≫
        (-(CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl ≫
          (K₁ ⊞ K₂).d (n + 1) (n + 2)) := by
        rw [CochainComplex.mappingCone.d_fst_v (biprod.map f₁ f₂) n (n + 1) (n + 2) rfl (by omega)]
    _ = -((rightComponentToConeBiprodMap f₁ f₂ n ≫
          (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl) ≫
        (K₁ ⊞ K₂).d (n + 1) (n + 2)) := by
        simp [Category.assoc]
    _ = -(((CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫
          (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 1)) ≫
        (K₁ ⊞ K₂).d (n + 1) (n + 2)) := by
        rw [rightComponentToConeBiprodMap_fst]
    _ = -(((CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫
          K₂.d (n + 1) (n + 2)) ≫
        (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 2)) := by
        have hsrc :
            ((CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫
                (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 1)) ≫
              (K₁ ⊞ K₂).d (n + 1) (n + 2) =
                ((CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫
                  K₂.d (n + 1) (n + 2)) ≫
                    (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 2) := by
          simp [Category.assoc]
        simp [hsrc]
    _ = ((CochainComplex.mappingCone f₂).d n (n + 1) ≫
          (CochainComplex.mappingCone.fst f₂).1.v (n + 1) (n + 2) (by omega)) ≫
        (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 2) := by
        rw [CochainComplex.mappingCone.d_fst_v f₂ n (n + 1) (n + 2) rfl (by omega)]
        simp [Category.assoc]
    _ = ((CochainComplex.mappingCone f₂).d n (n + 1) ≫
          rightComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2)
          (by omega) := by
        symm
        rw [Category.assoc, rightComponentToConeBiprodMap_fst_of_eq]
        rw [Category.assoc]

theorem rightComponentDifferentialSquareSndEquation_proof (n : ℤ) :
    rightComponentDifferentialSquareSndEquation f₁ f₂ n := by
  dsimp [rightComponentDifferentialSquareSndEquation]
  rw [Category.assoc]
  rw [CochainComplex.mappingCone.d_snd_v (biprod.map f₁ f₂) n (n + 1) rfl]
  rw [Preadditive.comp_add]
  rw [← Category.assoc, rightComponentToConeBiprodMap_fst]
  rw [← Category.assoc, rightComponentToConeBiprodMap_snd]
  rw [Category.assoc, biprodMap_inr_f]
  rw [Category.assoc, biprodCone_d_right_component]
  rw [← Category.assoc]
  rw [← Category.assoc]
  rw [← Preadditive.add_comp]
  rw [← CochainComplex.mappingCone.d_snd_v f₂ n (n + 1) rfl]
  rw [Category.assoc]
  rw [Category.assoc]
  rw [rightComponentToConeBiprodMap_snd]

theorem rightComponentDifferentialSquare_ext_to_iff (n : ℤ) :
    rightComponentDifferentialSquare f₁ f₂ n ↔
      rightComponentDifferentialSquareFstEquation f₁ f₂ n ∧
        rightComponentDifferentialSquareSndEquation f₁ f₂ n := by
  constructor
  · intro h
    constructor
    · dsimp [rightComponentDifferentialSquareFstEquation,
        rightComponentDifferentialSquare] at h ⊢
      rw [h]
    · dsimp [rightComponentDifferentialSquareSndEquation,
        rightComponentDifferentialSquare] at h ⊢
      rw [h]
  · rintro ⟨hfst, hsnd⟩
    dsimp [rightComponentDifferentialSquareFstEquation,
      rightComponentDifferentialSquareSndEquation, rightComponentDifferentialSquare] at hfst hsnd ⊢
    apply CochainComplex.mappingCone.ext_to (biprod.map f₁ f₂) (n + 1) (n + 2) (by omega)
    · simpa [Category.assoc] using hfst
    · simpa [Category.assoc] using hsnd

theorem rightComponentDifferentialSquare_proof (n : ℤ) :
    rightComponentDifferentialSquare f₁ f₂ n :=
  (rightComponentDifferentialSquare_ext_to_iff f₁ f₂ n).2
    ⟨rightComponentDifferentialSquareFstEquation_proof f₁ f₂ n,
      rightComponentDifferentialSquareSndEquation_proof f₁ f₂ n⟩

theorem biprodConeToConeBiprodMapX_differentialCompatibility (n : ℤ) :
    biprodConeToConeBiprodMapX f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) =
      (biprodCone f₁ f₂).d n (n + 1) ≫
        biprodConeToConeBiprodMapX f₁ f₂ (n + 1) := by
  apply HomologicalComplex.biprodX_ext_from
  · calc
      (biprod.inl : CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).f n ≫
          (biprodConeToConeBiprodMapX f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) =
        leftComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) := by
          rw [← Category.assoc, biprod_inl_f_comp_biprodConeToConeBiprodMapX]
      _ = (CochainComplex.mappingCone f₁).d n (n + 1) ≫
            leftComponentToConeBiprodMap f₁ f₂ (n + 1) := by
          exact leftComponentDifferentialSquare_proof f₁ f₂ n
      _ = ((biprod.inl : CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).f n ≫
            (biprodCone f₁ f₂).d n (n + 1)) ≫
            biprodConeToConeBiprodMapX f₁ f₂ (n + 1) := by
          rw [(biprod.inl : CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).comm n (n + 1)]
          rw [Category.assoc, biprod_inl_f_comp_biprodConeToConeBiprodMapX]
      _ = (biprod.inl : CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).f n ≫
          ((biprodCone f₁ f₂).d n (n + 1) ≫
            biprodConeToConeBiprodMapX f₁ f₂ (n + 1)) := by
          rw [Category.assoc]
  · calc
      (biprod.inr : CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
          (biprodConeToConeBiprodMapX f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) =
        rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) := by
          rw [← Category.assoc, biprod_inr_f_comp_biprodConeToConeBiprodMapX]
      _ = (CochainComplex.mappingCone f₂).d n (n + 1) ≫
            rightComponentToConeBiprodMap f₁ f₂ (n + 1) := by
          exact rightComponentDifferentialSquare_proof f₁ f₂ n
      _ = ((biprod.inr : CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
            (biprodCone f₁ f₂).d n (n + 1)) ≫
            biprodConeToConeBiprodMapX f₁ f₂ (n + 1) := by
          rw [(biprod.inr : CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).comm n (n + 1)]
          rw [Category.assoc, biprod_inr_f_comp_biprodConeToConeBiprodMapX]
      _ = (biprod.inr : CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
          ((biprodCone f₁ f₂).d n (n + 1) ≫
            biprodConeToConeBiprodMapX f₁ f₂ (n + 1)) := by
          rw [Category.assoc]

structure BinaryMappingConeBiprodDifferentialCompatibility : Prop where
  left_to_right :
    ∀ (n : ℤ),
      coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1) =
        (coneBiprodMap f₁ f₂).d n (n + 1) ≫ coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)
  right_to_left :
    ∀ (n : ℤ),
      biprodConeToConeBiprodMapX f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) =
        (biprodCone f₁ f₂).d n (n + 1) ≫ biprodConeToConeBiprodMapX f₁ f₂ (n + 1)

theorem binaryMappingConeBiprodDifferentialCompatibility :
    BinaryMappingConeBiprodDifferentialCompatibility f₁ f₂ where
  left_to_right n := by
    have hpost :
        (coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1)) ≫
            biprodConeToConeBiprodMapX f₁ f₂ (n + 1) =
          ((coneBiprodMap f₁ f₂).d n (n + 1) ≫
            coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) ≫
              biprodConeToConeBiprodMapX f₁ f₂ (n + 1) := by
      calc
        (coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1)) ≫
            biprodConeToConeBiprodMapX f₁ f₂ (n + 1) =
          coneBiprodMapToBiprodConeX f₁ f₂ n ≫
            ((biprodCone f₁ f₂).d n (n + 1) ≫
              biprodConeToConeBiprodMapX f₁ f₂ (n + 1)) := by
            rw [Category.assoc]
        _ = coneBiprodMapToBiprodConeX f₁ f₂ n ≫
            (biprodConeToConeBiprodMapX f₁ f₂ n ≫
              (coneBiprodMap f₁ f₂).d n (n + 1)) := by
            rw [← biprodConeToConeBiprodMapX_differentialCompatibility]
        _ = (coneBiprodMapToBiprodConeX f₁ f₂ n ≫
              biprodConeToConeBiprodMapX f₁ f₂ n) ≫
              (coneBiprodMap f₁ f₂).d n (n + 1) := by
            rw [Category.assoc]
        _ = (coneBiprodMap f₁ f₂).d n (n + 1) := by
            rw [coneBiprodMapToBiprodConeX_comp_biprodConeToConeBiprodMapX]
            simp
        _ = ((coneBiprodMap f₁ f₂).d n (n + 1) ≫
            coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) ≫
              biprodConeToConeBiprodMapX f₁ f₂ (n + 1) := by
            rw [Category.assoc, coneBiprodMapToBiprodConeX_comp_biprodConeToConeBiprodMapX]
            simp
    calc
      coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1) =
        (coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1)) ≫
          (biprodConeToConeBiprodMapX f₁ f₂ (n + 1) ≫
            coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) := by
          rw [biprodConeToConeBiprodMapX_comp_coneBiprodMapToBiprodConeX]
          simp
      _ = ((coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1)) ≫
            biprodConeToConeBiprodMapX f₁ f₂ (n + 1)) ≫
          coneBiprodMapToBiprodConeX f₁ f₂ (n + 1) := by
          simp [Category.assoc]
      _ = (((coneBiprodMap f₁ f₂).d n (n + 1) ≫
            coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) ≫
              biprodConeToConeBiprodMapX f₁ f₂ (n + 1)) ≫
          coneBiprodMapToBiprodConeX f₁ f₂ (n + 1) := by
          rw [hpost]
      _ = ((coneBiprodMap f₁ f₂).d n (n + 1) ≫
            coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) ≫
          (biprodConeToConeBiprodMapX f₁ f₂ (n + 1) ≫
            coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)) := by
          simp [Category.assoc]
      _ = (coneBiprodMap f₁ f₂).d n (n + 1) ≫
            coneBiprodMapToBiprodConeX f₁ f₂ (n + 1) := by
          rw [biprodConeToConeBiprodMapX_comp_coneBiprodMapToBiprodConeX]
          simp
  right_to_left := biprodConeToConeBiprodMapX_differentialCompatibility f₁ f₂

structure BinaryMappingConeBiprodInverseCompatibility : Prop where
  cone_biprod_cone :
    ∀ (n : ℤ),
      coneBiprodMapToBiprodConeX f₁ f₂ n ≫ biprodConeToConeBiprodMapX f₁ f₂ n = 𝟙 _
  biprod_cone_biprod :
    ∀ (n : ℤ),
      biprodConeToConeBiprodMapX f₁ f₂ n ≫ coneBiprodMapToBiprodConeX f₁ f₂ n = 𝟙 _

theorem binaryMappingConeBiprodInverseCompatibility :
    BinaryMappingConeBiprodInverseCompatibility f₁ f₂ where
  cone_biprod_cone := coneBiprodMapToBiprodConeX_comp_biprodConeToConeBiprodMapX f₁ f₂
  biprod_cone_biprod := biprodConeToConeBiprodMapX_comp_coneBiprodMapToBiprodConeX f₁ f₂

noncomputable def binaryMappingConeBiprodXIso (n : ℤ) :
    (coneBiprodMap f₁ f₂).X n ≅ (biprodCone f₁ f₂).X n where
  hom := coneBiprodMapToBiprodConeX f₁ f₂ n
  inv := biprodConeToConeBiprodMapX f₁ f₂ n
  hom_inv_id := coneBiprodMapToBiprodConeX_comp_biprodConeToConeBiprodMapX f₁ f₂ n
  inv_hom_id := biprodConeToConeBiprodMapX_comp_coneBiprodMapToBiprodConeX f₁ f₂ n

noncomputable def binaryMappingConeBiprodIso :
    coneBiprodMap f₁ f₂ ≅ biprodCone f₁ f₂ :=
  HomologicalComplex.Hom.isoOfComponents
    (binaryMappingConeBiprodXIso f₁ f₂)
    (fun i j hij => by
      dsimp [binaryMappingConeBiprodXIso]
      rw [ComplexShape.up_Rel] at hij
      subst j
      simpa using
        (binaryMappingConeBiprodDifferentialCompatibility f₁ f₂).left_to_right i)

theorem binaryMappingConeBiprodIso_hom_f (n : ℤ) :
    (binaryMappingConeBiprodIso f₁ f₂).hom.f n =
      coneBiprodMapToBiprodConeX f₁ f₂ n :=
  rfl

theorem binaryMappingConeBiprodIso_inv_f (n : ℤ) :
    (binaryMappingConeBiprodIso f₁ f₂).inv.f n =
      biprodConeToConeBiprodMapX f₁ f₂ n :=
  rfl

end MappingConeBiprodComparison

end LeanLCAExactChallenge
