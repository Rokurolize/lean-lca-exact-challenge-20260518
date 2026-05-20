import LeanLCAExactChallenge.Derived.Bounded

/-!
V189 probe: component maps for the binary mapping-cone/biproduct comparison.

This file records the lower construction needed after W142: the candidate degreewise maps
between `mappingCone (biprod.map f₁ f₂)` and the binary biproduct of the component mapping
cones.  The remaining hard part is proving these component maps commute with the differentials
and packaging them as a complex isomorphism.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MappingConeBiprodComparisonProbeV189

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
          simpa [Category.assoc] using
            congrArg
              (fun q =>
                (CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫ q)
              (biprodCone_d_right_source_component (K₁ := K₁) (K₂ := K₂) (n + 1))
        simpa [hsrc]
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

structure BinaryMappingConeBiprodDifferentialCompatibility : Prop where
  left_to_right :
    ∀ (n : ℤ),
      coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1) =
        (coneBiprodMap f₁ f₂).d n (n + 1) ≫ coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)
  right_to_left :
    ∀ (n : ℤ),
      biprodConeToConeBiprodMapX f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) =
        (biprodCone f₁ f₂).d n (n + 1) ≫ biprodConeToConeBiprodMapX f₁ f₂ (n + 1)

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

def v189ComponentMapFrontier : List String :=
  ["component maps from mappingCone (biprod.map f₁ f₂) to the biproduct cone",
    "component maps from the biproduct cone to mappingCone (biprod.map f₁ f₂)",
    "proved: inverse identities for the candidate degreewise maps",
    "proved: forward differential square reduces to left and right biproduct projections",
    "remaining: differential compatibility for both component-map families"]

theorem v189ComponentMapFrontier_count :
    v189ComponentMapFrontier.length = 5 := rfl

section Checks

#check coneBiprodMapToLeftComponent
#check coneBiprodMapToRightComponent
#check coneBiprodMapToBiprodConeX
#check leftComponentToConeBiprodMap
#check rightComponentToConeBiprodMap
#check biprodConeToConeBiprodMapX
#check biprod_total_f_comp
#check comp_biprod_total_f
#check coneBiprodMap_component_roundtrip
#check coneBiprodMapToBiprodConeX_comp_biprodConeToConeBiprodMapX
#check leftComponentToConeBiprodMap_comp_coneBiprodMapToLeftComponent
#check leftComponentToConeBiprodMap_comp_coneBiprodMapToRightComponent
#check rightComponentToConeBiprodMap_comp_coneBiprodMapToLeftComponent
#check rightComponentToConeBiprodMap_comp_coneBiprodMapToRightComponent
#check biprodConeToConeBiprodMapX_auxiliary_comp
#check biprodConeToConeBiprodMapX_comp_coneBiprodMapToBiprodConeX
#check biprodMap_fst_f
#check biprodMap_snd_f
#check forwardDifferentialSquare
#check forwardDifferentialSquareLeftProjection
#check forwardDifferentialSquareRightProjection
#check forwardDifferentialSquare_reduction_iff
#check biprod_inr_f_comp_biprodConeToConeBiprodMapX
#check biprod_inl_f_comp_biprodConeToConeBiprodMapX
#check rightComponentDifferentialSquare
#check rightComponentDifferentialSquareFstEquation
#check rightComponentDifferentialSquareSndEquation
#check rightComponentToConeBiprodMap_fst
#check rightComponentToConeBiprodMap_snd
#check biprodMap_inr_f
#check biprodCone_d_right_component
#check biprodCone_d_right_source_component
#check rightComponentDifferentialSquareFstEquation_proof
#check rightComponentDifferentialSquareSndEquation_proof
#check rightComponentDifferentialSquare_ext_to_iff
#check BinaryMappingConeBiprodDifferentialCompatibility
#check BinaryMappingConeBiprodInverseCompatibility
#check binaryMappingConeBiprodInverseCompatibility
#check v189ComponentMapFrontier
#check v189ComponentMapFrontier_count
#check CochainComplex.mappingCone.ext_to
#check CochainComplex.mappingCone.ext_from
#check HomologicalComplex.biprodXIso

end Checks

end MappingConeBiprodComparisonProbeV189

end LeanLCAExactChallenge
