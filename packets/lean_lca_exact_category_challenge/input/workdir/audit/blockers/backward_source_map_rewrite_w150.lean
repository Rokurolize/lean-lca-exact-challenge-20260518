import LeanLCAExactChallenge.Derived.Bounded

/-!
W150 audit: source-map rewrites for the backward binary mapping-cone/biproduct
comparison.

The SSoT-selected route is `obstruction-audit`.  This file records the exact
`inl`/`inr` source-map rewrites for the backward map and uses the right rewrite
to turn W148's right source component into the ordinary right component
chain-map square.  The remaining local obstruction is therefore not the
source-map rewrite, but the two target mapping-cone component equations.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BackwardSourceMapRewriteW150

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

variable {K₁ K₂ L₁ L₂ : CochainComplex C ℤ}
variable (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)

noncomputable abbrev coneBiprodMap : CochainComplex C ℤ :=
  CochainComplex.mappingCone (biprod.map f₁ f₂)

noncomputable abbrev biprodCone : CochainComplex C ℤ :=
  CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂

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

def backwardDifferentialSquareRightComponent (n : ℤ) : Prop :=
  (biprod.inr :
      CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
      (biprodConeToConeBiprodMapX f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) =
    (biprod.inr :
      CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
      ((biprodCone f₁ f₂).d n (n + 1) ≫ biprodConeToConeBiprodMapX f₁ f₂ (n + 1))

def rightComponentDifferentialSquare (n : ℤ) : Prop :=
  rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) =
    (CochainComplex.mappingCone f₂).d n (n + 1) ≫
      rightComponentToConeBiprodMap f₁ f₂ (n + 1)

def rightComponentDifferentialSquareFstEquation (n : ℤ) : Prop :=
  (rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
      (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2) (by omega) =
    ((CochainComplex.mappingCone f₂).d n (n + 1) ≫
      rightComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v (n + 1) (n + 2) (by omega)

def rightComponentDifferentialSquareSndEquation (n : ℤ) : Prop :=
  (rightComponentToConeBiprodMap f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1)) ≫
      (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v (n + 1) (n + 1)
        (add_zero (n + 1)) =
    ((CochainComplex.mappingCone f₂).d n (n + 1) ≫
      rightComponentToConeBiprodMap f₁ f₂ (n + 1)) ≫
        (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v (n + 1) (n + 1)
          (add_zero (n + 1))

theorem biprod_inr_f_comp_biprodConeToConeBiprodMapX (n : ℤ) :
    (biprod.inr :
        CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
      biprodConeToConeBiprodMapX f₁ f₂ n =
        rightComponentToConeBiprodMap f₁ f₂ n := by
  dsimp [biprodConeToConeBiprodMapX]
  rw [← Category.assoc]
  rw [show (biprod.inr :
        CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
      (HomologicalComplex.biprodXIso
        (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).hom =
        (biprod.inr :
          (CochainComplex.mappingCone f₂).X n ⟶
            (CochainComplex.mappingCone f₁).X n ⊞ (CochainComplex.mappingCone f₂).X n) by
    ext <;> simp [Category.assoc]]
  simp

theorem biprod_inl_f_comp_biprodConeToConeBiprodMapX (n : ℤ) :
    (biprod.inl :
        CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).f n ≫
      biprodConeToConeBiprodMapX f₁ f₂ n =
        leftComponentToConeBiprodMap f₁ f₂ n := by
  dsimp [biprodConeToConeBiprodMapX]
  rw [← Category.assoc]
  rw [show (biprod.inl :
        CochainComplex.mappingCone f₁ ⟶ biprodCone f₁ f₂).f n ≫
      (HomologicalComplex.biprodXIso
        (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).hom =
        (biprod.inl :
          (CochainComplex.mappingCone f₁).X n ⟶
            (CochainComplex.mappingCone f₁).X n ⊞ (CochainComplex.mappingCone f₂).X n) by
    ext <;> simp [Category.assoc]]
  simp

theorem biprodCone_d_right_component (n : ℤ) :
    (biprod.inr :
        CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f n ≫
      (biprodCone f₁ f₂).d n (n + 1) =
        (CochainComplex.mappingCone f₂).d n (n + 1) ≫
          (biprod.inr :
            CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).f (n + 1) := by
  exact
    (biprod.inr :
      CochainComplex.mappingCone f₂ ⟶ biprodCone f₁ f₂).comm n (n + 1)

theorem backwardRightComponent_iff_rightComponentDifferentialSquare (n : ℤ) :
    backwardDifferentialSquareRightComponent f₁ f₂ n ↔
      rightComponentDifferentialSquare f₁ f₂ n := by
  dsimp [backwardDifferentialSquareRightComponent, rightComponentDifferentialSquare]
  rw [← Category.assoc, biprod_inr_f_comp_biprodConeToConeBiprodMapX]
  rw [← Category.assoc, biprodCone_d_right_component]
  rw [Category.assoc, biprod_inr_f_comp_biprodConeToConeBiprodMapX]

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

def backwardSourceMapRewriteFrontier : List String :=
  ["proved right source-map rewrite: `(biprod.inr).f n ≫ biprodConeToConeBiprodMapX f₁ f₂ n = rightComponentToConeBiprodMap f₁ f₂ n`",
    "proved left source-map rewrite: `(biprod.inl).f n ≫ biprodConeToConeBiprodMapX f₁ f₂ n = leftComponentToConeBiprodMap f₁ f₂ n`",
    "proved W148 right source component is equivalent to rightComponentDifferentialSquare",
    "remaining right target equation: rightComponentDifferentialSquareFstEquation",
    "remaining right target equation: rightComponentDifferentialSquareSndEquation"]

theorem backwardSourceMapRewriteFrontier_count :
    backwardSourceMapRewriteFrontier.length = 5 := rfl

section Checks

#check biprod_inr_f_comp_biprodConeToConeBiprodMapX
#check biprod_inl_f_comp_biprodConeToConeBiprodMapX
#check biprodCone_d_right_component
#check backwardRightComponent_iff_rightComponentDifferentialSquare
#check rightComponentDifferentialSquare_ext_to_iff
#check backwardSourceMapRewriteFrontier
#check backwardSourceMapRewriteFrontier_count
#check HomologicalComplex.inr_biprodXIso_inv
#check HomologicalComplex.biprod_inr_desc_f
#check HomologicalComplex.biprod_inr_snd_f
#check HomologicalComplex.biprod_inr_fst_f
#check CochainComplex.mappingCone.d_fst_v
#check CochainComplex.mappingCone.d_snd_v

end Checks

end BackwardSourceMapRewriteW150

end LeanLCAExactChallenge
