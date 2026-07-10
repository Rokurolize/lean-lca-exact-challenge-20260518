import LeanLCAExactChallenge.Infinity.AlexanderWhitney

/-!
# Alexander--Whitney coassociativity

This file proves the coassociativity law for the unnormalized Alexander--Whitney chain map.
The proof compares the two iterated maps on every triple tensor summand.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace DoldKanMonoidal

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite

theorem aw_front_front (p q r : ℕ) :
    SimplexCategory.subinterval (n := p + q) 0 p (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) 0 (p + q) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) 0 p (by omega) := by
  ext i
  simp [SimplexCategory.subinterval]

theorem aw_middle_left (p q r : ℕ) :
    SimplexCategory.subinterval (n := p + q) p q (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) 0 (p + q) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) p q (by omega) := by
  ext i
  simp [SimplexCategory.subinterval]

theorem aw_middle_right (p q r : ℕ) :
    SimplexCategory.subinterval (n := q + r) 0 q (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) p (q + r) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) p q (by omega) := by
  ext i
  simp [SimplexCategory.subinterval, Nat.add_comm]

theorem aw_back_back (p q r : ℕ) :
    SimplexCategory.subinterval (n := q + r) q r (by omega) ≫
        SimplexCategory.subinterval (n := p + q + r) p (q + r) (by omega) =
      SimplexCategory.subinterval (n := p + q + r) (p + q) r (by omega) := by
  ext i
  simp [SimplexCategory.subinterval, Nat.add_comm, Nat.add_left_comm]

variable (X Y Z : SimplicialObject (ModuleCat.{0} ℤ))

abbrev complexTensorFamily
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) :=
  (((((curriedTensor (ModuleCat ℤ)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj K).obj L).toGradedObject.mapObjFun
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) n)

def complexTensorPairProjection
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (i j n : ℕ) (h : i + j = n) :
    (K ⊗ L).X n ⟶ K.X i ⊗ L.X j :=
  Sigma.π (complexTensorFamily K L n)
    ⟨⟨i, j⟩, by change i + j = n; exact h⟩

@[simp]
theorem complexTensorPairProjection_alternating
    (A B : SimplicialObject (ModuleCat.{0} ℤ))
    (i j n : ℕ) (h : i + j = n) :
    complexTensorPairProjection (alternatingChains A) (alternatingChains B)
        i j n h = tensorPairProjection A B i j n h := rfl

theorem alternatingAlexanderWhitney_comp_complexTensorPairProjection
    (A B : SimplicialObject (ModuleCat.{0} ℤ))
    (i j n : ℕ) (h : i + j = n) :
    (alternatingAlexanderWhitney A B).f n ≫
        complexTensorPairProjection (alternatingChains A) (alternatingChains B)
          i j n h =
      A.map (SimplexCategory.subinterval (n := n) 0 i (by omega)).op ⊗ₘ
        B.map (SimplexCategory.subinterval (n := n) i j (by omega)).op := by
  subst n
  rw [alternatingAlexanderWhitney_f,
    complexTensorPairProjection_alternating,
    alternatingAlexanderWhitneyDegree_comp_pairProjection]

theorem tensorHom_comp_complexTensorPairProjection
    {K₁ K₂ L₁ L₂ : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    (i j n : ℕ) (h : i + j = n) :
    (HomologicalComplex.tensorHom f g).f n ≫
        complexTensorPairProjection L₁ L₂ i j n h =
      complexTensorPairProjection K₁ K₂ i j n h ≫
        (f.f i ⊗ₘ g.f j) := by
  apply Sigma.hom_ext
  rintro ⟨⟨a, b⟩, hab⟩
  change a + b = n at hab
  by_cases hai : a = i
  · subst a
    have hbj : b = j := by omega
    subst b
    have hL :
        Sigma.ι (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, h⟩ = 𝟙 _ := by
      convert Sigma.ι_π_eq_id (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, hab⟩
    have hK :
        Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩ = 𝟙 _ := by
      convert Sigma.ι_π_eq_id (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, hab⟩
    have hK' :
        (Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩) ≫
            (f.f i ⊗ₘ g.f j) = f.f i ⊗ₘ g.f j := by
      rw [hK, Category.id_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    dsimp only [complexTensorPairProjection, complexTensorFamily,
      HomologicalComplex.ιMapBifunctor,
      HomologicalComplex₂.ιTotal, GradedObject.ιMapObj]
    erw [hL, hK']
    simpa only [Category.comp_id] using
      (MonoidalCategory.tensorHom_def (f.f i) (g.f j)).symm
  · have hpairs : (a, b) ≠ (i, j) := by
      intro hp
      exact hai (congrArg Prod.fst hp)
    have hLzero :
        Sigma.ι (complexTensorFamily L₁ L₂ n) ⟨⟨a, b⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily L₁ L₂ n) ⟨⟨i, j⟩, h⟩ = 0 := by
      apply Sigma.ι_π_of_ne
      intro hs
      exact hpairs (congrArg Subtype.val hs)
    have hKzero :
        Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨a, b⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩ = 0 := by
      apply Sigma.ι_π_of_ne
      intro hs
      exact hpairs (congrArg Subtype.val hs)
    have hKzero' :
        (Sigma.ι (complexTensorFamily K₁ K₂ n) ⟨⟨a, b⟩, hab⟩ ≫
            Sigma.π (complexTensorFamily K₁ K₂ n) ⟨⟨i, j⟩, h⟩) ≫
            (f.f i ⊗ₘ g.f j) = 0 := by
      rw [hKzero, zero_comp]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    dsimp only [complexTensorPairProjection, complexTensorFamily,
      HomologicalComplex.ιMapBifunctor,
      HomologicalComplex₂.ιTotal, GradedObject.ιMapObj]
    erw [hLzero, hKzero']
    exact comp_zero

def complexRightTripleProjection
    (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    (K ⊗ (L ⊗ M)).X n ⟶ K.X p ⊗ (L.X q ⊗ M.X r) :=
  complexTensorPairProjection K (L ⊗ M) p (q + r) n (by omega) ≫
    (𝟙 (K.X p) ⊗ₘ complexTensorPairProjection L M q r (q + r) rfl)

theorem aw_right_iterated_projection (p q r : ℕ) :
    (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r) ≫
        (HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
          (alternatingAlexanderWhitney Y Z)).f (p + q + r) ≫
        complexRightTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl =
      X.map
            (SimplexCategory.subinterval
              (n := p + q + r) 0 p (by omega)).op ⊗ₘ
        (Y.map
              (SimplexCategory.subinterval
                (n := p + q + r) p q (by omega)).op ⊗ₘ
          Z.map
            (SimplexCategory.subinterval
              (n := p + q + r) (p + q) r (by omega)).op) := by
  have hproj := tensorHom_comp_complexTensorPairProjection
    (𝟙 (alternatingChains X)) (alternatingAlexanderWhitney Y Z)
    p (q + r) (p + q + r) (by omega)
  have hcomp := congrArg
    (fun t =>
      (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r) ≫ t ≫
        (𝟙 ((alternatingChains X).X p) ⊗ₘ
          complexTensorPairProjection (alternatingChains Y) (alternatingChains Z)
            q r (q + r) rfl)) hproj
  calc
    _ = (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r) ≫
        complexTensorPairProjection (alternatingChains X)
          (alternatingChains (Y ⊗ Z)) p (q + r) (p + q + r) (by omega) ≫
        ((((𝟙 (alternatingChains X) :
              alternatingChains X ⟶ alternatingChains X).f p) ⊗ₘ
            (alternatingAlexanderWhitney Y Z).f (q + r)) ≫
          (𝟙 ((alternatingChains X).X p) ⊗ₘ
            complexTensorPairProjection (alternatingChains Y) (alternatingChains Z)
              q r (q + r) rfl)) := by
      simpa only [complexRightTripleProjection, Category.assoc] using hcomp
    _ = _ := by
      simp only [HomologicalComplex.id_f, MonoidalCategory.tensorHom_comp_tensorHom,
        Category.id_comp]
      rw [← Category.assoc,
        alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      rw [alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      simp only [Monoidal.tensorObj_map]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      erw [Category.comp_id]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      rw [← Y.map_comp, ← Z.map_comp]
      simp only [← op_comp]
      rw [aw_middle_right, aw_back_back]
      rfl

def complexLeftTripleProjection
    (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    ((K ⊗ L) ⊗ M).X n ⟶ (K.X p ⊗ L.X q) ⊗ M.X r :=
  complexTensorPairProjection (K ⊗ L) M (p + q) r n (by omega) ≫
    (complexTensorPairProjection K L p q (p + q) rfl ⊗ₘ 𝟙 (M.X r))

@[reassoc (attr := simp)]
lemma complexRightTripleIncl_proj_self (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    HomologicalComplex.mapBifunctor₂₃.ι
        (curriedTensor (ModuleCat ℤ)) (curriedTensor (ModuleCat ℤ)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        p q r n h ≫ complexRightTripleProjection K L M p q r n h = 𝟙 _ := by
  change GradedObject.Monoidal.ιTensorObj₃ K.X L.X M.X p q r n h ≫ _ = _
  rw [GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X M.X
    p q r n h (q + r) rfl]
  let ii : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
    ⟨⟨q, r⟩, by change q + r = q + r; rfl⟩
  let io : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨p, q + r⟩, by change p + (q + r) = n; omega⟩
  change
    (𝟙 (K.X p) ⊗ₘ Sigma.ι (complexTensorFamily L M (q + r)) ii) ≫
      Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
        Sigma.π (complexTensorFamily K (L ⊗ M) n) io ≫
          (𝟙 (K.X p) ⊗ₘ Sigma.π (complexTensorFamily L M (q + r)) ii) = 𝟙 _
  have ho :
      Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
          Sigma.π (complexTensorFamily K (L ⊗ M) n) io =
        𝟙 (K.X p ⊗ (L ⊗ M).X (q + r)) := by
    simpa only [complexTensorFamily] using
      Sigma.ι_π_eq_id (complexTensorFamily K (L ⊗ M) n) io
  dsimp [io, ii, complexTensorFamily] at ho ⊢
  slice_lhs 2 3 => erw [ho]
  slice_lhs 1 2 => erw [Category.comp_id]
  erw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [Category.id_comp]
  erw [Sigma.ι_π_eq_id]
  simp

@[reassoc]
lemma complexRightTripleIncl_proj_ne (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (i j k p q r n : ℕ) (hijk : i + j + k = n)
    (hpqr : p + q + r = n) (hne : (i, j, k) ≠ (p, q, r)) :
    HomologicalComplex.mapBifunctor₂₃.ι
        (curriedTensor (ModuleCat ℤ)) (curriedTensor (ModuleCat ℤ)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        i j k n hijk ≫ complexRightTripleProjection K L M p q r n hpqr = 0 := by
  change GradedObject.Monoidal.ιTensorObj₃ K.X L.X M.X i j k n hijk ≫ _ = 0
  by_cases hip : i = p
  · subst i
    have hs : j + k = q + r := by omega
    have hjk : (j, k) ≠ (q, r) := by
      intro e
      apply hne
      exact congrArg (fun x ↦ (p, x.1, x.2)) e
    rw [GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X M.X
      p j k n hijk (q + r) hs]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
      ⟨⟨j, k⟩, by change j + k = q + r; exact hs⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
      ⟨⟨q, r⟩, by change q + r = q + r; rfl⟩
    let io : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, q + r⟩, by change p + (q + r) = n; omega⟩
    change
      (𝟙 (K.X p) ⊗ₘ Sigma.ι (complexTensorFamily L M (q + r)) iis) ≫
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
          Sigma.π (complexTensorFamily K (L ⊗ M) n) io ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.π (complexTensorFamily L M (q + r)) iit) = 0
    have ho :
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) io ≫
            Sigma.π (complexTensorFamily K (L ⊗ M) n) io =
          𝟙 (K.X p ⊗ (L ⊗ M).X (q + r)) := by
      simpa only [complexTensorFamily] using
        Sigma.ι_π_eq_id (complexTensorFamily K (L ⊗ M) n) io
    dsimp [io, iis, iit, complexTensorFamily] at ho ⊢
    slice_lhs 2 3 => erw [ho]
    slice_lhs 1 2 => erw [Category.comp_id]
    erw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [Category.id_comp]
    have hz :
        Sigma.ι (complexTensorFamily L M (q + r)) iis ≫
            Sigma.π (complexTensorFamily L M (q + r)) iit = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hjk
      exact congrArg Subtype.val e
    erw [hz]
    exact MonoidalPreadditive.whiskerLeft_zero
      (C := ModuleCat ℤ) (X := K.X p)
      (Y := L.X j ⊗ M.X k) (Z := L.X q ⊗ M.X r)
  · rw [GradedObject.Monoidal.ιTensorObj₃_eq K.X L.X M.X
      i j k n hijk (j + k) rfl]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {j + k} } :=
      ⟨⟨j, k⟩, by change j + k = j + k; rfl⟩
    let ios : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨i, j + k⟩, by change i + (j + k) = n; omega⟩
    let iot : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, q + r⟩, by change p + (q + r) = n; omega⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {q + r} } :=
      ⟨⟨q, r⟩, by change q + r = q + r; rfl⟩
    change
      (𝟙 (K.X i) ⊗ₘ Sigma.ι (complexTensorFamily L M (j + k)) iis) ≫
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) ios ≫
          Sigma.π (complexTensorFamily K (L ⊗ M) n) iot ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.π (complexTensorFamily L M (q + r)) iit) = 0
    have hz :
        Sigma.ι (complexTensorFamily K (L ⊗ M) n) ios ≫
            Sigma.π (complexTensorFamily K (L ⊗ M) n) iot = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hip
      exact congrArg (fun x ↦ x.1.1) e
    dsimp [iis, ios, iot, iit, complexTensorFamily] at hz ⊢
    slice_lhs 2 3 => erw [hz]
    slice_lhs 1 2 => erw [comp_zero]
    erw [zero_comp]
    rfl

@[reassoc (attr := simp)]
lemma complexLeftTripleIncl_proj_self (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    HomologicalComplex.mapBifunctor₁₂.ι
        (curriedTensor (ModuleCat ℤ)) (curriedTensor (ModuleCat ℤ)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        p q r n h ≫ complexLeftTripleProjection K L M p q r n h = 𝟙 _ := by
  change GradedObject.Monoidal.ιTensorObj₃' K.X L.X M.X p q r n h ≫ _ = _
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X M.X
    p q r n h (p + q) rfl]
  let ii : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
    ⟨⟨p, q⟩, by change p + q = p + q; rfl⟩
  let io : { x : ℕ × ℕ // x ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨p + q, r⟩, by change p + q + r = n; exact h⟩
  change
    (Sigma.ι (complexTensorFamily K L (p + q)) ii ⊗ₘ 𝟙 (M.X r)) ≫
      Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
        Sigma.π (complexTensorFamily (K ⊗ L) M n) io ≫
          (Sigma.π (complexTensorFamily K L (p + q)) ii ⊗ₘ 𝟙 (M.X r)) = 𝟙 _
  have ho :
      Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
          Sigma.π (complexTensorFamily (K ⊗ L) M n) io =
        𝟙 ((K ⊗ L).X (p + q) ⊗ M.X r) := by
    simpa only [complexTensorFamily] using
      Sigma.ι_π_eq_id (complexTensorFamily (K ⊗ L) M n) io
  dsimp [io, ii, complexTensorFamily] at ho ⊢
  slice_lhs 2 3 => erw [ho]
  slice_lhs 1 2 => erw [Category.comp_id]
  erw [MonoidalCategory.tensorHom_comp_tensorHom]
  erw [Sigma.ι_π_eq_id]
  simp

@[reassoc]
lemma complexLeftTripleIncl_proj_ne (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (i j k p q r n : ℕ) (hijk : i + j + k = n)
    (hpqr : p + q + r = n) (hne : (i, j, k) ≠ (p, q, r)) :
    HomologicalComplex.mapBifunctor₁₂.ι
        (curriedTensor (ModuleCat ℤ)) (curriedTensor (ModuleCat ℤ)) K L M
        (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        i j k n hijk ≫ complexLeftTripleProjection K L M p q r n hpqr = 0 := by
  change GradedObject.Monoidal.ιTensorObj₃' K.X L.X M.X i j k n hijk ≫ _ = 0
  by_cases hkr : k = r
  · subst k
    have hs : i + j = p + q := by omega
    have hij : (i, j) ≠ (p, q) := by
      intro e
      apply hne
      exact congrArg (fun x ↦ (x.1, x.2, r)) e
    rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X M.X
      i j r n hijk (p + q) hs]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
      ⟨⟨i, j⟩, by change i + j = p + q; exact hs⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
      ⟨⟨p, q⟩, by change p + q = p + q; rfl⟩
    let io : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p + q, r⟩, by change p + q + r = n; exact hpqr⟩
    change
      (Sigma.ι (complexTensorFamily K L (p + q)) iis ⊗ₘ 𝟙 (M.X r)) ≫
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
          Sigma.π (complexTensorFamily (K ⊗ L) M n) io ≫
            (Sigma.π (complexTensorFamily K L (p + q)) iit ⊗ₘ 𝟙 (M.X r)) = 0
    have ho :
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) io ≫
            Sigma.π (complexTensorFamily (K ⊗ L) M n) io =
          𝟙 ((K ⊗ L).X (p + q) ⊗ M.X r) := by
      simpa only [complexTensorFamily] using
        Sigma.ι_π_eq_id (complexTensorFamily (K ⊗ L) M n) io
    dsimp [io, iis, iit, complexTensorFamily] at ho ⊢
    slice_lhs 2 3 => erw [ho]
    slice_lhs 1 2 => erw [Category.comp_id]
    erw [MonoidalCategory.tensorHom_comp_tensorHom]
    have hz :
        Sigma.ι (complexTensorFamily K L (p + q)) iis ≫
            Sigma.π (complexTensorFamily K L (p + q)) iit = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hij
      exact congrArg Subtype.val e
    erw [hz]
    exact MonoidalPreadditive.zero_whiskerRight
      (C := ModuleCat ℤ) (X := M.X r)
      (Y := K.X i ⊗ L.X j) (Z := K.X p ⊗ L.X q)
  · rw [GradedObject.Monoidal.ιTensorObj₃'_eq K.X L.X M.X
      i j k n hijk (i + j) rfl]
    let iis : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {i + j} } :=
      ⟨⟨i, j⟩, by change i + j = i + j; rfl⟩
    let ios : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨i + j, k⟩, by change i + j + k = n; exact hijk⟩
    let iot : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p + q, r⟩, by change p + q + r = n; exact hpqr⟩
    let iit : { x : ℕ × ℕ // x ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {p + q} } :=
      ⟨⟨p, q⟩, by change p + q = p + q; rfl⟩
    change
      (Sigma.ι (complexTensorFamily K L (i + j)) iis ⊗ₘ 𝟙 (M.X k)) ≫
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) ios ≫
          Sigma.π (complexTensorFamily (K ⊗ L) M n) iot ≫
            (Sigma.π (complexTensorFamily K L (p + q)) iit ⊗ₘ 𝟙 (M.X r)) = 0
    have hz :
        Sigma.ι (complexTensorFamily (K ⊗ L) M n) ios ≫
            Sigma.π (complexTensorFamily (K ⊗ L) M n) iot = 0 := by
      apply Sigma.ι_π_of_ne
      intro e
      apply hkr
      exact congrArg (fun x ↦ x.1.2) e
    dsimp [iis, ios, iot, iit, complexTensorFamily] at hz ⊢
    slice_lhs 2 3 => erw [hz]
    slice_lhs 1 2 => erw [comp_zero]
    erw [zero_comp]
    rfl

theorem aw_left_iterated_projection (p q r : ℕ) :
    (alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
        (HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
          (𝟙 (alternatingChains Z))).f (p + q + r) ≫
        complexLeftTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl =
      (X.map
            (SimplexCategory.subinterval
              (n := p + q + r) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval
            (n := p + q + r) p q (by omega)).op) ⊗ₘ
        Z.map
          (SimplexCategory.subinterval
            (n := p + q + r) (p + q) r (by omega)).op := by
  have hproj := tensorHom_comp_complexTensorPairProjection
    (alternatingAlexanderWhitney X Y) (𝟙 (alternatingChains Z))
    (p + q) r (p + q + r) (by omega)
  have hcomp := congrArg
    (fun t ↦
      (alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫ t ≫
        (complexTensorPairProjection (alternatingChains X) (alternatingChains Y)
            p q (p + q) rfl ⊗ₘ 𝟙 ((alternatingChains Z).X r))) hproj
  calc
    _ = (alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
        complexTensorPairProjection (alternatingChains (X ⊗ Y))
          (alternatingChains Z) (p + q) r (p + q + r) (by omega) ≫
        ((((alternatingAlexanderWhitney X Y).f (p + q)) ⊗ₘ
            ((𝟙 (alternatingChains Z) :
              alternatingChains Z ⟶ alternatingChains Z).f r)) ≫
          (complexTensorPairProjection (alternatingChains X) (alternatingChains Y)
              p q (p + q) rfl ⊗ₘ 𝟙 ((alternatingChains Z).X r))) := by
      simpa only [complexLeftTripleProjection, Category.assoc] using hcomp
    _ = _ := by
      simp only [HomologicalComplex.id_f,
        MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
      rw [← Category.assoc,
        alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      rw [alternatingAlexanderWhitney_comp_complexTensorPairProjection]
      simp only [Monoidal.tensorObj_map]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      erw [MonoidalCategory.tensorHom_comp_tensorHom]
      erw [Category.comp_id]
      rw [← X.map_comp, ← Y.map_comp]
      simp only [← op_comp]
      rw [aw_front_front, aw_middle_left]
      rfl

theorem complexAssociator_comp_rightTripleProjection
    (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) :
    ((α_ K L M).hom.f n) ≫ complexRightTripleProjection K L M p q r n h =
      complexLeftTripleProjection K L M p q r n h ≫
        (α_ (K.X p) (L.X q) (M.X r)).hom := by
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro i j k hijk
  have hassoc :
      (α_ K L M).hom.f n =
        (HomologicalComplex.mapBifunctorAssociatorX
          (MonoidalCategory.curriedAssociatorNatIso (ModuleCat ℤ)) K L M
          (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) n).hom := rfl
  rw [hassoc, HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  change i + j + k = n at hijk
  by_cases ht : (i, j, k) = (p, q, r)
  · have hi : i = p := congrArg (fun t ↦ t.1) ht
    have hj : j = q := congrArg (fun t ↦ t.2.1) ht
    have hk : k = r := congrArg (fun t ↦ t.2.2) ht
    subst i
    subst j
    subst k
    have hr := complexRightTripleIncl_proj_self K L M p q r n hijk
    have hl := complexLeftTripleIncl_proj_self K L M p q r n hijk
    change _ ≫ complexRightTripleProjection K L M p q r n h = 𝟙 _ at hr
    change _ ≫ complexLeftTripleProjection K L M p q r n h = 𝟙 _ at hl
    slice_lhs 2 3 => erw [hr]
    slice_rhs 1 2 => erw [hl]
    rfl
  · have hr :=
      complexRightTripleIncl_proj_ne K L M i j k p q r n hijk h ht
    have hl :=
      complexLeftTripleIncl_proj_ne K L M i j k p q r n hijk h ht
    change _ ≫ complexRightTripleProjection K L M p q r n h = 0 at hr
    change _ ≫ complexLeftTripleProjection K L M p q r n h = 0 at hl
    slice_lhs 2 3 => erw [hr]
    slice_rhs 1 2 => erw [hl]
    rfl

theorem alternatingAlexanderWhitney_coassociativity_projected
    (p q r : ℕ) :
    (((alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
          (HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z))).f (p + q + r)) ≫
        ((α_ (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z)).hom.f (p + q + r))) ≫
        complexRightTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl =
      ((((alternatingFaceMapComplex (ModuleCat ℤ)).map
            ((α_ X Y Z).hom)).f (p + q + r) ≫
          (alternatingAlexanderWhitney X (Y ⊗ Z)).f (p + q + r)) ≫
        (HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
          (alternatingAlexanderWhitney Y Z)).f (p + q + r)) ≫
        complexRightTripleProjection (alternatingChains X) (alternatingChains Y)
          (alternatingChains Z) p q r (p + q + r) rfl := by
  calc
    _ = (((alternatingAlexanderWhitney (X ⊗ Y) Z).f (p + q + r) ≫
          (HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z))).f (p + q + r)) ≫
          complexLeftTripleProjection (alternatingChains X) (alternatingChains Y)
            (alternatingChains Z) p q r (p + q + r) rfl) ≫
        (α_ ((alternatingChains X).X p) ((alternatingChains Y).X q)
          ((alternatingChains Z).X r)).hom := by
      simp only [Category.assoc]
      rw [complexAssociator_comp_rightTripleProjection]
    _ = ((X.map
              (SimplexCategory.subinterval
                (n := p + q + r) 0 p (by omega)).op ⊗ₘ
            Y.map
              (SimplexCategory.subinterval
                (n := p + q + r) p q (by omega)).op) ⊗ₘ
          Z.map
            (SimplexCategory.subinterval
              (n := p + q + r) (p + q) r (by omega)).op) ≫
        (α_ ((alternatingChains X).X p) ((alternatingChains Y).X q)
          ((alternatingChains Z).X r)).hom := by
      have hleft := congrArg
        (fun t ↦ t ≫
          (α_ ((alternatingChains X).X p) ((alternatingChains Y).X q)
            ((alternatingChains Z).X r)).hom)
        (aw_left_iterated_projection X Y Z p q r)
      simpa only [Category.assoc] using hleft
    _ = _ := by
      erw [MonoidalCategory.associator_naturality]
      have hright := congrArg
        (fun t =>
          (α_ ((alternatingChains X).X (p + q + r))
              ((alternatingChains Y).X (p + q + r))
              ((alternatingChains Z).X (p + q + r))).hom ≫ t)
        (aw_right_iterated_projection X Y Z p q r).symm
      simpa only [Category.assoc, alternatingFaceMapComplex_map_f,
        Monoidal.associator_hom_app] using hright

theorem tensorLeft_complexTensor_hom_ext
    (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (p n : ℕ) {A : ModuleCat.{0} ℤ}
    {f g : A ⟶ K.X p ⊗ (L ⊗ M).X n}
    (h : ∀ (q r : ℕ) (hqr : q + r = n),
      f ≫ (𝟙 (K.X p) ⊗ₘ complexTensorPairProjection L M q r n hqr) =
        g ≫ (𝟙 (K.X p) ⊗ₘ complexTensorPairProjection L M q r n hqr)) :
    f = g := by
  let J : Type := { qr : ℕ × ℕ // qr ∈
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n} }
  letI : Fintype J := Fintype.ofEquiv (Fin (n + 1)) (tensorCutEquiv n)
  let F := complexTensorFamily L M n
  have hinner : ∑ j, Sigma.π F j ≫ Sigma.ι F j = 𝟙 _ := by
    apply Sigma.hom_ext
    intro j
    rw [Preadditive.comp_sum, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [← Category.assoc, Sigma.ι_π_of_ne F hij.symm, zero_comp]
    · simp
  have htensor :
      ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
          (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) = 𝟙 _ := by
    calc
      _ = ∑ j, 𝟙 (K.X p) ⊗ₘ (Sigma.π F j ≫ Sigma.ι F j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
      _ = 𝟙 (K.X p) ⊗ₘ (∑ j, Sigma.π F j ≫ Sigma.ι F j) := by
        change ∑ j, ((curriedTensor (ModuleCat ℤ)).obj (K.X p)).map
            (Sigma.π F j ≫ Sigma.ι F j) = _
        rw [← Functor.map_sum]
        rfl
      _ = _ := by rw [hinner]; simp
  have htensor' :
      ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
          (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) =
        𝟙 (K.X p ⊗ (L ⊗ M).X n) := by
    simpa only [F, complexTensorFamily] using htensor
  have hfg :
      f = g ≫ ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
        (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) := by
    calc
      f = f ≫ 𝟙 (K.X p ⊗ (L ⊗ M).X n) := (Category.comp_id f).symm
      _ = f ≫ ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) := by
        erw [htensor']
        rfl
      _ = ∑ j, f ≫ ((𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j)) := by
        rw [Preadditive.comp_sum]
      _ = ∑ j, g ≫ ((𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j)) := by
        apply Finset.sum_congr rfl
        rintro ⟨⟨q, r⟩, hqr⟩ -
        change q + r = n at hqr
        rw [← Category.assoc]
        erw [h q r hqr]
        erw [Category.assoc]
      _ = g ≫ ∑ j, (𝟙 (K.X p) ⊗ₘ Sigma.π F j) ≫
            (𝟙 (K.X p) ⊗ₘ Sigma.ι F j) := by
        rw [Preadditive.comp_sum]
  erw [htensor'] at hfg
  simpa only [Category.comp_id] using hfg

theorem complexRightTriple_hom_ext
    (K L M : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {A : ModuleCat.{0} ℤ}
    {f g : A ⟶ (K ⊗ (L ⊗ M)).X n}
    (h : ∀ (p q r : ℕ) (hpqr : p + q + r = n),
      f ≫ complexRightTripleProjection K L M p q r n hpqr =
        g ≫ complexRightTripleProjection K L M p q r n hpqr) :
    f = g := by
  let J : Type := { ps : ℕ × ℕ // ps ∈
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n} }
  letI : Fintype J := Fintype.ofEquiv (Fin (n + 1)) (tensorCutEquiv n)
  apply finiteCoproduct_hom_ext (complexTensorFamily K (L ⊗ M) n)
  rintro ⟨⟨p, s⟩, hps⟩
  change p + s = n at hps
  apply tensorLeft_complexTensor_hom_ext K L M p s
  intro q r hqr
  subst s
  have hpqr : p + q + r = n := by omega
  simpa only [complexRightTripleProjection, Category.assoc] using
    h p q r hpqr

theorem alternatingAlexanderWhitney_coassociativity :
    alternatingAlexanderWhitney (X ⊗ Y) Z ≫
          HomologicalComplex.tensorHom (alternatingAlexanderWhitney X Y)
            (𝟙 (alternatingChains Z)) ≫
          (α_ (alternatingChains X) (alternatingChains Y)
            (alternatingChains Z)).hom =
      (alternatingFaceMapComplex (ModuleCat ℤ)).map ((α_ X Y Z).hom) ≫
        alternatingAlexanderWhitney X (Y ⊗ Z) ≫
        HomologicalComplex.tensorHom (𝟙 (alternatingChains X))
          (alternatingAlexanderWhitney Y Z) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply complexRightTriple_hom_ext (alternatingChains X) (alternatingChains Y)
    (alternatingChains Z) n
  intro p q r hpqr
  subst n
  simpa only [HomologicalComplex.comp_f, Category.assoc] using
    alternatingAlexanderWhitney_coassociativity_projected X Y Z p q r


end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
