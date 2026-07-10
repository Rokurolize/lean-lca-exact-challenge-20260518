import LeanLCAExactChallenge.Infinity.DoldKanMonoidal
import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# Alexander--Whitney chain maps

This file starts the explicit Alexander--Whitney construction for simplicial integer modules.
For a cut `p + q = n`, the front `p`-face and back `q`-face give a morphism into the
corresponding summand of the tensor product of alternating face-map complexes. Summing over
all cuts gives the standard degree-`n` Alexander--Whitney formula.

The face identities and cut projections below prove that the degree maps commute with the
alternating differentials. They therefore assemble into a natural chain map, which is then
composed with the normalized Moore inclusion and the `PInfty` retractions. The normalized
tensorator and its unit map are constructed here. Projector compatibility and the two unit laws
are proved in follow-up modules. The coassociativity and normalized transport modules then
complete the oplax package.
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

/-- Maps into a finite coproduct are determined by all canonical projections. -/
theorem finiteCoproduct_hom_ext {C : Type*} [Category* C] [Preadditive C]
    {A : C} {J : Type*} [Finite J] [DecidableEq J]
    (F : J → C) [HasCoproduct F] {f g : A ⟶ ∐ F}
    (h : ∀ j, f ≫ Sigma.π F j = g ≫ Sigma.π F j) : f = g := by
  letI := Fintype.ofFinite J
  have hid : ∑ j, Sigma.π F j ≫ Sigma.ι F j = 𝟙 _ := by
    apply Sigma.hom_ext
    intro j
    rw [Preadditive.comp_sum, Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [← Category.assoc, Sigma.ι_π_of_ne F hij.symm, zero_comp]
    · simp
  rw [← Category.comp_id f, ← Category.comp_id g, ← hid,
    Preadditive.comp_sum, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Category.assoc, h j, Category.assoc]

/-- A finite sum supported at exactly two distinct indices is their sum. -/
theorem fintype_sum_eq_add_two_of_eq_zero
    {I M : Type*} [Fintype I] [AddCommMonoid M]
    (a b : I) (hba : b ≠ a) (f : I → M)
    (hzero : ∀ i, i ≠ a → i ≠ b → f i = 0) :
    ∑ i, f i = f a + f b := by
  classical
  rw [Fintype.sum_eq_add_sum_compl a]
  congr 1
  apply Finset.sum_eq_single b
  · intro i hi hiba
    exact hzero i (by simpa using hi) hiba
  · intro hb
    exfalso
    exact hb (by simpa using hba)

/-- Alternating face-map chains, abbreviated for the tensor-component calculations below. -/
abbrev alternatingChains (X : SimplicialObject (ModuleCat.{0} ℤ)) :=
  (alternatingFaceMapComplex (ModuleCat ℤ)).obj X

/-- The coproduct family underlying degree `n` of the tensor of alternating chains. -/
abbrev tensorCutFamily (X Y : SimplicialObject (ModuleCat.{0} ℤ)) (n : ℕ) :=
  (((((curriedTensor (ModuleCat ℤ)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      (alternatingChains X)).obj (alternatingChains Y)).toGradedObject.mapObjFun
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) n)

/-- Projection from total tensor degree `n` to the component indexed by `i + j = n`. -/
def tensorPairProjection (X Y : SimplicialObject (ModuleCat.{0} ℤ))
    (i j n : ℕ) (h : i + j = n) :
    (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n ⟶
      (alternatingChains X).X i ⊗ (alternatingChains Y).X j :=
  Sigma.π (tensorCutFamily X Y n)
    ⟨⟨i, j⟩, by change i + j = n; exact h⟩

/-- Projection to the component selected by a front cut `p : Fin (n + 1)`. -/
def tensorCutProjection (X Y : SimplicialObject (ModuleCat.{0} ℤ))
    (n : ℕ) (p : Fin (n + 1)) :
    (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n ⟶
      (alternatingChains X).X p ⊗ (alternatingChains Y).X (n - p) :=
  tensorPairProjection X Y p (n - p) n (by omega)

/-- Cuts of `n` are equivalent to the fiber of addition over `n`. -/
def tensorCutEquiv (n : ℕ) :
    Fin (n + 1) ≃
      { pq : ℕ × ℕ // pq ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } where
  toFun p := ⟨(p, n - p), by change p + (n - p) = n; omega⟩
  invFun pq := ⟨pq.1.1, by
    have hpq := pq.2
    change pq.1.1 + pq.1.2 = n at hpq
    omega⟩
  left_inv p := by ext; rfl
  right_inv pq := by
    rcases pq with ⟨⟨p, q⟩, hpq⟩
    change p + q = n at hpq
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      omega

/-- Maps into a total tensor degree are determined by all cut projections. -/
theorem tensorDegree_hom_ext (X Y : SimplicialObject (ModuleCat.{0} ℤ))
    (n : ℕ) {A : ModuleCat.{0} ℤ}
    {f g : A ⟶
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n}
    (h : ∀ p : Fin (n + 1),
      f ≫ tensorCutProjection X Y n p = g ≫ tensorCutProjection X Y n p) :
    f = g := by
  let J : Type := { pq : ℕ × ℕ // pq ∈
    (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) ⁻¹' {n} }
  letI : Fintype J := Fintype.ofEquiv (Fin (n + 1)) (tensorCutEquiv n)
  apply finiteCoproduct_hom_ext _
  rintro ⟨⟨p, q⟩, hpq⟩
  change p + q = n at hpq
  have hp : p < n + 1 := by omega
  have hq : q = n - p := by omega
  subst q
  exact h ⟨p, hp⟩

@[reassoc (attr := simp)]
theorem ιTensorObj_tensorPairProjection_self
    (X Y : SimplicialObject (ModuleCat.{0} ℤ)) (i j n : ℕ) (h : i + j = n) :
    HomologicalComplex.ιMapBifunctor (alternatingChains X) (alternatingChains Y)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i j n h ≫
      tensorPairProjection X Y i j n h = 𝟙 _ := by
  exact Sigma.ι_π_eq_id _ _

@[reassoc]
theorem ιTensorObj_tensorPairProjection_of_ne
    (X Y : SimplicialObject (ModuleCat.{0} ℤ))
    (i j i' j' n : ℕ) (h : i + j = n) (h' : i' + j' = n)
    (hne : (i, j) ≠ (i', j')) :
    HomologicalComplex.ιMapBifunctor (alternatingChains X) (alternatingChains Y)
        (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) i j n h ≫
      tensorPairProjection X Y i' j' n h' = 0 := by
  apply Sigma.ι_π_of_ne
  intro heq
  exact hne (congrArg Subtype.val heq)

/-- The inclusion of the front `p`-face into an `n`-simplex. -/
def alexanderWhitneyFront (n : ℕ) (p : Fin (n + 1)) :
    SimplexCategory.mk (p : ℕ) ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval 0 p (by omega)

/-- The inclusion of the back `(n - p)`-face into an `n`-simplex. -/
def alexanderWhitneyBack (n : ℕ) (p : Fin (n + 1)) :
    SimplexCategory.mk (n - p) ⟶ SimplexCategory.mk n :=
  SimplexCategory.subinterval p (n - p) (by omega)

@[simp]
theorem alexanderWhitneyFront_apply (n : ℕ) (p : Fin (n + 1))
    (i : Fin ((p : ℕ) + 1)) :
    ((alexanderWhitneyFront n p).toOrderHom i).1 = i.1 := by
  rfl

@[simp]
theorem alexanderWhitneyBack_apply (n : ℕ) (p : Fin (n + 1))
    (i : Fin (n - (p : ℕ) + 1)) :
    ((alexanderWhitneyBack n p).toOrderHom i).1 = p + i := by
  simp [alexanderWhitneyBack, SimplexCategory.subinterval, Nat.add_comm]

@[simp]
theorem alexanderWhitneyFront_zero :
    alexanderWhitneyFront 0 0 = 𝟙 (SimplexCategory.mk 0) := by
  apply Subsingleton.elim

@[simp]
theorem alexanderWhitneyBack_zero :
    alexanderWhitneyBack 0 0 = 𝟙 (SimplexCategory.mk 0) := by
  apply Subsingleton.elim

/-- A face at or before the cut acts on the front simplex. -/
theorem alexanderWhitneyFront_face (n p i : ℕ) (hp : p ≤ n) (hi : i ≤ p) :
    SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + 2)) ≫
        alexanderWhitneyFront (n + 1) ⟨p + 1, by omega⟩ =
      alexanderWhitneyFront n ⟨p, by omega⟩ ≫
        SimplexCategory.δ (⟨i, by omega⟩ : Fin (n + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < p + 1 at hk
  change
    (Fin.succAbove (⟨i, by omega⟩ : Fin (p + 2)) ⟨k, hk⟩).val =
      (Fin.succAbove (⟨i, by omega⟩ : Fin (n + 2))
        (⟨k, by omega⟩ : Fin (n + 1))).val
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- A face on a back subinterval is the corresponding offset face of the whole simplex. -/
theorem alexanderWhitneyBack_face (p q : ℕ) (i : Fin (q + 2)) :
    SimplexCategory.δ i ≫
        SimplexCategory.subinterval p (q + 1) (by omega) =
      SimplexCategory.subinterval p q (by omega) ≫
        SimplexCategory.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < q + 1 at hk
  change
    (Fin.succAbove i ⟨k, hk⟩).val + p =
      (Fin.succAbove (⟨p + i, by omega⟩ : Fin (p + q + 2))
        (⟨k + p, by omega⟩ : Fin (p + q + 1))).val
  rcases i with ⟨i, hi⟩
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- Removing a vertex at or before the cut shifts the unchanged back interval. -/
theorem alexanderWhitneyBack_early_face (p q i : ℕ) (hi : i ≤ p) :
    SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega) =
      SimplexCategory.subinterval (n := p + q) p q (by omega) ≫
        SimplexCategory.δ (⟨i, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < q + 1 at hk
  change k + (p + 1) =
    (Fin.succAbove (⟨i, by omega⟩ : Fin (p + q + 2))
      (⟨k + p, by omega⟩ : Fin (p + q + 1))).val
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- Removing a vertex strictly after the cut leaves the front interval unchanged. -/
theorem alexanderWhitneyFront_late_face (p q : ℕ)
    (i : Fin (q + 2)) (hi : 0 < i) :
    SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega) =
      SimplexCategory.subinterval (n := p + q) 0 p (by omega) ≫
        SimplexCategory.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < p + 1 at hk
  change k =
    (Fin.succAbove (⟨p + i, by omega⟩ : Fin (p + q + 2))
      (⟨k, by omega⟩ : Fin (p + q + 1))).val
  simp only [Fin.succAbove]
  split_ifs <;> simp_all
  all_goals omega

/-- The last front face is the shorter front subinterval. -/
theorem alexanderWhitneyFront_last (p q : ℕ) :
    SimplexCategory.δ (Fin.last (p + 1)) ≫
        SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega) =
      SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < p + 1 at hk
  change (Fin.succAbove (Fin.last (p + 1)) ⟨k, hk⟩).val = k
  exact congrArg Fin.val
    (Fin.succAbove_last_apply (⟨k, hk⟩ : Fin (p + 1)))

/-- The zeroth back face is the back subinterval beginning one vertex later. -/
theorem alexanderWhitneyBack_zero_face (p q : ℕ) :
    SimplexCategory.δ (0 : Fin (q + 2)) ≫
        SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega) =
      SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega) := by
  ext k
  rcases k with ⟨k, hk⟩
  change k < q + 1 at hk
  change (Fin.succAbove (0 : Fin (q + 2)) ⟨k, hk⟩).val + p = k + (p + 1)
  simp [Fin.succAbove]
  omega

/-- Tensor maps along definitionally equal subinterval lengths are heterogeneously equal.
This isolates the dependent proof transport needed when normalizing a cut subtraction. -/
theorem tensor_map_subinterval_heq
    {A B : ModuleCat.{0} ℤ} (f : A ⟶ B)
    (Y : SimplicialObject (ModuleCat.{0} ℤ))
    (n a b b' : ℕ) (h : b = b')
    (hab : a + b ≤ n) (hab' : a + b' ≤ n) :
    (f ⊗ₘ Y.map (SimplexCategory.subinterval (n := n) a b hab).op) ≍
      (f ⊗ₘ Y.map (SimplexCategory.subinterval (n := n) a b' hab').op) := by
  subst b'
  rfl

variable (X Y : SimplicialObject (ModuleCat.{0} ℤ))

/-- An early face of the tensor simplex is the corresponding front-factor face of the
Alexander--Whitney summand; the back factor is unchanged after shifting the cut. -/
theorem alexanderWhitneyEarlyFace_tensor (p q i : ℕ) (hi : i ≤ p) :
    (X ⊗ Y).δ (⟨i, by omega⟩ : Fin (p + q + 2)) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
        (X.δ (⟨i, by omega⟩ : Fin (p + 2)) ⊗ₘ 𝟙 _) := by
  have hx :
      X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ≫
          X.δ (⟨i, by omega⟩ : Fin (p + 2)) =
        X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ≫
          X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op := by
    simpa only [op_comp, Functor.map_comp] using congrArg (fun f => X.map f.op)
      (alexanderWhitneyFront_face (p + q) p i (by omega) hi)
  have hy :
      Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op =
        Y.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ≫
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op := by
    simpa only [op_comp, Functor.map_comp] using congrArg (fun f => Y.map f.op)
      (alexanderWhitneyBack_early_face p q i hi)
  change
    (X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫ _ = _
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [← hx, ← hy, Category.comp_id]

/-- A late face of the tensor simplex is the corresponding back-factor face of the
Alexander--Whitney summand; the front factor is unchanged. -/
theorem alexanderWhitneyLateFace_tensor (p q : ℕ)
    (i : Fin (q + 2)) (hi : 0 < i) :
    (X ⊗ Y).δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 _ ⊗ₘ Y.δ i) := by
  have hx :
      X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op =
        X.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ≫
          X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op := by
    simpa only [op_comp, Functor.map_comp] using congrArg (fun f => X.map f.op)
      (alexanderWhitneyFront_late_face p q i hi)
  have hy :
      Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op ≫
          Y.δ i =
        Y.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ≫
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op := by
    simpa only [op_comp, Functor.map_comp] using congrArg (fun f => Y.map f.op)
      (alexanderWhitneyBack_face p q i)
  change
    (X.δ (⟨p + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨p + i, by omega⟩ : Fin (p + q + 2))) ≫ _ = _
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [← hx, ← hy, Category.comp_id]

/-- The last front-factor face and the zeroth back-factor face yield the same unsigned
Alexander--Whitney boundary morphism. -/
theorem alexanderWhitneyBoundary_tensor (p q : ℕ) :
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
        (X.δ (Fin.last (p + 1)) ⊗ₘ 𝟙 _) =
      (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 _ ⊗ₘ Y.δ (0 : Fin (q + 2))) := by
  have hx :
      X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ≫
          X.δ (Fin.last (p + 1)) =
        X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op := by
    simpa only [op_comp, Functor.map_comp] using congrArg (fun f => X.map f.op)
      (alexanderWhitneyFront_last p q)
  have hy :
      Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op ≫
          Y.δ (0 : Fin (q + 2)) =
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op := by
    simpa only [op_comp, Functor.map_comp] using congrArg (fun f => Y.map f.op)
      (alexanderWhitneyBack_zero_face p q)
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  rw [hx, hy]
  simp only [Category.comp_id]

/-- The internal first-factor faces of the front-adjacent source cut agree with the early
diagonal faces of the tensor simplex. -/
theorem alexanderWhitneyFirstInternal_tensor (p q : ℕ) (i : Fin (p + 1)) :
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
        (X.δ i.castSucc ⊗ₘ 𝟙 ((alternatingChains Y).X q)) =
      (X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
          Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
  simpa only using (alexanderWhitneyEarlyFace_tensor X Y p q i (by omega)).symm

/-- The internal second-factor faces of the back-adjacent source cut agree with the late
diagonal faces of the tensor simplex. -/
theorem alexanderWhitneySecondInternal_tensor (p q : ℕ) (i : Fin (q + 1)) :
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 ((alternatingChains X).X p) ⊗ₘ Y.δ i.succ) =
      (X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
          Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
  have hface :
      (⟨p + (i.succ : ℕ), by omega⟩ : Fin (p + q + 2)) =
        ⟨p + 1 + (i : ℕ), by omega⟩ := by
    ext
    simp
    omega
  simpa only [hface] using
    (alexanderWhitneyLateFace_tensor X Y p q i.succ (by simp)).symm

/-- Multiplying two alternating signs adds their exponents. -/
theorem neg_one_pow_smul_smul {A B : ModuleCat.{0} ℤ} (p i : ℕ) (f : A ⟶ B) :
    ((-1 : ℤ) ^ p) • (((-1 : ℤ) ^ i) • f) =
      ((-1 : ℤ) ^ (p + i)) • f := by
  rw [smul_smul, pow_add]

/-- The second-factor tensor sign and the positive-index face sign combine to the global
late-face sign. -/
theorem neg_one_pow_succ_smul_smul {A B : ModuleCat.{0} ℤ}
    (p q : ℕ) (i : Fin (q + 1)) (f : A ⟶ B) :
    ((-1 : ℤ) ^ p) • (((-1 : ℤ) ^ (i.succ : ℕ)) • f) =
      ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) • f := by
  rw [smul_smul, ← pow_add]
  congr 2
  simp
  omega

/-- The last front-face sign cancels the signed zeroth back-face sign. -/
theorem neg_one_pow_boundary_cancel {A B : ModuleCat.{0} ℤ} (p : ℕ) (f : A ⟶ B) :
    ((-1 : ℤ) ^ (p + 1)) • f + ((-1 : ℤ) ^ p) • f = 0 := by
  simp [pow_succ]

/-- Split a sum over all faces at the Alexander--Whitney cut. -/
theorem sum_faces_split {A B : ModuleCat.{0} ℤ} (p q : ℕ)
    (f : Fin (p + q + 2) → (A ⟶ B)) :
    (∑ i : Fin (p + q + 2), f i) =
      (∑ i : Fin (p + 1), f ⟨i, by omega⟩) +
        ∑ i : Fin (q + 1), f ⟨p + 1 + i, by omega⟩ := by
  let h : (p + 1) + (q + 1) = p + q + 2 := by omega
  let g : Fin ((p + 1) + (q + 1)) → (A ⟶ B) := fun i => f (Fin.cast h i)
  have hsum := Fin.sum_univ_add g
  have hleft : (∑ i, g i) = ∑ i, f i := by
    exact Fintype.sum_equiv (Fin.castOrderIso h).toEquiv g f (fun i => rfl)
  rw [← hleft]
  simpa only [g, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] using hsum

/-- Split an alternating face sum into its early and late families at the cut. -/
theorem alternating_sum_faces_split {A B : ModuleCat.{0} ℤ} (p q : ℕ)
    (f : Fin (p + q + 2) → (A ⟶ B)) :
    (∑ i : Fin (p + q + 2), ((-1 : ℤ) ^ (i : ℕ)) • f i) =
      (∑ i : Fin (p + 1), ((-1 : ℤ) ^ (i : ℕ)) • f ⟨i, by omega⟩) +
        ∑ i : Fin (q + 1),
          ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) • f ⟨p + 1 + i, by omega⟩ := by
  simpa only using sum_faces_split p q
    (fun i : Fin (p + q + 2) => ((-1 : ℤ) ^ (i : ℕ)) • f i)

/-- Expand the first alternating differential after tensoring with an identity. -/
theorem first_alternating_d_tensor_expand (p q : ℕ) :
    ((curriedTensor (ModuleCat ℤ)).map ((alternatingChains X).d (p + 1) p)).app
        ((alternatingChains Y).X q) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (X.δ i ⊗ₘ 𝟙 ((alternatingChains Y).X q)) := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  change
    ((∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • X.δ i) ⊗ₘ
      𝟙 ((alternatingChains Y).X q)) = _
  rw [CategoryTheory.sum_tensor]
  apply Finset.sum_congr rfl
  intro i _
  simp only [alternatingFaceMapComplex_obj_X, Int.reduceNeg, tensorHom_id]
  exact (tensorRight ((alternatingChains Y).X q)).map_zsmul

/-- Expand the second alternating differential after tensoring with an identity. -/
theorem second_alternating_d_tensor_expand (p q : ℕ) :
    ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
        ((alternatingChains Y).d (q + 1) q) =
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        (𝟙 ((alternatingChains X).X p) ⊗ₘ Y.δ i) := by
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  change
    (𝟙 ((alternatingChains X).X p) ⊗ₘ
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Y.δ i) = _
  rw [CategoryTheory.tensor_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [alternatingFaceMapComplex_obj_X, Int.reduceNeg, id_tensorHom]
  exact (tensorLeft ((alternatingChains X).X p)).map_zsmul

/-- The `p + (n - p) = n` summand of the unnormalized Alexander--Whitney map. -/
def alternatingAlexanderWhitneySummand (n : ℕ) (p : Fin (n + 1)) :
    (X ⊗ Y).obj (op (SimplexCategory.mk n)) ⟶
      (HomologicalComplex.tensorObj
        ((alternatingFaceMapComplex (ModuleCat ℤ)).obj X)
        ((alternatingFaceMapComplex (ModuleCat ℤ)).obj Y)).X n :=
  (X.map (alexanderWhitneyFront n p).op ⊗ₘ
      Y.map (alexanderWhitneyBack n p).op) ≫
    HomologicalComplex.ιTensorObj
      ((alternatingFaceMapComplex (ModuleCat ℤ)).obj X)
      ((alternatingFaceMapComplex (ModuleCat ℤ)).obj Y)
      p (n - p) n (by omega)

/-- The degree-`n` Alexander--Whitney formula on alternating face-map complexes. -/
def alternatingAlexanderWhitneyDegree (n : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat ℤ)).obj (X ⊗ Y)).X n ⟶
      (HomologicalComplex.tensorObj
        ((alternatingFaceMapComplex (ModuleCat ℤ)).obj X)
        ((alternatingFaceMapComplex (ModuleCat ℤ)).obj Y)).X n :=
  ∑ p : Fin (n + 1), alternatingAlexanderWhitneySummand X Y n p

/-- Normalize the front-adjacent Alexander--Whitney summand to the exact pair `(p+1,q)`. -/
theorem first_summand_eq_pair (p q : ℕ) :
    alternatingAlexanderWhitneySummand X Y (q + p + 1) ⟨p + 1, by omega⟩ =
      (X.map
            (SimplexCategory.subinterval
              (n := q + p + 1) 0 (p + 1) (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval
              (n := q + p + 1) (p + 1) q (by omega)).op) ≫
        HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) := by
  unfold alternatingAlexanderWhitneySummand
  simp only [alexanderWhitneyFront, alexanderWhitneyBack]
  let iraw : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p + 1, q + p + 1 - (p + 1)⟩, by
      change p + 1 + (q + p + 1 - (p + 1)) = q + p + 1
      omega⟩
  let iexact : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p + 1, q⟩, by change p + 1 + q = q + p + 1; omega⟩
  change _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iraw =
    _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iexact
  have hiraw : iraw = iexact := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [iraw, iexact]
      omega
  rw [← Sigma.eqToHom_comp_ι (tensorCutFamily X Y (q + p + 1)) hiraw]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply eq_of_heq
  apply (comp_eqToHom_heq _ _).trans
  apply tensor_map_subinterval_heq
  omega

/-- Normalize the back-adjacent Alexander--Whitney summand to the exact pair `(p,q+1)`. -/
theorem second_summand_eq_pair (p q : ℕ) :
    alternatingAlexanderWhitneySummand X Y (q + p + 1) ⟨p, by omega⟩ =
      (X.map
            (SimplexCategory.subinterval
              (n := q + p + 1) 0 p (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval
              (n := q + p + 1) p (q + 1) (by omega)).op) ≫
        HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) := by
  unfold alternatingAlexanderWhitneySummand
  simp only [alexanderWhitneyFront, alexanderWhitneyBack]
  let iraw : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p, q + p + 1 - p⟩, by
      change p + (q + p + 1 - p) = q + p + 1
      omega⟩
  let iexact : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {q + p + 1} } :=
    ⟨⟨p, q + 1⟩, by change p + (q + 1) = q + p + 1; omega⟩
  change _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iraw =
    _ ≫ Sigma.ι (tensorCutFamily X Y (q + p + 1)) iexact
  have hiraw : iraw = iexact := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [iraw, iexact]
      omega
  rw [← Sigma.eqToHom_comp_ι (tensorCutFamily X Y (q + p + 1)) hiraw]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply eq_of_heq
  apply (comp_eqToHom_heq _ _).trans
  apply tensor_map_subinterval_heq
  omega

@[simp]
theorem alternatingAlexanderWhitneyDegree_zero :
    alternatingAlexanderWhitneyDegree X Y 0 =
      HomologicalComplex.ιTensorObj
        ((alternatingFaceMapComplex (ModuleCat ℤ)).obj X)
        ((alternatingFaceMapComplex (ModuleCat ℤ)).obj Y)
        0 0 0 rfl := by
  simp [alternatingAlexanderWhitneyDegree, alternatingAlexanderWhitneySummand]

/-- Projecting the degreewise Alexander--Whitney sum to a cut recovers exactly its summand. -/
theorem alternatingAlexanderWhitneyDegree_comp_projection
    (n : ℕ) (p : Fin (n + 1)) :
    alternatingAlexanderWhitneyDegree X Y n ≫ tensorCutProjection X Y n p =
      X.map (alexanderWhitneyFront n p).op ⊗ₘ
        Y.map (alexanderWhitneyBack n p).op := by
  rw [alternatingAlexanderWhitneyDegree, Preadditive.sum_comp,
    Finset.sum_eq_single p]
  · simp only [alternatingAlexanderWhitneySummand]
    let ip : { pq // pq ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, n - p⟩, by change p + (n - p) = n; omega⟩
    change _ ≫
      (Sigma.ι (tensorCutFamily X Y n) ip ≫
        Sigma.π (tensorCutFamily X Y n) ip) = _
    rw [Sigma.ι_π_eq_id, Category.comp_id]
  · intro q _ hqp
    simp only [alternatingAlexanderWhitneySummand]
    let iq : { ij // ij ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨q, n - q⟩, by change q + (n - q) = n; omega⟩
    let ip : { ij // ij ∈
        (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ)) ⁻¹' {n} } :=
      ⟨⟨p, n - p⟩, by change p + (n - p) = n; omega⟩
    change _ ≫
      (Sigma.ι (tensorCutFamily X Y n) iq ≫
        Sigma.π (tensorCutFamily X Y n) ip) = 0
    rw [Sigma.ι_π_of_ne, comp_zero]
    intro h
    exact hqp (Fin.ext (congrArg (fun z => z.1.1) h))
  · simp

/-- The first-factor part of the total differential lands in the preceding front cut.
The second-factor part has a different cut and vanishes after projection. -/
theorem first_inclusion_d_comp_projection (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        (p + 1) q (q + p + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) =
    ((curriedTensor (ModuleCat ℤ)).map
      ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) := by
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) (p + 1) q (by change p + 1 + q = q + p + 1; omega)
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) (p + 1) q (by change p + 1 + q = q + p + 1; omega)
  have hD₁assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₁
  have hD₂assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₂
  have hD₁assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (p + 1) q (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    simpa only using hD₁assoc
  have hD₂assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (p + 1) q (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    simpa only using hD₂assoc
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, hD₁assoc', hD₂assoc']
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
    (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
    q (q + p) (by change p + q = q + p; omega)]
  have heps₁ : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p + 1, q) = 1 := rfl
  simp only [heps₁, one_smul, Category.assoc,
    ιTensorObj_tensorPairProjection_self]
  obtain rfl | q := q
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _
      (p + 1) 0 (0 + p) (by simp [ComplexShape.down])]
    rw [zero_comp]
    simpa only [Category.comp_id] using
      (add_zero (((curriedTensor (ModuleCat ℤ)).map
        ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X 0)))
  · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (p + 1)
      (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down])
      (q + 1 + p) (by change p + 1 + q = q + 1 + p; omega)]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [ιTensorObj_tensorPairProjection_of_ne X Y
      (p + 1) q p (q + 1) (q + 1 + p)
      (by omega) (by omega) (by
        intro h
        exact Nat.succ_ne_self p (congrArg Prod.fst h))]
    rw [comp_zero, smul_zero]
    simpa only [Category.comp_id] using
      (add_zero (((curriedTensor (ModuleCat ℤ)).map
        ((alternatingChains X).d (p + 1) p)).app
          ((alternatingChains Y).X (q + 1))))

/-- The second-factor part of the total differential lands in the preceding back cut,
with the tensor-complex sign determined by the first degree. The first-factor part has a
different cut and vanishes after projection. -/
theorem second_inclusion_d_comp_projection (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        p (q + 1) (q + p + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) =
    ((-1 : ℤ) ^ p) •
      ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
        ((alternatingChains Y).d (q + 1) q) := by
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) p (q + 1) (by change p + (q + 1) = q + p + 1; omega)
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) p (q + 1) (by change p + (q + 1) = q + p + 1; omega)
  have hD₁assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₁
  have hD₂assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₂
  have hD₁assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          p (q + 1) (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    simpa only using hD₁assoc
  have hD₂assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) ≫
        HomologicalComplex.mapBifunctor.D₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          p (q + 1) (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    simpa only using hD₂assoc
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, hD₁assoc', hD₂assoc']
  rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
    (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down])
    (q + p) (by change p + q = q + p; omega)]
  have heps₂ : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q + 1) = (-1 : ℤˣ) ^ p := rfl
  simp only [Linear.units_smul_comp, heps₂, Category.assoc,
    ιTensorObj_tensorPairProjection_self]
  rw [Units.smul_def]
  change _ + ((-1 : ℤ) ^ p) • _ = _
  obtain rfl | p := p
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _
      0 (q + 1) (q + 0) (by simp [ComplexShape.down])]
    rw [zero_comp]
    change 0 + ((-1 : ℤ) ^ 0) •
        (((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X 0)).map
          ((alternatingChains Y).d (q + 1) q) ≫ 𝟙 _) =
      ((-1 : ℤ) ^ 0) •
        ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X 0)).map
          ((alternatingChains Y).d (q + 1) q)
    rw [Category.comp_id, zero_add]
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
      (q + 1) (q + (p + 1)) (by change p + (q + 1) = q + (p + 1); omega)]
    simp only [Linear.units_smul_comp, Category.assoc]
    rw [ιTensorObj_tensorPairProjection_of_ne X Y
      p (q + 1) (p + 1) q (q + (p + 1))
      (by omega) (by omega) (by
        intro h
        exact Nat.succ_ne_self p (congrArg Prod.fst h).symm)]
    rw [comp_zero, smul_zero]
    change 0 + ((-1 : ℤ) ^ (p + 1)) •
        (((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X (p + 1))).map
          ((alternatingChains Y).d (q + 1) q) ≫ 𝟙 _) =
      ((-1 : ℤ) ^ (p + 1)) •
        ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X (p + 1))).map
          ((alternatingChains Y).d (q + 1) q)
    rw [Category.comp_id, zero_add]

/-- A source cut contributes to a target cut after one total differential only when it is
obtained by increasing exactly one coordinate of the target cut. -/
theorem nonadjacent_inclusion_d_comp_projection
    (i j p q : ℕ) (hij : i + j = q + p + 1)
    (hfirst : (i, j) ≠ (p + 1, q))
    (hsecond : (i, j) ≠ (p, q + 1)) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (q + p + 1) hij ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) = 0 := by
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) i j hij
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := alternatingChains X) (K₂ := alternatingChains Y)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (q + p + 1) (q + p) i j hij
  have hD₁assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₁
  have hD₂assoc := congrArg
    (fun t => t ≫ tensorPairProjection X Y p q (q + p) (by omega)) hD₂
  have hD₁assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j (q + p + 1) hij ≫
        HomologicalComplex.mapBifunctor.D₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          i j (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    simpa only using hD₁assoc
  have hD₂assoc' :
      (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j (q + p + 1) hij ≫
        HomologicalComplex.mapBifunctor.D₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          (q + p + 1) (q + p)) ≫
          tensorPairProjection X Y p q (q + p) (by omega) =
        HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          i j (q + p) ≫
            tensorPairProjection X Y p q (q + p) (by omega) := by
    simpa only using hD₂assoc
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, hD₁assoc', hD₂assoc']
  have hd₁ :
      HomologicalComplex.mapBifunctor.d₁ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          i j (q + p) ≫
        tensorPairProjection X Y p q (q + p) (by omega) = 0 := by
    obtain rfl | i := i
    · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _
        0 j (q + p) (by simp [ComplexShape.down])]
      rw [zero_comp]
    · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.down ℕ).Rel (i + 1) i by simp [ComplexShape.down])
        j (q + p) (by change i + j = q + p; omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTensorObj_tensorPairProjection_of_ne X Y
        i j p q (q + p) (by omega) (by omega) (by
          intro h
          apply hfirst
          have hi := congrArg Prod.fst h
          have hj := congrArg Prod.snd h
          simp only at hi hj
          exact Prod.ext (by omega) hj)]
      rw [comp_zero, smul_zero]
  have hd₂ :
      HomologicalComplex.mapBifunctor.d₂ (alternatingChains X) (alternatingChains Y)
          (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ)
          i j (q + p) ≫
        tensorPairProjection X Y p q (q + p) (by omega) = 0 := by
    obtain rfl | j := j
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _
        i 0 (q + p) (by simp [ComplexShape.down])]
      rw [zero_comp]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ i
        (show (ComplexShape.down ℕ).Rel (j + 1) j by simp [ComplexShape.down])
        (q + p) (by change i + j = q + p; omega)]
      simp only [Linear.units_smul_comp, Category.assoc]
      rw [ιTensorObj_tensorPairProjection_of_ne X Y
        i j p q (q + p) (by omega) (by omega) (by
          intro h
          apply hsecond
          have hi := congrArg Prod.fst h
          have hj := congrArg Prod.snd h
          simp only at hi hj
          exact Prod.ext hi (by omega))]
      rw [comp_zero, smul_zero]
  rw [hd₁, hd₂]
  change (0 : ((alternatingChains X).X i ⊗ (alternatingChains Y).X j) ⟶
    ((alternatingChains X).X p ⊗ (alternatingChains Y).X q)) + 0 = 0
  exact add_zero 0

/-- After projecting the target total degree to `(p,q)`, only the two adjacent source cuts
of the Alexander--Whitney sum survive. -/
theorem alternatingAlexanderWhitneyDegree_d_comp_projection (p q : ℕ) :
    (alternatingAlexanderWhitneyDegree X Y (q + p + 1) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (q + p + 1) (q + p)) ≫
      tensorPairProjection X Y p q (q + p) (by omega) =
    (X.map
          (SimplexCategory.subinterval (n := q + p + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := q + p + 1) (p + 1) q (by omega)).op) ≫
      ((curriedTensor (ModuleCat ℤ)).map
        ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) +
    (X.map (SimplexCategory.subinterval (n := q + p + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := q + p + 1) p (q + 1) (by omega)).op) ≫
      (((-1 : ℤ) ^ p) •
        ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
          ((alternatingChains Y).d (q + 1) q)) := by
  rw [alternatingAlexanderWhitneyDegree]
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  let a : Fin (q + p + 2) := ⟨p + 1, by omega⟩
  let b : Fin (q + p + 2) := ⟨p, by omega⟩
  rw [fintype_sum_eq_add_two_of_eq_zero a b (by
    intro h
    exact Nat.succ_ne_self p (congrArg Fin.val h).symm)]
  · dsimp only [a, b]
    congr 1
    · rw [first_summand_eq_pair]
      have h := congrArg
        (fun t =>
          (X.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) 0 (p + 1) (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) (p + 1) q (by omega)).op) ≫ t)
        (first_inclusion_d_comp_projection X Y p q)
      simpa only [Category.assoc] using h
    · rw [second_summand_eq_pair]
      have h := congrArg
        (fun t =>
          (X.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) 0 p (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval
                  (n := q + p + 1) p (q + 1) (by omega)).op) ≫ t)
        (second_inclusion_d_comp_projection X Y p q)
      simpa only [Category.assoc] using h
  · intro r hra hrb
    simp only [alternatingAlexanderWhitneySummand, Category.assoc]
    have hnon := nonadjacent_inclusion_d_comp_projection X Y
      r (q + p + 1 - r) p q (by omega) (by
        intro hpair
        apply hra
        apply Fin.ext
        exact congrArg Prod.fst hpair) (by
        intro hpair
        apply hrb
        apply Fin.ext
        exact congrArg Prod.fst hpair)
    have hassoc := congrArg
      (fun t =>
        (X.map (alexanderWhitneyFront (q + p + 1) r).op ⊗ₘ
          Y.map (alexanderWhitneyBack (q + p + 1) r).op) ≫ t) hnon
    simpa only [Category.assoc, comp_zero] using hassoc

/-- Expand the front-adjacent contribution into its internal faces and last boundary face. -/
theorem first_factor_faces_expansion (p q : ℕ) :
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
      ((curriedTensor (ModuleCat ℤ)).map
        ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) =
    (∑ i : Fin (p + 1), ((-1 : ℤ) ^ (i : ℕ)) •
      ((X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
          Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op))) +
      ((-1 : ℤ) ^ (p + 1)) •
        ((X.map
              (SimplexCategory.subinterval
                (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
            Y.map
              (SimplexCategory.subinterval
                (n := p + q + 1) (p + 1) q (by omega)).op) ≫
          (X.δ (Fin.last (p + 1)) ⊗ₘ
            𝟙 (Y.obj (Opposite.op (SimplexCategory.mk q))))) := by
  let front :=
    X.map (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
      Y.map
        (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op
  change front ≫ _ = _
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  have hmap := Functor.map_sum (curriedTensor (ModuleCat ℤ))
    (fun i : Fin (p + 2) => ((-1 : ℤ) ^ (i : ℕ)) • X.δ i) Finset.univ
  erw [hmap]
  rw [NatTrans.app_sum]
  have hcomp := Preadditive.comp_sum Finset.univ front
    (fun i : Fin (p + 2) =>
      ((curriedTensor (ModuleCat ℤ)).map
        (((-1 : ℤ) ^ (i : ℕ)) • X.δ i)).app ((alternatingChains Y).X q))
  erw [hcomp]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Functor.map_zsmul, NatTrans.app_zsmul]
    simp only [Fin.val_castSucc]
    have hface :
        front ≫
            ((curriedTensor (ModuleCat ℤ)).map (X.δ i.castSucc)).app
              ((alternatingChains Y).X q) =
          (X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
              Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
      simpa only [front, curriedTensor_map_app, ← tensorHom_id] using
        alexanderWhitneyFirstInternal_tensor X Y p q i
    calc
      _ = ((-1 : ℤ) ^ (i : ℕ)) •
          (front ≫ ((curriedTensor (ModuleCat ℤ)).map (X.δ i.castSucc)).app
            ((alternatingChains Y).X q)) :=
        Preadditive.comp_zsmul _ _ _
      _ = ((-1 : ℤ) ^ (i : ℕ)) • _ := congrArg _ hface
  · rw [Functor.map_zsmul, NatTrans.app_zsmul]
    change front ≫ (((-1 : ℤ) ^ (p + 1)) • _) =
      ((-1 : ℤ) ^ (p + 1)) • (front ≫ _)
    exact Preadditive.comp_zsmul _ _ _

/-- Expand the back-adjacent contribution into its zeroth boundary face and internal faces. -/
theorem second_factor_faces_expansion (p q : ℕ) :
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
      (((-1 : ℤ) ^ p) •
        ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
          ((alternatingChains Y).d (q + 1) q)) =
    ((-1 : ℤ) ^ p) •
      ((X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
        (𝟙 (X.obj (Opposite.op (SimplexCategory.mk p))) ⊗ₘ
          Y.δ (0 : Fin (q + 2)))) +
      ∑ i : Fin (q + 1), ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) •
        ((X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
            Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
          (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
            Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op)) := by
  let back :=
    X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
      Y.map
        (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op
  change back ≫ (((-1 : ℤ) ^ p) • _) = _
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  have hmap := Functor.map_sum
    ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p))
    (fun i : Fin (q + 2) => ((-1 : ℤ) ^ (i : ℕ)) • Y.δ i) Finset.univ
  erw [hmap]
  have houter := Preadditive.comp_zsmul back
    ((∑ i : Fin (q + 2),
      ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
        (((-1 : ℤ) ^ (i : ℕ)) • Y.δ i))) ((-1 : ℤ) ^ p)
  erw [houter]
  have hcomp := Preadditive.comp_sum Finset.univ back
    (fun i : Fin (q + 2) =>
      ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
        (((-1 : ℤ) ^ (i : ℕ)) • Y.δ i))
  erw [hcomp]
  rw [Fin.sum_univ_succ, smul_add]
  congr 1
  · rw [Functor.map_zsmul]
    simp only [Fin.val_zero, pow_zero, one_smul]
    congr 1
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Functor.map_zsmul]
    have hface :
        back ≫
            ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
              (Y.δ i.succ) =
          (X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
              Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) := by
      simpa only [back, curriedTensor_obj_map, ← id_tensorHom] using
        alexanderWhitneySecondInternal_tensor X Y p q i
    calc
      ((-1 : ℤ) ^ p) •
          (back ≫ (((-1 : ℤ) ^ (i.succ : ℕ)) • _)) =
        ((-1 : ℤ) ^ p) •
          (((-1 : ℤ) ^ (i.succ : ℕ)) • (back ≫ _)) := by
            rw [Preadditive.comp_zsmul]
      _ = ((-1 : ℤ) ^ p) •
          (((-1 : ℤ) ^ (i.succ : ℕ)) • _) :=
        congrArg _ (congrArg _ hface)
      _ = ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) • _ :=
        neg_one_pow_succ_smul_smul p q i _

/-- The alternating differential satisfies the Alexander--Whitney cut formula. -/
theorem alternating_d_comp_alexanderWhitney_cut (p q : ℕ) :
    (alternatingChains (X ⊗ Y)).d (p + q + 1) (p + q) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (X.map
            (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
          ((curriedTensor (ModuleCat ℤ)).map
            ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) +
        ((-1 : ℤ) ^ p) •
          ((X.map
                (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval (n := p + q + 1) p (q + 1)
                  (by omega)).op) ≫
            ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
              ((alternatingChains Y).d (q + 1) q)) := by
  rw [← Preadditive.comp_zsmul]
  rw [first_factor_faces_expansion X Y p q]
  erw [second_factor_faces_expansion X Y p q]
  rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD]
  erw [Preadditive.sum_comp]
  have hleft :
      (∑ i : Fin (p + q + 2),
          (((-1 : ℤ) ^ (i : ℕ)) • (X ⊗ Y).δ i) ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op)) =
        ∑ i : Fin (p + q + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((X ⊗ Y).δ i ≫
            (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
              Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Preadditive.zsmul_comp _ _ _
  erw [hleft]
  rw [alternating_sum_faces_split p q]
  let early := ∑ i : Fin (p + 1), ((-1 : ℤ) ^ (i : ℕ)) •
    ((X.δ (⟨i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨i, by omega⟩ : Fin (p + q + 2))) ≫
      (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
        Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op))
  let late := ∑ i : Fin (q + 1), ((-1 : ℤ) ^ (p + 1 + (i : ℕ))) •
    ((X.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2)) ⊗ₘ
        Y.δ (⟨p + 1 + i, by omega⟩ : Fin (p + q + 2))) ≫
      (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
        Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op))
  let firstBoundary :
      (X.obj (Opposite.op (SimplexCategory.mk (p + q + 1))) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk (p + q + 1)))) ⟶
        X.obj (Opposite.op (SimplexCategory.mk p)) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk q)) :=
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
      (X.δ (Fin.last (p + 1)) ⊗ₘ 𝟙 ((alternatingChains Y).X q))
  let secondBoundary :
      (X.obj (Opposite.op (SimplexCategory.mk (p + q + 1))) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk (p + q + 1)))) ⟶
        X.obj (Opposite.op (SimplexCategory.mk p)) ⊗
          Y.obj (Opposite.op (SimplexCategory.mk q)) :=
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
      (𝟙 ((alternatingChains X).X p) ⊗ₘ Y.δ (0 : Fin (q + 2)))
  change early + late =
    (early + ((-1 : ℤ) ^ (p + 1)) • firstBoundary) +
      (((-1 : ℤ) ^ p) • secondBoundary + late)
  have hboundary : firstBoundary = secondBoundary := by
    exact alexanderWhitneyBoundary_tensor X Y p q
  have hcancel :
      ((-1 : ℤ) ^ (p + 1)) • firstBoundary +
        ((-1 : ℤ) ^ p) • secondBoundary = 0 := by
    rw [hboundary]
    exact neg_one_pow_boundary_cancel p secondBoundary
  rw [show (early + ((-1 : ℤ) ^ (p + 1)) • firstBoundary) +
      (((-1 : ℤ) ^ p) • secondBoundary + late) =
        early +
          (((( -1 : ℤ) ^ (p + 1)) • firstBoundary +
            ((-1 : ℤ) ^ p) • secondBoundary) + late) by abel]
  rw [hcancel, zero_add]

/-- The subtraction-indexed AW summand rewritten using an exact pair of cut degrees. -/
theorem alternatingAlexanderWhitneySummand_pair
    (i j n : ℕ) (hij : i + j = n) :
    alternatingAlexanderWhitneySummand X Y n ⟨i, by omega⟩ =
      (X.map (SimplexCategory.subinterval (n := n) 0 i (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := n) i j (by omega)).op) ≫
        HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j n hij := by
  unfold alternatingAlexanderWhitneySummand
  simp only [alexanderWhitneyFront, alexanderWhitneyBack]
  let iraw : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨i, n - i⟩, by change i + (n - i) = n; omega⟩
  let iexact : { ij // ij ∈
      (ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ)) ⁻¹' {n} } :=
    ⟨⟨i, j⟩, by change i + j = n; exact hij⟩
  change _ ≫ Sigma.ι (tensorCutFamily X Y n) iraw =
    _ ≫ Sigma.ι (tensorCutFamily X Y n) iexact
  have hiraw : iraw = iexact := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp [iraw, iexact]
      omega
  rw [← Sigma.eqToHom_comp_ι (tensorCutFamily X Y n) hiraw]
  simp only [← Category.assoc]
  rw [cancel_mono]
  apply eq_of_heq
  apply (comp_eqToHom_heq _ _).trans
  apply tensor_map_subinterval_heq
  omega

theorem inclusion_d_comp_projection_congr_total
    (i j p q n n' : ℕ)
    (hsource : i + j = n + 1) (hsource' : i + j = n' + 1)
    (htarget : p + q = n) (htarget' : p + q = n') :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (n + 1) hsource ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (n + 1) n) ≫
      tensorPairProjection X Y p q n htarget =
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (n' + 1) hsource' ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (n' + 1) n') ≫
      tensorPairProjection X Y p q n' htarget' := by
  have hnn' : n = n' := htarget.symm.trans htarget'
  subst n'
  subst n
  rfl

theorem first_inclusion_d_comp_projection_pq (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        (p + 1) q (p + q + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl =
    ((curriedTensor (ModuleCat ℤ)).map
      ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) := by
  calc
    _ = (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          (p + 1) q (q + p + 1) (by omega) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (q + p + 1) (q + p)) ≫
        tensorPairProjection X Y p q (q + p) (by omega) := by
      exact inclusion_d_comp_projection_congr_total X Y
        (p + 1) q p q (p + q) (q + p) (by omega) (by omega) rfl (by omega)
    _ = _ := first_inclusion_d_comp_projection X Y p q

theorem second_inclusion_d_comp_projection_pq (p q : ℕ) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        p (q + 1) (p + q + 1) (by omega) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl =
    ((-1 : ℤ) ^ p) •
      ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
        ((alternatingChains Y).d (q + 1) q) := by
  calc
    _ = (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          p (q + 1) (q + p + 1) (by omega) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (q + p + 1) (q + p)) ≫
        tensorPairProjection X Y p q (q + p) (by omega) := by
      exact inclusion_d_comp_projection_congr_total X Y
        p (q + 1) p q (p + q) (q + p) (by omega) (by omega) rfl (by omega)
    _ = _ := second_inclusion_d_comp_projection X Y p q

theorem nonadjacent_inclusion_d_comp_projection_pq
    (i j p q : ℕ) (hij : i + j = p + q + 1)
    (hfirst : (i, j) ≠ (p + 1, q))
    (hsecond : (i, j) ≠ (p, q + 1)) :
    (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
        i j (p + q + 1) hij ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl = 0 := by
  have hij' : i + j = q + p + 1 := by omega
  calc
    _ = (HomologicalComplex.ιTensorObj (alternatingChains X) (alternatingChains Y)
          i j (q + p + 1) hij' ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (q + p + 1) (q + p)) ≫
        tensorPairProjection X Y p q (q + p) (by omega) := by
      exact inclusion_d_comp_projection_congr_total X Y
        i j p q (p + q) (q + p) (by omega) (by omega) rfl (by omega)
    _ = 0 := nonadjacent_inclusion_d_comp_projection X Y
      i j p q hij' hfirst hsecond

theorem aw_target_d_projection_explicit_pq (p q : ℕ) :
    (alternatingAlexanderWhitneyDegree X Y (p + q + 1) ≫
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
        (p + q + 1) (p + q)) ≫
      tensorPairProjection X Y p q (p + q) rfl =
    (X.map
          (SimplexCategory.subinterval (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) (p + 1) q (by omega)).op) ≫
      ((curriedTensor (ModuleCat ℤ)).map
        ((alternatingChains X).d (p + 1) p)).app ((alternatingChains Y).X q) +
    (X.map (SimplexCategory.subinterval (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
        Y.map
          (SimplexCategory.subinterval (n := p + q + 1) p (q + 1) (by omega)).op) ≫
      (((-1 : ℤ) ^ p) •
        ((curriedTensor (ModuleCat ℤ)).obj ((alternatingChains X).X p)).map
          ((alternatingChains Y).d (q + 1) q)) := by
  rw [alternatingAlexanderWhitneyDegree]
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  let a : Fin (p + q + 2) := ⟨p + 1, by omega⟩
  let b : Fin (p + q + 2) := ⟨p, by omega⟩
  rw [fintype_sum_eq_add_two_of_eq_zero a b (by
    intro h
    exact Nat.succ_ne_self p (congrArg Fin.val h).symm)]
  · dsimp only [a, b]
    congr 1
    · rw [alternatingAlexanderWhitneySummand_pair X Y (p + 1) q]
      have h := congrArg
        (fun t =>
          (X.map
                (SimplexCategory.subinterval
                  (n := p + q + 1) 0 (p + 1) (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval
                  (n := p + q + 1) (p + 1) q (by omega)).op) ≫ t)
        (first_inclusion_d_comp_projection_pq X Y p q)
      simpa only [Category.assoc] using h
    · rw [alternatingAlexanderWhitneySummand_pair X Y p (q + 1)]
      have h := congrArg
        (fun t =>
          (X.map
                (SimplexCategory.subinterval
                  (n := p + q + 1) 0 p (by omega)).op ⊗ₘ
              Y.map
                (SimplexCategory.subinterval
                  (n := p + q + 1) p (q + 1) (by omega)).op) ≫ t)
        (second_inclusion_d_comp_projection_pq X Y p q)
      simpa only [Category.assoc] using h
  · intro r hra hrb
    rw [alternatingAlexanderWhitneySummand_pair X Y r (p + q + 1 - r)]
    have hnon := nonadjacent_inclusion_d_comp_projection_pq X Y
      r (p + q + 1 - r) p q (by omega) (by
        intro hpair
        apply hra
        apply Fin.ext
        exact congrArg Prod.fst hpair) (by
        intro hpair
        apply hrb
        apply Fin.ext
        exact congrArg Prod.fst hpair)
    have hassoc := congrArg
      (fun t =>
        (X.map (SimplexCategory.subinterval
              (n := p + q + 1) 0 r (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval
              (n := p + q + 1) r (p + q + 1 - r) (by omega)).op) ≫ t) hnon
    simpa only [Category.assoc, comp_zero] using hassoc

theorem alternatingAlexanderWhitney_projected_chain (p q : ℕ) :
    (alternatingChains (X ⊗ Y)).d (p + q + 1) (p + q) ≫
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) =
      (alternatingAlexanderWhitneyDegree X Y (p + q + 1) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (p + q + 1) (p + q)) ≫
        tensorPairProjection X Y p q (p + q) rfl := by
  rw [alternating_d_comp_alexanderWhitney_cut X Y p q,
    aw_target_d_projection_explicit_pq X Y p q]
  congr 1

theorem alternatingAlexanderWhitneyDegree_comp_pairProjection (p q : ℕ) :
    alternatingAlexanderWhitneyDegree X Y (p + q) ≫
        tensorPairProjection X Y p q (p + q) rfl =
      X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
        Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op := by
  rw [alternatingAlexanderWhitneyDegree, Preadditive.sum_comp,
    Finset.sum_eq_single (⟨p, by omega⟩ : Fin (p + q + 1))]
  · rw [alternatingAlexanderWhitneySummand_pair X Y p q]
    have h := congrArg
      (fun t =>
        (X.map (SimplexCategory.subinterval (n := p + q) 0 p (by omega)).op ⊗ₘ
          Y.map (SimplexCategory.subinterval (n := p + q) p q (by omega)).op) ≫ t)
      (ιTensorObj_tensorPairProjection_self X Y p q (p + q) rfl)
    simpa only [Category.assoc, Category.comp_id] using h
  · intro r _ hrp
    rw [alternatingAlexanderWhitneySummand_pair X Y r (p + q - r)]
    have h := ιTensorObj_tensorPairProjection_of_ne X Y
      r (p + q - r) p q (p + q) (by omega) rfl (by
        intro hpair
        apply hrp
        apply Fin.ext
        exact congrArg Prod.fst hpair)
    have hassoc := congrArg
      (fun t =>
        (X.map (SimplexCategory.subinterval (n := p + q) 0 r (by omega)).op ⊗ₘ
          Y.map
            (SimplexCategory.subinterval (n := p + q) r (p + q - r) (by omega)).op) ≫ t) h
    simpa only [Category.assoc, comp_zero] using hassoc
  · simp

theorem tensorDegree_hom_ext_pair
    (n : ℕ) {A : ModuleCat.{0} ℤ}
    {f g : A ⟶
      (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).X n}
    (h : ∀ (p q : ℕ) (hpq : p + q = n),
      f ≫ tensorPairProjection X Y p q n hpq =
        g ≫ tensorPairProjection X Y p q n hpq) :
    f = g := by
  apply tensorDegree_hom_ext X Y n
  intro p
  simpa only [tensorCutProjection] using h p (n - p) (by omega)

theorem alternatingAlexanderWhitneyDegree_comm (n : ℕ) :
    (alternatingChains (X ⊗ Y)).d (n + 1) n ≫
        alternatingAlexanderWhitneyDegree X Y n =
      alternatingAlexanderWhitneyDegree X Y (n + 1) ≫
        (HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y)).d
          (n + 1) n := by
  apply tensorDegree_hom_ext_pair X Y n
  intro p q hpq
  subst n
  rw [Category.assoc,
    alternatingAlexanderWhitneyDegree_comp_pairProjection X Y p q]
  exact alternatingAlexanderWhitney_projected_chain X Y p q

/-- The unnormalized Alexander--Whitney chain map. -/
def alternatingAlexanderWhitney :
    alternatingChains (X ⊗ Y) ⟶
      HomologicalComplex.tensorObj (alternatingChains X) (alternatingChains Y) where
  f := alternatingAlexanderWhitneyDegree X Y
  comm' := by
    rintro _ n ⟨rfl⟩
    exact (alternatingAlexanderWhitneyDegree_comm X Y n).symm

@[simp]
theorem alternatingAlexanderWhitney_f (n : ℕ) :
    (alternatingAlexanderWhitney X Y).f n =
      alternatingAlexanderWhitneyDegree X Y n := rfl

theorem alternatingAlexanderWhitneySummand_natural
    {X' Y' : SimplicialObject (ModuleCat.{0} ℤ)}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) (p : Fin (n + 1)) :
    alternatingAlexanderWhitneySummand X Y n p ≫
        (HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map f)
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map g)).f n =
      (f ⊗ₘ g).app (op (SimplexCategory.mk n)) ≫
        alternatingAlexanderWhitneySummand X' Y' n p := by
  rw [alternatingAlexanderWhitneySummand, alternatingAlexanderWhitneySummand,
    Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  have hmid :
      ((curriedTensor (ModuleCat ℤ)).map
          (((alternatingFaceMapComplex (ModuleCat ℤ)).map f).f p)).app
            (((alternatingFaceMapComplex (ModuleCat ℤ)).obj Y).X (n - p)) ≫
        ((curriedTensor (ModuleCat ℤ)).obj
          (((alternatingFaceMapComplex (ModuleCat ℤ)).obj X').X p)).map
            (((alternatingFaceMapComplex (ModuleCat ℤ)).map g).f (n - p)) =
      (((alternatingFaceMapComplex (ModuleCat ℤ)).map f).f p ⊗ₘ
        ((alternatingFaceMapComplex (ModuleCat ℤ)).map g).f (n - p)) :=
    (MonoidalCategory.tensorHom_def _ _).symm
  have hpre :
      (X.map (alexanderWhitneyFront n p).op ⊗ₘ
          Y.map (alexanderWhitneyBack n p).op) ≫
          (((curriedTensor (ModuleCat ℤ)).map
            (((alternatingFaceMapComplex (ModuleCat ℤ)).map f).f p)).app
              (((alternatingFaceMapComplex (ModuleCat ℤ)).obj Y).X (n - p)) ≫
            ((curriedTensor (ModuleCat ℤ)).obj
              (((alternatingFaceMapComplex (ModuleCat ℤ)).obj X').X p)).map
                (((alternatingFaceMapComplex (ModuleCat ℤ)).map g).f (n - p))) =
        (f ⊗ₘ g).app (op (SimplexCategory.mk n)) ≫
          (X'.map (alexanderWhitneyFront n p).op ⊗ₘ
            Y'.map (alexanderWhitneyBack n p).op) := by
    have hfirst := congrArg
      (fun t =>
        (X.map (alexanderWhitneyFront n p).op ⊗ₘ
          Y.map (alexanderWhitneyBack n p).op) ≫ t) hmid
    refine hfirst.trans ?_
    simp only [alternatingFaceMapComplex_map_f]
    rw [Monoidal.tensorHom_app]
    calc
      (X.map (alexanderWhitneyFront n p).op ⊗ₘ
          Y.map (alexanderWhitneyBack n p).op) ≫
          (f.app (op (SimplexCategory.mk p)) ⊗ₘ
            g.app (op (SimplexCategory.mk (n - p)))) =
        (X.map (alexanderWhitneyFront n p).op ≫
            f.app (op (SimplexCategory.mk p))) ⊗ₘ
          (Y.map (alexanderWhitneyBack n p).op ≫
            g.app (op (SimplexCategory.mk (n - p)))) :=
        MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
      _ = (f.app (op (SimplexCategory.mk n)) ≫
              X'.map (alexanderWhitneyFront n p).op) ⊗ₘ
          (g.app (op (SimplexCategory.mk n)) ≫
            Y'.map (alexanderWhitneyBack n p).op) := by
        rw [f.naturality, g.naturality]
      _ = (f.app (op (SimplexCategory.mk n)) ⊗ₘ
            g.app (op (SimplexCategory.mk n))) ≫
          (X'.map (alexanderWhitneyFront n p).op ⊗ₘ
            Y'.map (alexanderWhitneyBack n p).op) :=
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
  have hpreAssoc := congrArg (fun t => t ≫
    HomologicalComplex.ιTensorObj
      ((alternatingFaceMapComplex (ModuleCat ℤ)).obj X')
      ((alternatingFaceMapComplex (ModuleCat ℤ)).obj Y')
      p (n - p) n (by omega)) hpre
  simpa only [Category.assoc] using hpreAssoc

/-- The Alexander--Whitney degree maps are natural in both simplicial modules. -/
theorem alternatingAlexanderWhitneyDegree_natural
    {X' Y' : SimplicialObject (ModuleCat.{0} ℤ)}
    (f : X ⟶ X') (g : Y ⟶ Y') (n : ℕ) :
    alternatingAlexanderWhitneyDegree X Y n ≫
        (HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map f)
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map g)).f n =
      (f ⊗ₘ g).app (op (SimplexCategory.mk n)) ≫
        alternatingAlexanderWhitneyDegree X' Y' n := by
  change
    (Finset.univ.sum fun p : Fin (n + 1) =>
      alternatingAlexanderWhitneySummand X Y n p) ≫ _ =
      _ ≫ Finset.univ.sum fun p : Fin (n + 1) =>
        alternatingAlexanderWhitneySummand X' Y' n p
  rw [CategoryTheory.Preadditive.sum_comp, CategoryTheory.Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun p _ =>
    alternatingAlexanderWhitneySummand_natural X Y f g n p

/-- The unnormalized Alexander--Whitney chain map is natural in both variables. -/
theorem alternatingAlexanderWhitney_natural
    {X' Y' : SimplicialObject (ModuleCat.{0} ℤ)}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    alternatingAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map f)
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map g) =
      (alternatingFaceMapComplex (ModuleCat ℤ)).map (f ⊗ₘ g) ≫
        alternatingAlexanderWhitney X' Y' := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact alternatingAlexanderWhitneyDegree_natural X Y f g n

/-- The degreewise normalized Alexander--Whitney candidate. It includes normalized chains
into alternating chains, applies the Alexander--Whitney formula, and then applies the two
normalized Moore projectors. -/
def normalizedAlexanderWhitneyDegree (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat ℤ)).obj (X ⊗ Y)).X n ⟶
      (HomologicalComplex.tensorObj
        ((normalizedMooreComplex (ModuleCat ℤ)).obj X)
        ((normalizedMooreComplex (ModuleCat ℤ)).obj Y)).X n :=
  (inclusionOfMooreComplexMap (X ⊗ Y)).f n ≫
    alternatingAlexanderWhitneyDegree X Y n ≫
    (HomologicalComplex.tensorHom
      (DoldKan.PInftyToNormalizedMooreComplex X)
      (DoldKan.PInftyToNormalizedMooreComplex Y)).f n

/-- The normalized Alexander--Whitney chain map. -/
def normalizedAlexanderWhitney :
    (normalizedMooreComplex (ModuleCat ℤ)).obj (X ⊗ Y) ⟶
      HomologicalComplex.tensorObj
        ((normalizedMooreComplex (ModuleCat ℤ)).obj X)
        ((normalizedMooreComplex (ModuleCat ℤ)).obj Y) :=
  inclusionOfMooreComplexMap (X ⊗ Y) ≫
    alternatingAlexanderWhitney X Y ≫
    HomologicalComplex.tensorHom
      (DoldKan.PInftyToNormalizedMooreComplex X)
      (DoldKan.PInftyToNormalizedMooreComplex Y)

@[simp]
theorem normalizedAlexanderWhitney_f (n : ℕ) :
    (normalizedAlexanderWhitney X Y).f n =
      normalizedAlexanderWhitneyDegree X Y n := rfl

/-- The normalized Alexander--Whitney chain map is natural in both variables. -/
theorem normalizedAlexanderWhitney_natural
    {X' Y' : SimplicialObject (ModuleCat.{0} ℤ)}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    normalizedAlexanderWhitney X Y ≫
        HomologicalComplex.tensorHom
          ((normalizedMooreComplex (ModuleCat ℤ)).map f)
          ((normalizedMooreComplex (ModuleCat ℤ)).map g) =
      (normalizedMooreComplex (ModuleCat ℤ)).map (f ⊗ₘ g) ≫
        normalizedAlexanderWhitney X' Y' := by
  simp only [normalizedAlexanderWhitney, Category.assoc]
  have htensor :
      HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X)
            (DoldKan.PInftyToNormalizedMooreComplex Y) ≫
          HomologicalComplex.tensorHom
            ((normalizedMooreComplex (ModuleCat ℤ)).map f)
            ((normalizedMooreComplex (ModuleCat ℤ)).map g) =
        HomologicalComplex.tensorHom
          (DoldKan.PInftyToNormalizedMooreComplex X ≫
            (normalizedMooreComplex (ModuleCat ℤ)).map f)
          (DoldKan.PInftyToNormalizedMooreComplex Y ≫
            (normalizedMooreComplex (ModuleCat ℤ)).map g) := by
    exact MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _
  erw [htensor]
  erw [← DoldKan.PInftyToNormalizedMooreComplex_naturality f,
    ← DoldKan.PInftyToNormalizedMooreComplex_naturality g]
  have htensor' :
      HomologicalComplex.tensorHom
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map f ≫
            DoldKan.PInftyToNormalizedMooreComplex X')
          ((alternatingFaceMapComplex (ModuleCat ℤ)).map g ≫
            DoldKan.PInftyToNormalizedMooreComplex Y') =
        HomologicalComplex.tensorHom
            ((alternatingFaceMapComplex (ModuleCat ℤ)).map f)
            ((alternatingFaceMapComplex (ModuleCat ℤ)).map g) ≫
          HomologicalComplex.tensorHom
            (DoldKan.PInftyToNormalizedMooreComplex X')
            (DoldKan.PInftyToNormalizedMooreComplex Y') := by
    exact (MonoidalCategory.tensorHom_comp_tensorHom
      ((alternatingFaceMapComplex (ModuleCat ℤ)).map f)
      ((alternatingFaceMapComplex (ModuleCat ℤ)).map g)
      (DoldKan.PInftyToNormalizedMooreComplex X')
      (DoldKan.PInftyToNormalizedMooreComplex Y')).symm
  erw [htensor']
  erw [← Category.assoc
    (alternatingAlexanderWhitney X Y)
    (HomologicalComplex.tensorHom
      ((alternatingFaceMapComplex (ModuleCat ℤ)).map f)
      ((alternatingFaceMapComplex (ModuleCat ℤ)).map g))
    (HomologicalComplex.tensorHom
      (DoldKan.PInftyToNormalizedMooreComplex X')
      (DoldKan.PInftyToNormalizedMooreComplex Y'))]
  rw [alternatingAlexanderWhitney_natural X Y f g]
  have hinc := congrArg
    (fun t => t ≫ alternatingAlexanderWhitney X' Y' ≫
      HomologicalComplex.tensorHom
        (DoldKan.PInftyToNormalizedMooreComplex X')
        (DoldKan.PInftyToNormalizedMooreComplex Y'))
    ((inclusionOfMooreComplex (ModuleCat ℤ)).naturality (f ⊗ₘ g)).symm
  simpa only [Category.assoc] using hinc

/-- The normalized Alexander--Whitney counit on the monoidal unit. -/
def normalizedAlexanderWhitneyUnit :
    (normalizedMooreComplex (ModuleCat ℤ)).obj
        (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ⟶
      𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ) := by
  change
    (normalizedMooreComplex (ModuleCat ℤ)).obj
        (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ⟶
      (ChainComplex.single₀ (ModuleCat ℤ)).obj (𝟙_ (ModuleCat ℤ))
  refine (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(NormalizedMooreComplex.objX
      (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) 0).arrow, ?_⟩
  rw [normalizedMooreComplex_objD]
  simp [NormalizedMooreComplex.objD, SimplicialObject.δ]
  have hf := CategoryTheory.Subobject.finset_inf_arrow_factors Finset.univ
    (fun _ : Fin 1 => Limits.kernelSubobject (𝟙 (𝟙_ (ModuleCat ℤ))))
    (0 : Fin 1) (by simp)
  have hz := (Limits.kernelSubobject_factors_iff
    (𝟙 (𝟙_ (ModuleCat ℤ))) _).mp hf
  simpa only [Category.comp_id] using hz

@[simp]
theorem normalizedAlexanderWhitneyUnit_f_zero :
    normalizedAlexanderWhitneyUnit.f 0 =
      (NormalizedMooreComplex.objX
        (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) 0).arrow := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

@[simp]
theorem normalizedAlexanderWhitneyUnit_f_succ (n : ℕ) :
    normalizedAlexanderWhitneyUnit.f (n + 1) = 0 := by
  apply (HomologicalComplex.isZero_single_obj_X
    (c := ComplexShape.down ℕ) 0 (𝟙_ (ModuleCat ℤ)) (n + 1) (by omega)).eq_of_tgt

/-- The normalized unit map expressed through the standard alternating-chain augmentation. -/
def normalizedAlexanderWhitneyUnitViaEpsilon :
    (normalizedMooreComplex (ModuleCat ℤ)).obj
        (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ⟶
      𝟙_ (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  inclusionOfMooreComplexMap
      (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
    AlternatingFaceMapComplex.ε.app
      (SimplicialObject.Augmented.const.obj (𝟙_ (ModuleCat ℤ)))

theorem normalizedAlexanderWhitneyUnitViaEpsilon_eq :
    normalizedAlexanderWhitneyUnitViaEpsilon =
      normalizedAlexanderWhitneyUnit := by
  apply HomologicalComplex.to_single_hom_ext
  simp [normalizedAlexanderWhitneyUnitViaEpsilon]

/-- Retracting alternating chains and then applying the normalized unit map is the standard
alternating-chain augmentation. -/
theorem pInfty_comp_normalizedAlexanderWhitneyUnit :
    DoldKan.PInftyToNormalizedMooreComplex
          (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
        normalizedAlexanderWhitneyUnit =
      AlternatingFaceMapComplex.ε.app
        (SimplicialObject.Augmented.const.obj (𝟙_ (ModuleCat ℤ))) := by
  apply HomologicalComplex.to_single_hom_ext
  simp

/-- Naturality of normalized Alexander--Whitney in its left variable. -/
theorem normalizedAlexanderWhitney_natural_left
    {X Y : SimplicialObject (ModuleCat.{0} ℤ)} (f : X ⟶ Y)
    (X' : SimplicialObject (ModuleCat.{0} ℤ)) :
    normalizedAlexanderWhitney X X' ≫
        (zModuleDoldKanEquivalence.functor.map f ▷
          zModuleDoldKanEquivalence.functor.obj X') =
      zModuleDoldKanEquivalence.functor.map (f ▷ X') ≫
        normalizedAlexanderWhitney Y X' := by
  have h := normalizedAlexanderWhitney_natural X X' f (CategoryStruct.id X')
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- Naturality of normalized Alexander--Whitney in its right variable. -/
theorem normalizedAlexanderWhitney_natural_right
    {X Y : SimplicialObject (ModuleCat.{0} ℤ)}
    (X' : SimplicialObject (ModuleCat.{0} ℤ)) (f : X ⟶ Y) :
    normalizedAlexanderWhitney X' X ≫
        (zModuleDoldKanEquivalence.functor.obj X' ◁
          zModuleDoldKanEquivalence.functor.map f) =
      zModuleDoldKanEquivalence.functor.map (X' ◁ f) ≫
        normalizedAlexanderWhitney X' Y := by
  have h := normalizedAlexanderWhitney_natural X' X (CategoryStruct.id X') f
  rw [CategoryTheory.Functor.map_id] at h
  exact h

/-- Package normalized Alexander--Whitney once its associativity and two unit laws are proved. -/
@[implicit_reducible]
def normalizedMooreOplaxMonoidalCandidate
    (hassoc : ∀ X Y Z : SimplicialObject (ModuleCat.{0} ℤ),
      normalizedAlexanderWhitney (X ⊗ Y) Z ≫
          (normalizedAlexanderWhitney X Y ▷
            zModuleDoldKanEquivalence.functor.obj Z) ≫
          (α_
            (zModuleDoldKanEquivalence.functor.obj X)
            (zModuleDoldKanEquivalence.functor.obj Y)
            (zModuleDoldKanEquivalence.functor.obj Z)).hom =
        zModuleDoldKanEquivalence.functor.map (α_ X Y Z).hom ≫
          normalizedAlexanderWhitney X (Y ⊗ Z) ≫
          (zModuleDoldKanEquivalence.functor.obj X ◁
            normalizedAlexanderWhitney Y Z))
    (hleft : ∀ X : SimplicialObject (ModuleCat.{0} ℤ),
      (λ_ (zModuleDoldKanEquivalence.functor.obj X)).inv =
        zModuleDoldKanEquivalence.functor.map (λ_ X).inv ≫
          normalizedAlexanderWhitney
            (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) X ≫
          (normalizedAlexanderWhitneyUnit ▷
            zModuleDoldKanEquivalence.functor.obj X))
    (hright : ∀ X : SimplicialObject (ModuleCat.{0} ℤ),
      (ρ_ (zModuleDoldKanEquivalence.functor.obj X)).inv =
        zModuleDoldKanEquivalence.functor.map (ρ_ X).inv ≫
          normalizedAlexanderWhitney X
            (𝟙_ (SimplicialObject (ModuleCat.{0} ℤ))) ≫
          (zModuleDoldKanEquivalence.functor.obj X ◁
            normalizedAlexanderWhitneyUnit)) :
    NormalizedMooreOplaxMonoidal where
  η := normalizedAlexanderWhitneyUnit
  δ := normalizedAlexanderWhitney
  δ_natural_left := normalizedAlexanderWhitney_natural_left
  δ_natural_right := normalizedAlexanderWhitney_natural_right
  oplax_associativity := hassoc
  oplax_left_unitality := hleft
  oplax_right_unitality := hright

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
