import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
# Path combinatorics for the locally-Kan coherent nerve theorem

This file develops cubical path-latching objects for coherent-nerve horn filling.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration

open CategoryTheory Simplicial MonoidalCategory

universe u

namespace SSet.Subcomplex

theorem image_preimage_eq_inf_range {X Y : SSet.{u}} (B : Y.Subcomplex) (f : X ⟶ Y) :
    (B.preimage f).image f = B ⊓ SSet.Subcomplex.range f := by
  ext n y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, ⟨x, rfl⟩⟩
  · rintro ⟨hy, x, rfl⟩
    exact ⟨x, hy, rfl⟩

/-- The union of two subcomplexes is obtained by gluing them along their intersection. -/
theorem inf_inclusions_isPushout {X : SSet.{u}} (A B : X.Subcomplex) :
    IsPushout
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A))
      (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B))
      (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B))
      (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) :=
  SSet.Subcomplex.BicartSq.isPushout
    ({ sup_eq := rfl
       inf_eq := rfl } : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B))

end SSet.Subcomplex

namespace Path

abbrev ThickPath {J : Type u} [LinearOrder J] (i j : J) :=
  SimplicialThickening.Path i j

/-- Strictly internal vertices of an ordered interval. -/
abbrev InteriorVertex {J : Type u} [LinearOrder J] (i j : J) := Set.Ioo i j

instance thickPathLE {J : Type u} [LinearOrder J] (i j : J) : LE (ThickPath i j) :=
  ⟨fun P Q ↦ P.I ⊆ Q.I⟩

instance thickPathPartialOrder {J : Type u} [LinearOrder J] (i j : J) :
    PartialOrder (ThickPath i j) where
  le_refl _ := Set.Subset.rfl
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm P Q hPQ hQP := by
    apply SimplicialThickening.Path.ext
    ext x
    exact ⟨fun hx ↦ hPQ hx, fun hx ↦ hQP hx⟩

instance thickPathHomSubsingleton {J : Type u} [LinearOrder J] {i j : J}
    (P Q : ThickPath i j) : Subsingleton (P ⟶ Q) := by
  constructor
  intro f g
  cases f
  cases g
  congr 1
  exact Subsingleton.elim _ _

/-- A path is exactly a choice of internal vertices, once its two compulsory endpoints are
removed.  This is the Boolean-lattice model underlying the cubical proof of the coherent-nerve
horn theorem. -/
def thickPathInteriorOrderIso {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j) :
    ThickPath i j ≃o Set (InteriorVertex i j) where
  toFun P := {x | x.1 ∈ P.I}
  invFun S :=
    { I := {x | x = i ∨ x = j ∨ ∃ h : i < x ∧ x < j, (⟨x, h⟩ : InteriorVertex i j) ∈ S}
      left := Or.inl rfl
      right := Or.inr (Or.inl rfl)
      left_le := by
        rintro x (rfl | rfl | ⟨h, _⟩)
        · exact le_rfl
        · exact hij
        · exact h.1.le
      le_right := by
        rintro x (rfl | rfl | ⟨h, _⟩)
        · exact hij
        · exact le_rfl
        · exact h.2.le }
  left_inv P := by
    apply SimplicialThickening.Path.ext
    ext x
    constructor
    · rintro (rfl | rfl | ⟨h, hx⟩)
      · exact P.left
      · exact P.right
      · exact hx
    · intro hx
      by_cases hxi : x = i
      · exact Or.inl hxi
      by_cases hxj : x = j
      · exact Or.inr (Or.inl hxj)
      · exact Or.inr (Or.inr ⟨⟨lt_of_le_of_ne (P.left_le x hx) (Ne.symm hxi),
            lt_of_le_of_ne (P.le_right x hx) hxj⟩, hx⟩)
  right_inv S := by
    ext x
    change (x.1 = i ∨ x.1 = j ∨ ∃ h : i < x.1 ∧ x.1 < j,
      (⟨x.1, h⟩ : InteriorVertex i j) ∈ S) ↔ x ∈ S
    constructor
    · rintro (h | h | ⟨h, hx⟩)
      · exact (ne_of_gt x.2.1 h).elim
      · exact (ne_of_lt x.2.2 h).elim
      · convert hx
    · intro hx
      exact Or.inr (Or.inr ⟨x.2, hx⟩)
  map_rel_iff' := by
    intro P Q
    change (∀ x : InteriorVertex i j, x.1 ∈ P.I → x.1 ∈ Q.I) ↔ P.I ⊆ Q.I
    constructor
    · intro h x hx
      by_cases hxi : x = i
      · exact hxi ▸ Q.left
      by_cases hxj : x = j
      · exact hxj ▸ Q.right
      exact h ⟨x, lt_of_le_of_ne (P.left_le x hx) (Ne.symm hxi),
        lt_of_le_of_ne (P.le_right x hx) hxj⟩ hx
    · exact fun h x hx ↦ h hx

/-- Forward functor from paths to the Boolean lattice of internal vertices. -/
def thickPathInteriorFunctor {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j) :
    CategoryTheory.Functor (ThickPath i j) (Set (InteriorVertex i j)) where
  obj := thickPathInteriorOrderIso hij
  map {_ _} f := homOfLE (fun _ hx ↦ f.1.1.1 hx)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Inverse functor adjoining the two compulsory endpoints to a Boolean vertex set. -/
def interiorThickPathFunctor {J : Type u} [LinearOrder J] {i j : J} (hij : i ≤ j) :
    CategoryTheory.Functor (Set (InteriorVertex i j)) (ThickPath i j) where
  obj := (thickPathInteriorOrderIso hij).symm
  map {S T} f := ⟨⟨⟨by
    intro x hx
    rcases hx with h | h | ⟨h, hx⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, leOfHom f hx⟩)⟩⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Categorical path/Boolean-lattice equivalence, compatible with the category used by the
simplicial thickening. -/
noncomputable def thickPathInteriorEquivalence {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) : ThickPath i j ≌ Set (InteriorVertex i j) :=
  CategoryTheory.Equivalence.mk
    (thickPathInteriorFunctor hij) (interiorThickPathFunctor hij)
    (NatIso.ofComponents (fun P ↦ eqToIso
      ((thickPathInteriorOrderIso hij).left_inv P).symm))
    (NatIso.ofComponents (fun S ↦ eqToIso
      ((thickPathInteriorOrderIso hij).right_inv S)))

theorem thickPathInteriorFunctor_comp {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) :
    thickPathInteriorFunctor hij ⋙ interiorThickPathFunctor hij =
      CategoryTheory.Functor.id (ThickPath i j) := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun P ↦ (thickPathInteriorOrderIso hij).left_inv P)
    (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)

theorem interiorThickPathFunctor_comp {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) :
    interiorThickPathFunctor hij ⋙ thickPathInteriorFunctor hij =
      CategoryTheory.Functor.id (Set (InteriorVertex i j)) := by
  exact CategoryTheory.Functor.ext
    (h_obj := fun S ↦ (thickPathInteriorOrderIso hij).right_inv S)
    (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The nerve of the path category is the nerve of its Boolean lattice of internal vertices. -/
noncomputable def thickPathNerveBooleanIso {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) :
    CategoryTheory.nerve (ThickPath i j) ≅
      CategoryTheory.nerve (Set (InteriorVertex i j)) where
  hom := CategoryTheory.nerveMap (thickPathInteriorFunctor hij)
  inv := CategoryTheory.nerveMap (interiorThickPathFunctor hij)
  hom_inv_id := by
    change CategoryTheory.nerveFunctor.map
        (thickPathInteriorFunctor hij).toCatHom ≫
      CategoryTheory.nerveFunctor.map
        (interiorThickPathFunctor hij).toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hc : (thickPathInteriorFunctor hij).toCatHom ≫
        (interiorThickPathFunctor hij).toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact thickPathInteriorFunctor_comp hij
    rw [hc, CategoryTheory.Functor.map_id]
    rfl

  inv_hom_id := by
    change CategoryTheory.nerveFunctor.map
        (interiorThickPathFunctor hij).toCatHom ≫
      CategoryTheory.nerveFunctor.map
        (thickPathInteriorFunctor hij).toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hc : (interiorThickPathFunctor hij).toCatHom ≫
        (thickPathInteriorFunctor hij).toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact interiorThickPathFunctor_comp hij
    rw [hc, CategoryTheory.Functor.map_id]
    rfl

/-- Boolean subsets as literal `0/1` bitvectors. -/
noncomputable def setBitvectorOrderIso (α : Type u) : Set α ≃o (α → Fin 2) := by
  classical
  exact
    { toFun := fun S a ↦ if a ∈ S then 1 else 0
      invFun := fun b ↦ {a | b a = 1}
      left_inv := fun S ↦ by
        ext a
        simp
      right_inv := fun b ↦ by
        funext a
        have hb : b a = 0 ∨ b a = 1 := by
          have hv := (b a).isLt
          change (b a).val < 2 at hv
          omega
        rcases hb with hb | hb <;> simp [hb]
      map_rel_iff' := by
        intro S T
        constructor
        · intro h a ha
          have hat := h a
          change (if a ∈ S then (1 : Fin 2) else 0) ≤
            (if a ∈ T then 1 else 0) at hat
          rw [if_pos ha] at hat
          by_contra hnot
          rw [if_neg hnot] at hat
          omega
        · intro h a
          change (if a ∈ S then (1 : Fin 2) else 0) ≤
            (if a ∈ T then 1 else 0)
          by_cases ha : a ∈ S
          · have hta := h ha
            simp [ha, hta]
          · simp [ha] }

/-- A thick path is therefore a bitvector indexed by its internal vertices. -/
noncomputable def thickPathBitvectorOrderIso {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) : ThickPath i j ≃o (InteriorVertex i j → Fin 2) :=
  (thickPathInteriorOrderIso hij).trans (setBitvectorOrderIso (InteriorVertex i j))

/-- The ordinary nerve carries a categorical binary product to the pointwise product of
simplicial sets.  Iteration is the finite-cube decomposition. -/
noncomputable def nerveBinaryProductIso (C D : Type u) [Category.{u} C] [Category.{u} D] :
    CategoryTheory.Iso
      (CategoryTheory.nerveFunctor.obj
        (CategoryTheory.Cat.of C ⨯ CategoryTheory.Cat.of D))
      (CategoryTheory.nerveFunctor.obj (CategoryTheory.Cat.of C) ⨯
        CategoryTheory.nerveFunctor.obj (CategoryTheory.Cat.of D)) :=
  asIso (CategoryTheory.Limits.prodComparison CategoryTheory.nerveFunctor
    (CategoryTheory.Cat.of C) (CategoryTheory.Cat.of D))

/-- The type-theoretic product category is a limiting binary fan in `Cat`.  We keep this
explicit because the chosen product object of `Cat` is not definitionally the type product. -/
noncomputable def typeProductFan (C D : Type u) [Category.{u} C] [Category.{u} D] :
    CategoryTheory.Limits.BinaryFan (CategoryTheory.Cat.of C) (CategoryTheory.Cat.of D) :=
  CategoryTheory.Limits.BinaryFan.mk (CategoryTheory.Prod.fst C D).toCatHom
    (CategoryTheory.Prod.snd C D).toCatHom

noncomputable def typeProductFanIsLimit (C D : Type u) [Category.{u} C] [Category.{u} D] :
    CategoryTheory.Limits.IsLimit (typeProductFan C D) :=
  CategoryTheory.Limits.BinaryFan.IsLimit.mk _
    (fun f g ↦ (f.toFunctor.prod' g.toFunctor).toCatHom)
    (fun _ _ ↦ by apply CategoryTheory.Cat.Hom.ext; rfl)
    (fun _ _ ↦ by apply CategoryTheory.Cat.Hom.ext; rfl)
    (fun f g m h₁ h₂ ↦ by
      apply CategoryTheory.Cat.Hom.ext
      change m.toFunctor = f.toFunctor.prod' g.toFunctor
      rw [← CategoryTheory.Cat.Hom.ext_iff.mp h₁, ← CategoryTheory.Cat.Hom.ext_iff.mp h₂]
      rfl)

/-- Comparison between the concrete type-product category and the chosen product in `Cat`. -/
noncomputable def typeProductIsoChosenProduct (C D : Type u) [Category.{u} C]
    [Category.{u} D] :
    CategoryTheory.Cat.of (C × D) ≅ CategoryTheory.Cat.of C ⨯ CategoryTheory.Cat.of D :=
  CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso (typeProductFanIsLimit C D)
    (CategoryTheory.Limits.limit.isLimit _)

/-- The nerve of the concrete product category is the pointwise product of nerves. -/
noncomputable def nerveTypeProductIso (C D : Type u) [Category.{u} C] [Category.{u} D] :
    CategoryTheory.nerve (C × D) ≅ CategoryTheory.nerve C ⨯ CategoryTheory.nerve D :=
  (CategoryTheory.nerveFunctor.mapIso (typeProductIsoChosenProduct C D)).trans
    (nerveBinaryProductIso C D)

/-- A computation-friendly product comparison for nerves.  In every simplicial degree it sends
a functor into the product category to the pair of its two projections. -/
def nerveTypeProductIsoExplicit (C D : Type u) [Category.{u} C] [Category.{u} D] :
    CategoryTheory.nerve (C × D) ≅ CategoryTheory.nerve C ⊗ CategoryTheory.nerve D where
  hom :=
    { app := fun _ ↦ ↾fun F ↦
        ⟨F ⋙ CategoryTheory.Prod.fst C D, F ⋙ CategoryTheory.Prod.snd C D⟩
      naturality := fun _ _ _ ↦ rfl }
  inv :=
    { app := fun _ ↦ ↾fun F ↦ F.1.prod' F.2
      naturality := fun _ _ _ ↦ rfl }
  hom_inv_id := by
    rfl
  inv_hom_id := by
    rfl

/-- Split an `(n+1)`-bit vector into its first `n` bits and its last bit. -/
def finBitvectorSuccOrderIso (n : ℕ) :
    (Fin (n + 1) → Fin 2) ≃o ((Fin n → Fin 2) × Fin 2) where
  toFun b := (⟨fun a ↦ b a.castSucc, b (Fin.last n)⟩)
  invFun b := Fin.lastCases b.2 b.1
  left_inv b := by
    funext a
    refine Fin.lastCases ?_ (fun i ↦ ?_) a
    · simp
    · simp
  right_inv b := by
    ext a
    · simp
    · simp
  map_rel_iff' := by
    intro a b
    constructor
    · rintro ⟨hinit, hlast⟩ i
      refine Fin.lastCases ?_ (fun q ↦ ?_) i
      · exact hlast
      · exact hinit q
    · intro h
      exact ⟨fun i ↦ h i.castSucc, h (Fin.last n)⟩

/-- An order isomorphism induces an actual isomorphism of ordinary nerves. -/
noncomputable def nerveOrderIso {α β : Type u} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) : CategoryTheory.nerve α ≅ CategoryTheory.nerve β where
  hom := CategoryTheory.nerveMap e.equivalence.functor
  inv := CategoryTheory.nerveMap e.equivalence.inverse
  hom_inv_id := by
    change CategoryTheory.nerveFunctor.map e.equivalence.functor.toCatHom ≫
      CategoryTheory.nerveFunctor.map e.equivalence.inverse.toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hf : e.equivalence.functor ⋙ e.equivalence.inverse =
        CategoryTheory.Functor.id α := by
      exact CategoryTheory.Functor.ext
        (h_obj := fun a ↦ e.left_inv a)
        (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
    have hc : e.equivalence.functor.toCatHom ≫ e.equivalence.inverse.toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact hf
    rw [hc, CategoryTheory.Functor.map_id]
    rfl
  inv_hom_id := by
    change CategoryTheory.nerveFunctor.map e.equivalence.inverse.toCatHom ≫
      CategoryTheory.nerveFunctor.map e.equivalence.functor.toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hf : e.equivalence.inverse ⋙ e.equivalence.functor =
        CategoryTheory.Functor.id β := by
      exact CategoryTheory.Functor.ext
        (h_obj := fun b ↦ e.right_inv b)
        (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
    have hc : e.equivalence.inverse.toCatHom ≫ e.equivalence.functor.toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact hf
    rw [hc, CategoryTheory.Functor.map_id]
    rfl

/-- One cubical coordinate splits off as one copy of the walking interval. -/
noncomputable def finBitvectorNerveSuccIso (n : ℕ) :
    @CategoryTheory.nerve (Fin (n + 1) → Fin 2)
      (Preorder.smallCategory (Fin (n + 1) → Fin 2)) ≅
      @CategoryTheory.nerve ((Fin n → Fin 2) × Fin 2)
        (Preorder.smallCategory ((Fin n → Fin 2) × Fin 2)) :=
  nerveOrderIso (finBitvectorSuccOrderIso n)

/-- Non-reducible wrapper selecting the thin preorder category on bitvectors. -/
@[ext]
structure ThinBits (n : ℕ) where
  val : Fin n → Fin 2

instance (n : ℕ) : PartialOrder (ThinBits n) :=
  PartialOrder.lift ThinBits.val (fun _ _ h ↦ ThinBits.ext h)

/-- Non-reducible wrapper selecting the pointwise Pi category on the same bitvectors. -/
@[ext]
structure PiBits (n : ℕ) where
  val : Fin n → Fin 2

instance (n : ℕ) : CategoryTheory.Category (PiBits n) where
  Hom a b := ∀ i, a.val i ⟶ b.val i
  id _ _ := 𝟙 _
  comp f g i := f i ≫ g i
  assoc _ _ _ := rfl

instance (n : ℕ) (a b : PiBits n) : Subsingleton (a ⟶ b) :=
  Pi.instSubsingleton

/-- Forget the pointwise categorical presentation to the thin presentation. -/
def piBitsToThinBitsFunctor (n : ℕ) : CategoryTheory.Functor (PiBits n) (ThinBits n) where
  obj b := ⟨b.val⟩
  map f := homOfLE (fun i ↦ leOfHom (f i))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Recover the pointwise categorical presentation from the thin presentation. -/
def thinBitsToPiBitsFunctor (n : ℕ) : CategoryTheory.Functor (ThinBits n) (PiBits n) where
  obj b := ⟨b.val⟩
  map f i := homOfLE (leOfHom f i)
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def piBitsThinBitsEquivalence (n : ℕ) : PiBits n ≌ ThinBits n :=
  CategoryTheory.Equivalence.mk (piBitsToThinBitsFunctor n) (thinBitsToPiBitsFunctor n)
    (NatIso.ofComponents (fun b ↦ Iso.refl _))
    (NatIso.ofComponents (fun b ↦ Iso.refl _))

/-- The two thin presentations have isomorphic ordinary nerves. -/
noncomputable def piBitsThinBitsNerveIso (n : ℕ) :
    CategoryTheory.nerve (PiBits n) ≅ CategoryTheory.nerve (ThinBits n) where
  hom := CategoryTheory.nerveMap (piBitsToThinBitsFunctor n)
  inv := CategoryTheory.nerveMap (thinBitsToPiBitsFunctor n)
  hom_inv_id := by
    change CategoryTheory.nerveFunctor.map (piBitsToThinBitsFunctor n).toCatHom ≫
      CategoryTheory.nerveFunctor.map (thinBitsToPiBitsFunctor n).toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hf : piBitsToThinBitsFunctor n ⋙ thinBitsToPiBitsFunctor n =
        CategoryTheory.Functor.id (PiBits n) := by
      exact CategoryTheory.Functor.ext
        (h_obj := fun _ ↦ rfl) (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
    have hc : (piBitsToThinBitsFunctor n).toCatHom ≫
        (thinBitsToPiBitsFunctor n).toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact hf
    rw [hc, CategoryTheory.Functor.map_id]
    rfl

  inv_hom_id := by
    change CategoryTheory.nerveFunctor.map (thinBitsToPiBitsFunctor n).toCatHom ≫
      CategoryTheory.nerveFunctor.map (piBitsToThinBitsFunctor n).toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hf : thinBitsToPiBitsFunctor n ⋙ piBitsToThinBitsFunctor n =
        CategoryTheory.Functor.id (ThinBits n) := by
      exact CategoryTheory.Functor.ext
        (h_obj := fun _ ↦ rfl) (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
    have hc : (thinBitsToPiBitsFunctor n).toCatHom ≫
        (piBitsToThinBitsFunctor n).toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact hf
    rw [hc, CategoryTheory.Functor.map_id]
    rfl

/-- The universe-lifted walking ordered pair is exactly the standard one-simplex. -/
noncomputable def stdSimplexOneIsoNerveFinTwo :
    (Δ[1] : SSet.{u}) ≅ CategoryTheory.nerve (ULift.{u} (Fin 2)) :=
  SSet.stdSimplex.isoNerve 1

/-- Universe-lifted pointwise bitvectors, so their nerve and every interval factor live in the
same simplicial-set universe. -/
@[ext]
structure LiftedPiBits (n : ℕ) : Type u where
  val : Fin n → ULift.{u} (Fin 2)

instance (n : ℕ) : CategoryTheory.Category (LiftedPiBits.{u} n) where
  Hom a b := ∀ i, a.val i ⟶ b.val i
  id _ _ := 𝟙 _
  comp f g i := f i ≫ g i
  assoc _ _ _ := rfl

instance (n : ℕ) (a b : LiftedPiBits.{u} n) : Subsingleton (a ⟶ b) :=
  Pi.instSubsingleton

instance (n : ℕ) (a b : LiftedPiBits.{u} n × ULift.{u} (Fin 2)) :
    Subsingleton (a ⟶ b) := by
  constructor
  intro f g
  ext
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

/-- Split the final lifted cubical coordinate. -/
def liftedPiBitsSuccEquiv (n : ℕ) :
    LiftedPiBits.{u} (n + 1) ≃ (LiftedPiBits.{u} n × ULift.{u} (Fin 2)) where
  toFun b := (⟨⟨fun i ↦ b.val i.castSucc⟩, b.val (Fin.last n)⟩)
  invFun b := ⟨Fin.lastCases b.2 b.1.val⟩
  left_inv b := by
    ext i
    refine Fin.lastCases ?_ (fun q ↦ ?_) i <;> simp
  right_inv b := by
    ext i
    · simp
    · simp

/-- Forward functor for the lifted final-coordinate split. -/
def liftedPiBitsSuccFunctor (n : ℕ) : CategoryTheory.Functor
    (LiftedPiBits.{u} (n + 1)) (LiftedPiBits.{u} n × ULift.{u} (Fin 2)) where
  obj := liftedPiBitsSuccEquiv n
  map f := ⟨fun i ↦ f i.castSucc, f (Fin.last n)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Inverse functor for the lifted final-coordinate split. -/
def liftedPiBitsSuccInverse (n : ℕ) : CategoryTheory.Functor
    (LiftedPiBits.{u} n × ULift.{u} (Fin 2)) (LiftedPiBits.{u} (n + 1)) where
  obj := (liftedPiBitsSuccEquiv n).symm
  map f i := by
    refine Fin.lastCases ?_ (fun q ↦ ?_) i
    · simpa [liftedPiBitsSuccEquiv] using f.2
    · simpa [liftedPiBitsSuccEquiv] using f.1 q
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The lifted bitvector nerve splits off its last interval coordinate. -/
noncomputable def liftedPiBitsNerveSuccIso (n : ℕ) :
    CategoryTheory.nerve (LiftedPiBits.{u} (n + 1)) ≅
      CategoryTheory.nerve (LiftedPiBits.{u} n × ULift.{u} (Fin 2)) where
  hom := CategoryTheory.nerveMap (liftedPiBitsSuccFunctor n)
  inv := CategoryTheory.nerveMap (liftedPiBitsSuccInverse n)
  hom_inv_id := by
    change CategoryTheory.nerveFunctor.map (liftedPiBitsSuccFunctor n).toCatHom ≫
      CategoryTheory.nerveFunctor.map (liftedPiBitsSuccInverse n).toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hf : liftedPiBitsSuccFunctor n ⋙ liftedPiBitsSuccInverse n =
        CategoryTheory.Functor.id (LiftedPiBits.{u} (n + 1)) := by
      exact CategoryTheory.Functor.ext
        (h_obj := fun b ↦ (liftedPiBitsSuccEquiv n).left_inv b)
        (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
    have hc : (liftedPiBitsSuccFunctor n).toCatHom ≫
        (liftedPiBitsSuccInverse n).toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact hf
    rw [hc, CategoryTheory.Functor.map_id]
    rfl

  inv_hom_id := by
    change CategoryTheory.nerveFunctor.map (liftedPiBitsSuccInverse n).toCatHom ≫
      CategoryTheory.nerveFunctor.map (liftedPiBitsSuccFunctor n).toCatHom = _
    rw [← CategoryTheory.Functor.map_comp]
    have hf : liftedPiBitsSuccInverse n ⋙ liftedPiBitsSuccFunctor n =
        CategoryTheory.Functor.id (LiftedPiBits.{u} n × ULift.{u} (Fin 2)) := by
      exact CategoryTheory.Functor.ext
        (h_obj := fun b ↦ (liftedPiBitsSuccEquiv n).right_inv b)
        (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
    have hc : (liftedPiBitsSuccInverse n).toCatHom ≫
        (liftedPiBitsSuccFunctor n).toCatHom = 𝟙 _ := by
      apply CategoryTheory.Cat.Hom.ext
      exact hf
    rw [hc, CategoryTheory.Functor.map_id]
    rfl

/-- The recursively parenthesized `n`-cube, with the harmless zero-dimensional factor kept as
the nerve of the empty bitvector category. -/
noncomputable def liftedIntervalCube : ℕ → SSet.{u}
  | 0 => CategoryTheory.nerve (LiftedPiBits.{u} 0)
  | n + 1 => liftedIntervalCube n ⊗ (Δ[1] : SSet.{u})

noncomputable def binaryProductIsoTensor (X Y : SSet.{u}) : X ⨯ Y ≅ X ⊗ Y :=
  ((CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso
    (CategoryTheory.Limits.prodIsProd X Y)).symm

/-- Cubical boundary, recursively expressed by the union-product (hence by a
pushout-product of inclusions). -/
noncomputable def liftedIntervalCubeBoundary : (n : ℕ) → (liftedIntervalCube n).Subcomplex
  | 0 => ⊥
  | n + 1 => (liftedIntervalCubeBoundary n).unionProd ∂Δ[1]

/-- The cubical horn omitting one of the two final-coordinate faces.  It contains the entire
boundary in the preceding coordinates and the selected endpoint in the final coordinate. -/
noncomputable def liftedIntervalCubeLastHorn (n : ℕ) (k : Fin 2) :
    (liftedIntervalCube (n + 1)).Subcomplex :=
  (liftedIntervalCubeBoundary n).unionProd (SSet.horn 1 k)

/-- A cubical horn inclusion is the pushout-product of a monomorphism with a one-dimensional
horn inclusion, and is therefore an anodyne extension. -/
theorem liftedIntervalCubeLastHorn_anodyne (n : ℕ) (k : Fin 2) :
    SSet.anodyneExtensions (liftedIntervalCubeLastHorn n k).ι :=
  SSet.anodyneExtensions_unionProd_ι (liftedIntervalCubeBoundary n) (SSet.horn 1 k)
    (SSet.anodyneExtensions.horn_ι k)

/-- Consequently every map having the Kan horn RLP has the required cubical-horn lift. -/
theorem liftedIntervalCubeLastHorn_hasLiftingProperty {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (n : ℕ) (k : Fin 2) :
    HasLiftingProperty (liftedIntervalCubeLastHorn n k).ι p := by
  have h := liftedIntervalCubeLastHorn_anodyne n k
  rw [SSet.anodyneExtensions_eq_llp_rlp] at h
  exact h p hp

/-- The actual cubical latching objects arising from a coherent inner horn are corner horns:
for every coordinate exactly one endpoint face is prescribed.  The function `ε` records the
chosen endpoint in each coordinate. -/
noncomputable def liftedIntervalCubeCorner : (n : ℕ) → (Fin n → Fin 2) →
    (liftedIntervalCube n).Subcomplex
  | 0, _ => ⊥
  | n + 1, ε =>
      liftedIntervalCubeCorner n (fun a ↦ ε a.castSucc) |>.unionProd
        (SSet.horn 1 (ε (Fin.last n)))

/-- A cubical corner horn is an iterated pushout-product of one-dimensional horn inclusions,
so its inclusion is an anodyne extension. -/
theorem liftedIntervalCubeCorner_anodyne (n : ℕ) (ε : Fin (n + 1) → Fin 2) :
    SSet.anodyneExtensions (liftedIntervalCubeCorner (n + 1) ε).ι :=
  SSet.anodyneExtensions_unionProd_ι
    (liftedIntervalCubeCorner n (fun a ↦ ε a.castSucc))
    (SSet.horn 1 (ε (Fin.last n)))
    (SSet.anodyneExtensions.horn_ι (ε (Fin.last n)))

theorem liftedIntervalCubeCorner_hasLiftingProperty {E B : SSet.{u}} (p : E ⟶ B)
    (hp : SSet.modelCategoryQuillen.J.rlp p) (n : ℕ) (ε : Fin (n + 1) → Fin 2) :
    HasLiftingProperty (liftedIntervalCubeCorner (n + 1) ε).ι p := by
  have h := liftedIntervalCubeCorner_anodyne n ε
  rw [SSet.anodyneExtensions_eq_llp_rlp] at h
  exact h p hp

/-- The nerve of lifted bitvectors is recursively a product of walking intervals. -/
noncomputable def liftedPiBitsCubeIso : (n : ℕ) →
    CategoryTheory.nerve (LiftedPiBits.{u} n) ≅ liftedIntervalCube n
  | 0 => Iso.refl _
  | n + 1 =>
      (liftedPiBitsNerveSuccIso n).trans <|
        (nerveTypeProductIso (LiftedPiBits.{u} n) (ULift.{u} (Fin 2))).trans <|
          CategoryTheory.Limits.prod.mapIso (liftedPiBitsCubeIso n)
            stdSimplexOneIsoNerveFinTwo.symm ≪≫
          binaryProductIsoTensor _ _

/-- Computation-friendly cube comparison, using the explicit pointwise nerve-product map in
every successor step. -/
noncomputable def liftedPiBitsCubeIsoExplicit : (n : ℕ) →
    CategoryTheory.nerve (LiftedPiBits.{u} n) ≅ liftedIntervalCube n
  | 0 => Iso.refl _
  | n + 1 =>
      liftedPiBitsNerveSuccIso n ≪≫
        nerveTypeProductIsoExplicit (LiftedPiBits.{u} n) (ULift.{u} (Fin 2)) ≪≫
          MonoidalCategory.tensorIso (liftedPiBitsCubeIsoExplicit n)
            stdSimplexOneIsoNerveFinTwo.symm

/-- Evaluation of a lifted bitvector at one cubical coordinate. -/
def liftedPiBitsEval (n : ℕ) (a : Fin n) :
    CategoryTheory.Functor (LiftedPiBits.{u} n) (ULift.{u} (Fin 2)) where
  obj b := b.val a
  map f := f a
  map_id _ := rfl
  map_comp _ _ := rfl

theorem liftedPiBitsCubeIsoExplicit_succ_fst (n : ℕ) (U : SimplexCategoryᵒᵖ)
    (x : (CategoryTheory.nerve (LiftedPiBits.{u} (n + 1))).obj U) :
    ((liftedPiBitsCubeIsoExplicit (n + 1)).hom.app U x).1 =
      (liftedPiBitsCubeIsoExplicit n).hom.app U
        ((CategoryTheory.nerveMap
          (liftedPiBitsSuccFunctor n ⋙
            CategoryTheory.Prod.fst (LiftedPiBits.{u} n) (ULift.{u} (Fin 2)))).app U x) :=
  rfl

theorem liftedPiBitsCubeIsoExplicit_succ_snd (n : ℕ) (U : SimplexCategoryᵒᵖ)
    (x : (CategoryTheory.nerve (LiftedPiBits.{u} (n + 1))).obj U) :
    ((liftedPiBitsCubeIsoExplicit (n + 1)).hom.app U x).2 =
      stdSimplexOneIsoNerveFinTwo.inv.app U
        ((CategoryTheory.nerveMap
          (liftedPiBitsSuccFunctor n ⋙
            CategoryTheory.Prod.snd (LiftedPiBits.{u} n) (ULift.{u} (Fin 2)))).app U x) :=
  rfl

theorem liftedPiBitsEval_castSucc (n : ℕ) (a : Fin n) (U : SimplexCategoryᵒᵖ)
    (x : (CategoryTheory.nerve (LiftedPiBits.{u} (n + 1))).obj U) :
    (CategoryTheory.nerveMap (liftedPiBitsEval n a)).app U
        ((CategoryTheory.nerveMap
          (liftedPiBitsSuccFunctor n ⋙
            CategoryTheory.Prod.fst (LiftedPiBits.{u} n) (ULift.{u} (Fin 2)))).app U x) =
      (CategoryTheory.nerveMap (liftedPiBitsEval (n + 1) a.castSucc)).app U x :=
  rfl

theorem liftedPiBitsEval_last (n : ℕ) (U : SimplexCategoryᵒᵖ)
    (x : (CategoryTheory.nerve (LiftedPiBits.{u} (n + 1))).obj U) :
    (CategoryTheory.nerveMap
        (liftedPiBitsSuccFunctor n ⋙
          CategoryTheory.Prod.snd (LiftedPiBits.{u} n) (ULift.{u} (Fin 2)))).app U x =
      (CategoryTheory.nerveMap (liftedPiBitsEval (n + 1) (Fin.last n))).app U x :=
  rfl

theorem mem_liftedIntervalCubeCorner_explicit_iff : ∀ (n : ℕ) (ε : Fin n → Fin 2)
    (U : SimplexCategoryᵒᵖ) (x : (CategoryTheory.nerve (LiftedPiBits.{u} n)).obj U),
    (liftedPiBitsCubeIsoExplicit n).hom.app U x ∈
        (liftedIntervalCubeCorner n ε).obj U ↔
      ∃ a : Fin n, (CategoryTheory.nerveMap (liftedPiBitsEval n a)).app U x ∈
        ((SSet.horn 1 (ε a)).preimage stdSimplexOneIsoNerveFinTwo.inv).obj U
  | 0, ε, U, x => by simp [liftedIntervalCubeCorner]
  | n + 1, ε, U, x => by
      rw [show liftedIntervalCubeCorner (n + 1) ε =
        (liftedIntervalCubeCorner n (fun a ↦ ε a.castSucc)).unionProd
          (SSet.horn 1 (ε (Fin.last n))) from rfl]
      have hm := SSet.Subcomplex.mem_unionProd_iff
        (S := liftedIntervalCubeCorner n (fun a ↦ ε a.castSucc))
        (T := SSet.horn 1 (ε (Fin.last n)))
        ((liftedPiBitsCubeIsoExplicit (n + 1)).hom.app U x)
      refine hm.trans ?_
      rw [liftedPiBitsCubeIsoExplicit_succ_fst,
        liftedPiBitsCubeIsoExplicit_succ_snd,
        mem_liftedIntervalCubeCorner_explicit_iff n (fun a ↦ ε a.castSucc)]
      constructor
      · rintro (hlast | ⟨a, ha⟩)
        · refine ⟨Fin.last n, ?_⟩
          simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_last] using hlast
        · refine ⟨a.castSucc, ?_⟩
          simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_castSucc] using ha
      · rintro ⟨a, ha⟩
        induction a using Fin.lastCases with
        | last =>
            left
            simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_last] using ha
        | cast b =>
            right
            refine ⟨b, ?_⟩
            simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_castSucc] using ha

/-- The explicit cubical boundary consists of simplices constant in some coordinate. -/
theorem mem_liftedIntervalCubeBoundary_explicit_iff : ∀ (n : ℕ)
    (U : SimplexCategoryᵒᵖ) (x : (CategoryTheory.nerve (LiftedPiBits.{u} n)).obj U),
    (liftedPiBitsCubeIsoExplicit n).hom.app U x ∈
        (liftedIntervalCubeBoundary n).obj U ↔
      ∃ a : Fin n, (CategoryTheory.nerveMap (liftedPiBitsEval n a)).app U x ∈
        ((∂Δ[1]).preimage stdSimplexOneIsoNerveFinTwo.inv).obj U
  | 0, U, x => by simp [liftedIntervalCubeBoundary]
  | n + 1, U, x => by
      rw [show liftedIntervalCubeBoundary (n + 1) =
        (liftedIntervalCubeBoundary n).unionProd ∂Δ[1] from rfl]
      have hm := SSet.Subcomplex.mem_unionProd_iff
        (S := liftedIntervalCubeBoundary n) (T := ∂Δ[1])
        ((liftedPiBitsCubeIsoExplicit (n + 1)).hom.app U x)
      refine hm.trans ?_
      rw [liftedPiBitsCubeIsoExplicit_succ_fst,
        liftedPiBitsCubeIsoExplicit_succ_snd,
        mem_liftedIntervalCubeBoundary_explicit_iff n]
      constructor
      · rintro (hlast | ⟨a, ha⟩)
        · refine ⟨Fin.last n, ?_⟩
          simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_last] using hlast
        · refine ⟨a.castSucc, ?_⟩
          simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_castSucc] using ha
      · rintro ⟨a, ha⟩
        induction a using Fin.lastCases with
        | last =>
            left
            simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_last] using ha
        | cast b =>
            right
            refine ⟨b, ?_⟩
            simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_castSucc] using ha

/-- The last horn contains earlier boundary faces and one final-coordinate endpoint. -/
theorem mem_liftedIntervalCubeLastHorn_explicit_iff (n : ℕ) (k : Fin 2)
    (U : SimplexCategoryᵒᵖ)
    (x : (CategoryTheory.nerve (LiftedPiBits.{u} (n + 1))).obj U) :
    (liftedPiBitsCubeIsoExplicit (n + 1)).hom.app U x ∈
        (liftedIntervalCubeLastHorn n k).obj U ↔
      (∃ a : Fin n,
        (CategoryTheory.nerveMap (liftedPiBitsEval (n + 1) a.castSucc)).app U x ∈
          ((∂Δ[1]).preimage stdSimplexOneIsoNerveFinTwo.inv).obj U) ∨
        (CategoryTheory.nerveMap
          (liftedPiBitsEval (n + 1) (Fin.last n))).app U x ∈
            ((SSet.horn 1 k).preimage stdSimplexOneIsoNerveFinTwo.inv).obj U := by
  rw [show liftedIntervalCubeLastHorn n k =
    (liftedIntervalCubeBoundary n).unionProd (SSet.horn 1 k) from rfl]
  have hm := SSet.Subcomplex.mem_unionProd_iff
    (S := liftedIntervalCubeBoundary n) (T := SSet.horn 1 k)
    ((liftedPiBitsCubeIsoExplicit (n + 1)).hom.app U x)
  refine hm.trans ?_
  rw [liftedPiBitsCubeIsoExplicit_succ_fst,
    liftedPiBitsCubeIsoExplicit_succ_snd,
    mem_liftedIntervalCubeBoundary_explicit_iff n]
  constructor
  · rintro (hlast | ⟨a, ha⟩)
    · right
      simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_last] using hlast
    · left
      exact ⟨a, by simpa [SSet.Subcomplex.preimage_obj,
        liftedPiBitsEval_castSucc] using ha⟩
  · rintro (⟨a, ha⟩ | hlast)
    · right
      exact ⟨a, by simpa [SSet.Subcomplex.preimage_obj,
        liftedPiBitsEval_castSucc] using ha⟩
    · left
      simpa [SSet.Subcomplex.preimage_obj, liftedPiBitsEval_last] using hlast


/-- A numbering of the internal vertices identifies the path poset with the lifted cubical
bitvector category. -/
noncomputable def thickPathLiftedPiBitsEquiv {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    ThickPath i j ≃ LiftedPiBits.{u} n where
  toFun P := ⟨fun a ↦ ULift.up ((thickPathBitvectorOrderIso hij P) (e.symm a))⟩
  invFun b := (thickPathBitvectorOrderIso hij).symm (fun x ↦ (b.val (e x)).down)
  left_inv P := by
    apply (thickPathBitvectorOrderIso hij).injective
    funext x
    simp
  right_inv b := by
    ext a
    simp

/-- Forward categorical presentation of the numbered cubical path poset. -/
noncomputable def thickPathToLiftedPiBitsFunctor {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    CategoryTheory.Functor (ThickPath i j) (LiftedPiBits.{u} n) where
  obj := thickPathLiftedPiBitsEquiv hij n e
  map {P Q} f a := by
    apply homOfLE
    change ((thickPathBitvectorOrderIso hij P) (e.symm a)) ≤
      ((thickPathBitvectorOrderIso hij Q) (e.symm a))
    exact ((thickPathBitvectorOrderIso hij).le_iff_le.mpr (fun _ hx ↦ f.1.1.1 hx))
      (e.symm a)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Inverse categorical presentation of the numbered cubical path poset. -/
noncomputable def liftedPiBitsToThickPathFunctor {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    CategoryTheory.Functor (LiftedPiBits.{u} n) (ThickPath i j) where
  obj := (thickPathLiftedPiBitsEquiv hij n e).symm
  map {P Q} f := by
    refine ⟨⟨⟨?_⟩⟩⟩
    apply (thickPathBitvectorOrderIso hij).le_iff_le.mp
    intro x
    simpa [thickPathLiftedPiBitsEquiv] using leOfHom (f (e x))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The path mapping nerve is the cube indexed by any chosen enumeration of its internal
vertices. -/
noncomputable def thickPathNerveCubeIso {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    CategoryTheory.nerve (ThickPath i j) ≅ liftedIntervalCube n :=
  ({ hom := CategoryTheory.nerveMap (thickPathToLiftedPiBitsFunctor hij n e)
     inv := CategoryTheory.nerveMap (liftedPiBitsToThickPathFunctor hij n e)
     hom_inv_id := by
       change CategoryTheory.nerveFunctor.map
           (thickPathToLiftedPiBitsFunctor hij n e).toCatHom ≫
         CategoryTheory.nerveFunctor.map
           (liftedPiBitsToThickPathFunctor hij n e).toCatHom = _
       rw [← CategoryTheory.Functor.map_comp]
       have hf : thickPathToLiftedPiBitsFunctor hij n e ⋙
           liftedPiBitsToThickPathFunctor hij n e = CategoryTheory.Functor.id _ :=
         CategoryTheory.Functor.ext
         (h_obj := fun P ↦ (thickPathLiftedPiBitsEquiv hij n e).left_inv P)
         (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
       have hc : (thickPathToLiftedPiBitsFunctor hij n e).toCatHom ≫
           (liftedPiBitsToThickPathFunctor hij n e).toCatHom = 𝟙 _ := by
         apply CategoryTheory.Cat.Hom.ext
         exact hf
       rw [hc, CategoryTheory.Functor.map_id]
       rfl
     inv_hom_id := by
       change CategoryTheory.nerveFunctor.map
           (liftedPiBitsToThickPathFunctor hij n e).toCatHom ≫
         CategoryTheory.nerveFunctor.map
           (thickPathToLiftedPiBitsFunctor hij n e).toCatHom = _
       rw [← CategoryTheory.Functor.map_comp]
       have hf : liftedPiBitsToThickPathFunctor hij n e ⋙
           thickPathToLiftedPiBitsFunctor hij n e = CategoryTheory.Functor.id _ :=
         CategoryTheory.Functor.ext
         (h_obj := fun b ↦ (thickPathLiftedPiBitsEquiv hij n e).right_inv b)
         (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
       have hc : (liftedPiBitsToThickPathFunctor hij n e).toCatHom ≫
           (thickPathToLiftedPiBitsFunctor hij n e).toCatHom = 𝟙 _ := by
         apply CategoryTheory.Cat.Hom.ext
         exact hf
       rw [hc, CategoryTheory.Functor.map_id]
       rfl } :
      CategoryTheory.nerve (ThickPath i j) ≅ CategoryTheory.nerve (LiftedPiBits.{u} n)).trans
    (liftedPiBitsCubeIso n)

/-- The computation-friendly path-cube comparison, obtained by composing the explicit
bitvector presentation directly with the recursive explicit cube comparison. -/
noncomputable def thickPathNerveCubeIsoExplicit {J : Type u} [LinearOrder J]
    {i j : J} (hij : i ≤ j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    CategoryTheory.nerve (ThickPath i j) ≅ liftedIntervalCube n :=
  ({ hom := CategoryTheory.nerveMap (thickPathToLiftedPiBitsFunctor hij n e)
     inv := CategoryTheory.nerveMap (liftedPiBitsToThickPathFunctor hij n e)
     hom_inv_id := by
       change CategoryTheory.nerveFunctor.map
           (thickPathToLiftedPiBitsFunctor hij n e).toCatHom ≫
         CategoryTheory.nerveFunctor.map
           (liftedPiBitsToThickPathFunctor hij n e).toCatHom = _
       rw [← CategoryTheory.Functor.map_comp]
       have hf : thickPathToLiftedPiBitsFunctor hij n e ⋙
           liftedPiBitsToThickPathFunctor hij n e = CategoryTheory.Functor.id _ :=
         CategoryTheory.Functor.ext
         (h_obj := fun P ↦ (thickPathLiftedPiBitsEquiv hij n e).left_inv P)
         (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
       have hc : (thickPathToLiftedPiBitsFunctor hij n e).toCatHom ≫
           (liftedPiBitsToThickPathFunctor hij n e).toCatHom = 𝟙 _ := by
         apply CategoryTheory.Cat.Hom.ext
         exact hf
       rw [hc, CategoryTheory.Functor.map_id]
       rfl
     inv_hom_id := by
       change CategoryTheory.nerveFunctor.map
           (liftedPiBitsToThickPathFunctor hij n e).toCatHom ≫
         CategoryTheory.nerveFunctor.map
           (thickPathToLiftedPiBitsFunctor hij n e).toCatHom = _
       rw [← CategoryTheory.Functor.map_comp]
       have hf : liftedPiBitsToThickPathFunctor hij n e ⋙
           thickPathToLiftedPiBitsFunctor hij n e = CategoryTheory.Functor.id _ :=
         CategoryTheory.Functor.ext
         (h_obj := fun b ↦ (thickPathLiftedPiBitsEquiv hij n e).right_inv b)
         (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)
       have hc : (liftedPiBitsToThickPathFunctor hij n e).toCatHom ≫
           (thickPathToLiftedPiBitsFunctor hij n e).toCatHom = 𝟙 _ := by
         apply CategoryTheory.Cat.Hom.ext
         exact hf
       rw [hc, CategoryTheory.Functor.map_id]
       rfl } :
      CategoryTheory.nerve (ThickPath i j) ≅ CategoryTheory.nerve (LiftedPiBits.{u} n)).trans
    (liftedPiBitsCubeIsoExplicit n)

/-- The prefix of a path at one of its vertices. -/
def beforePath {J : Type u} [LinearOrder J] {i j k : J} (P : ThickPath i j)
    (hk : k ∈ P.I) : ThickPath i k where
  I := P.I ∩ Set.Iic k
  left := ⟨P.left, P.left_le k hk⟩
  right := ⟨hk, le_rfl⟩
  left_le _ hl := P.left_le _ hl.1
  le_right _ hl := hl.2

/-- The suffix of a path at one of its vertices. -/
def afterPath {J : Type u} [LinearOrder J] {i j k : J} (P : ThickPath i j)
    (hk : k ∈ P.I) : ThickPath k j where
  I := P.I ∩ Set.Ici k
  left := ⟨hk, le_rfl⟩
  right := ⟨P.right, P.le_right k hk⟩
  left_le _ hl := hl.2
  le_right _ hl := P.le_right _ hl.1

@[simp]
theorem mem_prefix_iff {J : Type u} [LinearOrder J] {i j k : J}
    (P : ThickPath i j) (hk : k ∈ P.I) (l : J) :
    l ∈ (beforePath P hk).I ↔ l ∈ P.I ∧ l ≤ k :=
  Iff.rfl

@[simp]
theorem mem_suffix_iff {J : Type u} [LinearOrder J] {i j k : J}
    (P : ThickPath i j) (hk : k ∈ P.I) (l : J) :
    l ∈ (afterPath P hk).I ↔ l ∈ P.I ∧ k ≤ l :=
  Iff.rfl

/-- Concatenate two paths meeting at an intermediate vertex. -/
def join {J : Type u} [LinearOrder J] {i j k : J}
    (P : ThickPath i k) (Q : ThickPath k j) : ThickPath i j where
  I := P.I ∪ Q.I
  left := Or.inl P.left
  right := Or.inr Q.right
  left_le l := by
    rintro (hl | hl)
    · exact P.left_le l hl
    · exact (P.left_le k P.right).trans (Q.left_le l hl)
  le_right l := by
    rintro (hl | hl)
    · exact (P.le_right l hl).trans (Q.le_right k Q.left)
    · exact Q.le_right l hl

@[simp]
theorem mem_join_iff {J : Type u} [LinearOrder J] {i j k : J}
    (P : ThickPath i k) (Q : ThickPath k j) (l : J) :
    l ∈ (join P Q).I ↔ l ∈ P.I ∨ l ∈ Q.I :=
  Iff.rfl

/-- Concatenation reflects inclusion.  At the meeting point, membership can move from one
piece to the other, but both pieces contain that point, so no information is lost. -/
theorem join_subset_iff {J : Type u} [LinearOrder J] {i j k : J}
    (P P' : ThickPath i k) (Q Q' : ThickPath k j) :
    (join P Q).I ⊆ (join P' Q').I ↔ P.I ⊆ P'.I ∧ Q.I ⊆ Q'.I := by
  constructor
  · intro h
    constructor
    · intro l hl
      rcases h (Or.inl hl) with hl' | hl'
      · exact hl'
      · have hlk := P.le_right l hl
        have hkl := Q'.left_le l hl'
        exact (le_antisymm hlk hkl) ▸ P'.right
    · intro l hl
      rcases h (Or.inr hl) with hl' | hl'
      · have hkl := Q.left_le l hl
        have hlk := P'.le_right l hl'
        exact (le_antisymm hkl hlk) ▸ Q'.left
      · exact hl'
  · rintro ⟨hP, hQ⟩ l (hl | hl)
    · exact Or.inl (hP hl)
    · exact Or.inr (hQ hl)

/-- Splitting a path at a contained vertex and composing the pieces recovers the path. -/
theorem beforePath_comp_afterPath {J : Type u} [LinearOrder J] {i j k : J}
    (P : ThickPath i j) (hk : k ∈ P.I) :
    join (beforePath P hk) (afterPath P hk) = P := by
  apply SimplicialThickening.Path.ext
  ext l
  constructor
  · rintro (hl | hl)
    · exact hl.1
    · exact hl.1
  · intro hl
    rcases le_total l k with hlk | hkl
    · exact Or.inl ⟨hl, hlk⟩
    · exact Or.inr ⟨hl, hkl⟩

/-- Inclusion of paths restricts to inclusion of their prefixes. -/
def beforePathMap {J : Type u} [LinearOrder J] {i j k : J}
    {P Q : ThickPath i j} (f : P ⟶ Q) (hkP : k ∈ P.I) :
    beforePath P hkP ⟶ beforePath Q (f.1.1.1 hkP) :=
  ⟨⟨⟨fun _ hl ↦ ⟨f.1.1.1 hl.1, hl.2⟩⟩⟩⟩

/-- Inclusion of paths restricts to inclusion of their suffixes. -/
def afterPathMap {J : Type u} [LinearOrder J] {i j k : J}
    {P Q : ThickPath i j} (f : P ⟶ Q) (hkP : k ∈ P.I) :
    afterPath P hkP ⟶ afterPath Q (f.1.1.1 hkP) :=
  ⟨⟨⟨fun _ hl ↦ ⟨f.1.1.1 hl.1, hl.2⟩⟩⟩⟩

/-- A path is `k`-critical when it contains the intermediate vertex `k`. -/
def Critical {J : Type u} [LinearOrder J] {i j : J} (k : J) :=
  { P : ThickPath i j // k ∈ P.I }

/-- Split a critical path into composable prefix and suffix paths. -/
def splitCritical {J : Type u} [LinearOrder J] {i j k : J} :
    Critical (i := i) (j := j) k →
      ThickPath i k × ThickPath k j :=
  fun P ↦ (beforePath P.1 P.2, afterPath P.1 P.2)

/-- Compose a prefix and suffix to obtain a critical path. -/
def joinCritical {J : Type u} [LinearOrder J] {i j k : J} :
    ThickPath i k × ThickPath k j → Critical (i := i) (j := j) k :=
  fun P ↦ ⟨join P.1 P.2, Or.inl P.1.right⟩

theorem splitCritical_joinCritical {J : Type u} [LinearOrder J] {i j k : J}
    (P : ThickPath i k × ThickPath k j) :
    splitCritical (joinCritical P) = P := by
  rcases P with ⟨P, Q⟩
  apply Prod.ext
  · apply SimplicialThickening.Path.ext
    ext l
    constructor
    · rintro ⟨hl | hl, hlk⟩
      · exact hl
      · exact (le_antisymm (Q.left_le l hl) hlk) ▸ P.right
    · intro hl
      exact ⟨Or.inl hl, P.le_right l hl⟩
  · apply SimplicialThickening.Path.ext
    ext l
    constructor
    · rintro ⟨hl | hl, hkl⟩
      · exact (le_antisymm hkl (P.le_right l hl)) ▸ Q.left
      · exact hl
    · intro hl
      exact ⟨Or.inr hl, Q.left_le l hl⟩

theorem joinCritical_splitCritical {J : Type u} [LinearOrder J] {i j k : J}
    (P : Critical (i := i) (j := j) k) :
    joinCritical (splitCritical P) = P := by
  apply Subtype.ext
  exact beforePath_comp_afterPath P.1 P.2

/-- Critical paths are exactly pairs of composable paths through `k`. -/
def criticalEquivProduct {J : Type u} [LinearOrder J] {i j k : J} :
    Critical (i := i) (j := j) k ≃ ThickPath i k × ThickPath k j where
  toFun := splitCritical
  invFun := joinCritical
  left_inv := joinCritical_splitCritical
  right_inv := splitCritical_joinCritical

end Path

namespace Chain

open Path

/-- A simplex in the nerve of a path poset, presented as an increasing finite chain. -/
@[ext]
structure PathChain {J : Type u} [LinearOrder J] (r : ℕ) (i j : J) where
  path : Fin (r + 1) → ThickPath i j
  monotone' : ∀ {a b : Fin (r + 1)}, a ≤ b → (path a).I ⊆ (path b).I

namespace PathChain

variable {J : Type u} [LinearOrder J] {r s : ℕ} {i j : J}

/-- Extract the increasing path chain represented by a simplex of the path-poset nerve. -/
def ofNerveSimplex
    (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r))) : PathChain r i j where
  path := x.obj
  monotone' := fun {_ _} hab ↦
    (x.map (CategoryTheory.homOfLE hab)).1.1.1

@[simp]
theorem ofNerveSimplex_path
    (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r))) (a : Fin (r + 1)) :
    (ofNerveSimplex x).path a = x.obj a :=
  rfl

private def homOfSubset {P Q : ThickPath i j} (h : P.I ⊆ Q.I) : P ⟶ Q :=
  ⟨⟨⟨h⟩⟩⟩

/-- Realize an increasing path chain as a simplex of the path-poset nerve. -/
noncomputable def toNerveSimplex (c : PathChain r i j) :
    (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r)) :=
  CategoryTheory.ComposableArrows.mkOfObjOfMapSucc c.path
    (fun a ↦ homOfSubset (c.monotone' (Fin.castSucc_le_succ a)))

@[simp]
theorem toNerveSimplex_obj (c : PathChain r i j) (a : Fin (r + 1)) :
    (c.toNerveSimplex).obj a = c.path a :=
  rfl

/-- Coordinate evaluation of the explicit cubical presentation records exactly the
corresponding bit of every path in the chain. -/
theorem thickPathToLiftedPiBits_toNerveSimplex_obj (c : PathChain r i j)
    (hij : i ≤ j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n)
    (a : Fin (r + 1)) (q : Fin n) :
    (((CategoryTheory.nerveMap
      (thickPathToLiftedPiBitsFunctor hij n e)).app
        (Opposite.op (SimplexCategory.mk r)) c.toNerveSimplex).obj a).val q =
      ULift.up ((thickPathBitvectorOrderIso hij (c.path a)) (e.symm q)) :=
  rfl

/-- Passing from a path chain to the corresponding nerve simplex and back changes no paths. -/
theorem ofNerveSimplex_toNerveSimplex (c : PathChain r i j) :
    ofNerveSimplex c.toNerveSimplex = c := by
  cases c
  rfl

/-- The chain presentation loses no information from a path-poset nerve simplex. -/
theorem toNerveSimplex_ofNerveSimplex
    (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r))) :
    (ofNerveSimplex x).toNerveSimplex = x := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Simplices of a path-poset nerve are equivalently increasing finite chains of paths. -/
noncomputable def nerveSimplexEquivPathChain :
    (CategoryTheory.nerve (ThickPath i j)).obj
        (Opposite.op (SimplexCategory.mk r)) ≃ PathChain r i j where
  toFun := ofNerveSimplex
  invFun := toNerveSimplex
  left_inv := toNerveSimplex_ofNerveSimplex
  right_inv := ofNerveSimplex_toNerveSimplex

/-- The least path in a nonempty path chain. -/
def first (c : PathChain r i j) : ThickPath i j := c.path 0

/-- The greatest path in a nonempty path chain. -/
def last (c : PathChain r i j) : ThickPath i j := c.path (Fin.last r)

/-- Reindex a path chain along a monotone map of finite ordinals. -/
def reindex (c : PathChain r i j) (f : Fin (s + 1) →o Fin (r + 1)) :
    PathChain s i j where
  path := c.path ∘ f
  monotone' := fun hab ↦ c.monotone' (f.monotone hab)

@[simp]
theorem reindex_path (c : PathChain r i j) (f : Fin (s + 1) →o Fin (r + 1))
    (a : Fin (s + 1)) : (c.reindex f).path a = c.path (f a) :=
  rfl

/-- Simplicial operators on the nerve are exactly monotone reindexings of path chains. -/
theorem ofNerveSimplex_map_toNerveSimplex (c : PathChain r i j)
    (f : SimplexCategory.mk s ⟶ SimplexCategory.mk r) :
    ofNerveSimplex ((CategoryTheory.nerve (ThickPath i j)).map f.op c.toNerveSimplex) =
      c.reindex f.toOrderHom := by
  apply PathChain.ext
  funext a
  rfl

theorem mem_ofSimplex_toNerveSimplex_iff (c : PathChain r i j) (d : PathChain s i j) :
    d.toNerveSimplex ∈ (SSet.Subcomplex.ofSimplex c.toNerveSimplex).obj _ ↔
      ∃ f : SimplexCategory.mk s ⟶ SimplexCategory.mk r,
        d = c.reindex f.toOrderHom := by
  rw [SSet.Subcomplex.mem_ofSimplex_obj_iff]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    have h := congrArg ofNerveSimplex hf
    simpa only [ofNerveSimplex_map_toNerveSimplex,
      ofNerveSimplex_toNerveSimplex] using h.symm
  · rintro ⟨f, rfl⟩
    refine ⟨f, ?_⟩
    rw [← toNerveSimplex_ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f.op c.toNerveSimplex)]
    rw [ofNerveSimplex_map_toNerveSimplex]

theorem first_le (c : PathChain r i j) (a : Fin (r + 1)) :
    c.first.I ⊆ (c.path a).I := by
  exact c.monotone' (Fin.zero_le a)

theorem le_last (c : PathChain r i j) (a : Fin (r + 1)) :
    (c.path a).I ⊆ c.last.I := by
  exact c.monotone' (Fin.le_last a)

/-- If the least path passes through a vertex, every path in the chain passes through it. -/
theorem mem_of_mem_first (c : PathChain r i j) {k : J} (hk : k ∈ c.first.I)
    (a : Fin (r + 1)) : k ∈ (c.path a).I :=
  c.first_le a hk

/-- If the greatest path omits a vertex, every path in the chain omits it. -/
theorem not_mem_of_not_mem_last (c : PathChain r i j) {k : J} (hk : k ∉ c.last.I)
    (a : Fin (r + 1)) : k ∉ (c.path a).I := by
  intro h
  exact hk (c.le_last a h)

/-- Append a specified greatest path.  The `dite` presentation makes the last face of the
paired cell definitionally visible. -/
def appendTop (c : PathChain r i j) (P : ThickPath i j) (hP : c.last.I ⊆ P.I) :
    PathChain (r + 1) i j where
  path a := if ha : a = Fin.last (r + 1) then P else c.path (a.castPred ha)
  monotone' := by
    intro a b hab
    by_cases hb : b = Fin.last (r + 1)
    · subst b
      simp only [dite_true]
      by_cases ha : a = Fin.last (r + 1)
      · subst a
        simp
      · simp only [dite_false, ha]
        exact fun _ h ↦ hP (c.le_last _ h)
    · have ha : a ≠ Fin.last (r + 1) := fun ha ↦
        hb (le_antisymm (Fin.le_last b) (ha ▸ hab))
      simp only [dite_false, ha, hb]
      exact c.monotone' (Fin.castPred_le_castPred_iff.2 hab)

@[simp]
theorem appendTop_path_castSucc (c : PathChain r i j) (P : ThickPath i j)
    (hP : c.last.I ⊆ P.I) (a : Fin (r + 1)) :
    (c.appendTop P hP).path a.castSucc = c.path a := by
  simp [appendTop, Fin.castSucc_ne_last]

@[simp]
theorem appendTop_path_last (c : PathChain r i j) (P : ThickPath i j)
    (hP : c.last.I ⊆ P.I) :
    (c.appendTop P hP).path (Fin.last (r + 1)) = P := by
  simp [appendTop]

/-- The full path between two endpoints. -/
def fullPath (i j : J) (hij : i ≤ j) : ThickPath i j where
  I := Set.Icc i j
  left := ⟨le_rfl, hij⟩
  right := ⟨hij, le_rfl⟩
  left_le _ h := h.1
  le_right _ h := h.2

@[simp]
theorem mem_fullPath_iff (i j l : J) (hij : i ≤ j) :
    l ∈ (fullPath i j hij).I ↔ i ≤ l ∧ l ≤ j :=
  Iff.rfl

/-- Adjoin a bounded vertex to a path. -/
def adjoinVertex (P : ThickPath i j) (k : J) (hik : i ≤ k) (hkj : k ≤ j) :
    ThickPath i j where
  I := P.I ∪ {k}
  left := Or.inl P.left
  right := Or.inl P.right
  left_le l := by
    rintro (hl | rfl)
    · exact P.left_le l hl
    · exact hik
  le_right l := by
    rintro (hl | rfl)
    · exact P.le_right l hl
    · exact hkj

@[simp]
theorem mem_adjoinVertex_iff (P : ThickPath i j) (k l : J)
    (hik : i ≤ k) (hkj : k ≤ j) :
    l ∈ (adjoinVertex P k hik hkj).I ↔ l ∈ P.I ∨ l = k := by
  simp only [adjoinVertex, Set.mem_union, Set.mem_singleton_iff]

theorem subset_adjoinVertex (P : ThickPath i j) (k : J)
    (hik : i ≤ k) (hkj : k ≤ j) :
    P.I ⊆ (adjoinVertex P k hik hkj).I :=
  fun _ h ↦ Or.inl h

/-- Remove a non-endpoint vertex from a path. -/
def eraseVertex (P : ThickPath i j) (k : J) (hik : i ≠ k) (hkj : j ≠ k) :
    ThickPath i j where
  I := P.I \ {k}
  left := ⟨P.left, by simpa using hik⟩
  right := ⟨P.right, by simpa using hkj⟩
  left_le l hl := P.left_le l hl.1
  le_right l hl := P.le_right l hl.1

@[simp]
theorem mem_eraseVertex_iff (P : ThickPath i j) (k l : J)
    (hik : i ≠ k) (hkj : j ≠ k) :
    l ∈ (eraseVertex P k hik hkj).I ↔ l ∈ P.I ∧ l ≠ k := by
  simp [eraseVertex]

theorem eraseVertex_subset (P : ThickPath i j) (k : J)
    (hik : i ≠ k) (hkj : j ≠ k) :
    (eraseVertex P k hik hkj).I ⊆ P.I :=
  fun _ h ↦ h.1

/-- Removing and then adjoining a contained inner vertex recovers the path. -/
theorem adjoin_eraseVertex {P : ThickPath i j} {k : J}
    (hik : i ≠ k) (hkj : j ≠ k) (hik' : i ≤ k) (hkj' : k ≤ j)
    (hk : k ∈ P.I) :
    adjoinVertex (eraseVertex P k hik hkj) k hik' hkj' = P := by
  apply SimplicialThickening.Path.ext
  ext l
  constructor
  · rintro (hl | rfl)
    · exact hl.1
    · exact hk
  · intro hl
    by_cases hlk : l = k
    · exact Or.inr hlk
    · exact Or.inl ⟨hl, hlk⟩

@[simp]
theorem adjoinVertex_eq_self_iff (P : ThickPath i j) (k : J)
    (hik : i ≤ k) (hkj : k ≤ j) :
    adjoinVertex P k hik hkj = P ↔ k ∈ P.I := by
  constructor
  · intro h
    rw [← h]
    exact Or.inr rfl
  · intro hk
    apply SimplicialThickening.Path.ext
    ext l
    constructor
    · rintro (hl | rfl)
      · exact hl
      · exact hk
    · exact Or.inl

/-- The part of the path-poset nerve already supplied by the `k`th inner horn.  A chain is
known if its least member factors through `k`, or if its greatest member omits some other
vertex of the interval. -/
def KnownAt (c : PathChain r i j) (k : J) : Prop :=
  k ∈ c.first.I ∨ ∃ l : J, i ≤ l ∧ l ≤ j ∧ l ≠ k ∧ l ∉ c.last.I

/-- The path factors internally or omits an available horn vertex. -/
def FullyKnownAt (c : PathChain r i j) (k : J) : Prop :=
  (∃ m : InteriorVertex i j, m.1 ∈ c.first.I) ∨
    ∃ l : InteriorVertex i j, l.1 ≠ k ∧ l.1 ∉ c.last.I

/-- In Boolean coordinates, the coherent-horn latching condition is a cubical corner:
the missing coordinate is fixed at `1` on the first path, or one of the other coordinates is
fixed at `0` on the last path. -/
theorem knownAt_iff_bitvector_corner (c : PathChain r i j) (k : J)
    (hik : i < k) (hkj : k < j) :
    c.KnownAt k ↔
      (thickPathBitvectorOrderIso (le_trans (le_of_lt hik) (le_of_lt hkj)) c.first)
          ⟨k, hik, hkj⟩ = 1 ∨
        ∃ x : InteriorVertex i j, x.1 ≠ k ∧
          (thickPathBitvectorOrderIso (le_trans (le_of_lt hik) (le_of_lt hkj)) c.last) x = 0 := by
  classical
  simp only [KnownAt, thickPathBitvectorOrderIso, OrderIso.trans_apply,
    setBitvectorOrderIso, thickPathInteriorOrderIso]
  constructor
  · rintro (hk | ⟨l, hil, hlj, hlk, hl⟩)
    · exact Or.inl (by simp [hk])
    · have hil' : i < l := lt_of_le_of_ne hil (by
        intro h
        apply hl
        simpa [h] using c.last.left)
      have hlj' : l < j := lt_of_le_of_ne hlj (by
        intro h
        apply hl
        simpa [h] using c.last.right)
      exact Or.inr ⟨⟨l, hil', hlj'⟩, hlk, by simp [hl]⟩
  · rintro (hk | ⟨x, hxk, hx⟩)
    · left
      simpa using hk
    · right
      refine ⟨x.1, le_of_lt x.2.1, le_of_lt x.2.2, hxk, ?_⟩
      simpa using hx

/-- Boolean coordinates identify the full latching condition with a cubical horn. -/
theorem fullyKnownAt_iff_bitvector_horn (c : PathChain r i j) (k : J)
    (hik : i < k) (hkj : k < j) :
    c.FullyKnownAt k ↔
      (∃ x : InteriorVertex i j,
        (thickPathBitvectorOrderIso (le_trans (le_of_lt hik) (le_of_lt hkj)) c.first) x = 1) ∨
      ∃ x : InteriorVertex i j, x.1 ≠ k ∧
        (thickPathBitvectorOrderIso (le_trans (le_of_lt hik) (le_of_lt hkj)) c.last) x = 0 := by
  simp only [FullyKnownAt]
  constructor
  · rintro (⟨x, hx⟩ | ⟨x, hxk, hx⟩)
    · exact Or.inl ⟨x, by simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
        setBitvectorOrderIso, thickPathInteriorOrderIso] using hx⟩
    · exact Or.inr ⟨x, hxk, by simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
        setBitvectorOrderIso, thickPathInteriorOrderIso] using hx⟩
  · rintro (⟨x, hx⟩ | ⟨x, hxk, hx⟩)
    · exact Or.inl ⟨x, by simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
        setBitvectorOrderIso, thickPathInteriorOrderIso] using hx⟩
    · exact Or.inr ⟨x, hxk, by simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
        setBitvectorOrderIso, thickPathInteriorOrderIso] using hx⟩

/-- A monotone path chain is constantly `1` in one Boolean coordinate exactly when its
least path is `1` in that coordinate. -/
theorem bitvector_all_one_iff_first (c : PathChain r i j) (hij : i ≤ j)
    (x : InteriorVertex i j) :
    (∀ a, (thickPathBitvectorOrderIso hij (c.path a)) x = 1) ↔
      (thickPathBitvectorOrderIso hij c.first) x = 1 := by
  constructor
  · intro h
    exact h 0
  · intro h a
    have hx : x.1 ∈ c.first.I := by
      simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
        setBitvectorOrderIso, thickPathInteriorOrderIso] using h
    have hsub : c.first.I ⊆ (c.path a).I := c.monotone' (Fin.zero_le a)
    simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
      setBitvectorOrderIso, thickPathInteriorOrderIso] using hsub hx

/-- A monotone path chain is constantly `0` in one Boolean coordinate exactly when its
greatest path is `0` in that coordinate. -/
theorem bitvector_all_zero_iff_last (c : PathChain r i j) (hij : i ≤ j)
    (x : InteriorVertex i j) :
    (∀ a, (thickPathBitvectorOrderIso hij (c.path a)) x = 0) ↔
      (thickPathBitvectorOrderIso hij c.last) x = 0 := by
  constructor
  · intro h
    exact h (Fin.last r)
  · intro h a
    have hx : x.1 ∉ c.last.I := by
      simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
        setBitvectorOrderIso, thickPathInteriorOrderIso] using h
    have hsub : (c.path a).I ⊆ c.last.I := c.monotone' (Fin.le_last a)
    by_contra ha
    have : x.1 ∈ (c.path a).I := by
      simpa [thickPathBitvectorOrderIso, OrderIso.trans_apply,
        setBitvectorOrderIso, thickPathInteriorOrderIso] using ha
    exact hx (hsub this)

/-- Endpoint signs for the cubical corner supplied by the `k`th coherent horn: the coordinate
of `k` is fixed at `1`, while every other internal coordinate is fixed at `0`. -/
noncomputable def coherentCornerSign (k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin n) : Fin n → Fin 2 :=
  fun a ↦ if e.symm a = ⟨k, hik, hkj⟩ then 1 else 0

@[simp]
theorem coherentCornerSign_at_missing (k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    coherentCornerSign k hik hkj n e (e ⟨k, hik, hkj⟩) = 1 := by
  simp [coherentCornerSign]

theorem coherentCornerSign_of_ne (k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin n) (a : Fin n)
    (ha : (e.symm a).1 ≠ k) : coherentCornerSign k hik hkj n e a = 0 := by
  simp only [coherentCornerSign]
  split
  · rename_i h
    exact (ha (congrArg Subtype.val h)).elim
  · rfl

/-- A simplex of the one-dimensional standard simplex lies in a one-dimensional horn exactly
when it is constantly the selected endpoint. -/
theorem mem_horn_one_iff_constant {d : ℕ} (s : (Δ[1] : SSet.{u}).obj (Opposite.op ⦋d⦌))
    (k : Fin 2) : s ∈ (SSet.horn 1 k).obj _ ↔ ∀ a, s a = k := by
  rw [SSet.mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hjk, hj⟩ a
    by_contra hsk
    apply hj
    refine ⟨a, ?_⟩
    apply Fin.ext
    have hs := (s a).isLt
    have hj' := j.isLt
    have hk' := k.isLt
    simp only [Fin.ext_iff] at hjk hsk ⊢
    omega
  · intro h
    fin_cases k
    · refine ⟨1, by simp, ?_⟩
      rintro ⟨a, ha⟩
      exact Fin.zero_ne_one ((h a).symm.trans ha)
    · refine ⟨0, by simp, ?_⟩
      rintro ⟨a, ha⟩
      exact Fin.zero_ne_one (ha.symm.trans (h a))

/-- A walking-interval simplex is in the boundary exactly when it is constant. -/
theorem mem_boundary_one_iff_constant {d : ℕ}
    (s : (Δ[1] : SSet.{u}).obj (Opposite.op ⦋d⦌)) :
    s ∈ (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).obj _ ↔
      (∀ a, s a = 0) ∨ ∀ a, s a = 1 := by
  rw [SSet.mem_boundary_iff_notMem_range]
  have eq_one_of_ne_zero (z : Fin 2) (hz : z ≠ 0) : z = 1 := by
    rcases Fin.eq_zero_or_eq_succ z with rfl | ⟨q, rfl⟩
    · exact (hz rfl).elim
    · apply Fin.ext
      simp
  have eq_zero_of_ne_one (z : Fin 2) (hz : z ≠ 1) : z = 0 := by
    rcases Fin.eq_zero_or_eq_succ z with rfl | ⟨q, rfl⟩
    · rfl
    · exfalso
      apply hz
      apply Fin.ext
      simp
  constructor
  · rintro ⟨j, hj⟩
    fin_cases j
    · right
      intro a
      exact eq_one_of_ne_zero (s a) (fun h ↦ hj ⟨a, h⟩)
    · left
      intro a
      exact eq_zero_of_ne_one (s a) (fun h ↦ hj ⟨a, h⟩)
  · rintro (h | h)
    · refine ⟨1, ?_⟩
      rintro ⟨a, ha⟩
      exact Fin.zero_ne_one ((h a).symm.trans ha)
    · refine ⟨0, ?_⟩
      rintro ⟨a, ha⟩
      exact Fin.zero_ne_one (ha.symm.trans (h a))

theorem pathCoordinate_mem_oneHorn_iff_first
    (c : PathChain r i j) (hij : i ≤ j) (n : ℕ)
    (e : InteriorVertex i j ≃ Fin n) (q : Fin n) :
    (CategoryTheory.nerveMap (liftedPiBitsEval n q)).app
        (Opposite.op (SimplexCategory.mk r))
        ((CategoryTheory.nerveMap
          (thickPathToLiftedPiBitsFunctor hij n e)).app _ c.toNerveSimplex) ∈
      ((SSet.horn 1 (1 : Fin 2)).preimage stdSimplexOneIsoNerveFinTwo.inv).obj _ ↔
    (thickPathBitvectorOrderIso hij c.first) (e.symm q) = 1 := by
  change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈
      (SSet.horn 1 (1 : Fin 2)).obj _ ↔ _
  rw [mem_horn_one_iff_constant]
  change (∀ a : Fin (r + 1),
    (thickPathBitvectorOrderIso hij (c.path a)) (e.symm q) = 1) ↔ _
  exact bitvector_all_one_iff_first c hij (e.symm q)

theorem pathCoordinate_mem_zeroHorn_iff_last
    (c : PathChain r i j) (hij : i ≤ j) (n : ℕ)
    (e : InteriorVertex i j ≃ Fin n) (q : Fin n) :
    (CategoryTheory.nerveMap (liftedPiBitsEval n q)).app
        (Opposite.op (SimplexCategory.mk r))
        ((CategoryTheory.nerveMap
          (thickPathToLiftedPiBitsFunctor hij n e)).app _ c.toNerveSimplex) ∈
      ((SSet.horn 1 (0 : Fin 2)).preimage stdSimplexOneIsoNerveFinTwo.inv).obj _ ↔
    (thickPathBitvectorOrderIso hij c.last) (e.symm q) = 0 := by
  change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈
      (SSet.horn 1 (0 : Fin 2)).obj _ ↔ _
  rw [mem_horn_one_iff_constant]
  change (∀ a : Fin (r + 1),
    (thickPathBitvectorOrderIso hij (c.path a)) (e.symm q) = 0) ↔ _
  exact bitvector_all_zero_iff_last c hij (e.symm q)

/-- Under the explicit cubical path comparison, the coherent-horn latching condition is
exactly the corresponding cubical corner. -/
theorem thickPathCube_mem_corner_iff_knownAt
    (c : PathChain r i j) (k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    (thickPathNerveCubeIsoExplicit (le_trans (le_of_lt hik) (le_of_lt hkj)) n e).hom.app
        (Opposite.op (SimplexCategory.mk r)) c.toNerveSimplex ∈
      (liftedIntervalCubeCorner n (coherentCornerSign k hik hkj n e)).obj _ ↔
    c.KnownAt k := by
  let hij := le_trans (le_of_lt hik) (le_of_lt hkj)
  rw [show (thickPathNerveCubeIsoExplicit hij n e).hom.app
      (Opposite.op (SimplexCategory.mk r)) c.toNerveSimplex =
      (liftedPiBitsCubeIsoExplicit n).hom.app _
        ((CategoryTheory.nerveMap
          (thickPathToLiftedPiBitsFunctor hij n e)).app _ c.toNerveSimplex) from rfl]
  rw [mem_liftedIntervalCubeCorner_explicit_iff]
  rw [knownAt_iff_bitvector_corner c k hik hkj]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hqk : (e.symm q).1 = k
    · have heq : e.symm q = ⟨k, hik, hkj⟩ := Subtype.ext hqk
      left
      rw [show coherentCornerSign k hik hkj n e q = 1 by
        simp [coherentCornerSign, heq]] at hq
      rw [pathCoordinate_mem_oneHorn_iff_first c hij n e q] at hq
      simpa [heq] using hq
    · right
      refine ⟨e.symm q, hqk, ?_⟩
      rw [coherentCornerSign_of_ne k hik hkj n e q hqk] at hq
      exact (pathCoordinate_mem_zeroHorn_iff_last c hij n e q).1 hq
  · rintro (hk | ⟨x, hxk, hx⟩)
    · let q := e ⟨k, hik, hkj⟩
      refine ⟨q, ?_⟩
      rw [show coherentCornerSign k hik hkj n e q = 1 by
        simp [q, coherentCornerSign]]
      rw [pathCoordinate_mem_oneHorn_iff_first c hij n e q]
      simpa [q] using hk
    · let q := e x
      refine ⟨q, ?_⟩
      rw [coherentCornerSign_of_ne k hik hkj n e q (by simpa [q])]
      rw [pathCoordinate_mem_zeroHorn_iff_last c hij n e q]
      simpa [q] using hx

/-- Numbering the missing vertex last identifies full path latching with the last horn. -/
theorem thickPathCube_mem_lastHorn_iff_fullyKnownAt
    (c : PathChain r i j) (k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin (n + 1))
    (hkLast : e ⟨k, hik, hkj⟩ = Fin.last n) :
    (thickPathNerveCubeIsoExplicit (le_trans (le_of_lt hik) (le_of_lt hkj))
      (n + 1) e).hom.app (Opposite.op (SimplexCategory.mk r)) c.toNerveSimplex ∈
        (liftedIntervalCubeLastHorn n 1).obj _ ↔ c.FullyKnownAt k := by
  let hij := le_trans (le_of_lt hik) (le_of_lt hkj)
  rw [show (thickPathNerveCubeIsoExplicit hij (n + 1) e).hom.app
      (Opposite.op (SimplexCategory.mk r)) c.toNerveSimplex =
      (liftedPiBitsCubeIsoExplicit (n + 1)).hom.app _
        ((CategoryTheory.nerveMap
          (thickPathToLiftedPiBitsFunctor hij (n + 1) e)).app _ c.toNerveSimplex) from rfl]
  rw [mem_liftedIntervalCubeLastHorn_explicit_iff]
  rw [fullyKnownAt_iff_bitvector_horn c k hik hkj]
  constructor
  · rintro (⟨q, hq⟩ | hlast)
    · let x := e.symm q.castSucc
      have hxk : x.1 ≠ k := by
        intro hx
        have heq : x = ⟨k, hik, hkj⟩ := Subtype.ext hx
        have he : e x = q.castSucc := by simp [x]
        rw [heq, hkLast] at he
        exact Fin.castSucc_ne_last q he.symm
      change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈ (∂Δ[1]).obj _ at hq
      rw [mem_boundary_one_iff_constant] at hq
      rcases hq with hzero | hone
      · right
        refine ⟨x, hxk, ?_⟩
        have hz :
            (CategoryTheory.nerveMap (liftedPiBitsEval (n + 1) q.castSucc)).app _
                ((CategoryTheory.nerveMap
                  (thickPathToLiftedPiBitsFunctor hij (n + 1) e)).app _
                    c.toNerveSimplex) ∈
              ((SSet.horn 1 (0 : Fin 2)).preimage
                stdSimplexOneIsoNerveFinTwo.inv).obj _ := by
          change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈ (SSet.horn 1 0).obj _
          rw [mem_horn_one_iff_constant]
          exact hzero
        exact (pathCoordinate_mem_zeroHorn_iff_last c hij (n + 1) e q.castSucc).1 hz
      · left
        refine ⟨x, ?_⟩
        have ho :
            (CategoryTheory.nerveMap (liftedPiBitsEval (n + 1) q.castSucc)).app _
                ((CategoryTheory.nerveMap
                  (thickPathToLiftedPiBitsFunctor hij (n + 1) e)).app _
                    c.toNerveSimplex) ∈
              ((SSet.horn 1 (1 : Fin 2)).preimage
                stdSimplexOneIsoNerveFinTwo.inv).obj _ := by
          change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈ (SSet.horn 1 1).obj _
          rw [mem_horn_one_iff_constant]
          exact hone
        exact (pathCoordinate_mem_oneHorn_iff_first c hij (n + 1) e q.castSucc).1 ho
    · left
      refine ⟨⟨k, hik, hkj⟩, ?_⟩
      have h := (pathCoordinate_mem_oneHorn_iff_first c hij (n + 1) e
        (Fin.last n)).1 hlast
      have heLast : e.symm (Fin.last n) = ⟨k, hik, hkj⟩ := by
        rw [← hkLast, e.symm_apply_apply]
      rw [heLast] at h
      exact h
  · rintro (⟨x, hx⟩ | ⟨x, hxk, hx⟩)
    · let q := e x
      by_cases hq : q = Fin.last n
      · right
        apply (pathCoordinate_mem_oneHorn_iff_first c hij (n + 1) e
          (Fin.last n)).2
        have hx' : x = ⟨k, hik, hkj⟩ := by
          apply e.injective
          rw [hkLast, ← hq]
        have heLast : e.symm (Fin.last n) = ⟨k, hik, hkj⟩ := by
          rw [← hkLast, e.symm_apply_apply]
        rw [heLast]
        rw [hx'] at hx
        exact hx
      · obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last hq
        left
        refine ⟨a, ?_⟩
        have hone := (pathCoordinate_mem_oneHorn_iff_first c hij (n + 1) e q).2
          (by simpa [q] using hx)
        rw [← ha] at hone
        change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈ (∂Δ[1]).obj _
        rw [mem_boundary_one_iff_constant]
        right
        change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈ (SSet.horn 1 1).obj _ at hone
        rwa [mem_horn_one_iff_constant] at hone
    · let q := e x
      have hq : q ≠ Fin.last n := by
        intro hq
        apply hxk
        have hx' : x = ⟨k, hik, hkj⟩ := by
          apply e.injective
          exact hq.trans hkLast.symm
        exact congrArg Subtype.val hx'
      obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last hq
      left
      refine ⟨a, ?_⟩
      have hzero := (pathCoordinate_mem_zeroHorn_iff_last c hij (n + 1) e q).2
        (by simpa [q] using hx)
      rw [← ha] at hzero
      change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈ (∂Δ[1]).obj _
      rw [mem_boundary_one_iff_constant]
      left
      change stdSimplexOneIsoNerveFinTwo.inv.app _ _ ∈ (SSet.horn 1 0).obj _ at hzero
      rwa [mem_horn_one_iff_constant] at hzero

/-- Arbitrary monotone reindexing preserves the known-horn condition. -/
theorem knownAt_reindex (c : PathChain r i j) (k : J)
    (f : Fin (s + 1) →o Fin (r + 1)) (h : c.KnownAt k) :
    (c.reindex f).KnownAt k := by
  rcases h with h | ⟨l, hil, hlj, hlk, hl⟩
  · left
    exact c.first_le (f 0) h
  · right
    exact ⟨l, hil, hlj, hlk, fun hmem ↦ hl (c.le_last _ hmem)⟩

/-- Monotone reindexing preserves the full strict-composition latching condition. -/
theorem fullyKnownAt_reindex (c : PathChain r i j) (k : J)
    (f : Fin (s + 1) →o Fin (r + 1)) (h : c.FullyKnownAt k) :
    (c.reindex f).FullyKnownAt k := by
  rcases h with ⟨m, hm⟩ | ⟨l, hlk, hl⟩
  · exact Or.inl ⟨m, c.first_le (f 0) hm⟩
  · exact Or.inr ⟨l, hlk, fun hmem ↦ hl (c.le_last _ hmem)⟩

/-- The simplicial subcomplex of path chains supplied by an inner horn. -/
def knownPathSubcomplex (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex where
  obj U := {x | (ofNerveSimplex x).KnownAt k}
  map {U V} f x hx := by
    change (ofNerveSimplex ((CategoryTheory.nerve (ThickPath i j)).map f x)).KnownAt k
    exact knownAt_reindex (c := ofNerveSimplex x) k f.unop.toOrderHom hx

/-- The subcomplex encoding all strict factorizations and available horn faces. -/
def fullyKnownPathSubcomplex (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex where
  obj U := {x | (ofNerveSimplex x).FullyKnownAt k}
  map {U V} f x hx := by
    change (ofNerveSimplex ((CategoryTheory.nerve (ThickPath i j)).map f x)).FullyKnownAt k
    exact fullyKnownAt_reindex (c := ofNerveSimplex x) k f.unop.toOrderHom hx

theorem mem_knownPathSubcomplex_iff (i j k : J) (r : ℕ)
    (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r))) :
    x ∈ (knownPathSubcomplex i j k).obj _ ↔ (ofNerveSimplex x).KnownAt k :=
  Iff.rfl

theorem mem_knownPathSubcomplex_preimage_explicit_iff_corner
    (i j k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin n) (r : ℕ)
    (x : (liftedIntervalCube n).obj (Opposite.op (SimplexCategory.mk r))) :
    x ∈ ((knownPathSubcomplex i j k).preimage
        (thickPathNerveCubeIsoExplicit
          (le_trans (le_of_lt hik) (le_of_lt hkj)) n e).inv).obj _ ↔
      x ∈ (liftedIntervalCubeCorner n
        (coherentCornerSign k hik hkj n e)).obj _ := by
  let iso := thickPathNerveCubeIsoExplicit
    (le_trans (le_of_lt hik) (le_of_lt hkj)) n e
  let c := ofNerveSimplex (iso.inv.app _ x)
  change c.KnownAt k ↔ _
  rw [← thickPathCube_mem_corner_iff_knownAt c k hik hkj n e]
  have hc : c.toNerveSimplex = iso.inv.app _ x :=
    toNerveSimplex_ofNerveSimplex _
  rw [hc]
  change iso.hom.app _ (iso.inv.app _ x) ∈ _ ↔ x ∈ _
  rw [Iso.inv_hom_id_app_apply]

theorem knownPathSubcomplex_preimage_explicit_eq_corner
    (i j k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    (knownPathSubcomplex i j k).preimage
        (thickPathNerveCubeIsoExplicit
          (le_trans (le_of_lt hik) (le_of_lt hkj)) n e).inv =
      liftedIntervalCubeCorner n (coherentCornerSign k hik hkj n e) := by
  ext U x
  obtain ⟨⟨r⟩⟩ := U
  exact mem_knownPathSubcomplex_preimage_explicit_iff_corner
    i j k hik hkj n e r x

theorem mem_fullyKnownPathSubcomplex_preimage_explicit_iff_lastHorn
    (i j k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin (n + 1))
    (hkLast : e ⟨k, hik, hkj⟩ = Fin.last n) (r : ℕ)
    (x : (liftedIntervalCube (n + 1)).obj
      (Opposite.op (SimplexCategory.mk r))) :
    x ∈ ((fullyKnownPathSubcomplex i j k).preimage
        (thickPathNerveCubeIsoExplicit
          (le_trans (le_of_lt hik) (le_of_lt hkj)) (n + 1) e).inv).obj _ ↔
      x ∈ (liftedIntervalCubeLastHorn n 1).obj _ := by
  let iso := thickPathNerveCubeIsoExplicit
    (le_trans (le_of_lt hik) (le_of_lt hkj)) (n + 1) e
  let c := ofNerveSimplex (iso.inv.app _ x)
  change c.FullyKnownAt k ↔ _
  rw [← thickPathCube_mem_lastHorn_iff_fullyKnownAt c k hik hkj n e hkLast]
  have hc : c.toNerveSimplex = iso.inv.app _ x :=
    toNerveSimplex_ofNerveSimplex _
  rw [hc]
  change iso.hom.app _ (iso.inv.app _ x) ∈ _ ↔ x ∈ _
  rw [Iso.inv_hom_id_app_apply]

/-- The full path-latching subcomplex is the last-coordinate cubical horn. -/
theorem fullyKnownPathSubcomplex_preimage_explicit_eq_lastHorn
    (i j k : J) (hik : i < k) (hkj : k < j)
    (n : ℕ) (e : InteriorVertex i j ≃ Fin (n + 1))
    (hkLast : e ⟨k, hik, hkj⟩ = Fin.last n) :
    (fullyKnownPathSubcomplex i j k).preimage
        (thickPathNerveCubeIsoExplicit
          (le_trans (le_of_lt hik) (le_of_lt hkj)) (n + 1) e).inv =
      liftedIntervalCubeLastHorn n 1 := by
  ext U x
  obtain ⟨⟨r⟩⟩ := U
  exact mem_fullyKnownPathSubcomplex_preimage_explicit_iff_lastHorn
    i j k hik hkj n e hkLast r x

/-- A chain outside the known horn has full greatest path and its least path avoids `k`,
expressed without choosing a decidable finite enumeration. -/
theorem not_knownAt_iff (c : PathChain r i j) (k : J) :
    ¬ c.KnownAt k ↔
      k ∉ c.first.I ∧ ∀ l : J, i ≤ l → l ≤ j → l ≠ k → l ∈ c.last.I := by
  simp only [KnownAt, not_or, not_exists, not_and]
  constructor
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun l hil hlj hlk ↦ ?_⟩
    exact Classical.byContradiction fun hl ↦ h l hil hlj hlk hl
  · rintro ⟨hk, h⟩
    refine ⟨hk, fun l hil ↦ ?_⟩
    refine fun hlj ↦ ?_
    refine fun hlk ↦ ?_
    exact fun hl ↦ hl (h l hil hlj hlk)

end PathChain

end Chain

open CategoryTheory.SimplicialCategory CategoryTheory.EnrichedCategory

/-- Global coherent-simplex data, separated out as an interface for the distance induction used
to extend coherent inner horns.  A later partial variant replaces each full mapping object by its
already constructed latching subcomplex. -/
structure PartialCoherentSimplexMap (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] (J : Type u) [LinearOrder J] where
  obj : CategoryTheory.SimplicialThickening J → C
  map : ∀ i j : CategoryTheory.SimplicialThickening J,
    CategoryTheory.nerve (i ⟶ j) ⟶ (obj i ⟶[SSet] obj j)
  map_id : ∀ i,
    CategoryTheory.eId SSet i ≫ map i i = CategoryTheory.eId SSet (obj i)
  map_comp : ∀ i j k,
    CategoryTheory.eComp SSet i j k ≫ map i k =
      (map i j ⊗ₘ map j k) ≫
        CategoryTheory.eComp SSet (obj i) (obj j) (obj k)

/-- The global interface is exactly an enriched functor once every latching map has been
extended. -/
def partialCoherentSimplexMapEquiv (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] (J : Type u) [LinearOrder J] :
    PartialCoherentSimplexMap C J ≃
      CategoryTheory.EnrichedFunctor SSet (CategoryTheory.SimplicialThickening J) C where
  toFun F :=
    { obj := F.obj
      map := F.map
      map_id := F.map_id
      map_comp := F.map_comp }
  invFun F :=
    { obj := F.obj
      map := F.map
      map_id := F.map_id
      map_comp := F.map_comp }
  left_inv F := by cases F; rfl
  right_inv F := by cases F; rfl

/-- In the simplex dimensions used by `SimplicialNerve`, global coherent-simplex data are
literally its simplices. -/
def partialCoherentSimplexMapEquivSimplicialNerveObj (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] (n : SimplexCategoryᵒᵖ) :
    PartialCoherentSimplexMap C (ULift (Fin (n.unop.len + 1))) ≃
      (CategoryTheory.SimplicialNerve C).obj n :=
  partialCoherentSimplexMapEquiv C _

end LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
