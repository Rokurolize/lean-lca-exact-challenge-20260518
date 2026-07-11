import Mathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Order.Extension.Well

/-!
# Path combinatorics for the locally-Kan coherent nerve theorem

The mapping objects in the simplicial thickening are nerves of posets of paths.  This file
isolates the elementary splitting operation at an intermediate vertex.  It is the set-theoretic
operation used in the cell filtration of an inner horn: a path containing the missing vertex is
the composite of its beforePath and afterPath there.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration

open CategoryTheory Simplicial

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
  map {P Q} f := homOfLE (fun x hx ↦ f.1.1.1 hx)
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

/-- A chain is nondegenerate when distinct indices carry distinct paths.  For a monotone chain
in a poset this is the strict-chain condition. -/
def IsNondegenerate (c : PathChain r i j) : Prop := Function.Injective c.path

/-- The number of paths in a chain which contain `k`.  This is the primary finite rank
separating the punctured layer from the full-top and entry layers. -/
noncomputable def kMultiplicity (c : PathChain r i j) (k : J) : ℕ :=
  by
    classical
    exact ((Finset.univ : Finset (Fin (r + 1))).filter fun a ↦ k ∈ (c.path a).I).card

theorem kMultiplicity_eq_zero_iff (c : PathChain r i j) (k : J) :
    c.kMultiplicity k = 0 ↔ ∀ a, k ∉ (c.path a).I := by
  classical
  simp [kMultiplicity]

theorem kMultiplicity_eq_zero_of_not_mem_last (c : PathChain r i j) (k : J)
    (hk : k ∉ c.last.I) : c.kMultiplicity k = 0 := by
  rw [c.kMultiplicity_eq_zero_iff k]
  intro a h
  exact hk (c.le_last a h)

theorem kMultiplicity_pos_of_mem_last (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) : 0 < c.kMultiplicity k := by
  classical
  rw [Nat.pos_iff_ne_zero]
  intro h
  exact (c.kMultiplicity_eq_zero_iff k).1 h (Fin.last r) hk

/-- Nondegeneracy is preserved by injective simplicial operators. -/
theorem isNondegenerate_reindex (c : PathChain r i j)
    (f : Fin (s + 1) →o Fin (r + 1)) (hc : c.IsNondegenerate)
    (hf : Function.Injective f) : (c.reindex f).IsNondegenerate :=
  hc.comp hf

/-- Delete a vertex of a path chain. -/
def deleteAt (c : PathChain (r + 1) i j) (p : Fin (r + 2)) : PathChain r i j :=
  c.reindex (Fin.succAboveOrderEmb p).toOrderHom

@[simp]
theorem deleteAt_path (c : PathChain (r + 1) i j) (p : Fin (r + 2))
    (a : Fin (r + 1)) :
    (c.deleteAt p).path a = c.path (p.succAbove a) :=
  rfl

theorem isNondegenerate_deleteAt (c : PathChain (r + 1) i j) (p : Fin (r + 2))
    (hc : c.IsNondegenerate) : (c.deleteAt p).IsNondegenerate :=
  c.isNondegenerate_reindex _ hc (Fin.succAboveOrderEmb p).injective

theorem knownAt_deleteAt (c : PathChain (r + 1) i j) (p : Fin (r + 2)) (k : J)
    (hc : c.KnownAt k) : (c.deleteAt p).KnownAt k :=
  by
    rcases hc with hc | ⟨l, hil, hlj, hlk, hl⟩
    · exact Or.inl (c.first_le (p.succAbove 0) hc)
    · refine Or.inr ⟨l, hil, hlj, hlk, ?_⟩
      intro h
      exact hl (c.le_last _ h)

/-- Taking a face cannot increase the number of paths containing `k`. -/
theorem kMultiplicity_deleteAt_le (c : PathChain (r + 1) i j) (p : Fin (r + 2))
    (k : J) : (c.deleteAt p).kMultiplicity k ≤ c.kMultiplicity k := by
  classical
  unfold kMultiplicity
  apply Finset.card_le_card_of_injOn (p.succAbove)
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    change k ∈ (c.path (p.succAbove a)).I at ha
    simpa only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · exact (Fin.succAboveOrderEmb p).injective.injOn

theorem kMultiplicity_deleteAt_lt_of_mem (c : PathChain (r + 1) i j)
    (p : Fin (r + 2)) (k : J) (hp : k ∈ (c.path p).I) :
    (c.deleteAt p).kMultiplicity k < c.kMultiplicity k := by
  classical
  let s := (Finset.univ : Finset (Fin (r + 1))).filter fun a ↦
    k ∈ ((c.deleteAt p).path a).I
  let t := (Finset.univ : Finset (Fin (r + 2))).filter fun a ↦ k ∈ (c.path a).I
  have hsub : s.image p.succAbove ⊆ t := by
    intro a ha
    simp only [Finset.mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' : k ∈ ((c.deleteAt p).path b).I := by simpa [s] using hb
    simpa [t] using hb'
  have hpT : p ∈ t := by simp [t, hp]
  have hpI : p ∉ s.image p.succAbove := by
    simp [Fin.succAbove_ne]
  have hss : s.image p.succAbove ⊂ t :=
    Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h ↦ hpI (h.symm ▸ hpT)⟩
  have hcard := Finset.card_lt_card hss
  have hcardeq : (s.image p.succAbove).card = s.card :=
    Finset.card_image_of_injective _ (Fin.succAboveOrderEmb p).injective
  rw [hcardeq] at hcard
  simpa [kMultiplicity, s, t] using hcard

theorem kMultiplicity_deleteAt_eq_of_not_mem (c : PathChain (r + 1) i j)
    (p : Fin (r + 2)) (k : J) (hp : k ∉ (c.path p).I) :
    (c.deleteAt p).kMultiplicity k = c.kMultiplicity k := by
  classical
  let s := (Finset.univ : Finset (Fin (r + 1))).filter fun a ↦
    k ∈ ((c.deleteAt p).path a).I
  let t := (Finset.univ : Finset (Fin (r + 2))).filter fun a ↦ k ∈ (c.path a).I
  have himage : s.image p.succAbove = t := by
    ext a
    constructor
    · intro ha
      simp only [Finset.mem_image] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      have hb' : k ∈ ((c.deleteAt p).path b).I := by simpa [s] using hb
      simpa [t] using hb'
    · intro ha
      have ha' : k ∈ (c.path a).I := by simpa [t] using ha
      have hap : a ≠ p := fun h ↦ hp (h ▸ ha')
      obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hap
      subst a
      apply Finset.mem_image.2
      refine ⟨b, ?_, rfl⟩
      simpa [s] using ha'
  have hcard := congrArg Finset.card himage
  have hcardeq : (s.image p.succAbove).card = s.card :=
    Finset.card_image_of_injective _ (Fin.succAboveOrderEmb p).injective
  rw [hcardeq] at hcard
  simpa [kMultiplicity, s, t] using hcard

/-- The well-founded lexicographic rank: first simplex dimension, then multiplicity. -/
noncomputable def filtrationRank (c : PathChain r i j) (k : J) : ℕ × ℕ :=
  (r, c.kMultiplicity k)

/-- Every face has strictly smaller lexicographic rank than its source. -/
theorem filtrationRank_deleteAt (c : PathChain (r + 1) i j) (p : Fin (r + 2))
    (k : J) :
    Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      ((c.deleteAt p).filtrationRank k) (c.filtrationRank k) := by
  exact Prod.Lex.left _ _ (Nat.lt_succ_self r)

/-- Complete combinatorial data for one ranked inner-horn attachment. -/
structure RankedInnerFacePair (r : ℕ) (i j k : J) where
  lower : PathChain r i j
  upper : PathChain (r + 1) i j
  upperNondegenerate : upper.IsNondegenerate
  face : Fin (r + 2)
  face_pos : 0 < face
  face_lt_last : face < Fin.last (r + 1)
  lower_eq : upper.deleteAt face = lower
  other_face_lower_rank : ∀ q : Fin (r + 2), q ≠ face →
    Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      ((upper.deleteAt q).filtrationRank k) (upper.filtrationRank k)

/-- Ranked horn-attachment data in a Kan mapping object.  Unlike
`RankedInnerFacePair`, the missing face may be an outer face. -/
structure RankedKanFacePair (r : ℕ) (i j k : J) where
  lower : PathChain r i j
  upper : PathChain (r + 1) i j
  upperNondegenerate : upper.IsNondegenerate
  face : Fin (r + 2)
  lower_eq : upper.deleteAt face = lower
  other_face_lower_rank : ∀ q : Fin (r + 2), q ≠ face →
    Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      ((upper.deleteAt q).filtrationRank k) (upper.filtrationRank k)

/-- Forget that the missing face of an inner pair is inner. -/
def RankedInnerFacePair.toRankedKanFacePair {k : J}
    (a : RankedInnerFacePair r i j k) : RankedKanFacePair r i j k where
  lower := a.lower
  upper := a.upper
  upperNondegenerate := a.upperNondegenerate
  face := a.face
  lower_eq := a.lower_eq
  other_face_lower_rank := a.other_face_lower_rank

/-- Package any deletion of a nondegenerate upper chain as ranked Kan horn data. -/
def rankedKanFacePairOfDelete (lower : PathChain r i j) (upper : PathChain (r + 1) i j)
    (k : J) (hupper : upper.IsNondegenerate) (face : Fin (r + 2))
    (hdelete : upper.deleteAt face = lower) : RankedKanFacePair r i j k where
  lower := lower
  upper := upper
  upperNondegenerate := hupper
  face := face
  lower_eq := hdelete
  other_face_lower_rank := fun q _ ↦ upper.filtrationRank_deleteAt q k

namespace RankedKanFacePair

variable {k : J} (a : RankedKanFacePair r i j k)

/-- Classifying map of the upper simplex of a Kan-face pair. -/
noncomputable def upperMap : Δ[r + 1] ⟶ CategoryTheory.nerve (ThickPath i j) :=
  SSet.yonedaEquiv.symm a.upper.toNerveSimplex

/-- The horn map containing all faces except the selected face. -/
noncomputable def hornMap : (SSet.horn (r + 1) a.face : SSet) ⟶
    CategoryTheory.nerve (ThickPath i j) :=
  (SSet.horn (r + 1) a.face).ι ≫ a.upperMap

/-- The actual range of the attaching horn. -/
noncomputable def hornRange : (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  SSet.Subcomplex.range a.hornMap

noncomputable instance mono_upperMap : Mono a.upperMap := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  intro x y hxy
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext q
  apply a.upperNondegenerate
  have hxy' :
      (SSet.yonedaEquiv.symm a.upper.toNerveSimplex).app U
          (SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv x)) =
        (SSet.yonedaEquiv.symm a.upper.toNerveSimplex).app U
          (SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv y)) := by
    simpa [upperMap] using hxy
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm,
    SSet.yonedaEquiv_symm_app_objEquiv_symm] at hxy'
  exact congrArg (fun z ↦ (PathChain.ofNerveSimplex z).path q) hxy'

noncomputable instance mono_hornMap : Mono a.hornMap := by
  dsimp [hornMap]
  infer_instance

theorem range_upperMap : SSet.Subcomplex.range a.upperMap =
    SSet.Subcomplex.ofSimplex a.upper.toNerveSimplex := by
  rw [SSet.Subcomplex.range_eq_ofSimplex]
  simp [upperMap]

theorem hornRange_eq_horn_image : a.hornRange =
    (SSet.horn (r + 1) a.face).image a.upperMap := by
  rw [SSet.Subcomplex.image_eq_range]
  rfl

/-- A stage whose inverse image in the upper simplex is contained in the attaching horn
meets the generated upper simplex in exactly the horn range. -/
theorem inf_upperRange_eq_hornRange
    (A : (CategoryTheory.nerve (ThickPath i j)).Subcomplex)
    (hA : A.preimage a.upperMap ≤ SSet.horn (r + 1) a.face)
    (hhorn : a.hornRange ≤ A) :
    A ⊓ SSet.Subcomplex.ofSimplex a.upper.toNerveSimplex = a.hornRange := by
  apply le_antisymm
  · rw [← a.range_upperMap, ← SSet.Subcomplex.image_preimage_eq_inf_range,
      a.hornRange_eq_horn_image]
    exact SSet.Subcomplex.image_monotone a.upperMap hA
  · apply le_inf hhorn
    rw [a.hornRange_eq_horn_image, ← a.range_upperMap]
    exact SSet.Subcomplex.image_le_range (SSet.horn (r + 1) a.face) a.upperMap

end RankedKanFacePair

/-- Any certified inner face pair acquires the rank condition automatically from the global
face-rank theorem. -/
def rankedInnerFacePairOfDelete (lower : PathChain r i j) (upper : PathChain (r + 1) i j)
    (k : J) (hupper : upper.IsNondegenerate) (face : Fin (r + 2)) (hpos : 0 < face)
    (hlast : face < Fin.last (r + 1)) (hdelete : upper.deleteAt face = lower) :
    RankedInnerFacePair r i j k where
  lower := lower
  upper := upper
  upperNondegenerate := hupper
  face := face
  face_pos := hpos
  face_lt_last := hlast
  lower_eq := hdelete
  other_face_lower_rank := fun q _ ↦ upper.filtrationRank_deleteAt q k

namespace RankedInnerFacePair

variable {k : J} (a : RankedInnerFacePair r i j k)

/-- The horn map containing every face of the upper cell except the selected lower face. -/
noncomputable def hornMap : (SSet.horn (r + 1) a.face : SSet) ⟶
    CategoryTheory.nerve (ThickPath i j) :=
  (SSet.horn (r + 1) a.face).ι ≫ SSet.yonedaEquiv.symm a.upper.toNerveSimplex

/-- The subcomplex generated by all nonmissing faces of the upper cell. -/
noncomputable def hornRange : (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  SSet.Subcomplex.range a.hornMap

end RankedInnerFacePair

/-- Chain deletion is exactly the corresponding simplicial face of the path-poset nerve. -/
theorem toNerveSimplex_deleteAt (c : PathChain (r + 1) i j) (p : Fin (r + 2)) :
    (c.deleteAt p).toNerveSimplex =
      (CategoryTheory.nerve (ThickPath i j)).δ p c.toNerveSimplex := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Insert a path at an arbitrary position, assuming it lies between all paths below and above
that position. -/
def insertAt (c : PathChain r i j) (p : Fin (r + 2)) (P : ThickPath i j)
    (hbelow : ∀ a : Fin (r + 1), p.succAbove a < p → (c.path a).I ⊆ P.I)
    (habove : ∀ a : Fin (r + 1), p < p.succAbove a → P.I ⊆ (c.path a).I) :
    PathChain (r + 1) i j where
  path := Fin.insertNth p P c.path
  monotone' := by
    intro a b hab
    rcases Fin.eq_self_or_eq_succAbove p a with ha | ⟨a', ha⟩
    · subst a
      rcases Fin.eq_self_or_eq_succAbove p b with hb | ⟨b', hb⟩
      · subst b
        simp
      · subst b
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        exact habove b' (lt_of_le_of_ne hab (Fin.succAbove_ne p b').symm)
    · subst a
      rcases Fin.eq_self_or_eq_succAbove p b with hb | ⟨b', hb⟩
      · subst b
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        exact hbelow a' (lt_of_le_of_ne hab (Fin.succAbove_ne p a'))
      · subst b
        simp only [Fin.insertNth_apply_succAbove]
        exact c.monotone' ((Fin.succAboveOrderEmb p).le_iff_le.1 hab)

@[simp]
theorem insertAt_path_same (c : PathChain r i j) (p : Fin (r + 2)) (P : ThickPath i j)
    (hbelow) (habove) : (c.insertAt p P hbelow habove).path p = P := by
  simp [insertAt]

@[simp]
theorem insertAt_path_succAbove (c : PathChain r i j) (p : Fin (r + 2))
    (P : ThickPath i j) (hbelow) (habove) (a : Fin (r + 1)) :
    (c.insertAt p P hbelow habove).path (p.succAbove a) = c.path a := by
  simp [insertAt]

/-- Deleting the newly inserted path recovers the original chain. -/
theorem deleteAt_insertAt (c : PathChain r i j) (p : Fin (r + 2)) (P : ThickPath i j)
    (hbelow) (habove) : (c.insertAt p P hbelow habove).deleteAt p = c := by
  apply PathChain.ext
  funext a
  simp

/-- Deleting a position different from the insertion position leaves the inserted path present
in the resulting chain. -/
theorem exists_path_deleteAt_insertAt_eq_inserted (c : PathChain r i j)
    (p q : Fin (r + 2)) (P : ThickPath i j) (hbelow) (habove) (hpq : p ≠ q) :
    ∃ b : Fin (r + 1), ((c.insertAt p P hbelow habove).deleteAt q).path b = P := by
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hpq
  refine ⟨b, ?_⟩
  change (c.insertAt p P hbelow habove).path (q.succAbove b) = P
  rw [hb, insertAt_path_same]

/-- The inserted chain is independent of the proofs of its sandwich conditions. -/
theorem insertAt_proof_irrel (c : PathChain r i j) (p : Fin (r + 2)) (P : ThickPath i j)
    (hbelow hbelow' : ∀ a : Fin (r + 1), p.succAbove a < p → (c.path a).I ⊆ P.I)
    (habove habove' : ∀ a : Fin (r + 1), p < p.succAbove a → P.I ⊆ (c.path a).I) :
    c.insertAt p P hbelow habove = c.insertAt p P hbelow' habove' :=
  rfl

/-- A finite chain is uniquely determined by one deleted face and the path at the deleted
position. -/
theorem eq_of_deleteAt_eq_of_path_eq (c d : PathChain (r + 1) i j) (p : Fin (r + 2))
    (hdelete : c.deleteAt p = d.deleteAt p) (hpath : c.path p = d.path p) : c = d := by
  apply PathChain.ext
  funext a
  rcases Fin.eq_self_or_eq_succAbove p a with ha | ⟨b, hb⟩
  · exact ha ▸ hpath
  · subst a
    have h := congrArg (fun z : PathChain r i j ↦ z.path b) hdelete
    exact h

/-- Injectivity of the upper path tuple identifies the unique order map representing a chosen
codimension-one face. -/
theorem orderHom_eq_succAbove_of_path_comp_eq {A : Type*}
    (u : Fin (r + 2) → A) (hu : Function.Injective u) (p : Fin (r + 2))
    (f : Fin (r + 1) →o Fin (r + 2))
    (h : ∀ a, u (f a) = u (p.succAbove a)) :
    f = (Fin.succAboveOrderEmb p).toOrderHom := by
  ext a
  exact congrArg Fin.val (hu (h a))

theorem range_orderHom_eq_compl_singleton_of_path_comp_eq {A : Type*}
    (u : Fin (r + 2) → A) (hu : Function.Injective u) (p : Fin (r + 2))
    (f : Fin (r + 1) →o Fin (r + 2))
    (h : ∀ a, u (f a) = u (p.succAbove a)) :
    Set.range f = {p}ᶜ := by
  rw [orderHom_eq_succAbove_of_path_comp_eq u hu p f h]
  exact Fin.range_succAboveOrderEmb p

theorem range_union_singleton_eq_univ_of_path_comp_eq {A : Type*}
    (u : Fin (r + 2) → A) (hu : Function.Injective u) (p : Fin (r + 2))
    (f : Fin (r + 1) →o Fin (r + 2))
    (h : ∀ a, u (f a) = u (p.succAbove a)) :
    Set.range f ∪ {p} = Set.univ := by
  rw [range_orderHom_eq_compl_singleton_of_path_comp_eq u hu p f h]
  exact Set.compl_union_self {p}

/-- A map presenting a nondegenerate path tuple as a face of another tuple is injective. -/
theorem orderHom_injective_of_path_comp_injective {A : Type*} {m n : ℕ}
    (lower : Fin (m + 1) → A) (hlower : Function.Injective lower)
    (upper : Fin (n + 1) → A) (f : Fin (m + 1) →o Fin (n + 1))
    (h : ∀ a, lower a = upper (f a)) : Function.Injective f := by
  intro a b hab
  apply hlower
  rw [h a, h b, hab]

theorem dimension_le_of_path_comp_injective {A : Type*} {m n : ℕ}
    (lower : Fin (m + 1) → A) (hlower : Function.Injective lower)
    (upper : Fin (n + 1) → A) (f : Fin (m + 1) →o Fin (n + 1))
    (h : ∀ a, lower a = upper (f a)) : m ≤ n := by
  have hf := orderHom_injective_of_path_comp_injective lower hlower upper f h
  simpa using Fintype.card_le_of_injective f hf

/-- Every injective monotone map of codimension one is a unique coface map. -/
theorem orderHom_eq_succAbove_of_injective (f : Fin (r + 1) →o Fin (r + 2))
    (hf : Function.Injective f) :
    ∃ p : Fin (r + 2), f = (Fin.succAboveOrderEmb p).toOrderHom := by
  let θ : SimplexCategory.mk r ⟶ SimplexCategory.mk (r + 1) :=
    SimplexCategory.Hom.mk f
  haveI : Mono θ := (SimplexCategory.mono_iff_injective).2 hf
  obtain ⟨p, hp⟩ := SimplexCategory.eq_δ_of_mono θ
  refine ⟨p, ?_⟩
  have hp' := congrArg SimplexCategory.Hom.toOrderHom hp
  exact hp'

theorem orderHom_eq_succAbove_unique (f : Fin (r + 1) →o Fin (r + 2))
    (hf : Function.Injective f) :
    ∃! p : Fin (r + 2), f = (Fin.succAboveOrderEmb p).toOrderHom := by
  obtain ⟨p, hp⟩ := orderHom_eq_succAbove_of_injective f hf
  refine ⟨p, hp, fun q hq ↦ ?_⟩
  apply Fin.succAbove_left_injective
  funext a
  have h := congrArg (fun g : Fin (r + 1) →o Fin (r + 2) ↦ g a) (hp.symm.trans hq)
  exact h.symm

/-- The distinguished lower simplex is not contained in the range of the complementary horn. -/
theorem RankedInnerFacePair.lower_not_mem_hornRange {k : J}
    (a : RankedInnerFacePair r i j k) :
    a.lower.toNerveSimplex ∉ a.hornRange.obj
      (Opposite.op (SimplexCategory.mk r)) := by
  intro h
  change a.lower.toNerveSimplex ∈ Set.range
    (a.hornMap.app (Opposite.op (SimplexCategory.mk r))) at h
  rcases h with ⟨z, hz⟩
  let f : Fin (r + 1) →o Fin (r + 2) := SSet.stdSimplex.asOrderHom z.1
  have hcomp : ∀ b, a.upper.path (f b) = a.upper.path (a.face.succAbove b) := by
    intro b
    have hz' := congrArg (fun x ↦ x.obj b) hz
    change a.upper.path (f b) = a.lower.path b at hz'
    have hface := congrArg (fun x : PathChain r i j ↦ x.path b) a.lower_eq.symm
    exact hz'.trans hface
  have hrange := range_union_singleton_eq_univ_of_path_comp_eq
    a.upper.path a.upperNondegenerate a.face f hcomp
  exact z.2 hrange

/-- The distinguished lower simplex of a Kan-face pair is not in its complementary horn. -/
theorem RankedKanFacePair.lower_not_mem_hornRange {k : J}
    (a : RankedKanFacePair r i j k) :
    a.lower.toNerveSimplex ∉ a.hornRange.obj
      (Opposite.op (SimplexCategory.mk r)) := by
  intro h
  change a.lower.toNerveSimplex ∈ Set.range
    (a.hornMap.app (Opposite.op (SimplexCategory.mk r))) at h
  rcases h with ⟨z, hz⟩
  let f : Fin (r + 1) →o Fin (r + 2) := SSet.stdSimplex.asOrderHom z.1
  have hcomp : ∀ b, a.upper.path (f b) = a.upper.path (a.face.succAbove b) := by
    intro b
    have hz' := congrArg (fun x ↦ x.obj b) hz
    change a.upper.path (f b) = a.lower.path b at hz'
    have hface := congrArg (fun x : PathChain r i j ↦ x.path b) a.lower_eq.symm
    exact hz'.trans hface
  have hrange := range_union_singleton_eq_univ_of_path_comp_eq
    a.upper.path a.upperNondegenerate a.face f hcomp
  exact z.2 hrange

/-- Inserting a new path not already present preserves nondegeneracy. -/
theorem isNondegenerate_insertAt (c : PathChain r i j) (p : Fin (r + 2))
    (P : ThickPath i j) (hbelow) (habove) (hc : c.IsNondegenerate)
    (hnew : ∀ a, P ≠ c.path a) : (c.insertAt p P hbelow habove).IsNondegenerate := by
  intro a b h
  rcases Fin.eq_self_or_eq_succAbove p a with ha | ⟨a', ha⟩
  · subst a
    rcases Fin.eq_self_or_eq_succAbove p b with hb | ⟨b', hb⟩
    · exact hb.symm
    · subst b
      simp only [insertAt_path_same, insertAt_path_succAbove] at h
      exact (hnew b' h).elim
  · subst a
    rcases Fin.eq_self_or_eq_succAbove p b with hb | ⟨b', hb⟩
    · subst b
      simp only [insertAt_path_same, insertAt_path_succAbove] at h
      exact (hnew a' h.symm).elim
    · subst b
      exact congrArg (p.succAbove) (hc (by
        simpa only [insertAt_path_succAbove] using h))

private theorem deleted_below (c : PathChain (r + 1) i j) (p : Fin (r + 2))
    (a : Fin (r + 1)) (ha : p.succAbove a < p) :
    ((c.deleteAt p).path a).I ⊆ (c.path p).I :=
  c.monotone' ha.le

private theorem deleted_above (c : PathChain (r + 1) i j) (p : Fin (r + 2))
    (a : Fin (r + 1)) (ha : p < p.succAbove a) :
    (c.path p).I ⊆ ((c.deleteAt p).path a).I :=
  c.monotone' ha.le

/-- Reinsert the path removed at `p`. -/
def reinsertDeleted (c : PathChain (r + 1) i j) (p : Fin (r + 2)) :
    PathChain (r + 1) i j :=
  (c.deleteAt p).insertAt p (c.path p) (deleted_below c p) (deleted_above c p)

/-- Deletion followed by reinsertion at the same position is the identity. -/
theorem reinsertDeleted_eq (c : PathChain (r + 1) i j) (p : Fin (r + 2)) :
    c.reinsertDeleted p = c := by
  apply PathChain.ext
  funext a
  exact Fin.succAboveCases p (by simp [reinsertDeleted])
    (fun b ↦ by simp [reinsertDeleted]) a

/-- A nondegenerate chain has a strict inclusion at every adjacent pair. -/
theorem ne_succ_of_isNondegenerate (c : PathChain (r + 1) i j)
    (hc : c.IsNondegenerate) (a : Fin (r + 1)) :
    c.path a.castSucc ≠ c.path a.succ := by
  intro h
  exact (Fin.ne_of_lt a.castSucc_lt_succ) (hc h)

/-- A nondegenerate cell missing from the horn-path subcomplex. -/
@[ext]
structure UnknownCell (r : ℕ) (i j k : J) where
  chain : PathChain r i j
  nondegenerate : chain.IsNondegenerate
  unknown : ¬ chain.KnownAt k

theorem UnknownCell.first_avoids {k : J} (c : UnknownCell r i j k) :
    k ∉ c.chain.first.I := by
  intro h
  exact c.unknown (Or.inl h)

theorem UnknownCell.last_contains_other {k : J} (c : UnknownCell r i j k)
    (l : J) (hil : i ≤ l) (hlj : l ≤ j) (hlk : l ≠ k) :
    l ∈ c.chain.last.I := by
  apply Classical.byContradiction
  intro hl
  exact c.unknown (Or.inr ⟨l, hil, hlj, hlk, hl⟩)

/-- If the greatest path of an unknown cell contains `k`, it is the full path. -/
theorem UnknownCell.last_eq_fullPath_of_mem {k : J} (c : UnknownCell r i j k)
    (hk : k ∈ c.chain.last.I) :
    c.chain.last = fullPath i j (SimplicialThickening.Path.le c.chain.last) := by
  apply SimplicialThickening.Path.ext
  ext l
  constructor
  · intro hl
    exact ⟨c.chain.last.left_le l hl, c.chain.last.le_right l hl⟩
  · rintro ⟨hil, hlj⟩
    by_cases hlk : l = k
    · exact hlk ▸ hk
    · exact c.last_contains_other l hil hlj hlk

/-- If the greatest path of an unknown cell omits `k`, adjoining `k` makes it full.  Thus
unknown cells occur in the canonical pair obtained by toggling `k` in their greatest path. -/
theorem UnknownCell.adjoin_last_eq_fullPath_of_not_mem {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    adjoinVertex c.chain.last k hik hkj = fullPath i j (hik.trans hkj) := by
  apply SimplicialThickening.Path.ext
  ext l
  constructor
  · rintro (hl | rfl)
    · exact ⟨c.chain.last.left_le l hl, c.chain.last.le_right l hl⟩
    · exact ⟨hik, hkj⟩
  · rintro ⟨hil, hlj⟩
    by_cases hlk : l = k
    · exact Or.inr hlk
    · exact Or.inl (c.last_contains_other l hil hlj hlk)

/-- The top-path toggle is genuinely strict in the punctured case. -/
theorem UnknownCell.last_ne_adjoin_of_not_mem {k : J} (c : UnknownCell r i j k)
    (hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j) :
    c.chain.last ≠ adjoinVertex c.chain.last k hik hkj := by
  intro h
  exact hk (h ▸ Or.inr rfl)

/-- The higher-dimensional member of the canonical pair for a punctured unknown cell: append
the full path obtained by adjoining `k`.  Its last face is the original punctured cell, while
deleting the penultimate vertex gives the full-top partner. -/
def UnknownCell.pairUp {k : J} (c : UnknownCell r i j k)
    (_hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j) :
    PathChain (r + 1) i j :=
  c.chain.appendTop (adjoinVertex c.chain.last k hik hkj)
    (subset_adjoinVertex c.chain.last k hik hkj)

@[simp]
theorem UnknownCell.pairUp_castSucc {k : J} (c : UnknownCell r i j k)
    (hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j)
    (a : Fin (r + 1)) :
    (c.pairUp hk hik hkj).path a.castSucc = c.chain.path a := by
  simp [UnknownCell.pairUp]

@[simp]
theorem UnknownCell.pairUp_last {k : J} (c : UnknownCell r i j k)
    (hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j) :
    (c.pairUp hk hik hkj).last = fullPath i j (hik.trans hkj) := by
  change (c.pairUp hk hik hkj).path (Fin.last (r + 1)) = _
  simp only [UnknownCell.pairUp, appendTop]
  exact c.adjoin_last_eq_fullPath_of_not_mem hk hik hkj

/-- Deleting the final vertex of the paired higher cell recovers the punctured cell. -/
theorem UnknownCell.deleteAt_last_pairUp {k : J} (c : UnknownCell r i j k)
    (hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j) :
    (c.pairUp hk hik hkj).deleteAt (Fin.last (r + 1)) = c.chain := by
  apply PathChain.ext
  funext a
  simp [UnknownCell.pairUp, deleteAt]

private theorem puncturedTop_below {k : J} (c : UnknownCell r i j k)
    (_hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j)
    (a : Fin (r + 1))
    (_ha : (Fin.last (r + 1)).succAbove a < Fin.last (r + 1)) :
    (c.chain.path a).I ⊆ (adjoinVertex c.chain.last k hik hkj).I :=
  (c.chain.le_last a).trans (subset_adjoinVertex c.chain.last k hik hkj)

private theorem puncturedTop_above {k : J} (c : UnknownCell r i j k)
    (_hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j)
    (a : Fin (r + 1))
    (ha : Fin.last (r + 1) < (Fin.last (r + 1)).succAbove a) :
    (adjoinVertex c.chain.last k hik hkj).I ⊆ (c.chain.path a).I :=
  (not_lt_of_ge (Fin.le_last _) ha).elim

/-- The top higher chain, uniformly defined by insertion at the final position. -/
def UnknownCell.puncturedTopHigher {k : J} (c : UnknownCell r i j k)
    (hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j) :
    PathChain (r + 1) i j :=
  c.chain.insertAt (Fin.last (r + 1)) (adjoinVertex c.chain.last k hik hkj)
    (puncturedTop_below c hk hik hkj) (puncturedTop_above c hk hik hkj)

theorem UnknownCell.puncturedTopHigher_nondegenerate {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedTopHigher hk hik hkj).IsNondegenerate := by
  apply isNondegenerate_insertAt _ _ _ _ _ c.nondegenerate
  intro a h
  have hka : k ∉ (c.chain.path a).I := fun hka ↦ hk (c.chain.le_last a hka)
  exact hka (h ▸ Or.inr rfl)

theorem UnknownCell.mem_puncturedTopHigher_iff {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (a : Fin (r + 2)) :
    k ∈ ((c.puncturedTopHigher hk hik hkj).path a).I ↔ a = Fin.last (r + 1) := by
  rcases Fin.eq_self_or_eq_succAbove (Fin.last (r + 1)) a with ha | ⟨b, hb⟩
  · subst a
    simp [UnknownCell.puncturedTopHigher]
  · subst a
    simp only [UnknownCell.puncturedTopHigher, insertAt_path_succAbove,
      Fin.succAbove_ne]
    rw [iff_false]
    intro h
    exact hk (c.chain.le_last b h)

@[simp]
theorem UnknownCell.puncturedTopHigher_last {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedTopHigher hk hik hkj).last = fullPath i j (hik.trans hkj) := by
  change (c.puncturedTopHigher hk hik hkj).path (Fin.last (r + 1)) = _
  simp only [UnknownCell.puncturedTopHigher, insertAt_path_same]
  exact c.adjoin_last_eq_fullPath_of_not_mem hk hik hkj

/-- The outer last face of the top higher chain is the original punctured chain. -/
theorem UnknownCell.deleteAt_last_puncturedTopHigher {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedTopHigher hk hik hkj).deleteAt (Fin.last (r + 1)) = c.chain :=
  deleteAt_insertAt _ _ _ _ _

theorem UnknownCell.puncturedTopHigher_unknown {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    ¬ (c.puncturedTopHigher hk hik hkj).KnownAt k := by
  intro h
  apply c.unknown
  rw [← c.deleteAt_last_puncturedTopHigher hk hik hkj]
  exact (c.puncturedTopHigher hk hik hkj).knownAt_deleteAt (Fin.last (r + 1)) k h

/-- The top higher simplex is itself an unknown nondegenerate cell. -/
def UnknownCell.puncturedTopHigherCell {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) : UnknownCell (r + 1) i j k where
  chain := c.puncturedTopHigher hk hik hkj
  nondegenerate := c.puncturedTopHigher_nondegenerate hk hik hkj
  unknown := c.puncturedTopHigher_unknown hk hik hkj

/-- On actual nerve simplices, the outer last face is the earlier punctured cell. -/
theorem UnknownCell.puncturedTopHigher_outer_face {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (CategoryTheory.nerve (ThickPath i j)).δ (Fin.last (r + 1))
        (c.puncturedTopHigher hk hik hkj).toNerveSimplex = c.chain.toNerveSimplex := by
  rw [← toNerveSimplex_deleteAt]
  exact congrArg toNerveSimplex (c.deleteAt_last_puncturedTopHigher hk hik hkj)

/-- The missing degree-zero punctured vertex is attached by the outer last horn of the edge
from that punctured path to the full path. -/
def UnknownCell.degreeZeroPuncturedRankedKanFacePair {k : J}
    (c : UnknownCell 0 i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) : RankedKanFacePair 0 i j k :=
  rankedKanFacePairOfDelete c.chain (c.puncturedTopHigher hk hik hkj) k
    (c.puncturedTopHigher_nondegenerate hk hik hkj) (Fin.last 1)
    (c.deleteAt_last_puncturedTopHigher hk hik hkj)

@[simp]
theorem UnknownCell.degreeZeroPuncturedRankedKanFacePair_lower {k : J}
    (c : UnknownCell 0 i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.degreeZeroPuncturedRankedKanFacePair hk hik hkj).lower = c.chain :=
  rfl

@[simp]
theorem UnknownCell.degreeZeroPuncturedRankedKanFacePair_upper {k : J}
    (c : UnknownCell 0 i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.degreeZeroPuncturedRankedKanFacePair hk hik hkj).upper =
      c.puncturedTopHigher hk hik hkj :=
  rfl

@[simp]
theorem UnknownCell.degreeZeroPuncturedRankedKanFacePair_face {k : J}
    (c : UnknownCell 0 i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.degreeZeroPuncturedRankedKanFacePair hk hik hkj).face = Fin.last 1 :=
  rfl

/-- The penultimate position in a positive-dimensional top higher chain. -/
def puncturedTopInnerPosition (r : ℕ) : Fin (r + 3) :=
  Fin.castSucc (Fin.last (r + 1))

theorem puncturedTopInnerPosition_inner (r : ℕ) :
    0 < puncturedTopInnerPosition r ∧
      puncturedTopInnerPosition r < Fin.last (r + 2) := by
  constructor
  · apply Fin.castSucc_pos'
    exact Fin.last_pos
  · exact Fin.castSucc_lt_last _

/-- Every face of the top higher cell is either the outer punctured face, the distinguished
full-top face, or lies strictly before both and is therefore recursive. -/
theorem puncturedTop_face_trichotomy (r : ℕ) (q : Fin (r + 3)) :
    q = Fin.last (r + 2) ∨ q = puncturedTopInnerPosition r ∨
      q < puncturedTopInnerPosition r := by
  by_cases hlast : q = Fin.last (r + 2)
  · exact Or.inl hlast
  · right
    have hq : q < Fin.last (r + 2) := Fin.lt_last_iff_ne_last.2 hlast
    by_cases hpen : q = puncturedTopInnerPosition r
    · exact Or.inl hpen
    · have hle : q ≤ puncturedTopInnerPosition r := by
        change q.val ≤ r + 1
        change q.val < r + 2 at hq
        omega
      exact Or.inr (lt_of_le_of_ne hle hpen)

/-- A strictly earlier top face descends to a face index of the original punctured chain. -/
def puncturedTopEarlierIndex (r : ℕ) (q : Fin (r + 3))
    (hq : q < puncturedTopInnerPosition r) : Fin (r + 2) :=
  q.castPred (Fin.ne_last_of_lt (hq.trans (puncturedTopInnerPosition_inner r).2))

@[simp]
theorem puncturedTopEarlierIndex_castSucc (r : ℕ) (q : Fin (r + 3))
    (hq : q < puncturedTopInnerPosition r) :
    Fin.castSucc (puncturedTopEarlierIndex r q hq) = q :=
  Fin.castSucc_castPred _ _

theorem puncturedTopEarlierIndex_lt_last (r : ℕ) (q : Fin (r + 3))
    (hq : q < puncturedTopInnerPosition r) :
    puncturedTopEarlierIndex r q hq < Fin.last (r + 1) := by
  change q.val < r + 1
  change q.val < (puncturedTopInnerPosition r).val at hq
  exact hq

/-- Deleting a strictly earlier face preserves the full top path, so these faces belong to the
recursive full-top part of the filtration. -/
theorem UnknownCell.puncturedTopEarlierFace_last {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (q : Fin (r + 3))
    (hq : q < puncturedTopInnerPosition r) :
    ((c.puncturedTopHigher hk hik hkj).deleteAt q).last =
      fullPath i j (hik.trans hkj) := by
  apply SimplicialThickening.Path.ext
  ext l
  change l ∈ ((c.puncturedTopHigher hk hik hkj).path
    (q.succAbove (Fin.last (r + 1)))).I ↔ _
  rw [Fin.succAbove_ne_last_last (Fin.ne_of_lt
    (hq.trans (puncturedTopInnerPosition_inner r).2))]
  change l ∈ (c.puncturedTopHigher hk hik hkj).last.I ↔ _
  rw [c.puncturedTopHigher_last hk hik hkj]

/-- The full-top lower face paired with a positive-dimensional punctured cell. -/
def UnknownCell.puncturedFullTopPartner {k : J} (c : UnknownCell (r + 1) i j k)
    (hk : k ∉ c.chain.last.I) (hik : i ≤ k) (hkj : k ≤ j) :
    PathChain (r + 1) i j :=
  (c.puncturedTopHigher hk hik hkj).deleteAt (puncturedTopInnerPosition r)

/-- The full-top partner is the distinguished inner face. -/
theorem UnknownCell.puncturedFullTopPartner_face {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (CategoryTheory.nerve (ThickPath i j)).δ (puncturedTopInnerPosition r)
        (c.puncturedTopHigher hk hik hkj).toNerveSimplex =
      (c.puncturedFullTopPartner hk hik hkj).toNerveSimplex := by
  rw [← toNerveSimplex_deleteAt]
  rfl

theorem UnknownCell.puncturedFullTopPartner_first {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedFullTopPartner hk hik hkj).first = c.chain.first := by
  apply SimplicialThickening.Path.ext
  ext l
  change l ∈ ((c.puncturedTopHigher hk hik hkj).path
    ((puncturedTopInnerPosition r).succAbove 0)).I ↔ l ∈ (c.chain.path 0).I
  rw [Fin.succAbove_ne_zero_zero
    (Fin.ne_of_gt (puncturedTopInnerPosition_inner r).1)]
  change l ∈ ((c.puncturedTopHigher hk hik hkj).path
    ((Fin.last (r + 2)).succAbove 0)).I ↔ l ∈ (c.chain.path 0).I
  simp only [UnknownCell.puncturedTopHigher, insertAt_path_succAbove]

theorem UnknownCell.puncturedFullTopPartner_last {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedFullTopPartner hk hik hkj).last = fullPath i j (hik.trans hkj) := by
  apply SimplicialThickening.Path.ext
  ext l
  change l ∈ ((c.puncturedTopHigher hk hik hkj).path
    ((puncturedTopInnerPosition r).succAbove (Fin.last (r + 1)))).I ↔ _
  rw [Fin.succAbove_ne_last_last
    (Fin.ne_of_lt (puncturedTopInnerPosition_inner r).2)]
  change l ∈ (c.puncturedTopHigher hk hik hkj).last.I ↔ _
  rw [c.puncturedTopHigher_last hk hik hkj]

theorem UnknownCell.mem_puncturedFullTopPartner_iff {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (a : Fin (r + 2)) :
    k ∈ ((c.puncturedFullTopPartner hk hik hkj).path a).I ↔
      a = Fin.last (r + 1) := by
  change k ∈ ((c.puncturedTopHigher hk hik hkj).path
    ((puncturedTopInnerPosition r).succAbove a)).I ↔ _
  rw [c.mem_puncturedTopHigher_iff hk hik hkj]
  exact Fin.succAbove_eq_last_iff
    (Fin.ne_of_lt (puncturedTopInnerPosition_inner r).2)

theorem UnknownCell.puncturedFullTopPartner_unknown {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    ¬ (c.puncturedFullTopPartner hk hik hkj).KnownAt k := by
  intro h
  rcases h with h | ⟨l, hil, hlj, hlk, hl⟩
  · exact c.first_avoids (c.puncturedFullTopPartner_first hk hik hkj ▸ h)
  · rw [c.puncturedFullTopPartner_last hk hik hkj] at hl
    exact hl ⟨hil, hlj⟩

/-- The full-top partner is a genuine unknown nondegenerate cell. -/
def UnknownCell.puncturedFullTopCell {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) : UnknownCell (r + 1) i j k where
  chain := c.puncturedFullTopPartner hk hik hkj
  nondegenerate := (c.puncturedTopHigher_nondegenerate hk hik hkj).comp
    (Fin.succAboveOrderEmb (puncturedTopInnerPosition r)).injective
  unknown := c.puncturedFullTopPartner_unknown hk hik hkj

/-- In a top pair the punctured outer face has multiplicity zero. -/
theorem UnknownCell.punctured_kMultiplicity_zero {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I) :
    c.chain.kMultiplicity k = 0 :=
  c.chain.kMultiplicity_eq_zero_of_not_mem_last k hk

/-- The full-top missing face has positive multiplicity.  Thus the punctured outer face is
strictly earlier in the primary multiplicity rank. -/
theorem UnknownCell.puncturedFullTop_kMultiplicity_pos {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    0 < (c.puncturedFullTopCell hk hik hkj).chain.kMultiplicity k := by
  apply kMultiplicity_pos_of_mem_last
  change k ∈ (c.puncturedFullTopPartner hk hik hkj).last.I
  rw [c.puncturedFullTopPartner_last hk hik hkj]
  exact ⟨hik, hkj⟩

/-- The punctured support face is strictly earlier than its full-top selected lower partner. -/
theorem UnknownCell.punctured_support_rank_lt_fullTop {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      (c.chain.filtrationRank k)
      ((c.puncturedFullTopCell hk hik hkj).chain.filtrationRank k) := by
  unfold filtrationRank
  apply Prod.Lex.right _
  rw [c.punctured_kMultiplicity_zero hk]
  exact c.puncturedFullTop_kMultiplicity_pos hk hik hkj

/-- The punctured/full-top matching as complete ranked attachment data. -/
noncomputable def UnknownCell.puncturedRankedInnerFacePair {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) : RankedInnerFacePair (r + 1) i j k :=
  rankedInnerFacePairOfDelete (c.puncturedFullTopPartner hk hik hkj)
    (c.puncturedTopHigher hk hik hkj) k
    (c.puncturedTopHigher_nondegenerate hk hik hkj) (puncturedTopInnerPosition r)
    (puncturedTopInnerPosition_inner r).1 (puncturedTopInnerPosition_inner r).2 rfl

/-- If the least path passes through `k`, every path in the chain passes through `k`. -/
theorem mem_of_mem_first (c : PathChain r i j) {k : J} (hk : k ∈ c.first.I)
    (a : Fin (r + 1)) : k ∈ (c.path a).I :=
  c.first_le a hk

/-- If the greatest path omits a vertex, every path in the chain omits it. -/
theorem not_mem_of_not_mem_last (c : PathChain r i j) {k : J} (hk : k ∉ c.last.I)
    (a : Fin (r + 1)) : k ∉ (c.path a).I := by
  intro h
  exact hk (c.le_last a h)

/-- The first index at which a vertex enters a finite path chain. -/
noncomputable def entryIndex (c : PathChain r i j) (k : J) (hk : k ∈ c.last.I) :
    Fin (r + 1) := by
  classical
  let p : ℕ → Prop := fun n ↦ ∃ hn : n < r + 1, k ∈ (c.path ⟨n, hn⟩).I
  have hp : ∃ n, p n := ⟨r, by
    let hr : r < r + 1 := by omega
    refine ⟨hr, ?_⟩
    have he : (⟨r, hr⟩ : Fin (r + 1)) = Fin.last r := Fin.ext rfl
    simpa [last, he] using hk⟩
  exact ⟨Nat.find hp, (Nat.find_spec hp).choose⟩

theorem mem_entryIndex (c : PathChain r i j) (k : J) (hk : k ∈ c.last.I) :
    k ∈ (c.path (c.entryIndex k hk)).I := by
  classical
  let p : ℕ → Prop := fun n ↦ ∃ hn : n < r + 1, k ∈ (c.path ⟨n, hn⟩).I
  have hp : ∃ n, p n := ⟨r, by
    let hr : r < r + 1 := by omega
    refine ⟨hr, ?_⟩
    have he : (⟨r, hr⟩ : Fin (r + 1)) = Fin.last r := Fin.ext rfl
    simpa [last, he] using hk⟩
  change k ∈ (c.path ⟨Nat.find hp, _⟩).I
  exact (Nat.find_spec hp).choose_spec

theorem UnknownCell.puncturedTopHigher_memLast {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    k ∈ (c.puncturedTopHigher hk hik hkj).last.I := by
  change k ∈ ((c.puncturedTopHigher hk hik hkj).path (Fin.last (r + 1))).I
  exact (c.mem_puncturedTopHigher_iff hk hik hkj _).2 rfl

theorem UnknownCell.puncturedTopHigher_entryIndex_eq_last {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedTopHigher hk hik hkj).entryIndex k
      (c.puncturedTopHigher_memLast hk hik hkj) = Fin.last (r + 1) := by
  apply (c.mem_puncturedTopHigher_iff hk hik hkj _).1
  apply mem_entryIndex

theorem UnknownCell.puncturedFullTopPartner_memLast {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    k ∈ (c.puncturedFullTopPartner hk hik hkj).last.I := by
  change k ∈ ((c.puncturedFullTopPartner hk hik hkj).path (Fin.last (r + 1))).I
  exact (c.mem_puncturedFullTopPartner_iff hk hik hkj _).2 rfl

theorem UnknownCell.puncturedFullTopPartner_entryIndex_eq_last {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedFullTopPartner hk hik hkj).entryIndex k
      (c.puncturedFullTopPartner_memLast hk hik hkj) = Fin.last (r + 1) := by
  apply (c.mem_puncturedFullTopPartner_iff hk hik hkj _).1
  apply mem_entryIndex

theorem not_mem_before_entryIndex (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (a : Fin (r + 1)) (ha : a < c.entryIndex k hk) :
    k ∉ (c.path a).I := by
  classical
  intro h
  let p : ℕ → Prop := fun n ↦ ∃ hn : n < r + 1, k ∈ (c.path ⟨n, hn⟩).I
  have hp : ∃ n, p n := ⟨r, by
    let hr : r < r + 1 := by omega
    refine ⟨hr, ?_⟩
    have he : (⟨r, hr⟩ : Fin (r + 1)) = Fin.last r := Fin.ext rfl
    simpa [last, he] using hk⟩
  have hpa : p a := ⟨a.isLt, h⟩
  have hmin := Nat.find_min' hp hpa
  have hentry : (c.entryIndex k hk).val = Nat.find hp := by
    rfl
  have hlt : a.val < Nat.find hp := by
    simpa [Fin.lt_def, hentry] using ha
  exact (Nat.not_lt_of_ge hmin) hlt

/-- Characterization of the first-entry index without exposing its `Nat.find` implementation. -/
theorem entryIndex_eq_of_mem_of_before_not_mem (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (a : Fin (r + 1)) (ha : k ∈ (c.path a).I)
    (hbefore : ∀ b : Fin (r + 1), b < a → k ∉ (c.path b).I) :
    c.entryIndex k hk = a := by
  apply le_antisymm
  · apply Fin.not_lt.1
    intro h
    exact c.not_mem_before_entryIndex k hk a h ha
  · apply Fin.not_lt.1
    intro h
    exact hbefore _ h (c.mem_entryIndex k hk)

theorem entryIndex_pos_of_not_mem_first (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (h0 : k ∉ c.first.I) : 0 < c.entryIndex k hk := by
  apply Fin.pos_iff_ne_zero.2
  intro h
  apply h0
  simpa [first, h] using c.mem_entryIndex k hk

/-- The index immediately preceding the first occurrence of `k`. -/
noncomputable def beforeEntryIndex (c : PathChain r i j) (k : J) (hk : k ∈ c.last.I)
    (hpos : 0 < c.entryIndex k hk) : Fin (r + 1) :=
  Fin.castSucc ((c.entryIndex k hk).pred (Fin.ne_zero_of_lt hpos))

theorem beforeEntryIndex_lt (c : PathChain r i j) (k : J) (hk : k ∈ c.last.I)
    (hpos : 0 < c.entryIndex k hk) :
    c.beforeEntryIndex k hk hpos < c.entryIndex k hk :=
  Fin.castSucc_pred_lt _

theorem UnknownCell.puncturedTopHigher_beforeEntry_eq_oldLast {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j)
    (hpos : 0 < (c.puncturedTopHigher hk hik hkj).entryIndex k
      (c.puncturedTopHigher_memLast hk hik hkj)) :
    (c.puncturedTopHigher hk hik hkj).beforeEntryIndex k
      (c.puncturedTopHigher_memLast hk hik hkj) hpos =
        Fin.castSucc (Fin.last r) := by
  apply Fin.ext
  simp [beforeEntryIndex, c.puncturedTopHigher_entryIndex_eq_last hk hik hkj]

theorem UnknownCell.puncturedFullTop_beforeEntry_eq_penultimate {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j)
    (hpos : 0 < (c.puncturedFullTopPartner hk hik hkj).entryIndex k
      (c.puncturedFullTopPartner_memLast hk hik hkj)) :
    (c.puncturedFullTopPartner hk hik hkj).beforeEntryIndex k
      (c.puncturedFullTopPartner_memLast hk hik hkj) hpos =
        Fin.castSucc (Fin.last r) := by
  apply Fin.ext
  simp [beforeEntryIndex, c.puncturedFullTopPartner_entryIndex_eq_last hk hik hkj]

theorem UnknownCell.erase_puncturedTopHigher_entry_eq_oldLast {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    eraseVertex ((c.puncturedTopHigher hk hik hkj).path
      ((c.puncturedTopHigher hk hik hkj).entryIndex k
        (c.puncturedTopHigher_memLast hk hik hkj))) k hikne hkjne = c.chain.last := by
  rw [c.puncturedTopHigher_entryIndex_eq_last hk hik hkj]
  simp only [UnknownCell.puncturedTopHigher, insertAt_path_same]
  apply SimplicialThickening.Path.ext
  ext l
  constructor
  · rintro ⟨hl | rfl, hlk⟩
    · exact hl
    · exact (hlk rfl).elim
  · intro hl
    exact ⟨Or.inl hl, fun hlk ↦ hk (hlk ▸ hl)⟩

theorem UnknownCell.erase_puncturedFullTop_entry_eq_oldLast {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    eraseVertex ((c.puncturedFullTopPartner hk hik hkj).path
      ((c.puncturedFullTopPartner hk hik hkj).entryIndex k
        (c.puncturedFullTopPartner_memLast hk hik hkj))) k hikne hkjne = c.chain.last := by
  rw [c.puncturedFullTopPartner_entryIndex_eq_last hk hik hkj]
  change eraseVertex (c.puncturedFullTopPartner hk hik hkj).last k hikne hkjne = _
  rw [c.puncturedFullTopPartner_last hk hik hkj]
  apply SimplicialThickening.Path.ext
  ext l
  constructor
  · rintro ⟨⟨hil, hlj⟩, hlk⟩
    exact c.last_contains_other l hil hlj hlk
  · intro hl
    exact ⟨⟨c.chain.last.left_le l hl, c.chain.last.le_right l hl⟩,
      fun hlk ↦ hk (hlk ▸ hl)⟩

theorem UnknownCell.puncturedFullTop_penultimate_path {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) :
    (c.puncturedFullTopPartner hk hik hkj).path (Fin.castSucc (Fin.last r)) =
      c.chain.path (Fin.castSucc (Fin.last r)) := by
  change (c.puncturedTopHigher hk hik hkj).path
    ((puncturedTopInnerPosition r).succAbove (Fin.castSucc (Fin.last r))) = _
  rw [Fin.succAbove_of_castSucc_lt]
  · rw [← Fin.succAbove_last_apply (Fin.castSucc (Fin.last r))]
    simp only [UnknownCell.puncturedTopHigher, insertAt_path_succAbove]
  · change r < r + 1
    omega

theorem not_mem_beforeEntryIndex (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hpos : 0 < c.entryIndex k hk) :
    k ∉ (c.path (c.beforeEntryIndex k hk hpos)).I :=
  c.not_mem_before_entryIndex k hk _ (c.beforeEntryIndex_lt k hk hpos)

/-- At the first `k`-transition, erasing `k` from the new path produces an intermediate path
between the preceding path and the new path.  This is the cell inserted/deleted by the matching. -/
theorem entry_erase_sandwich (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hpos : 0 < c.entryIndex k hk)
    (hik : i ≠ k) (hkj : j ≠ k) :
    (c.path (c.beforeEntryIndex k hk hpos)).I ⊆
        (eraseVertex (c.path (c.entryIndex k hk)) k hik hkj).I ∧
      (eraseVertex (c.path (c.entryIndex k hk)) k hik hkj).I ⊆
        (c.path (c.entryIndex k hk)).I := by
  constructor
  · intro l hl
    refine ⟨c.monotone' (c.beforeEntryIndex_lt k hk hpos).le hl, ?_⟩
    intro hlk
    exact c.not_mem_beforeEntryIndex k hk hpos (hlk ▸ hl)
  · exact eraseVertex_subset _ _ _ _

/-- The entry path is recovered by adjoining `k` to the intermediate erased path. -/
theorem adjoin_entryErase (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hik : i ≠ k) (hkj : j ≠ k)
    (hik' : i ≤ k) (hkj' : k ≤ j) :
    adjoinVertex (eraseVertex (c.path (c.entryIndex k hk)) k hik hkj) k hik' hkj' =
      c.path (c.entryIndex k hk) :=
  adjoin_eraseVertex hik hkj hik' hkj' (c.mem_entryIndex k hk)

/-- Whether the erased entry path is already the predecessor.  The matching deletes it in this
case and inserts it otherwise. -/
def EntryErasePresent (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hpos : 0 < c.entryIndex k hk)
    (hik : i ≠ k) (hkj : j ≠ k) : Prop :=
  eraseVertex (c.path (c.entryIndex k hk)) k hik hkj =
    c.path (c.beforeEntryIndex k hk hpos)

theorem UnknownCell.puncturedTopHigher_entryErasePresent {k : J}
    (c : UnknownCell r i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k)
    (hpos : 0 < (c.puncturedTopHigher hk hik hkj).entryIndex k
      (c.puncturedTopHigher_memLast hk hik hkj)) :
    (c.puncturedTopHigher hk hik hkj).EntryErasePresent k
      (c.puncturedTopHigher_memLast hk hik hkj) hpos hikne hkjne := by
  unfold EntryErasePresent
  rw [c.erase_puncturedTopHigher_entry_eq_oldLast hk hik hkj hikne hkjne,
    c.puncturedTopHigher_beforeEntry_eq_oldLast hk hik hkj hpos]
  rw [← Fin.succAbove_last_apply (Fin.last r)]
  simp only [UnknownCell.puncturedTopHigher, insertAt_path_succAbove]
  rfl

theorem UnknownCell.puncturedFullTop_entryErase_notPresent {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k)
    (hpos : 0 < (c.puncturedFullTopPartner hk hik hkj).entryIndex k
      (c.puncturedFullTopPartner_memLast hk hik hkj)) :
    ¬ (c.puncturedFullTopPartner hk hik hkj).EntryErasePresent k
      (c.puncturedFullTopPartner_memLast hk hik hkj) hpos hikne hkjne := by
  intro hp
  unfold EntryErasePresent at hp
  rw [c.erase_puncturedFullTop_entry_eq_oldLast hk hik hkj hikne hkjne,
    c.puncturedFullTop_beforeEntry_eq_penultimate hk hik hkj hpos,
    c.puncturedFullTop_penultimate_path hk hik hkj] at hp
  have hind : Fin.last (r + 1) = Fin.castSucc (Fin.last r) :=
    c.nondegenerate hp
  exact (Fin.ne_of_gt (Fin.castSucc_lt_last (Fin.last r))) hind

/-- The three exhaustive branches of the cell matching. -/
inductive MatchingBranch {k : J} (c : UnknownCell r i j k)
    (hik : i ≠ k) (hkj : j ≠ k) : Type u
  | punctured (h : k ∉ c.chain.last.I)
  | entryDelete (h : k ∈ c.chain.last.I)
      (hpresent : c.chain.EntryErasePresent k h
        (c.chain.entryIndex_pos_of_not_mem_first k h c.first_avoids) hik hkj)
  | entryInsert (h : k ∈ c.chain.last.I)
      (hnew : ¬ c.chain.EntryErasePresent k h
        (c.chain.entryIndex_pos_of_not_mem_first k h c.first_avoids) hik hkj)

/-- Every unknown nondegenerate chain lies in one of the operational branches used by the
matching algorithm. -/
noncomputable def UnknownCell.matchingBranch {k : J} (c : UnknownCell r i j k)
    (hik : i ≠ k) (hkj : j ≠ k) : MatchingBranch c hik hkj := by
  classical
  by_cases hlast : k ∈ c.chain.last.I
  · let hpos := c.chain.entryIndex_pos_of_not_mem_first k hlast c.first_avoids
    by_cases hp : c.chain.EntryErasePresent k hlast hpos hik hkj
    · exact .entryDelete hlast hp
    · exact .entryInsert hlast hp
  · exact .punctured hlast

/-- The exhaustive operational roles in the filtration.  Punctured cells are support faces,
not selected missing faces; entry index one is a known-base boundary case. -/
inductive GlobalCellRole {k : J} (c : UnknownCell r i j k)
    (hik : i ≠ k) (hkj : j ≠ k) : Type u
  | puncturedSupport (h : k ∉ c.chain.last.I)
  | entrySelectedLower (h : k ∈ c.chain.last.I)
      (hnew : ¬ c.chain.EntryErasePresent k h
        (c.chain.entryIndex_pos_of_not_mem_first k h c.first_avoids) hik hkj)
  | entryKnownBase (h : k ∈ c.chain.last.I)
      (hpresent : c.chain.EntryErasePresent k h
        (c.chain.entryIndex_pos_of_not_mem_first k h c.first_avoids) hik hkj)
      (hindex : c.chain.entryIndex k h = 1)
  | entryRecursiveUpper (h : k ∈ c.chain.last.I)
      (hpresent : c.chain.EntryErasePresent k h
        (c.chain.entryIndex_pos_of_not_mem_first k h c.first_avoids) hik hkj)
      (hindex : c.chain.entryIndex k h ≠ 1)

/-- Every unknown cell has exactly one operational role chosen by the matching algorithm. -/
noncomputable def UnknownCell.globalCellRole {k : J} (c : UnknownCell r i j k)
    (hik : i ≠ k) (hkj : j ≠ k) : GlobalCellRole c hik hkj := by
  classical
  match c.matchingBranch hik hkj with
  | .punctured h => exact .puncturedSupport h
  | .entryInsert h hn => exact .entrySelectedLower h hn
  | .entryDelete h hp =>
      by_cases hi : c.chain.entryIndex k h = 1
      · exact .entryKnownBase h hp hi
      · exact .entryRecursiveUpper h hp hi

/-- The full-top partner has the selected-lower role. -/
noncomputable def UnknownCell.puncturedFullTop_selectedLowerRole {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    GlobalCellRole (c.puncturedFullTopCell hk hik hkj) hikne hkjne := by
  apply GlobalCellRole.entrySelectedLower
    (c.puncturedFullTopPartner_memLast hk hik hkj)
  apply c.puncturedFullTop_entryErase_notPresent hk hik hkj hikne hkjne

/-- The associated top higher cell has the recursive-upper role. -/
noncomputable def UnknownCell.puncturedTop_recursiveUpperRole {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    GlobalCellRole (c.puncturedTopHigherCell hk hik hkj) hikne hkjne := by
  apply GlobalCellRole.entryRecursiveUpper
    (c.puncturedTopHigher_memLast hk hik hkj)
  · apply c.puncturedTopHigher_entryErasePresent hk hik hkj hikne hkjne
  · intro h
    change (c.puncturedTopHigher hk hik hkj).entryIndex k _ = 1 at h
    have he := c.puncturedTopHigher_entryIndex_eq_last hk hik hkj
    have hv := congrArg Fin.val (h.symm.trans he)
    simp at hv

/-- Data for the reverse (`entryDelete`) branch in positive dimension. -/
structure EntryDeleteCell (r : ℕ) (i j k : J) where
  cell : UnknownCell (r + 1) i j k
  memLast : k ∈ cell.chain.last.I
  left_ne : i ≠ k
  right_ne : j ≠ k
  present : cell.chain.EntryErasePresent k memLast
    (cell.chain.entryIndex_pos_of_not_mem_first k memLast cell.first_avoids)
    left_ne right_ne

namespace EntryDeleteCell

variable {k : J} (c : EntryDeleteCell r i j k)

noncomputable def position : Fin (r + 2) :=
  c.cell.chain.beforeEntryIndex k c.memLast
    (c.cell.chain.entryIndex_pos_of_not_mem_first k c.memLast c.cell.first_avoids)

/-- Delete the already-present erased entry path. -/
noncomputable def lowerChain : PathChain r i j := c.cell.chain.deleteAt c.position

theorem reinsert_lowerChain : c.cell.chain.reinsertDeleted c.position = c.cell.chain :=
  reinsertDeleted_eq _ _

/-- The deleted path is precisely the erased entry path. -/
theorem path_position_eq_entryErase :
    c.cell.chain.path c.position =
      eraseVertex (c.cell.chain.path (c.cell.chain.entryIndex k c.memLast)) k
        c.left_ne c.right_ne := by
  exact c.present.symm

/-- Reinserting the erased entry path into the reconstructed lower chain recovers the upper
chain. -/
theorem insert_erased_lower_eq_upper :
    c.lowerChain.insertAt c.position (c.cell.chain.path c.position)
      (deleted_below c.cell.chain c.position) (deleted_above c.cell.chain c.position) =
        c.cell.chain :=
  c.reinsert_lowerChain

theorem position_eq_zero_of_entryIndex_eq_one
    (hentry : c.cell.chain.entryIndex k c.memLast = 1) : c.position = 0 := by
  apply Fin.ext
  simp [position, beforeEntryIndex, hentry]

/-- At entry index one, deleting the erased predecessor exposes a first path containing `k`,
so this is a known-face base case rather than another unknown lower cell. -/
theorem lowerChain_known_of_entryIndex_eq_one
    (hentry : c.cell.chain.entryIndex k c.memLast = 1) : c.lowerChain.KnownAt k := by
  left
  change k ∈ (c.cell.chain.path (c.position.succAbove 0)).I
  rw [c.position_eq_zero_of_entryIndex_eq_one hentry, Fin.succAbove_zero_apply]
  convert c.cell.chain.mem_entryIndex k c.memLast using 1
  simp [hentry]

/-- Above the base case, deleting the erased predecessor preserves the first and last paths. -/
theorem lowerChain_first_last_of_one_lt_entry
    (hentry : (1 : Fin (r + 2)) < c.cell.chain.entryIndex k c.memLast) :
    c.lowerChain.first = c.cell.chain.first ∧
      c.lowerChain.last = c.cell.chain.last := by
  have hp0 : c.position ≠ 0 := by
    intro hp
    have hle : (1 : Fin (r + 2)) ≤ c.position := by
      exact (Fin.le_castSucc_pred_iff (Fin.ne_zero_of_lt
        (c.cell.chain.entryIndex_pos_of_not_mem_first k c.memLast
          c.cell.first_avoids))).2 hentry
    rw [hp] at hle
    exact (not_le_of_gt (show (0 : Fin (r + 2)) < 1 from Fin.zero_lt_one)) hle
  have hplast : c.position ≠ Fin.last (r + 1) := by
    exact Fin.ne_of_lt ((c.cell.chain.beforeEntryIndex_lt k c.memLast _).trans_le
      (Fin.le_last _))
  constructor
  · apply SimplicialThickening.Path.ext
    ext l
    change l ∈ (c.cell.chain.path (c.position.succAbove 0)).I ↔
      l ∈ (c.cell.chain.path 0).I
    rw [Fin.succAbove_ne_zero_zero hp0]
  · apply SimplicialThickening.Path.ext
    ext l
    change l ∈ (c.cell.chain.path (c.position.succAbove (Fin.last r))).I ↔
      l ∈ (c.cell.chain.path (Fin.last (r + 1))).I
    rw [Fin.succAbove_ne_last_last hplast]

/-- For entry index greater than one, the reconstructed lower chain remains outside the known
horn subcomplex. -/
theorem lowerChain_unknown_of_one_lt_entry
    (hentry : (1 : Fin (r + 2)) < c.cell.chain.entryIndex k c.memLast) :
    ¬ c.lowerChain.KnownAt k := by
  intro h
  obtain ⟨hfirst, hlast⟩ := c.lowerChain_first_last_of_one_lt_entry hentry
  rcases h with hk | ⟨l, hil, hlj, hlk, hl⟩
  · exact c.cell.first_avoids (hfirst ▸ hk)
  · exact hl (hlast ▸ c.cell.last_contains_other l hil hlj hlk)

/-- The recursive delete branch produces a genuine lower unknown cell. -/
noncomputable def lowerCellOfOneLtEntry
    (hentry : (1 : Fin (r + 2)) < c.cell.chain.entryIndex k c.memLast) :
    UnknownCell r i j k where
  chain := c.lowerChain
  nondegenerate := c.cell.chain.isNondegenerate_deleteAt c.position c.cell.nondegenerate
  unknown := c.lowerChain_unknown_of_one_lt_entry hentry

theorem lowerCell_chain
    (hentry : (1 : Fin (r + 2)) < c.cell.chain.entryIndex k c.memLast) :
    (c.lowerCellOfOneLtEntry hentry).chain = c.lowerChain :=
  rfl

/-- The upper cell is recovered by reinserting the deleted erased path into the bundled lower
cell. -/
theorem reinsert_lowerCell_eq_upper
    (hentry : (1 : Fin (r + 2)) < c.cell.chain.entryIndex k c.memLast) :
    (c.lowerCellOfOneLtEntry hentry).chain.insertAt c.position
      (c.cell.chain.path c.position) (deleted_below c.cell.chain c.position)
      (deleted_above c.cell.chain c.position) = c.cell.chain :=
  c.insert_erased_lower_eq_upper

end EntryDeleteCell

/-- The insertion position for the erased entry path is an inner vertex of the paired simplex. -/
theorem entryInsertion_inner (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hpos : 0 < c.entryIndex k hk) :
    0 < Fin.castSucc (c.entryIndex k hk) ∧
      Fin.castSucc (c.entryIndex k hk) < Fin.last (r + 1) := by
  constructor
  · simpa using hpos
  · exact Fin.castSucc_lt_last _

private theorem entryErase_below (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hik : i ≠ k) (hkj : j ≠ k)
    (a : Fin (r + 1))
    (ha : (Fin.castSucc (c.entryIndex k hk)).succAbove a <
      Fin.castSucc (c.entryIndex k hk)) :
    (c.path a).I ⊆ (eraseVertex (c.path (c.entryIndex k hk)) k hik hkj).I := by
  have hae : a < c.entryIndex k hk := by
    exact (Fin.castSucc_lt_castSucc_iff.1
      ((Fin.succAbove_lt_iff_castSucc_lt _ _).1 ha))
  intro l hl
  exact ⟨c.monotone' hae.le hl, fun hlk ↦ c.not_mem_before_entryIndex k hk a hae (hlk ▸ hl)⟩

private theorem entryErase_above (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hik : i ≠ k) (hkj : j ≠ k)
    (a : Fin (r + 1))
    (ha : Fin.castSucc (c.entryIndex k hk) <
      (Fin.castSucc (c.entryIndex k hk)).succAbove a) :
    (eraseVertex (c.path (c.entryIndex k hk)) k hik hkj).I ⊆ (c.path a).I := by
  have hea : c.entryIndex k hk ≤ a := by
    exact Fin.castSucc_le_castSucc_iff.1 ((Fin.lt_succAbove_iff_le_castSucc _ _).1 ha)
  exact (eraseVertex_subset _ _ _ _).trans (c.monotone' hea)

/-- Insert the erased entry path at the first `k`-transition. -/
noncomputable def insertEntryErase (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hik : i ≠ k) (hkj : j ≠ k) :
    PathChain (r + 1) i j :=
  c.insertAt (Fin.castSucc (c.entryIndex k hk))
    (eraseVertex (c.path (c.entryIndex k hk)) k hik hkj)
    (entryErase_below c k hk hik hkj) (entryErase_above c k hk hik hkj)

/-- Deleting the distinguished inner face of the entry pair recovers the original chain. -/
theorem deleteAt_insertEntryErase (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hik : i ≠ k) (hkj : j ≠ k) :
    (c.insertEntryErase k hk hik hkj).deleteAt
      (Fin.castSucc (c.entryIndex k hk)) = c :=
  deleteAt_insertAt _ _ _ _ _

/-- If the erased entry path is not already the predecessor, then it is new to the whole chain. -/
theorem entryErase_ne_path_of_ne_predecessor (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hpos : 0 < c.entryIndex k hk)
    (hik : i ≠ k) (hkj : j ≠ k)
    (hne : ¬ c.EntryErasePresent k hk hpos hik hkj) (a : Fin (r + 1)) :
    eraseVertex (c.path (c.entryIndex k hk)) k hik hkj ≠ c.path a := by
  intro h
  by_cases ha : a < c.entryIndex k hk
  · apply hne
    apply SimplicialThickening.Path.ext
    ext l
    constructor
    · intro hl
      have hap : a ≤ c.beforeEntryIndex k hk hpos := by
        exact (Fin.le_castSucc_pred_iff (Fin.ne_zero_of_lt hpos)).2 ha
      have hpa := c.monotone' hap
      exact hpa (by rw [← h]; exact hl)
    · intro hl
      exact (c.entry_erase_sandwich k hk hpos hik hkj).1 hl
  · have hea : c.entryIndex k hk ≤ a := Fin.not_lt.1 ha
    have hka : k ∈ (c.path a).I := c.monotone' hea (c.mem_entryIndex k hk)
    have hkErase : k ∉ (eraseVertex (c.path (c.entryIndex k hk)) k hik hkj).I := by
      simp
    exact hkErase (h ▸ hka)

/-- In the insertion branch the entry matching produces a nondegenerate higher cell. -/
theorem isNondegenerate_insertEntryErase (c : PathChain r i j) (k : J)
    (hk : k ∈ c.last.I) (hpos : 0 < c.entryIndex k hk)
    (hik : i ≠ k) (hkj : j ≠ k) (hc : c.IsNondegenerate)
    (hne : ¬ c.EntryErasePresent k hk hpos hik hkj) :
    (c.insertEntryErase k hk hik hkj).IsNondegenerate :=
  isNondegenerate_insertAt _ _ _ _ _ hc
    (c.entryErase_ne_path_of_ne_predecessor k hk hpos hik hkj hne)

/-- A lower cell in the entry matching: `k` occurs eventually, and the erased entry path is not
already present as its predecessor. -/
structure EntryLowerCell (r : ℕ) (i j k : J) where
  cell : UnknownCell r i j k
  memLast : k ∈ cell.chain.last.I
  left_ne : i ≠ k
  right_ne : j ≠ k
  erase_new : ¬ cell.chain.EntryErasePresent k memLast
    (cell.chain.entryIndex_pos_of_not_mem_first k memLast cell.first_avoids)
    left_ne right_ne

theorem EntryLowerCell.ext_of_chain_eq {k : J} {a b : EntryLowerCell r i j k}
    (h : a.cell.chain = b.cell.chain) : a = b := by
  have hc : a.cell = b.cell := UnknownCell.ext h
  cases a
  cases b
  cases hc
  rfl

/-- Construct the canonical global pair from a selected-lower role witness. -/
def entryLowerCellOfSelectedRole {k : J} (c : UnknownCell r i j k)
    (hik : i ≠ k) (hkj : j ≠ k) (hmem : k ∈ c.chain.last.I)
    (hnew : ¬ c.chain.EntryErasePresent k hmem
      (c.chain.entryIndex_pos_of_not_mem_first k hmem c.first_avoids) hik hkj) :
    EntryLowerCell r i j k where
  cell := c
  memLast := hmem
  left_ne := hik
  right_ne := hkj
  erase_new := hnew

/-- A global pair is a selected lower cell together with its canonical upper attachment. -/
abbrev GlobalPair (r : ℕ) (i j k : J) := EntryLowerCell r i j k

namespace EntryLowerCell

variable {k : J} (c : EntryLowerCell r i j k)

/-- The distinguished insertion position of the matching. -/
noncomputable def position : Fin (r + 2) :=
  Fin.castSucc (c.cell.chain.entryIndex k c.memLast)

theorem position_inner : 0 < c.position ∧ c.position < Fin.last (r + 1) :=
  c.cell.chain.entryInsertion_inner k c.memLast
    (c.cell.chain.entryIndex_pos_of_not_mem_first k c.memLast c.cell.first_avoids)

/-- The upper cell obtained by inserting the erased entry path. -/
noncomputable def upperChain : PathChain (r + 1) i j :=
  c.cell.chain.insertEntryErase k c.memLast c.left_ne c.right_ne

theorem upperChain_path_position :
    c.upperChain.path c.position =
      eraseVertex (c.cell.chain.path (c.cell.chain.entryIndex k c.memLast)) k
        c.left_ne c.right_ne := by
  change (c.cell.chain.insertAt (Fin.castSucc (c.cell.chain.entryIndex k c.memLast))
    (eraseVertex (c.cell.chain.path (c.cell.chain.entryIndex k c.memLast)) k
      c.left_ne c.right_ne)
      (entryErase_below c.cell.chain k c.memLast c.left_ne c.right_ne)
      (entryErase_above c.cell.chain k c.memLast c.left_ne c.right_ne)).path
      (Fin.castSucc (c.cell.chain.entryIndex k c.memLast)) = _
  rw [insertAt_path_same]

/-- The old first `k`-path is immediately after the inserted erased path. -/
theorem upperChain_path_entrySucc :
    c.upperChain.path (c.cell.chain.entryIndex k c.memLast).succ =
      c.cell.chain.path (c.cell.chain.entryIndex k c.memLast) := by
  change (c.cell.chain.insertAt c.position
    (eraseVertex (c.cell.chain.path (c.cell.chain.entryIndex k c.memLast)) k
      c.left_ne c.right_ne)
      (entryErase_below c.cell.chain k c.memLast c.left_ne c.right_ne)
      (entryErase_above c.cell.chain k c.memLast c.left_ne c.right_ne)).path
      (c.cell.chain.entryIndex k c.memLast).succ = _
  rw [← Fin.succAbove_castSucc_self]
  exact insertAt_path_succAbove _ _ _ _ _ _

theorem upperChain_memLast : k ∈ c.upperChain.last.I := by
  exact c.upperChain.monotone'
    (Fin.le_last (c.cell.chain.entryIndex k c.memLast).succ)
    (c.upperChain_path_entrySucc ▸ c.cell.chain.mem_entryIndex k c.memLast)

/-- In the paired upper chain, the first occurrence of `k` is shifted one place to the right. -/
theorem upperChain_entryIndex :
    c.upperChain.entryIndex k c.upperChain_memLast =
      (c.cell.chain.entryIndex k c.memLast).succ := by
  apply c.upperChain.entryIndex_eq_of_mem_of_before_not_mem k c.upperChain_memLast
  · rw [c.upperChain_path_entrySucc]
    exact c.cell.chain.mem_entryIndex k c.memLast
  · intro b hb
    obtain rfl | ⟨a, rfl⟩ := Fin.eq_self_or_eq_succAbove c.position b
    · rw [c.upperChain_path_position]
      simp
    · change k ∉ ((c.cell.chain.insertAt c.position
        (eraseVertex (c.cell.chain.path (c.cell.chain.entryIndex k c.memLast)) k
          c.left_ne c.right_ne)
        (entryErase_below c.cell.chain k c.memLast c.left_ne c.right_ne)
        (entryErase_above c.cell.chain k c.memLast c.left_ne c.right_ne)).path
          (c.position.succAbove a)).I
      rw [insertAt_path_succAbove]
      apply c.cell.chain.not_mem_before_entryIndex k c.memLast a
      change c.position.succAbove a < (c.cell.chain.entryIndex k c.memLast).succ at hb
      rw [← Fin.succAbove_castSucc_self] at hb
      exact Fin.succAbove_lt_succAbove_iff.1 hb

theorem upperChain_beforeEntryIndex
    (hpos : 0 < c.upperChain.entryIndex k c.upperChain_memLast) :
    c.upperChain.beforeEntryIndex k c.upperChain_memLast hpos = c.position := by
  apply Fin.ext
  simp [beforeEntryIndex, c.upperChain_entryIndex, position]

/-- The paired upper cell has the recursive-upper adjacency witness: its erased first
`k`-path is exactly the immediately preceding inserted path. -/
theorem upperChain_entryErasePresent
    (hpos : 0 < c.upperChain.entryIndex k c.upperChain_memLast) :
    c.upperChain.EntryErasePresent k c.upperChain_memLast hpos c.left_ne c.right_ne := by
  unfold EntryErasePresent
  rw [c.upperChain_entryIndex, c.upperChain_beforeEntryIndex hpos,
    c.upperChain_path_entrySucc, c.upperChain_path_position]

/-- An upper cell, whose erased entry is present, cannot itself be a selected lower cell. -/
theorem upperChain_ne_selectedLower (p : EntryLowerCell (r + 1) i j k) :
    c.upperChain ≠ p.cell.chain := by
  intro hEq
  have hpos : 0 < c.upperChain.entryIndex k c.upperChain_memLast := by
    rw [c.upperChain_entryIndex]
    exact Fin.succ_pos _
  have hex : ∃ (hk : k ∈ c.upperChain.last.I)
      (hp : 0 < c.upperChain.entryIndex k hk),
      c.upperChain.EntryErasePresent k hk hp c.left_ne c.right_ne :=
    ⟨c.upperChain_memLast, hpos, c.upperChain_entryErasePresent hpos⟩
  have hex' : ∃ (hk : k ∈ p.cell.chain.last.I)
      (hp : 0 < p.cell.chain.entryIndex k hk),
      p.cell.chain.EntryErasePresent k hk hp p.left_ne p.right_ne := by
    simpa only [hEq] using hex
  obtain ⟨hk, hp, hpresent⟩ := hex'
  apply p.erase_new
  convert hpresent using 1

/-- Every face of the paired upper cell except the distinguished missing face still contains
the newly inserted erased-entry path.  This is the key same-rank separation invariant: a
nonmissing face cannot silently discard the datum which distinguishes an upper cell from its
selected lower partner. -/
theorem exists_erasedEntry_path_deleteAt_of_ne (q : Fin (r + 2))
    (hq : c.position ≠ q) :
    ∃ b : Fin (r + 1), (c.upperChain.deleteAt q).path b =
      eraseVertex (c.cell.chain.path (c.cell.chain.entryIndex k c.memLast)) k
        c.left_ne c.right_ne := by
  exact exists_path_deleteAt_insertAt_eq_inserted c.cell.chain c.position q
    (eraseVertex (c.cell.chain.path (c.cell.chain.entryIndex k c.memLast)) k
      c.left_ne c.right_ne)
    (entryErase_below c.cell.chain k c.memLast c.left_ne c.right_ne)
    (entryErase_above c.cell.chain k c.memLast c.left_ne c.right_ne) hq

/-- Deleting a `k`-free nonmissing path preserves the erased-entry adjacency, not merely the
presence of the erased path. -/
theorem deleteAt_entryErasePresent_of_not_mem (q : Fin (r + 2))
    (hqpos : c.position ≠ q) (hqk : k ∉ (c.upperChain.path q).I) :
    ∃ (hk : k ∈ (c.upperChain.deleteAt q).last.I)
      (hpos : 0 < (c.upperChain.deleteAt q).entryIndex k hk),
      (c.upperChain.deleteAt q).EntryErasePresent k hk hpos c.left_ne c.right_ne := by
  have hqentry : (c.cell.chain.entryIndex k c.memLast).succ ≠ q := by
    intro h
    apply hqk
    rw [← h, c.upperChain_path_entrySucc]
    exact c.cell.chain.mem_entryIndex k c.memLast
  obtain ⟨e, he⟩ := Fin.exists_succAbove_eq hqentry
  obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq hqpos
  have hq_lt_entry : q < (c.cell.chain.entryIndex k c.memLast).succ := by
    apply lt_of_not_ge
    intro h
    exact hqk (c.upperChain.monotone' h
      (c.upperChain_path_entrySucc ▸ c.cell.chain.mem_entryIndex k c.memLast))
  have hq_lt_pos : q < c.position := by
    have hv : q.val < (c.cell.chain.entryIndex k c.memLast).val + 1 := hq_lt_entry
    have hne : q.val ≠ (c.cell.chain.entryIndex k c.memLast).val := by
      intro h
      apply hqpos
      apply Fin.ext
      simpa [position] using h.symm
    change q.val < (c.cell.chain.entryIndex k c.memLast).val
    omega
  let hkFace : k ∈ (c.upperChain.deleteAt q).last.I := by
    exact (c.upperChain.deleteAt q).monotone' (Fin.le_last e) (by
      rw [deleteAt_path, he, c.upperChain_path_entrySucc]
      exact c.cell.chain.mem_entryIndex k c.memLast)
  have hentry : (c.upperChain.deleteAt q).entryIndex k hkFace = e := by
    apply (c.upperChain.deleteAt q).entryIndex_eq_of_mem_of_before_not_mem k hkFace
    · rw [deleteAt_path, he, c.upperChain_path_entrySucc]
      exact c.cell.chain.mem_entryIndex k c.memLast
    · intro a ha hka
      apply c.upperChain.not_mem_before_entryIndex k c.upperChain_memLast
        (q.succAbove a)
      · rw [c.upperChain_entryIndex, ← he]
        exact Fin.succAbove_lt_succAbove_iff.2 ha
      · exact hka
  have hepos : 0 < e := by
    have hqe : q ≤ e.castSucc :=
      (Fin.lt_succAbove_iff_le_castSucc q e).1 (he ▸ hq_lt_entry)
    have he' := he
    rw [Fin.succAbove_of_le_castSucc _ _ hqe] at he'
    have heq : e = c.cell.chain.entryIndex k c.memLast := by
      exact Fin.succ_injective _ he'
    rw [heq]
    exact c.cell.chain.entryIndex_pos_of_not_mem_first k c.memLast c.cell.first_avoids
  refine ⟨hkFace, hentry ▸ hepos, ?_⟩
  unfold EntryErasePresent
  simp only [hentry]
  have hbefore : (c.upperChain.deleteAt q).beforeEntryIndex k hkFace (hentry ▸ hepos) = b := by
    apply Fin.ext
    change ((c.upperChain.deleteAt q).entryIndex k hkFace).val - 1 = b.val
    rw [hentry]
    have hbv := congrArg Fin.val hb
    have hev := congrArg Fin.val he
    have hqb : q ≤ b.castSucc :=
      (Fin.lt_succAbove_iff_le_castSucc q b).1 (hb ▸ hq_lt_pos)
    have hqe : q ≤ e.castSucc :=
      (Fin.lt_succAbove_iff_le_castSucc q e).1 (he ▸ hq_lt_entry)
    rw [Fin.succAbove_of_le_castSucc _ _ hqb] at hb
    rw [Fin.succAbove_of_le_castSucc _ _ hqe] at he
    have hbv := congrArg Fin.val hb
    have hev := congrArg Fin.val he
    simp [position] at hbv hev
    omega
  rw [hbefore, deleteAt_path, he, c.upperChain_path_entrySucc]
  rw [deleteAt_path, hb, c.upperChain_path_position]

/-- A `k`-free same-dimensional nonmissing face of an upper cell cannot be any selected lower
cell: the face has `EntryErasePresent`, while selected lowers require its negation. -/
theorem deleteAt_ne_selectedLower_of_not_mem (p : EntryLowerCell r i j k)
    (q : Fin (r + 2)) (hqpos : c.position ≠ q)
    (hqk : k ∉ (c.upperChain.path q).I) :
    c.upperChain.deleteAt q ≠ p.cell.chain := by
  intro hEq
  obtain ⟨hk, hpos, hpresent⟩ :=
    c.deleteAt_entryErasePresent_of_not_mem q hqpos hqk
  have hex : ∃ (hk : k ∈ (c.upperChain.deleteAt q).last.I)
      (hpos : 0 < (c.upperChain.deleteAt q).entryIndex k hk),
      (c.upperChain.deleteAt q).EntryErasePresent k hk hpos c.left_ne c.right_ne :=
    ⟨hk, hpos, hpresent⟩
  have hex' : ∃ (hk : k ∈ p.cell.chain.last.I)
      (hpos : 0 < p.cell.chain.entryIndex k hk),
      p.cell.chain.EntryErasePresent k hk hpos p.left_ne p.right_ne := by
    simpa only [hEq]
      using hex
  obtain ⟨hk', hpos', hpresent'⟩ := hex'
  apply p.erase_new
  convert hpresent' using 1

theorem upperChain_nondegenerate : c.upperChain.IsNondegenerate :=
  c.cell.chain.isNondegenerate_insertEntryErase k c.memLast
    (c.cell.chain.entryIndex_pos_of_not_mem_first k c.memLast c.cell.first_avoids)
    c.left_ne c.right_ne c.cell.nondegenerate c.erase_new

theorem delete_position_upperChain : c.upperChain.deleteAt c.position = c.cell.chain :=
  c.cell.chain.deleteAt_insertEntryErase k c.memLast c.left_ne c.right_ne

/-- Inserting the `k`-free erased path does not change `k`-multiplicity. -/
theorem cell_kMultiplicity_eq_upperChain :
    c.cell.chain.kMultiplicity k = c.upperChain.kMultiplicity k := by
  rw [← c.delete_position_upperChain]
  apply kMultiplicity_deleteAt_eq_of_not_mem
  rw [c.upperChain_path_position]
  simp

theorem upperChain_unknown : ¬ c.upperChain.KnownAt k := by
  intro h
  apply c.cell.unknown
  rw [← c.delete_position_upperChain]
  exact c.upperChain.knownAt_deleteAt c.position k h

/-- The paired upper cell, with nondegeneracy and horn-unknownness certified. -/
noncomputable def upperCell : UnknownCell (r + 1) i j k where
  chain := c.upperChain
  nondegenerate := c.upperChain_nondegenerate
  unknown := c.upperChain_unknown

theorem delete_position_upperCell : c.upperCell.chain.deleteAt c.position = c.cell.chain :=
  c.delete_position_upperChain

/-- On actual nerve simplices, the distinguished inner face of the upper cell is the lower cell. -/
theorem nerve_face_upper_eq_lower :
    (CategoryTheory.nerve (ThickPath i j)).δ c.position
        c.upperCell.chain.toNerveSimplex = c.cell.chain.toNerveSimplex := by
  rw [← toNerveSimplex_deleteAt]
  exact congrArg toNerveSimplex c.delete_position_upperCell

/-- The concrete data of the inner-horn cell attachment supplied by an entry pair. -/
structure NerveInnerFacePair where
  lower : (CategoryTheory.nerve (ThickPath i j)).obj
    (Opposite.op (SimplexCategory.mk r))
  upper : (CategoryTheory.nerve (ThickPath i j)).obj
    (Opposite.op (SimplexCategory.mk (r + 1)))
  face : Fin (r + 2)
  face_pos : 0 < face
  face_lt_last : face < Fin.last (r + 1)
  face_eq : (CategoryTheory.nerve (ThickPath i j)).δ face upper = lower

/-- Package the matching as an actual inner face pair in the path-poset nerve. -/
noncomputable def nerveInnerFacePair : NerveInnerFacePair (r := r) (i := i) (j := j) where
  lower := c.cell.chain.toNerveSimplex
  upper := c.upperCell.chain.toNerveSimplex
  face := c.position
  face_pos := c.position_inner.1
  face_lt_last := c.position_inner.2
  face_eq := c.nerve_face_upper_eq_lower

/-- The entry matching as complete ranked attachment data. -/
noncomputable def rankedInnerFacePair : RankedInnerFacePair r i j k :=
  rankedInnerFacePairOfDelete c.cell.chain c.upperCell.chain k c.upperCell.nondegenerate c.position
    c.position_inner.1 c.position_inner.2 c.delete_position_upperCell

end EntryLowerCell

theorem EntryLowerCell.upperRank_lt_of_dimension_lt {k : J}
    (p : EntryLowerCell r i j k) (q : EntryLowerCell s i j k) (hrs : r < s) :
    Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      (p.upperChain.filtrationRank k) (q.upperChain.filtrationRank k) := by
  exact Prod.Lex.left _ _ (Nat.add_lt_add_right hrs 1)

/-- The full-top selected lower, promoted to the uniform entry-pairing structure. -/
noncomputable def UnknownCell.puncturedFullTopEntryLowerCell {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    EntryLowerCell (r + 1) i j k where
  cell := c.puncturedFullTopCell hk hik hkj
  memLast := c.puncturedFullTopPartner_memLast hk hik hkj
  left_ne := hikne
  right_ne := hkjne
  erase_new := by
    apply c.puncturedFullTop_entryErase_notPresent hk hik hkj hikne hkjne

theorem UnknownCell.puncturedFullTopEntryLowerCell_position {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    (c.puncturedFullTopEntryLowerCell hk hik hkj hikne hkjne).position =
      puncturedTopInnerPosition r := by
  change Fin.castSucc ((c.puncturedFullTopPartner hk hik hkj).entryIndex k _) =
    Fin.castSucc (Fin.last (r + 1))
  congr 1
  exact c.puncturedFullTopPartner_entryIndex_eq_last hk hik hkj

/-- Raw upper chain built directly from the full-top partner, avoiding bundled proof fields. -/
noncomputable def UnknownCell.puncturedFullTopRawUpper {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    PathChain (r + 2) i j :=
  (c.puncturedFullTopPartner hk hik hkj).insertEntryErase k
    (c.puncturedFullTopPartner_memLast hk hik hkj) hikne hkjne

theorem UnknownCell.puncturedFullTopRawUpper_eq_topHigher {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    c.puncturedFullTopRawUpper hk hik hkj hikne hkjne =
      c.puncturedTopHigher hk hik hkj := by
  let p := puncturedTopInnerPosition r
  apply eq_of_deleteAt_eq_of_path_eq _ _ p
  · have hp : Fin.castSucc ((c.puncturedFullTopPartner hk hik hkj).entryIndex k
        (c.puncturedFullTopPartner_memLast hk hik hkj)) = p := by
      change Fin.castSucc ((c.puncturedFullTopPartner hk hik hkj).entryIndex k _) =
        Fin.castSucc (Fin.last (r + 1))
      congr 1
      exact c.puncturedFullTopPartner_entryIndex_eq_last hk hik hkj
    rw [← hp]
    change ((c.puncturedFullTopPartner hk hik hkj).insertEntryErase k
      (c.puncturedFullTopPartner_memLast hk hik hkj) hikne hkjne).deleteAt _ = _
    rw [deleteAt_insertEntryErase]
    rw [hp]
    rfl
  · have hp : Fin.castSucc ((c.puncturedFullTopPartner hk hik hkj).entryIndex k
        (c.puncturedFullTopPartner_memLast hk hik hkj)) = p := by
      change Fin.castSucc ((c.puncturedFullTopPartner hk hik hkj).entryIndex k _) =
        Fin.castSucc (Fin.last (r + 1))
      congr 1
      exact c.puncturedFullTopPartner_entryIndex_eq_last hk hik hkj
    rw [← hp]
    change ((c.puncturedFullTopPartner hk hik hkj).insertEntryErase k
      (c.puncturedFullTopPartner_memLast hk hik hkj) hikne hkjne).path _ = _
    simp only [insertEntryErase, insertAt_path_same]
    rw [c.erase_puncturedFullTop_entry_eq_oldLast hk hik hkj hikne hkjne]
    rw [hp]
    dsimp [p]
    simp only [puncturedTopInnerPosition]
    rw [← Fin.succAbove_last_apply (Fin.last (r + 1))]
    simp only [UnknownCell.puncturedTopHigher, insertAt_path_succAbove]
    rfl

theorem UnknownCell.puncturedFullTop_bundledUpper_eq_raw {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    (c.puncturedFullTopEntryLowerCell hk hik hkj hikne hkjne).upperChain =
      c.puncturedFullTopRawUpper hk hik hkj hikne hkjne :=
  rfl

theorem UnknownCell.puncturedFullTop_bundledUpper_eq_topHigher {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    (c.puncturedFullTopEntryLowerCell hk hik hkj hikne hkjne).upperChain =
      c.puncturedTopHigher hk hik hkj :=
  c.puncturedFullTop_bundledUpper_eq_raw hk hik hkj hikne hkjne |>.trans
    (c.puncturedFullTopRawUpper_eq_topHigher hk hik hkj hikne hkjne)

theorem UnknownCell.puncturedFullTop_bundledUpperCell_eq_topHigherCell {k : J}
    (c : UnknownCell (r + 1) i j k) (hk : k ∉ c.chain.last.I)
    (hik : i ≤ k) (hkj : k ≤ j) (hikne : i ≠ k) (hkjne : j ≠ k) :
    (c.puncturedFullTopEntryLowerCell hk hik hkj hikne hkjne).upperCell =
      c.puncturedTopHigherCell hk hik hkj := by
  apply UnknownCell.ext
  exact c.puncturedFullTop_bundledUpper_eq_topHigher hk hik hkj hikne hkjne

/-- All canonical selected-lower/upper pairs in all dimensions. -/
abbrev GlobalPairIndex (i j k : J) := Σ r : ℕ, EntryLowerCell r i j k

/-- The degree-zero punctured vertices omitted by the positive-dimensional entry pairing. -/
abbrev DegreeZeroPuncturedIndex (i j k : J) :=
  {c : UnknownCell 0 i j k // k ∉ c.chain.last.I}

/-- The complete first approximation to the Kan-cell index: outer degree-zero base cells,
followed by the existing selected-entry cells. -/
abbrev ExtendedGlobalPairIndex (i j k : J) :=
  DegreeZeroPuncturedIndex i j k ⊕ GlobalPairIndex i j k

/-- The outer-horn attachments whose missing lower face is already in the known subcomplex.
These are indispensable for exhaustion: an unknown upper cell may have entry index one and
an erased predecessor as its first path. -/
abbrev EntryKnownBaseIndex (i j k : J) :=
  Σ r : ℕ, {c : EntryDeleteCell r i j k //
    c.cell.chain.entryIndex k c.memLast = 1}

/-- The complete Kan-cell enumeration.  Besides degree-zero punctured and selected-entry
pairs it includes the outer base attachments whose missing face is known. -/
abbrev CompleteGlobalPairIndex (i j k : J) :=
  EntryKnownBaseIndex i j k ⊕ ExtendedGlobalPairIndex i j k

/-- Complete index in role order: punctured vertices, known-base uppers, selected-entry pairs. -/
abbrev Extended2GlobalPairIndex (i j k : J) :=
  DegreeZeroPuncturedIndex i j k ⊕ (EntryKnownBaseIndex i j k ⊕ GlobalPairIndex i j k)

/-- Ranked outer-horn data for an entry-known-base cell. -/
noncomputable def EntryKnownBaseIndex.rankedKanFacePair {i j k : J}
    (p : EntryKnownBaseIndex i j k) : RankedKanFacePair p.1 i j k :=
  rankedKanFacePairOfDelete p.2.1.lowerChain p.2.1.cell.chain k
    p.2.1.cell.nondegenerate p.2.1.position rfl

@[simp]
theorem EntryKnownBaseIndex.rankedKanFacePair_lower {i j k : J}
    (p : EntryKnownBaseIndex i j k) :
    p.rankedKanFacePair.lower = p.2.1.lowerChain :=
  rfl

@[simp]
theorem EntryKnownBaseIndex.rankedKanFacePair_upper {i j k : J}
    (p : EntryKnownBaseIndex i j k) :
    p.rankedKanFacePair.upper = p.2.1.cell.chain :=
  rfl

theorem EntryKnownBaseIndex.lower_known {i j k : J}
    (p : EntryKnownBaseIndex i j k) : p.rankedKanFacePair.lower.KnownAt k := by
  change p.2.1.lowerChain.KnownAt k
  exact p.2.1.lowerChain_known_of_entryIndex_eq_one p.2.2

/-- The ranked Kan pair belonging to a complete role index. -/
noncomputable def Extended2GlobalPairIndex.rankedKanFacePair {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : Extended2GlobalPairIndex i j k) :
    Σ r : ℕ, RankedKanFacePair r i j k :=
  match p with
  | .inl c => ⟨0, c.1.degreeZeroPuncturedRankedKanFacePair c.2 hik hkj⟩
  | .inr (.inl p) => ⟨p.1, p.rankedKanFacePair⟩
  | .inr (.inr p) => ⟨p.1, p.2.rankedInnerFacePair.toRankedKanFacePair⟩

@[simp]
theorem Extended2GlobalPairIndex.rankedKanFacePair_inl {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (c : DegreeZeroPuncturedIndex i j k) :
    ((Extended2GlobalPairIndex.rankedKanFacePair hik hkj (.inl c)).2).lower = c.1.chain :=
  rfl

@[simp]
theorem Extended2GlobalPairIndex.rankedKanFacePair_knownBase {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : EntryKnownBaseIndex i j k) :
    ((Extended2GlobalPairIndex.rankedKanFacePair hik hkj (.inr (.inl p))).2).upper =
      p.2.1.cell.chain :=
  rfl

@[simp]
theorem Extended2GlobalPairIndex.rankedKanFacePair_global {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : GlobalPairIndex i j k) :
    (Extended2GlobalPairIndex.rankedKanFacePair hik hkj (.inr (.inr p))).1 = p.1 :=
  rfl

noncomputable def Extended2GlobalPairIndex.rank {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : Extended2GlobalPairIndex i j k) : ℕ × ℕ :=
  (p.rankedKanFacePair hik hkj).2.upper.filtrationRank k

noncomputable def Extended2GlobalPairIndex.RankRel {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j)
    (a b : Extended2GlobalPairIndex i j k) : Prop :=
  Prod.Lex (fun x y : ℕ ↦ x < y) (fun x y : ℕ ↦ x < y)
    (a.rank hik hkj) (b.rank hik hkj)

theorem Extended2GlobalPairIndex.rankRel_wellFounded {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) :
    WellFounded (Extended2GlobalPairIndex.RankRel hik hkj) :=
  (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf).onFun

noncomputable instance Extended2GlobalPairIndex.rankRel_isWellFounded {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) :
    IsWellFounded (Extended2GlobalPairIndex i j k)
      (Extended2GlobalPairIndex.RankRel hik hkj) :=
  ⟨Extended2GlobalPairIndex.rankRel_wellFounded hik hkj⟩

@[implicit_reducible]
noncomputable def Extended2GlobalPairIndex.wellOrder {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) : LinearOrder (Extended2GlobalPairIndex i j k) :=
  IsWellFounded.wellOrderExtension (Extended2GlobalPairIndex.RankRel hik hkj)

theorem Extended2GlobalPairIndex.rankRel_lt_wellOrder {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) {a b : Extended2GlobalPairIndex i j k}
    (h : Extended2GlobalPairIndex.RankRel hik hkj a b) :
    @LT.lt _ (Extended2GlobalPairIndex.wellOrder hik hkj).toLT a b :=
  Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel h)

/-- The ranked Kan horn belonging to either kind of extended global pair. -/
noncomputable def ExtendedGlobalPairIndex.rankedKanFacePair {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    Σ r : ℕ, RankedKanFacePair r i j k :=
  match p with
  | .inl c => ⟨0, c.1.degreeZeroPuncturedRankedKanFacePair c.2 hik hkj⟩
  | .inr p => ⟨p.1, p.2.rankedInnerFacePair.toRankedKanFacePair⟩

@[simp]
theorem ExtendedGlobalPairIndex.rankedKanFacePair_inl {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (c : DegreeZeroPuncturedIndex i j k) :
    ((ExtendedGlobalPairIndex.rankedKanFacePair hik hkj (.inl c)).2).lower = c.1.chain :=
  rfl

@[simp]
theorem ExtendedGlobalPairIndex.rankedKanFacePair_inr {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : GlobalPairIndex i j k) :
    (ExtendedGlobalPairIndex.rankedKanFacePair hik hkj (.inr p)).1 = p.1 :=
  rfl

/-- Dependency rank of an extended Kan-cell attachment. -/
noncomputable def ExtendedGlobalPairIndex.rank {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) : ℕ × ℕ :=
  (p.rankedKanFacePair hik hkj).2.upper.filtrationRank k

/-- Rank dependency before a deterministic well-order tie-break. -/
noncomputable def ExtendedGlobalPairIndex.RankRel {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (a b : ExtendedGlobalPairIndex i j k) : Prop :=
  Prod.Lex (fun x y : ℕ ↦ x < y) (fun x y : ℕ ↦ x < y)
    (a.rank hik hkj) (b.rank hik hkj)

theorem ExtendedGlobalPairIndex.rankRel_wellFounded {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) :
    WellFounded (ExtendedGlobalPairIndex.RankRel hik hkj) :=
  (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf).onFun

noncomputable instance ExtendedGlobalPairIndex.rankRel_isWellFounded {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) :
    IsWellFounded (ExtendedGlobalPairIndex i j k)
      (ExtendedGlobalPairIndex.RankRel hik hkj) :=
  ⟨ExtendedGlobalPairIndex.rankRel_wellFounded hik hkj⟩

/-- A well-order extending the dependency rank on all outer and inner mapping-space cells. -/
@[implicit_reducible]
noncomputable def ExtendedGlobalPairIndex.wellOrder {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) : LinearOrder (ExtendedGlobalPairIndex i j k) :=
  IsWellFounded.wellOrderExtension (ExtendedGlobalPairIndex.RankRel hik hkj)

theorem ExtendedGlobalPairIndex.rankRel_lt_wellOrder {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) {a b : ExtendedGlobalPairIndex i j k}
    (h : ExtendedGlobalPairIndex.RankRel hik hkj a b) :
    @LT.lt _ (ExtendedGlobalPairIndex.wellOrder hik hkj).toLT a b :=
  Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel h)

noncomputable def GlobalPairIndex.rank {i j k : J} (a : GlobalPairIndex i j k) :
    ℕ × ℕ :=
  a.2.upperChain.filtrationRank k

/-- Rank-only relation before adding a tie-break. -/
noncomputable def GlobalPairIndex.RankRel {i j k : J}
    (a b : GlobalPairIndex i j k) : Prop :=
  Prod.Lex (fun x y : ℕ ↦ x < y) (fun x y : ℕ ↦ x < y) a.rank b.rank

theorem GlobalPairIndex.rankRel_wellFounded {i j k : J} :
    WellFounded (GlobalPairIndex.RankRel (i := i) (j := j) (k := k)) := by
  exact (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf).onFun

noncomputable instance GlobalPairIndex.rankRel_isWellFounded {i j k : J} :
    IsWellFounded (GlobalPairIndex i j k)
      (GlobalPairIndex.RankRel (i := i) (j := j) (k := k)) :=
  ⟨GlobalPairIndex.rankRel_wellFounded⟩

/-- A well-order extending the rank relation, used to enumerate same-rank attachments. -/
@[implicit_reducible]
noncomputable def GlobalPairIndex.wellOrder {i j k : J} :
    LinearOrder (GlobalPairIndex i j k) :=
  IsWellFounded.wellOrderExtension
    (GlobalPairIndex.RankRel (i := i) (j := j) (k := k))

theorem GlobalPairIndex.rankRel_lt_wellOrder {i j k : J}
    {a b : GlobalPairIndex i j k} (h : GlobalPairIndex.RankRel a b) :
    @LT.lt _ (GlobalPairIndex.wellOrder (i := i) (j := j) (k := k)).toLT a b := by
  exact Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel h)

/-- A cofinal reindexing preserves the greatest member of a chain. -/
theorem last_reindex_of_map_last (c : PathChain r i j)
    (f : Fin (s + 1) →o Fin (r + 1)) (hf : f (Fin.last s) = Fin.last r) :
    (c.reindex f).last = c.last := by
  apply SimplicialThickening.Path.ext
  ext l
  change l ∈ (c.path (f (Fin.last s))).I ↔ l ∈ (c.path (Fin.last r)).I
  rw [hf]

/-- An initial reindexing preserves the least member of a chain. -/
theorem first_reindex_of_map_zero (c : PathChain r i j)
    (f : Fin (s + 1) →o Fin (r + 1)) (hf : f 0 = 0) :
    (c.reindex f).first = c.first := by
  apply SimplicialThickening.Path.ext
  ext l
  change l ∈ (c.path (f 0)).I ↔ l ∈ (c.path 0).I
  rw [hf]

/-- A reindexing preserving both endpoints preserves the known-horn condition. -/
theorem knownAt_reindex_of_endpoints (c : PathChain r i j) (k : J)
    (f : Fin (s + 1) →o Fin (r + 1)) (h0 : f 0 = 0)
    (hlast : f (Fin.last s) = Fin.last r) (h : c.KnownAt k) :
    (c.reindex f).KnownAt k := by
  rcases h with h | ⟨l, hil, hlj, hlk, hl⟩
  · left
    rw [c.first_reindex_of_map_zero f h0]
    exact h
  · right
    refine ⟨l, hil, hlj, hlk, ?_⟩
    rw [c.last_reindex_of_map_last f hlast]
    exact hl

/-- The known-horn chains form a simplicial subset: arbitrary monotone reindexing preserves
the condition. -/
theorem knownAt_reindex (c : PathChain r i j) (k : J)
    (f : Fin (s + 1) →o Fin (r + 1)) (h : c.KnownAt k) :
    (c.reindex f).KnownAt k := by
  rcases h with h | ⟨l, hil, hlj, hlk, hl⟩
  · left
    exact c.first_le (f 0) h
  · right
    refine ⟨l, hil, hlj, hlk, ?_⟩
    exact c.not_mem_of_not_mem_last hl (f (Fin.last s))

/-- The actual simplicial subcomplex of the path-poset nerve supplied by the inner horn. -/
def knownPathSubcomplex (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex where
  obj U := {x | (ofNerveSimplex x).KnownAt k}
  map {U V} f x hx := by
    change (ofNerveSimplex ((CategoryTheory.nerve (ThickPath i j)).map f x)).KnownAt k
    exact knownAt_reindex (c := ofNerveSimplex x) k f.unop.toOrderHom hx

theorem mem_knownPathSubcomplex_iff (i j k : J) (r : ℕ)
    (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r))) :
    x ∈ (knownPathSubcomplex i j k).obj _ ↔ (ofNerveSimplex x).KnownAt k :=
  Iff.rfl

/-- Simplicial closure of a degreewise collection of path-nerve simplices, together with the
known horn subcomplex. -/
def generatedPathStage (i j k : J)
    (P : ∀ r : ℕ, (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r)) → Prop) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  knownPathSubcomplex i j k ⊔
    ⨆ (r : ℕ), ⨆ (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r))), ⨆ (_h : P r x), SSet.Subcomplex.ofSimplex x

theorem knownPathSubcomplex_le_generatedPathStage (i j k : J) (P) :
    knownPathSubcomplex i j k ≤ generatedPathStage i j k P :=
  le_sup_left

theorem ofSimplex_le_generatedPathStage (i j k : J) (P) (r : ℕ)
    (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r))) (hx : P r x) :
    SSet.Subcomplex.ofSimplex x ≤ generatedPathStage i j k P := by
  apply le_sup_of_le_right
  exact le_iSup_of_le r (le_iSup_of_le x (le_iSup_of_le hx (le_refl _)))

/-- Enlarging the generating predicate enlarges the generated stage. -/
theorem generatedPathStage_mono (i j k : J) {P Q}
    (hPQ : ∀ r x, P r x → Q r x) :
    generatedPathStage i j k P ≤ generatedPathStage i j k Q := by
  apply sup_le
  · exact knownPathSubcomplex_le_generatedPathStage i j k Q
  · simp only [iSup_le_iff]
    intro r x hx
    exact ofSimplex_le_generatedPathStage i j k Q r x (hPQ r x hx)

/-- The stage generated by simplices of rank strictly below `ρ`. -/
noncomputable def rankGeneratedPathStage (i j k : J) (ρ : ℕ × ℕ) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  generatedPathStage i j k fun _ x ↦
    Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      ((ofNerveSimplex x).filtrationRank k) ρ

/-- A simplex below the rank cutoff belongs to the corresponding generated stage. -/
theorem ofSimplex_le_rankGeneratedPathStage (i j k : J) (ρ : ℕ × ℕ) (r : ℕ)
    (x : (CategoryTheory.nerve (ThickPath i j)).obj
      (Opposite.op (SimplexCategory.mk r)))
    (hx : Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)
      ((ofNerveSimplex x).filtrationRank k) ρ) :
    SSet.Subcomplex.ofSimplex x ≤ rankGeneratedPathStage i j k ρ :=
  ofSimplex_le_generatedPathStage i j k _ r x hx

/-- The cumulative stage generated by all extended pairs preceding `p`. -/
noncomputable def ExtendedGlobalPairIndex.earlierStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  knownPathSubcomplex i j k ⊔
    ⨆ (q : ExtendedGlobalPairIndex i j k), ⨆ (_h : @LT.lt _
      (ExtendedGlobalPairIndex.wellOrder hik hkj).toLT q p),
      SSet.Subcomplex.ofSimplex (q.rankedKanFacePair hik hkj).2.upper.toNerveSimplex

noncomputable def ExtendedGlobalPairIndex.previousStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  p.earlierStage hik hkj ⊔ (p.rankedKanFacePair hik hkj).2.hornRange

noncomputable def ExtendedGlobalPairIndex.nextStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  p.previousStage hik hkj ⊔
    SSet.Subcomplex.ofSimplex (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex

theorem ExtendedGlobalPairIndex.hornRange_le_previousStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (p.rankedKanFacePair hik hkj).2.hornRange ≤ p.previousStage hik hkj :=
  le_sup_right

theorem ExtendedGlobalPairIndex.previousStage_le_nextStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    p.previousStage hik hkj ≤ p.nextStage hik hkj :=
  le_sup_left

noncomputable def Extended2GlobalPairIndex.earlierStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : Extended2GlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  knownPathSubcomplex i j k ⊔
    ⨆ (q : Extended2GlobalPairIndex i j k), ⨆ (_h : @LT.lt _
      (Extended2GlobalPairIndex.wellOrder hik hkj).toLT q p),
      SSet.Subcomplex.ofSimplex (q.rankedKanFacePair hik hkj).2.upper.toNerveSimplex

noncomputable def Extended2GlobalPairIndex.previousStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : Extended2GlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  p.earlierStage hik hkj ⊔ (p.rankedKanFacePair hik hkj).2.hornRange

noncomputable def Extended2GlobalPairIndex.nextStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : Extended2GlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  p.previousStage hik hkj ⊔
    SSet.Subcomplex.ofSimplex (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex

theorem Extended2GlobalPairIndex.hornRange_le_previousStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : Extended2GlobalPairIndex i j k) :
    (p.rankedKanFacePair hik hkj).2.hornRange ≤ p.previousStage hik hkj :=
  le_sup_right

theorem Extended2GlobalPairIndex.previousStage_le_nextStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : Extended2GlobalPairIndex i j k) :
    p.previousStage hik hkj ≤ p.nextStage hik hkj :=
  le_sup_left

/-- A known-base index cannot be attached by taking its known lower face as the missing horn
face: that face is already present in every earlier stage.  This records the obstruction which
forces any complete matching to pair the known-base cell upward by a different construction. -/
theorem EntryKnownBaseIndex.lower_mem_extended2EarlierStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : EntryKnownBaseIndex i j k) :
    p.rankedKanFacePair.lower.toNerveSimplex ∈
      (Extended2GlobalPairIndex.earlierStage hik hkj (.inr (.inl p))).obj _ := by
  have hle : knownPathSubcomplex i j k ≤
      Extended2GlobalPairIndex.earlierStage hik hkj (.inr (.inl p)) := le_sup_left
  exact hle _ p.lower_known

theorem EntryKnownBaseIndex.lower_mem_extended2PreviousStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : EntryKnownBaseIndex i j k) :
    p.rankedKanFacePair.lower.toNerveSimplex ∈
      (Extended2GlobalPairIndex.previousStage hik hkj (.inr (.inl p))).obj _ :=
  (show Extended2GlobalPairIndex.earlierStage hik hkj (.inr (.inl p)) ≤
      Extended2GlobalPairIndex.previousStage hik hkj (.inr (.inl p)) from le_sup_left)
    _ (p.lower_mem_extended2EarlierStage hik hkj)

/-- There are no selected inner-face cells in degree zero. -/
theorem EntryLowerCell.false_of_degreeZero {k : J} (p : EntryLowerCell 0 i j k) : False := by
  have hpos := p.rankedInnerFacePair.face_pos
  have hlast := p.rankedInnerFacePair.face_lt_last
  omega

/-- The lower simplex of an extended pair is not generated by an earlier upper simplex. -/
theorem ExtendedGlobalPairIndex.lower_not_mem_ofSimplex_earlierUpper {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p q : ExtendedGlobalPairIndex i j k)
    (hqp : @LT.lt _ (ExtendedGlobalPairIndex.wellOrder hik hkj).toLT q p) :
    (p.rankedKanFacePair hik hkj).2.lower.toNerveSimplex ∉
      (SSet.Subcomplex.ofSimplex
        (q.rankedKanFacePair hik hkj).2.upper.toNerveSimplex).obj _ := by
  rcases p with cp | ⟨r, p⟩
  · rcases q with cq | ⟨s, q⟩
    · intro hmem
      rw [mem_ofSimplex_toNerveSimplex_iff] at hmem
      obtain ⟨f, hf⟩ := hmem
      change SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1 at f
      change cp.1.chain =
        (cq.1.puncturedTopHigher cq.2 hik hkj).reindex f.toOrderHom at hf
      have hzero : f.toOrderHom 0 = 0 ∨ f.toOrderHom 0 = Fin.last 1 := by
        have hv : (f.toOrderHom 0).val = 0 ∨ (f.toOrderHom 0).val = 1 := by
          have hvlt := (f.toOrderHom 0).isLt
          change (f.toOrderHom 0).val < 2 at hvlt
          omega
        rcases hv with hv | hv
        · left
          apply Fin.ext
          exact hv
        · right
          apply Fin.ext
          simpa using hv
      rcases hzero with hzero | hlast
      · have heq : cp.1.chain = cq.1.chain := by
          apply PathChain.ext
          funext a
          fin_cases a
          have h := congrArg (fun z : PathChain 0 i j ↦ z.path 0) hf
          change cp.1.chain.path 0 =
            (cq.1.puncturedTopHigher cq.2 hik hkj).path (f.toOrderHom 0) at h
          rw [hzero] at h
          exact h
        have hpq : cp = cq := by
          apply Subtype.ext
          apply UnknownCell.ext
          exact heq
        subst cq
        exact (asymm hqp hqp).elim
      · have hkfull : k ∈
            ((cq.1.puncturedTopHigher cq.2 hik hkj).path (Fin.last 1)).I := by
          change k ∈ (cq.1.puncturedTopHigher cq.2 hik hkj).last.I
          rw [cq.1.puncturedTopHigher_last cq.2 hik hkj]
          exact (mem_fullPath_iff i j k (hik.trans hkj)).2 ⟨hik, hkj⟩
        have hpath := congrArg (fun z : PathChain 0 i j ↦ z.path 0) hf
        change cp.1.chain.path 0 =
          (cq.1.puncturedTopHigher cq.2 hik hkj).path (f.toOrderHom 0) at hpath
        have : cp.1.chain.path 0 =
            (cq.1.puncturedTopHigher cq.2 hik hkj).path (Fin.last 1) := by
          simpa only [hlast] using hpath
        have : k ∈ cp.1.chain.last.I := by
          change k ∈ (cp.1.chain.path 0).I
          rw [this]
          exact hkfull
        exact cp.2 this
    · have hs : s = 0 := by
        by_contra hs
        have hrank : ExtendedGlobalPairIndex.RankRel hik hkj
            (.inl cp) (.inr (⟨s, q⟩ : GlobalPairIndex i j k)) := by
          apply Prod.Lex.left
          change 1 < s + 1
          omega
        exact (asymm hqp
          (ExtendedGlobalPairIndex.rankRel_lt_wellOrder hik hkj hrank)).elim
      subst s
      exact q.false_of_degreeZero.elim
  · rcases q with cq | ⟨s, q⟩
    · intro hmem
      rw [mem_ofSimplex_toNerveSimplex_iff] at hmem
      obtain ⟨f, hf⟩ := hmem
      change SimplexCategory.mk r ⟶ SimplexCategory.mk 1 at f
      change p.cell.chain =
        (cq.1.puncturedTopHigher cq.2 hik hkj).reindex f.toOrderHom at hf
      have hfinj : Function.Injective f.toOrderHom :=
        orderHom_injective_of_path_comp_injective p.cell.chain.path p.cell.nondegenerate
          (cq.1.puncturedTopHigher cq.2 hik hkj).path f.toOrderHom (fun a ↦ by
            have h := congrArg (fun z : PathChain r i j ↦ z.path a) hf
            exact h)
      have hrle : r ≤ 1 := by
        have hc := Fintype.card_le_of_injective f.toOrderHom hfinj
        simp only [Fintype.card_fin] at hc
        omega
      rcases Nat.eq_zero_or_pos r with rfl | hrpos
      · exact p.false_of_degreeZero.elim
      · have hr : r = 1 := by omega
        subst r
        have hfid : f.toOrderHom = OrderHom.id :=
          OrderHom.eq_id_of_injective f.toOrderHom hfinj
        have hupeq : cq.1.puncturedTopHigher cq.2 hik hkj = p.cell.chain := by
          rw [hf, hfid]
          apply PathChain.ext
          funext a
          rfl
        have hpos : 0 < (cq.1.puncturedTopHigher cq.2 hik hkj).entryIndex k
            (cq.1.puncturedTopHigher_memLast cq.2 hik hkj) := by
          rw [cq.1.puncturedTopHigher_entryIndex_eq_last cq.2 hik hkj]
          exact Fin.last_pos
        have hpresent := cq.1.puncturedTopHigher_entryErasePresent cq.2 hik hkj
          p.left_ne p.right_ne hpos
        have hex0 : ∃ (hk : k ∈
            (cq.1.puncturedTopHigher cq.2 hik hkj).last.I)
            (hp : 0 < (cq.1.puncturedTopHigher cq.2 hik hkj).entryIndex k hk),
            (cq.1.puncturedTopHigher cq.2 hik hkj).EntryErasePresent k hk hp
              p.left_ne p.right_ne :=
          ⟨cq.1.puncturedTopHigher_memLast cq.2 hik hkj, hpos, hpresent⟩
        rw [hupeq] at hex0
        have hex : ∃ (hk : k ∈ p.cell.chain.last.I)
            (hp : 0 < p.cell.chain.entryIndex k hk),
            p.cell.chain.EntryErasePresent k hk hp p.left_ne p.right_ne := hex0
        obtain ⟨hk, hp, hpresent⟩ := hex
        apply p.erase_new
        convert hpresent using 1
    · intro hmem
      rw [mem_ofSimplex_toNerveSimplex_iff] at hmem
      obtain ⟨f, hf⟩ := hmem
      change SimplexCategory.mk r ⟶ SimplexCategory.mk (s + 1) at f
      change p.cell.chain = q.upperChain.reindex f.toOrderHom at hf
      have hfinj : Function.Injective f.toOrderHom :=
        orderHom_injective_of_path_comp_injective p.cell.chain.path p.cell.nondegenerate
          q.upperChain.path f.toOrderHom (fun a ↦ by
            have h := congrArg (fun z : PathChain r i j ↦ z.path a) hf
            exact h)
      have hrs : r ≤ s + 1 := by
        have hc := Fintype.card_le_of_injective f.toOrderHom hfinj
        simp only [Fintype.card_fin] at hc
        omega
      rcases lt_trichotomy r s with hrslt | hrseq | hrslt
      · have hrank : ExtendedGlobalPairIndex.RankRel hik hkj
            (.inr (⟨r, p⟩ : GlobalPairIndex i j k))
            (.inr (⟨s, q⟩ : GlobalPairIndex i j k)) := by
          apply Prod.Lex.left
          change r + 1 < s + 1
          omega
        exact (asymm hqp
          (ExtendedGlobalPairIndex.rankRel_lt_wellOrder hik hkj hrank)).elim
      · subst s
        obtain ⟨t, ht⟩ := orderHom_eq_succAbove_of_injective f.toOrderHom hfinj
        have hface : p.cell.chain = q.upperChain.deleteAt t := by
          rw [hf, deleteAt]
          congr 1
        by_cases htpos : t = q.position
        · subst t
          have hpqchain : p.cell.chain = q.cell.chain :=
            hface.trans q.delete_position_upperChain
          have hpq : p = q := EntryLowerCell.ext_of_chain_eq hpqchain
          subst p
          exact (asymm hqp hqp).elim
        · by_cases htk : k ∈ (q.upperChain.path t).I
          · have hmultFace : p.cell.chain.kMultiplicity k <
                q.upperChain.kMultiplicity k := by
              rw [hface]
              exact kMultiplicity_deleteAt_lt_of_mem q.upperChain t k htk
            have hmult : p.upperChain.kMultiplicity k <
                q.upperChain.kMultiplicity k := by
              rw [← p.cell_kMultiplicity_eq_upperChain]
              exact hmultFace
            have hrank : ExtendedGlobalPairIndex.RankRel hik hkj
                (.inr (⟨r, p⟩ : GlobalPairIndex i j k))
                (.inr (⟨r, q⟩ : GlobalPairIndex i j k)) := by
              apply Prod.Lex.right
              exact hmult
            exact (asymm hqp
              (ExtendedGlobalPairIndex.rankRel_lt_wellOrder hik hkj hrank)).elim
          · exact q.deleteAt_ne_selectedLower_of_not_mem p t (Ne.symm htpos) htk hface.symm
      · have hrsucc : r = s + 1 := by omega
        subst r
        have hfid : f.toOrderHom = OrderHom.id :=
          OrderHom.eq_id_of_injective f.toOrderHom hfinj
        have hupeq : q.upperChain = p.cell.chain := by
          rw [hf, hfid]
          rfl
        exact q.upperChain_ne_selectedLower p hupeq

/-- The selected lower simplex is absent from the entire extended earlier stage. -/
theorem ExtendedGlobalPairIndex.lower_not_mem_earlierStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (p.rankedKanFacePair hik hkj).2.lower.toNerveSimplex ∉
      (p.earlierStage hik hkj).obj _ := by
  intro h
  rcases h with hknown | hearlier
  · rcases p with p | ⟨r, p⟩
    · exact p.1.unknown hknown
    · exact p.cell.unknown hknown
  · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hearlier
    obtain ⟨q, hq, hmem⟩ := hearlier
    exact p.lower_not_mem_ofSimplex_earlierUpper hik hkj q hq hmem

theorem ExtendedGlobalPairIndex.lower_not_mem_previousStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (p.rankedKanFacePair hik hkj).2.lower.toNerveSimplex ∉
      (p.previousStage hik hkj).obj _ := by
  intro h
  rcases h with hearlier | hhorn
  · exact p.lower_not_mem_earlierStage hik hkj hearlier
  · exact (p.rankedKanFacePair hik hkj).2.lower_not_mem_hornRange hhorn

theorem RankedKanFacePair.missingFace_image_upperMap {k : J}
    (a : RankedKanFacePair r i j k) :
    (SSet.stdSimplex.face {a.face}ᶜ).image a.upperMap =
      SSet.Subcomplex.ofSimplex a.lower.toNerveSimplex := by
  rw [← SSet.stdSimplex.range_δ, ← SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_ofSimplex]
  rw [SSet.yonedaEquiv_comp]
  change SSet.Subcomplex.ofSimplex
    ((CategoryTheory.nerve (ThickPath i j)).δ a.face a.upper.toNerveSimplex) = _
  rw [← toNerveSimplex_deleteAt, a.lower_eq]

theorem ExtendedGlobalPairIndex.previousStage_preimage_upperMap_le_horn {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (p.previousStage hik hkj).preimage
        (p.rankedKanFacePair hik hkj).2.upperMap ≤
      SSet.horn ((p.rankedKanFacePair hik hkj).1 + 1)
        (p.rankedKanFacePair hik hkj).2.face := by
  rw [SSet.subcomplex_le_horn_iff]
  intro hface
  let a := (p.rankedKanFacePair hik hkj).2
  have himage : (SSet.stdSimplex.face {a.face}ᶜ).image a.upperMap ≤
      p.previousStage hik hkj :=
    (SSet.Subcomplex.image_le_iff (f := a.upperMap)
      (A := SSet.stdSimplex.face {a.face}ᶜ) (p.previousStage hik hkj)).2 hface
  rw [a.missingFace_image_upperMap] at himage
  exact p.lower_not_mem_previousStage hik hkj
    ((SSet.Subcomplex.ofSimplex_le_iff _ _).1 himage)

theorem ExtendedGlobalPairIndex.previousStage_inf_upper_eq_hornRange {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    p.previousStage hik hkj ⊓
        SSet.Subcomplex.ofSimplex
          (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex =
      (p.rankedKanFacePair hik hkj).2.hornRange := by
  exact (p.rankedKanFacePair hik hkj).2.inf_upperRange_eq_hornRange
    (p.previousStage hik hkj)
    (p.previousStage_preimage_upperMap_le_horn hik hkj)
    (p.hornRange_le_previousStage hik hkj)

noncomputable def ExtendedGlobalPairIndex.hornIsoOverlap {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (SSet.horn ((p.rankedKanFacePair hik hkj).1 + 1)
      (p.rankedKanFacePair hik hkj).2.face : SSet) ≅
      ((p.previousStage hik hkj ⊓ SSet.Subcomplex.ofSimplex
        (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex :
          (CategoryTheory.nerve (ThickPath i j)).Subcomplex) : SSet) := by
  let a := (p.rankedKanFacePair hik hkj).2
  let f := a.hornMap
  letI : Mono f := by dsimp [f]; infer_instance
  exact asIso (SSet.Subcomplex.toRange f) ≪≫
    SSet.Subcomplex.eqToIso (p.previousStage_inf_upper_eq_hornRange hik hkj).symm

noncomputable def ExtendedGlobalPairIndex.simplexIsoUpperRange {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    Δ[(p.rankedKanFacePair hik hkj).1 + 1] ≅
      (SSet.Subcomplex.ofSimplex
        (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex : SSet) :=
  asIso (SSet.Subcomplex.toRange (p.rankedKanFacePair hik hkj).2.upperMap) ≪≫
    SSet.Subcomplex.eqToIso (p.rankedKanFacePair hik hkj).2.range_upperMap

noncomputable def ExtendedGlobalPairIndex.hornToPreviousStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (SSet.horn ((p.rankedKanFacePair hik hkj).1 + 1)
      (p.rankedKanFacePair hik hkj).2.face : SSet) ⟶
      (p.previousStage hik hkj : SSet) :=
  (p.hornIsoOverlap hik hkj).hom ≫
    SSet.Subcomplex.homOfLE (inf_le_left : p.previousStage hik hkj ⊓
      SSet.Subcomplex.ofSimplex
        (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex ≤ p.previousStage hik hkj)

noncomputable def ExtendedGlobalPairIndex.previousToNextStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    (p.previousStage hik hkj : SSet) ⟶ (p.nextStage hik hkj : SSet) :=
  SSet.Subcomplex.homOfLE (p.previousStage_le_nextStage hik hkj)

noncomputable def ExtendedGlobalPairIndex.simplexToNextStage {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    Δ[(p.rankedKanFacePair hik hkj).1 + 1] ⟶ (p.nextStage hik hkj : SSet) :=
  (p.simplexIsoUpperRange hik hkj).hom ≫ SSet.Subcomplex.homOfLE (le_sup_right :
    SSet.Subcomplex.ofSimplex
      (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex ≤ p.nextStage hik hkj)

/-- Every extended successor stage is the actual pushout of its (possibly outer) Kan horn. -/
theorem ExtendedGlobalPairIndex.hornAttachment_isPushout {i j k : J}
    (hik : i ≤ k) (hkj : k ≤ j) (p : ExtendedGlobalPairIndex i j k) :
    IsPushout (p.hornToPreviousStage hik hkj)
      (SSet.horn ((p.rankedKanFacePair hik hkj).1 + 1)
        (p.rankedKanFacePair hik hkj).2.face).ι
      (p.previousToNextStage hik hkj) (p.simplexToNextStage hik hkj) := by
  let A := p.previousStage hik hkj
  let B := SSet.Subcomplex.ofSimplex
    (p.rankedKanFacePair hik hkj).2.upper.toNerveSimplex
  have h := SSet.Subcomplex.inf_inclusions_isPushout A B
  apply h.of_iso' (p.hornIsoOverlap hik hkj) (Iso.refl _)
    (p.simplexIsoUpperRange hik hkj) (Iso.refl _)
  · simp [ExtendedGlobalPairIndex.hornToPreviousStage]
  · apply (cancel_mono B.ι).1
    simp [ExtendedGlobalPairIndex.hornIsoOverlap,
      ExtendedGlobalPairIndex.simplexIsoUpperRange, RankedKanFacePair.upperMap]
    rfl
  · rfl
  · change (p.simplexIsoUpperRange hik hkj).hom ≫ _ = _
    rfl

/-- The subcomplex generated by all upper cells preceding `p` in the global enumeration. -/
noncomputable def GlobalPairIndex.earlierStage {i j k : J} (p : GlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  knownPathSubcomplex i j k ⊔
    ⨆ (q : GlobalPairIndex i j k), ⨆ (_h : @LT.lt _
      (GlobalPairIndex.wellOrder (i := i) (j := j) (k := k)).toLT q p),
      SSet.Subcomplex.ofSimplex q.2.upperChain.toNerveSimplex

/-- Earlier pairs together with every nonmissing face of the current upper cell. -/
noncomputable def GlobalPairIndex.previousStage {i j k : J} (p : GlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  p.earlierStage ⊔ p.2.rankedInnerFacePair.hornRange

theorem GlobalPairIndex.known_le_previousStage {i j k : J}
    (p : GlobalPairIndex i j k) : knownPathSubcomplex i j k ≤ p.previousStage :=
  le_trans le_sup_left le_sup_left

theorem GlobalPairIndex.hornRange_le_previousStage {i j k : J}
    (p : GlobalPairIndex i j k) :
    p.2.rankedInnerFacePair.hornRange ≤ p.previousStage :=
  le_sup_right

noncomputable def GlobalPairIndex.nextStage {i j k : J} (p : GlobalPairIndex i j k) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  p.previousStage ⊔ SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex

theorem GlobalPairIndex.previousStage_le_nextStage {i j k : J}
    (p : GlobalPairIndex i j k) : p.previousStage ≤ p.nextStage :=
  le_sup_left

/-- A selected missing lower simplex is not already in the known horn subcomplex. -/
theorem EntryLowerCell.lower_not_mem_knownPathSubcomplex {k : J}
    (p : EntryLowerCell r i j k) :
    p.cell.chain.toNerveSimplex ∉ (knownPathSubcomplex i j k).obj _ := by
  intro h
  exact p.cell.unknown h

/-- Equivalently, the subcomplex generated by the missing lower simplex is not contained in the
known subcomplex. -/
theorem EntryLowerCell.lower_ofSimplex_not_le_known {k : J}
    (p : EntryLowerCell r i j k) :
    ¬ SSet.Subcomplex.ofSimplex p.cell.chain.toNerveSimplex ≤
      knownPathSubcomplex i j k := by
  rw [SSet.Subcomplex.ofSimplex_le_iff]
  exact p.lower_not_mem_knownPathSubcomplex

theorem EntryLowerCell.lower_not_mem_hornRange {k : J}
    (p : EntryLowerCell r i j k) :
    p.cell.chain.toNerveSimplex ∉ p.rankedInnerFacePair.hornRange.obj _ :=
  p.rankedInnerFacePair.lower_not_mem_hornRange

theorem EntryLowerCell.lower_not_mem_known_sup_hornRange {k : J}
    (p : EntryLowerCell r i j k) :
    p.cell.chain.toNerveSimplex ∉
      (knownPathSubcomplex i j k ⊔ p.rankedInnerFacePair.hornRange).obj _ := by
  intro h
  rcases h with h | h
  · exact p.lower_not_mem_knownPathSubcomplex h
  · exact p.lower_not_mem_hornRange h

/-- A selected lower simplex is not generated by an upper cell which precedes it in the global
well-order.  The proof separates lower-dimensional factors, codimension-one faces, and the
same-dimensional factor. -/
theorem GlobalPairIndex.lower_not_mem_ofSimplex_earlierUpper {k : J}
    (p : EntryLowerCell r i j k) (q : EntryLowerCell s i j k)
    (hqp : @LT.lt _ (GlobalPairIndex.wellOrder (i := i) (j := j) (k := k)).toLT
      (⟨s, q⟩ : GlobalPairIndex i j k) ⟨r, p⟩) :
    p.cell.chain.toNerveSimplex ∉
      (SSet.Subcomplex.ofSimplex q.upperChain.toNerveSimplex).obj _ := by
  intro hmem
  rw [mem_ofSimplex_toNerveSimplex_iff] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hfinj : Function.Injective f.toOrderHom :=
    orderHom_injective_of_path_comp_injective p.cell.chain.path p.cell.nondegenerate
      q.upperChain.path f.toOrderHom (fun a ↦ by
        have h := congrArg (fun z : PathChain r i j ↦ z.path a) hf
        exact h)
  have hrs : r ≤ s + 1 := by
    simpa using Fintype.card_le_of_injective f.toOrderHom hfinj
  rcases lt_trichotomy r s with hrslt | hrseq | hrslt
  · have hrank : GlobalPairIndex.RankRel
        (⟨r, p⟩ : GlobalPairIndex i j k) ⟨s, q⟩ := by
      apply Prod.Lex.left
      change r + 1 < s + 1
      omega
    exact (asymm hqp (GlobalPairIndex.rankRel_lt_wellOrder hrank)).elim
  · subst s
    obtain ⟨t, ht⟩ := orderHom_eq_succAbove_of_injective f.toOrderHom hfinj
    have hface : p.cell.chain = q.upperChain.deleteAt t := by
      rw [hf, deleteAt]
      congr 1
    by_cases htpos : t = q.position
    · subst t
      have hpqchain : p.cell.chain = q.cell.chain :=
        hface.trans q.delete_position_upperChain
      have hpq : p = q := by
        exact EntryLowerCell.ext_of_chain_eq hpqchain
      subst p
      exact (asymm hqp hqp).elim
    · by_cases htk : k ∈ (q.upperChain.path t).I
      · have hmultFace : p.cell.chain.kMultiplicity k < q.upperChain.kMultiplicity k := by
          rw [hface]
          exact kMultiplicity_deleteAt_lt_of_mem q.upperChain t k htk
        have hmult : p.upperChain.kMultiplicity k < q.upperChain.kMultiplicity k := by
          rw [← p.cell_kMultiplicity_eq_upperChain]
          exact hmultFace
        have hrank : GlobalPairIndex.RankRel
            (⟨r, p⟩ : GlobalPairIndex i j k) ⟨r, q⟩ := by
          apply Prod.Lex.right
          exact hmult
        exact (asymm hqp (GlobalPairIndex.rankRel_lt_wellOrder hrank)).elim
      · exact q.deleteAt_ne_selectedLower_of_not_mem p t (Ne.symm htpos) htk hface.symm
  · have hrsucc : r = s + 1 := by omega
    subst r
    have hfid : f.toOrderHom = OrderHom.id :=
      OrderHom.eq_id_of_injective f.toOrderHom hfinj
    have hupeq : q.upperChain = p.cell.chain := by
      rw [hf, hfid]
      rfl
    exact q.upperChain_ne_selectedLower p hupeq

/-- The missing lower simplex of a pair is absent from the entire stage generated by all
earlier upper cells. -/
theorem GlobalPairIndex.lower_not_mem_earlierStage {k : J}
    (p : GlobalPairIndex i j k) :
    p.2.cell.chain.toNerveSimplex ∉ p.earlierStage.obj _ := by
  intro h
  rcases h with hknown | hearlier
  · exact p.2.lower_not_mem_knownPathSubcomplex hknown
  · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hearlier
    obtain ⟨q, hq, hmem⟩ := hearlier
    exact GlobalPairIndex.lower_not_mem_ofSimplex_earlierUpper p.2 q.2 hq hmem

theorem GlobalPairIndex.lower_not_mem_previousStage {k : J}
    (p : GlobalPairIndex i j k) :
    p.2.cell.chain.toNerveSimplex ∉ p.previousStage.obj _ := by
  intro h
  rcases h with hearlier | hhorn
  · exact p.lower_not_mem_earlierStage hearlier
  · exact p.2.lower_not_mem_hornRange hhorn

/-- The upper simplex itself is absent from the previous stage, since otherwise simplicial
closure would put its distinguished lower face there as well. -/
theorem GlobalPairIndex.upper_not_mem_previousStage {k : J}
    (p : GlobalPairIndex i j k) :
    p.2.upperChain.toNerveSimplex ∉ p.previousStage.obj _ := by
  intro hu
  apply p.lower_not_mem_previousStage
  have hface := p.previousStage.map (SimplexCategory.δ p.2.position).op hu
  rw [← p.2.nerve_face_upper_eq_lower]
  exact hface

noncomputable def GlobalPairIndex.upperMap {k : J} (p : GlobalPairIndex i j k) :
    Δ[p.1 + 1] ⟶ CategoryTheory.nerve (ThickPath i j) :=
  SSet.yonedaEquiv.symm p.2.upperChain.toNerveSimplex

theorem GlobalPairIndex.range_upperMap {k : J} (p : GlobalPairIndex i j k) :
    SSet.Subcomplex.range p.upperMap =
      SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex := by
  rw [SSet.Subcomplex.range_eq_ofSimplex]
  simp [upperMap]

theorem GlobalPairIndex.missingFace_image_upperMap {k : J}
    (p : GlobalPairIndex i j k) :
    (SSet.stdSimplex.face {p.2.position}ᶜ).image p.upperMap =
      SSet.Subcomplex.ofSimplex p.2.cell.chain.toNerveSimplex := by
  rw [← SSet.stdSimplex.range_δ, ← SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_eq_ofSimplex]
  rw [SSet.yonedaEquiv_comp]
  change SSet.Subcomplex.ofSimplex
    ((CategoryTheory.nerve (ThickPath i j)).δ p.2.position
      p.2.upperChain.toNerveSimplex) = _
  have h := p.2.nerve_face_upper_eq_lower
  change (CategoryTheory.nerve (ThickPath i j)).δ p.2.position
    p.2.upperChain.toNerveSimplex = p.2.cell.chain.toNerveSimplex at h
  exact congrArg SSet.Subcomplex.ofSimplex h

/-- Pulling the previous stage back to the standard upper simplex lands in the attaching horn. -/
theorem GlobalPairIndex.previousStage_preimage_upperMap_le_horn {k : J}
    (p : GlobalPairIndex i j k) :
    p.previousStage.preimage p.upperMap ≤ SSet.horn (p.1 + 1) p.2.position := by
  rw [SSet.subcomplex_le_horn_iff]
  intro hface
  have himage : (SSet.stdSimplex.face {p.2.position}ᶜ).image p.upperMap ≤
      p.previousStage :=
    (SSet.Subcomplex.image_le_iff (f := p.upperMap)
      (A := SSet.stdSimplex.face {p.2.position}ᶜ) p.previousStage).2 hface
  rw [p.missingFace_image_upperMap] at himage
  exact p.lower_not_mem_previousStage
    ((SSet.Subcomplex.ofSimplex_le_iff _ _).1 himage)

theorem GlobalPairIndex.hornRange_eq_horn_image_upperMap {k : J}
    (p : GlobalPairIndex i j k) :
    p.2.rankedInnerFacePair.hornRange =
      (SSet.horn (p.1 + 1) p.2.position).image p.upperMap := by
  rw [SSet.Subcomplex.image_eq_range]
  rfl

/-- The overlap of the previous stage with the newly generated simplex is exactly the horn
along which it is attached. -/
theorem GlobalPairIndex.previousStage_inf_upper_ofSimplex_eq_hornRange {k : J}
    (p : GlobalPairIndex i j k) :
    p.previousStage ⊓ SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex =
      p.2.rankedInnerFacePair.hornRange := by
  apply le_antisymm
  · rw [← p.range_upperMap,
      ← SSet.Subcomplex.image_preimage_eq_inf_range]
    rw [p.hornRange_eq_horn_image_upperMap]
    exact SSet.Subcomplex.image_monotone p.upperMap
      p.previousStage_preimage_upperMap_le_horn
  · apply le_inf p.hornRange_le_previousStage
    rw [p.hornRange_eq_horn_image_upperMap,
      ← p.range_upperMap]
    exact SSet.Subcomplex.image_le_range (SSet.horn (p.1 + 1) p.2.position) p.upperMap

/-- The upper simplex classifying a global pair is a monomorphism. -/
noncomputable instance GlobalPairIndex.mono_upperMap {k : J}
    (p : GlobalPairIndex i j k) : Mono p.upperMap := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  intro x y hxy
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext a
  apply p.2.rankedInnerFacePair.upperNondegenerate
  have hxy' :
      (SSet.yonedaEquiv.symm p.2.upperChain.toNerveSimplex).app U
          (SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv x)) =
        (SSet.yonedaEquiv.symm p.2.upperChain.toNerveSimplex).app U
          (SSet.stdSimplex.objEquiv.symm (SSet.stdSimplex.objEquiv y)) := by
    simpa [upperMap] using hxy
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm,
    SSet.yonedaEquiv_symm_app_objEquiv_symm] at hxy'
  exact congrArg (fun z ↦ (PathChain.ofNerveSimplex z).path a) hxy'

/-- The horn map of a global pair is a monomorphism. -/
noncomputable instance GlobalPairIndex.mono_hornMap {k : J}
    (p : GlobalPairIndex i j k) : Mono p.2.rankedInnerFacePair.hornMap := by
  change Mono ((SSet.horn (p.1 + 1) p.2.position).ι ≫ p.upperMap)
  infer_instance

/-- The canonical identification of the attaching horn with the actual overlap subcomplex. -/
noncomputable def GlobalPairIndex.hornIsoOverlap {k : J}
    (p : GlobalPairIndex i j k) :
    (SSet.horn (p.1 + 1) p.2.position : SSet) ≅
      ((p.previousStage ⊓
        SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex :
          (CategoryTheory.nerve (ThickPath i j)).Subcomplex) : SSet) := by
  let f := (SSet.horn (p.1 + 1) p.2.position).ι ≫ p.upperMap
  letI : Mono f := by dsimp [f]; infer_instance
  change (SSet.horn (p.1 + 1) p.2.position : SSet) ≅ _
  exact asIso (SSet.Subcomplex.toRange f) ≪≫
    SSet.Subcomplex.eqToIso p.previousStage_inf_upper_ofSimplex_eq_hornRange.symm

/-- The canonical identification of the standard simplex with the subcomplex it generates. -/
noncomputable def GlobalPairIndex.simplexIsoUpperRange {k : J}
    (p : GlobalPairIndex i j k) :
    Δ[p.1 + 1] ≅
      (SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex : SSet) :=
  asIso (SSet.Subcomplex.toRange p.upperMap) ≪≫
    SSet.Subcomplex.eqToIso p.range_upperMap

/-- The attaching horn mapped into the stage preceding a global pair. -/
noncomputable def GlobalPairIndex.hornToPreviousStage {k : J}
    (p : GlobalPairIndex i j k) :
    (SSet.horn (p.1 + 1) p.2.position : SSet) ⟶ (p.previousStage : SSet) :=
  p.hornIsoOverlap.hom ≫
    SSet.Subcomplex.homOfLE (inf_le_left :
      p.previousStage ⊓ SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex ≤
        p.previousStage)

/-- The preceding-stage inclusion in the stage obtained by adjoining the upper simplex. -/
noncomputable def GlobalPairIndex.previousToNextStage {k : J}
    (p : GlobalPairIndex i j k) : (p.previousStage : SSet) ⟶ (p.nextStage : SSet) :=
  SSet.Subcomplex.homOfLE p.previousStage_le_nextStage

/-- The upper standard simplex mapped into the stage obtained by adjoining it. -/
noncomputable def GlobalPairIndex.simplexToNextStage {k : J}
    (p : GlobalPairIndex i j k) : Δ[p.1 + 1] ⟶ (p.nextStage : SSet) :=
  p.simplexIsoUpperRange.hom ≫
    SSet.Subcomplex.homOfLE (le_sup_right :
      SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex ≤ p.nextStage)

/-- Each successor step in the path filtration is the actual pushout of an inner horn. -/
theorem GlobalPairIndex.innerHornAttachment_isPushout {k : J}
    (p : GlobalPairIndex i j k) :
    IsPushout p.hornToPreviousStage
      (SSet.horn (p.1 + 1) p.2.position).ι
      p.previousToNextStage p.simplexToNextStage := by
  let A := p.previousStage
  let B := SSet.Subcomplex.ofSimplex p.2.upperChain.toNerveSimplex
  have h := SSet.Subcomplex.inf_inclusions_isPushout A B
  apply h.of_iso'
    p.hornIsoOverlap (Iso.refl _) p.simplexIsoUpperRange (Iso.refl _)
  · rfl
  · apply (cancel_mono B.ι).1
    simp [hornIsoOverlap, simplexIsoUpperRange, upperMap]
    rfl
  · rfl
  · rfl

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

end LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
