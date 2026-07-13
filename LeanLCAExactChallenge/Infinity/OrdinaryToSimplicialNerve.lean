import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# Ordinary nerves inside homotopy-coherent nerves

Ordinary composable chains define coherent simplices with locally constant hom maps.

These simplices give a canonical map from the ordinary nerve to the homotopy-coherent nerve.
-/

set_option autoImplicit false

noncomputable section

universe v u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.EnrichedCategory
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  Simplicial Opposite
open scoped MonoidalCategory Simplicial

namespace OrdinaryToSimplicialNerve

/-- The unique map out of an empty path nerve. -/
def emptyPathNerveMap
    {J : Type v} [LinearOrder J]
    (i j : CategoryTheory.SimplicialThickening J) (h : ¬ i.as ≤ j.as)
    (X : SSet.{v}) : CategoryTheory.nerve (i ⟶ j) ⟶ X where
  app n := ConcreteCategory.ofHom (TypeCat.Fun.mk (fun F =>
    (h (CategoryTheory.SimplicialThickening.Path.le (F.obj 0))).elim))
  naturality _ _ _ := by
    ext F
    exact (h (CategoryTheory.SimplicialThickening.Path.le
      (F.obj 0))).elim

variable (C : Type u) [Category.{v} C] [CategoryTheory.SimplicialCategory C]

lemma uliftFin_down_mono {n : ℕ}
    {a b : ULift.{v, 0} (Fin n)} (h : a ≤ b) : a.down ≤ b.down := by
  exact h

/-- The locally constant coherent hom map associated to an ordinary composable chain. -/
def coherentMapOfChain
    {n : ℕ} (F : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n)
    (i j : CategoryTheory.SimplicialThickening (ULift (Fin (n + 1)))) :
    CategoryTheory.nerve (i ⟶ j) ⟶
      (CategoryTheory.ForgetEnrichment.to SSet (F.obj i.as.down) ⟶[SSet]
        CategoryTheory.ForgetEnrichment.to SSet (F.obj j.as.down)) :=
  if h : i.as ≤ j.as then
    toUnit _ ≫ CategoryTheory.ForgetEnrichment.homTo SSet
      (F.map (homOfLE (uliftFin_down_mono h)))
  else
    emptyPathNerveMap i j h _

/-- An ordinary composable chain regarded as a locally constant homotopy-coherent simplex. -/
def coherentSimplexOfChain
    {n : ℕ} (F : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift (Fin (n + 1)))) C where
  obj i := CategoryTheory.ForgetEnrichment.to SSet (F.obj i.as.down)
  map := coherentMapOfChain C F
  map_id i := by
    unfold coherentMapOfChain
    rw [dif_pos le_rfl]
    have hm : (homOfLE (by simp) : i.as.down ⟶ i.as.down) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [hm, F.map_id]
    have he : CategoryTheory.eId SSet i ≫
        toUnit (CategoryTheory.nerve (i ⟶ i)) = 𝟙 (𝟙_ SSet) :=
      toUnit_unique _ _
    rw [← Category.assoc, he, Category.id_comp,
      CategoryTheory.ForgetEnrichment.homTo_id]
  map_comp i j k := by
    have prove_le (a b : CategoryTheory.SimplicialThickening
        (ULift (Fin (n + 1)))) (p : a ⟶ b) : a.as ≤ b.as :=
      CategoryTheory.SimplicialThickening.Path.le p
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro q
    have hij : i.as ≤ j.as := prove_le i j (q.1.obj 0)
    have hjk : j.as ≤ k.as := prove_le j k (q.2.obj 0)
    have hik : i.as ≤ k.as := hij.trans hjk
    simp only [coherentMapOfChain, dif_pos hij, dif_pos hjk, dif_pos hik,
      NatTrans.comp_app, comp_apply]
    have hF : F.map (homOfLE (uliftFin_down_mono hik)) =
        F.map (homOfLE (uliftFin_down_mono hij)) ≫
          F.map (homOfLE (uliftFin_down_mono hjk)) := by
      rw [← F.map_comp]
      congr
    rw [hF, CategoryTheory.ForgetEnrichment.homTo_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Map the ordinary nerve to the coherent nerve by making each hom simplex locally constant. -/
def ordinaryNerveToSimplicialNerve :
    CategoryTheory.nerve
        (CategoryTheory.ForgetEnrichment SSet.{v} C) ⟶
      CategoryTheory.SimplicialNerve C where
  app Δ := ConcreteCategory.ofHom (TypeCat.Fun.mk (fun F =>
    coherentSimplexOfChain C F))
  naturality Δ Δ' f := by
    apply ConcreteCategory.hom_ext
    intro F
    let L := ((CategoryTheory.nerve
      (CategoryTheory.ForgetEnrichment SSet C)).map f ≫
        ConcreteCategory.ofHom (TypeCat.Fun.mk (fun F =>
          coherentSimplexOfChain C F))) F
    let R := (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun F =>
      coherentSimplexOfChain C F)) ≫
        (CategoryTheory.SimplicialNerve C).map f) F
    change L = R
    have h_obj : ∀ i, L.obj i = R.obj i := fun i => rfl
    refine CategoryTheory.EnrichedFunctor.ext SSet h_obj ?_
    intro i j
    dsimp only [L, R] at *
    simp only [eqToHom_refl, Category.comp_id]
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro p
    have hij : i.as ≤ j.as :=
      CategoryTheory.SimplicialThickening.Path.le (p.obj 0)
    let φ : ULift.{v} (Fin (Δ'.unop.len + 1)) →o
        ULift.{v} (Fin (Δ.unop.len + 1)) :=
      OrderHom.uliftMap f.unop.toOrderHom
    have hij' : φ i.as ≤ φ j.as := φ.monotone hij
    change (((coherentSimplexOfChain C
      (F.whiskerLeft (SimplexCategory.toCat.map f.unop).toFunctor)).map
        i j).app U) p =
      (((CategoryTheory.SimplicialThickening.functor
        φ).comp SSet
          (coherentSimplexOfChain C F)).map i j).app U p
    simp only [
      CategoryTheory.EnrichedFunctor.comp_map,
      CategoryTheory.SimplicialThickening.functor_map,
      CategoryTheory.SimplicialThickening.functor_obj_as,
      CategoryTheory.nerveMap_app,
      CategoryTheory.ComposableArrows.whiskerLeft_map,
      coherentSimplexOfChain, coherentMapOfChain, dif_pos hij,
      dif_pos hij',
      NatTrans.comp_app, comp_apply]
    have hmap : (SimplexCategory.toCat.map f.unop).toFunctor.map
        (show i.as.down ⟶ j.as.down from
          homOfLE (uliftFin_down_mono hij)) =
      (homOfLE (uliftFin_down_mono hij') :
        (φ i.as).down ⟶ (φ j.as).down) := Subsingleton.elim _ _
    rw [hmap]
    congr

/-- The object of the thickening represented by a vertex of the standard simplex. -/
def thickeningVertex {n : ℕ} (i : Fin (n + 1)) :
    CategoryTheory.SimplicialThickening (ULift.{v} (Fin (n + 1))) :=
  .mk (ULift.up i)

@[simp]
lemma ordinaryNerveToSimplicialNerve_obj
    {n : ℕ}
    (F : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n)
    (i : Fin (n + 1)) :
    ((ordinaryNerveToSimplicialNerve C).app (op (SimplexCategory.mk n)) F).obj
        (thickeningVertex i) =
      CategoryTheory.ForgetEnrichment.to SSet (F.obj i) :=
  rfl

lemma ordinaryNerveToSimplicialNerve_map
    {n : ℕ}
    (F : CategoryTheory.ComposableArrows
      (CategoryTheory.ForgetEnrichment SSet.{v} C) n)
    {i j : Fin (n + 1)} (h : i ≤ j) :
    ((ordinaryNerveToSimplicialNerve C).app (op (SimplexCategory.mk n)) F).map
        (thickeningVertex i) (thickeningVertex j) =
      toUnit _ ≫ CategoryTheory.ForgetEnrichment.homTo SSet
        (F.map (homOfLE h)) := by
  change coherentMapOfChain C F (thickeningVertex i)
    (thickeningVertex j) = _
  unfold coherentMapOfChain
  dsimp only [thickeningVertex]
  rw [dif_pos (show (ULift.up i : ULift.{v} _) ≤ ULift.up j from h)]
  congr

lemma ordinaryNerveToSimplicialNerve_edge
    {X Y : CategoryTheory.ForgetEnrichment SSet.{v} C} (f : X ⟶ Y) :
    ((ordinaryNerveToSimplicialNerve C).app (op (SimplexCategory.mk 1))
      (CategoryTheory.ComposableArrows.mk₁ f)).map
        (thickeningVertex (0 : Fin 2))
        (thickeningVertex (1 : Fin 2)) =
      toUnit _ ≫ CategoryTheory.ForgetEnrichment.homTo SSet f := by
  rw [ordinaryNerveToSimplicialNerve_map C _ (show (0 : Fin 2) ≤ 1 by decide)]
  rfl

end OrdinaryToSimplicialNerve

end LeanLCAExactChallenge.Infinity
