import LeanLCAExactChallenge.Infinity.CoherentNerveKanExtension
import Mathlib.Order.Fin.SuccAboveOrderIso

/-!
# Compatibility of coherent-nerve path latching maps

Composition factors through the known-path latching subcomplex.

The through-vertex piece is the product of the two shorter path nerves.

Kan extension preserves the resulting enriched-composition equation.

The pairwise overlap equation between the constructed omitted-vertex face maps remains to be proved.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration

open CategoryTheory Opposite Simplicial MonoidalCategory
open CategoryTheory.SimplicialCategory CategoryTheory.EnrichedCategory
open Path Chain Chain.PathChain

/-- The object of a coherent horn at a vertex, extracted from its constant zero-simplex. -/
noncomputable def innerHornObject (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {n : ℕ} {k : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (a : CategoryTheory.SimplicialThickening (ULift (Fin (n + 3)))) : C :=
  (σ.app (op (.mk 0)) (SSet.horn.const n k a.as.down (op (.mk 0)))).obj
    (CategoryTheory.SimplicialThickening.mk (ULift.up 0))

/-- The enriched functor carried by one available codimension-one face of a coherent horn. -/
def innerHornFaceFunctor (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {n : ℕ} {k l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift (Fin (n + 2)))) C :=
  σ.app _ (SSet.horn.face k l hlk)

/-- Every available horn face has the common object assignment extracted from horn vertices. -/
theorem innerHornFaceFunctor_obj (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {n : ℕ} {k l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k)
    (a : CategoryTheory.SimplicialThickening (ULift (Fin (n + 2)))) :
    (innerHornFaceFunctor C σ hlk).obj a =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (l.succAbove a.as.down))) := by
  have h := σ.naturality_apply
    (SimplexCategory.const (.mk 0) (.mk (n + 1)) a.as.down).op
    (SSet.horn.face k l hlk)
  have hobj := congrArg
    (fun F ↦ F.obj (CategoryTheory.SimplicialThickening.mk (ULift.up 0))) h
  have hface :
      (SSet.horn (n + 2) k : SSet).map
          (SimplexCategory.const (.mk 0) (.mk (n + 1)) a.as.down).op
          (SSet.horn.face k l hlk) =
        SSet.horn.const n k (l.succAbove a.as.down) (op (.mk 0)) := by
    apply Subtype.ext
    ext b
    rfl
  rw [hface] at hobj
  change innerHornObject C σ
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (l.succAbove a.as.down))) =
    (innerHornFaceFunctor C σ hlk).obj a at hobj
  exact hobj.symm

/-- Delete a specified vertex from a different finite ordinal vertex. -/
noncomputable def deleteFinVertex {n : ℕ} (l : Fin (n + 2))
    (a : Fin (n + 2)) (hal : a ≠ l) : Fin (n + 1) :=
  (Fin.succAboveOrderIso l).symm ⟨a, by simpa using hal⟩

@[simp]
theorem succAbove_deleteFinVertex {n : ℕ} (l : Fin (n + 2))
    (a : Fin (n + 2)) (hal : a ≠ l) :
    l.succAbove (deleteFinVertex l a hal) = a := by
  exact congrArg Subtype.val ((Fin.succAboveOrderIso l).apply_symm_apply
    ⟨a, by simpa using hal⟩)

/-- Deletion is injective away from the deleted vertex. -/
theorem deleteFinVertex_ne {n : ℕ} (l a b : Fin (n + 2))
    (hal : a ≠ l) (hbl : b ≠ l) (hab : a ≠ b) :
    deleteFinVertex l a hal ≠ deleteFinVertex l b hbl := by
  intro h
  apply hab
  rw [← succAbove_deleteFinVertex l a hal,
    ← succAbove_deleteFinVertex l b hbl, h]

/-- Deleting a lower vertex shifts a higher vertex down by one. -/
theorem deleteFinVertex_of_lt {n : ℕ} {l a : Fin (n + 2)} (h : l < a) :
    deleteFinVertex l a (ne_of_gt h) = a.pred (Fin.ne_zero_of_lt h) := by
  apply l.succAbove_right_injective
  rw [succAbove_deleteFinVertex, Fin.succAbove_pred_of_lt _ _ h]

/-- Deleting a higher vertex leaves a lower vertex at its cast-pred position. -/
theorem deleteFinVertex_of_gt {n : ℕ} {l a : Fin (n + 2)} (h : a < l) :
    deleteFinVertex l a (ne_of_lt h) = a.castPred (Fin.ne_last_of_lt h) := by
  apply l.succAbove_right_injective
  rw [succAbove_deleteFinVertex, Fin.succAbove_castPred_of_lt _ _ h]

/-- After deleting the lower of two vertices, the position of the lower vertex after deleting
the higher one is the corresponding `predAbove` index. -/
theorem deleteFinVertex_swapIndex {n : ℕ} {l m : Fin (n + 3)} (hlm : l < m) :
    deleteFinVertex m l (ne_of_lt hlm) =
      (deleteFinVertex l m (ne_of_gt hlm)).predAbove l := by
  apply m.succAbove_right_injective
  rw [succAbove_deleteFinVertex]
  have hm : l.succAbove (deleteFinVertex l m (ne_of_gt hlm)) = m :=
    succAbove_deleteFinVertex l m (ne_of_gt hlm)
  symm
  calc
    m.succAbove ((deleteFinVertex l m (ne_of_gt hlm)).predAbove l) =
        (l.succAbove (deleteFinVertex l m (ne_of_gt hlm))).succAbove
          ((deleteFinVertex l m (ne_of_gt hlm)).predAbove l) := by rw [hm]
    _ = l := Fin.succAbove_succAbove_predAbove l _

/-- Reinserting two ordered deleted vertices is independent of the insertion order. -/
theorem succAbove_deleteFinVertex_comm {n : ℕ} {l m : Fin (n + 3)}
    (hlm : l < m) (q : Fin (n + 1)) :
    l.succAbove ((deleteFinVertex l m (ne_of_gt hlm)).succAbove q) =
      m.succAbove ((deleteFinVertex m l (ne_of_lt hlm)).succAbove q) := by
  rw [deleteFinVertex_swapIndex hlm]
  calc
    l.succAbove ((deleteFinVertex l m (ne_of_gt hlm)).succAbove q) =
        (l.succAbove (deleteFinVertex l m (ne_of_gt hlm))).succAbove
          (((deleteFinVertex l m (ne_of_gt hlm)).predAbove l).succAbove q) :=
      (Fin.succAbove_succAbove_succAbove_predAbove l _ q).symm
    _ = m.succAbove
        (((deleteFinVertex l m (ne_of_gt hlm)).predAbove l).succAbove q) := by
      rw [succAbove_deleteFinVertex]

/-- Deleting two distinct vertices gives the same remaining coordinate in either order. -/
theorem deleteFinVertex_delete_comm {n : ℕ} {l m q : Fin (n + 3)}
    (hlm : l < m) (hql : q ≠ l) (hqm : q ≠ m) :
    deleteFinVertex (deleteFinVertex l m (ne_of_gt hlm))
        (deleteFinVertex l q hql)
        (deleteFinVertex_ne l q m hql (ne_of_gt hlm) hqm) =
      deleteFinVertex (deleteFinVertex m l (ne_of_lt hlm))
        (deleteFinVertex m q hqm)
        (deleteFinVertex_ne m q l hqm (ne_of_lt hlm) hql) := by
  let ml := deleteFinVertex l m (ne_of_gt hlm)
  let lm := deleteFinVertex m l (ne_of_lt hlm)
  apply (l.succAbove_right_injective.comp ml.succAbove_right_injective)
  change l.succAbove (ml.succAbove
      (deleteFinVertex ml (deleteFinVertex l q hql) _)) =
    l.succAbove (ml.succAbove
      (deleteFinVertex lm (deleteFinVertex m q hqm) _))
  rw [succAbove_deleteFinVertex, succAbove_deleteFinVertex]
  have hins : (fun x ↦ l.succAbove (ml.succAbove x)) =
      fun x ↦ m.succAbove (lm.succAbove x) := by
    funext x
    dsimp only [lm]
    rw [deleteFinVertex_swapIndex hlm]
    calc
      l.succAbove (ml.succAbove x) =
          (l.succAbove ml).succAbove ((ml.predAbove l).succAbove x) :=
        (Fin.succAbove_succAbove_succAbove_predAbove l ml x).symm
      _ = m.succAbove ((ml.predAbove l).succAbove x) := by
        rw [show l.succAbove ml = m from succAbove_deleteFinVertex l m (ne_of_gt hlm)]
  change q = (fun x ↦ l.succAbove (ml.succAbove x))
    (deleteFinVertex lm (deleteFinVertex m q hqm) _)
  rw [hins]
  change q = m.succAbove (lm.succAbove
    (deleteFinVertex lm (deleteFinVertex m q hqm) _))
  rw [succAbove_deleteFinVertex, succAbove_deleteFinVertex]

/-- Delete a vertex omitted by a thick path, reindexing the path in the smaller ordinal. -/
noncomputable def deletePathVertex
    {n : ℕ} {i j : Fin (n + 2)}
    (p : CategoryTheory.SimplicialThickening.Path (ULift.up i) (ULift.up j))
    (l : Fin (n + 2))
    (hli : i ≠ l) (hlj : j ≠ l) :
    CategoryTheory.SimplicialThickening.Path
      (ULift.up (deleteFinVertex l i hli))
      (ULift.up (deleteFinVertex l j hlj)) where
  I := {q | ULift.up (l.succAbove q.down) ∈ p.I}
  left := by simpa using p.left
  right := by simpa using p.right
  left_le q hq := by
    change deleteFinVertex l i hli ≤ q.down
    rw [← (Fin.succAboveOrderEmb l).le_iff_le]
    simp only [Fin.succAboveOrderEmb_apply, succAbove_deleteFinVertex]
    change i ≤ l.succAbove q.down
    simpa using p.left_le (ULift.up (l.succAbove q.down)) hq
  le_right q hq := by
    change q.down ≤ deleteFinVertex l j hlj
    rw [← (Fin.succAboveOrderEmb l).le_iff_le]
    simp only [Fin.succAboveOrderEmb_apply, succAbove_deleteFinVertex]
    change l.succAbove q.down ≤ j
    simpa using p.le_right (ULift.up (l.succAbove q.down)) hq

/-- Deleting one vertex preserves omission of every other vertex, with the latter reindexed. -/
theorem deletePathVertex_not_mem {n : ℕ} {i j : Fin (n + 2)}
    (p : CategoryTheory.SimplicialThickening.Path (ULift.up i) (ULift.up j))
    (l m : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) (hml : m ≠ l)
    (hm : ULift.up m ∉ p.I) :
    ULift.up (deleteFinVertex l m hml) ∉ (deletePathVertex p l hli hlj).I := by
  intro h
  apply hm
  change ULift.up (l.succAbove (deleteFinVertex l m hml)) ∈ p.I at h
  rw [succAbove_deleteFinVertex] at h
  exact h

/-- Reinsert a deleted finite-ordinal vertex into a thick path. -/
noncomputable def insertPathVertex {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (p : CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u, 0} (deleteFinVertex l i hli))
      (ULift.up.{u, 0} (deleteFinVertex l j hlj))) :
    CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u, 0} i) (ULift.up.{u, 0} j) where
  I := {q | ∃ r ∈ p.I, q = ULift.up.{u, 0} (l.succAbove r.down)}
  left := ⟨ULift.up.{u, 0} (deleteFinVertex l i hli), p.left, by
    apply ULift.ext
    exact (succAbove_deleteFinVertex l i hli).symm⟩
  right := ⟨ULift.up.{u, 0} (deleteFinVertex l j hlj), p.right, by
    apply ULift.ext
    exact (succAbove_deleteFinVertex l j hlj).symm⟩
  left_le q := by
    rintro ⟨r, hr, rfl⟩
    change i ≤ l.succAbove r.down
    rw [← succAbove_deleteFinVertex l i hli]
    have h := p.left_le r hr
    change deleteFinVertex l i hli ≤ r.down at h
    exact (Fin.succAboveOrderEmb l).monotone h
  le_right q := by
    rintro ⟨r, hr, rfl⟩
    change l.succAbove r.down ≤ j
    rw [← succAbove_deleteFinVertex l j hlj]
    have h := p.le_right r hr
    change r.down ≤ deleteFinVertex l j hlj at h
    exact (Fin.succAboveOrderEmb l).monotone h

/-- Reinserting a deleted vertex recovers any path which omitted that vertex. -/
theorem insert_deletePathVertex {n : ℕ} {i j : Fin (n + 2)}
    (p : CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u, 0} i) (ULift.up.{u, 0} j))
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (hlp : ULift.up.{u, 0} l ∉ p.I) :
    insertPathVertex l hli hlj (deletePathVertex p l hli hlj) = p := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  ext q
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact hr
  · intro hq
    have hql : q.down ≠ l := by
      intro hql
      apply hlp
      have hq' : q = ULift.up.{u, 0} l := by
        apply ULift.ext
        exact hql
      exact hq' ▸ hq
    refine ⟨ULift.up.{u, 0} (deleteFinVertex l q.down hql), ?_, ?_⟩
    · change ULift.up.{u, 0}
        (l.succAbove (deleteFinVertex l q.down hql)) ∈ p.I
      rw [succAbove_deleteFinVertex]
      exact hq
    · apply ULift.ext
      exact (succAbove_deleteFinVertex l q.down hql).symm

/-- Reindex thick paths by reinserting one finite-ordinal vertex. -/
noncomputable def insertVertexPathFunctor {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    ThickPath (ULift.up.{u, 0} (deleteFinVertex l i hli))
        (ULift.up.{u, 0} (deleteFinVertex l j hlj)) ⥤
      ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} j) where
  obj p := insertPathVertex l hli hlj p
  map f := ⟨⟨⟨by
    rintro _ ⟨r, hr, hq⟩
    exact ⟨r, f.1.1.1 hr, hq⟩⟩⟩⟩

/-- The path-nerve map induced by reinserting a vertex. -/
noncomputable def insertVertexPathNerveMap {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} (deleteFinVertex l i hli))
          (ULift.up.{u, 0} (deleteFinVertex l j hlj))) ⟶
      CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)) :=
  CategoryTheory.nerveMap (insertVertexPathFunctor l hli hlj)

/-- Paths with propositionally equal endpoints are heterogeneously equal when their vertex sets
agree. -/
theorem path_heq_of_endpoint_eq {J : Type u} [LinearOrder J]
    {i j i' j' : J} (hi : i = i') (hj : j = j')
    (p : CategoryTheory.SimplicialThickening.Path i j)
    (q : CategoryTheory.SimplicialThickening.Path i' j') (hI : p.I = q.I) :
    HEq p q := by
  subst i'
  subst j'
  exact heq_of_eq (CategoryTheory.SimplicialThickening.Path.ext hI)

/-- Deleting two vertices from a thick path is independent of the deletion order, up to the
propositionally equal double-deleted endpoints. -/
theorem deletePathVertex_delete_heq
    {n : ℕ} {i j l m : Fin (n + 3)}
    (p : CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u, 0} i) (ULift.up.{u, 0} j))
    (hlm : l < m) (hli : i ≠ l) (hlj : j ≠ l)
    (hmi : i ≠ m) (hmj : j ≠ m) :
    HEq
      (deletePathVertex (deletePathVertex p l hli hlj)
        (deleteFinVertex l m (ne_of_gt hlm))
        (deleteFinVertex_ne l i m hli (ne_of_gt hlm) hmi)
        (deleteFinVertex_ne l j m hlj (ne_of_gt hlm) hmj))
      (deletePathVertex (deletePathVertex p m hmi hmj)
        (deleteFinVertex m l (ne_of_lt hlm))
        (deleteFinVertex_ne m i l hmi (ne_of_lt hlm) hli)
        (deleteFinVertex_ne m j l hmj (ne_of_lt hlm) hlj)) := by
  apply path_heq_of_endpoint_eq
  · apply ULift.ext
    exact deleteFinVertex_delete_comm hlm hli hmi
  · apply ULift.ext
    exact deleteFinVertex_delete_comm hlm hlj hmj
  · ext q
    change ULift.up.{u, 0}
        (l.succAbove ((deleteFinVertex l m (ne_of_gt hlm)).succAbove q.down)) ∈ p.I ↔
      ULift.up.{u, 0}
        (m.succAbove ((deleteFinVertex m l (ne_of_lt hlm)).succAbove q.down)) ∈ p.I
    rw [succAbove_deleteFinVertex_comm hlm]

/-- The nerves of thick-path categories respect propositional equality of their endpoints. -/
theorem nerve_thickPath_eq_of_endpoint_eq {J : Type u} [LinearOrder J]
    {i j i' j' : J} (hi : i = i') (hj : j = j') :
    CategoryTheory.nerve (ThickPath i j) =
      CategoryTheory.nerve (ThickPath i' j') := by
  subst i'
  subst j'
  rfl

/-- Explicit vertex reinsertion agrees heterogeneously with the thickening face functor. -/
theorem insertVertexPathFunctor_obj_heq {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (p : ThickPath
      (ULift.up.{u, 0} (deleteFinVertex l i hli))
      (ULift.up.{u, 0} (deleteFinVertex l j hlj))) :
    HEq ((insertVertexPathFunctor l hli hlj).obj p)
      ((CategoryTheory.SimplicialThickening.functorMap
        (SimplexCategory.δ l).toOrderHom.uliftMap
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up.{u, 0} (deleteFinVertex l i hli)))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up.{u, 0} (deleteFinVertex l j hlj)))).obj p) := by
  apply path_heq_of_endpoint_eq
  · apply ULift.ext
    exact (succAbove_deleteFinVertex l i hli).symm
  · apply ULift.ext
    exact (succAbove_deleteFinVertex l j hlj).symm
  · ext q
    simp only [insertVertexPathFunctor, insertPathVertex, Set.mem_image]
    constructor
    · rintro ⟨r, hr, hq⟩
      exact ⟨r, hr, hq.symm⟩
    · rintro ⟨r, hr, hq⟩
      exact ⟨r, hr, hq.symm⟩

/-- Objectwise heterogeneous equality of path-valued functors induces heterogeneous equality
of their nerve simplices when the endpoints agree propositionally. -/
theorem nerveMap_app_heq_of_pathFunctor_obj_heq
    {J A : Type u} [LinearOrder J] [Category.{u} A]
    {i j i' j' : J} (hi : i = i') (hj : j = j')
    (F : CategoryTheory.Functor A (ThickPath i j))
    (G : CategoryTheory.Functor A (ThickPath i' j'))
    (hobj : ∀ a, HEq (F.obj a) (G.obj a))
    (U : SimplexCategoryᵒᵖ) (x : (CategoryTheory.nerve A).obj U) :
    HEq ((CategoryTheory.nerveMap F).app U x)
      ((CategoryTheory.nerveMap G).app U x) := by
  subst i'
  subst j'
  apply heq_of_eq
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ eq_of_heq (hobj (x.obj a)))
    (h_map := fun _ _ _ ↦ Subsingleton.elim _ _)

/-- The preceding simplexwise comparison assembles into a heterogeneous equality of nerve
maps. -/
theorem nerveMap_heq_of_pathFunctor_obj_heq
    {J A : Type u} [LinearOrder J] [Category.{u} A]
    {i j i' j' : J} (hi : i = i') (hj : j = j')
    (F : CategoryTheory.Functor A (ThickPath i j))
    (G : CategoryTheory.Functor A (ThickPath i' j'))
    (hobj : ∀ a, HEq (F.obj a) (G.obj a)) :
    HEq (CategoryTheory.nerveMap F) (CategoryTheory.nerveMap G) := by
  subst i'
  subst j'
  apply heq_of_eq
  apply CategoryTheory.NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  exact eq_of_heq
    (nerveMap_app_heq_of_pathFunctor_obj_heq rfl rfl F G hobj U x)

/-- Explicit and canonical vertex reinsertion induce the same nerve simplex, up to their
propositionally equal endpoint types. -/
theorem insertVertexPathNerveMap_app_heq {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (U : SimplexCategoryᵒᵖ) (x : (CategoryTheory.nerve
      (ThickPath
        (ULift.up.{u, 0} (deleteFinVertex l i hli))
        (ULift.up.{u, 0} (deleteFinVertex l j hlj)))).obj U) :
    HEq ((insertVertexPathNerveMap l hli hlj).app U x)
      ((CategoryTheory.nerveMap
        (CategoryTheory.SimplicialThickening.functorMap
          (SimplexCategory.δ l).toOrderHom.uliftMap
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up.{u, 0} (deleteFinVertex l i hli)))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up.{u, 0} (deleteFinVertex l j hlj))))).app U x) := by
  apply nerveMap_app_heq_of_pathFunctor_obj_heq
  · apply ULift.ext
    exact (succAbove_deleteFinVertex l i hli).symm
  · apply ULift.ext
    exact (succAbove_deleteFinVertex l j hlj).symm
  · intro p
    exact insertVertexPathFunctor_obj_heq l hli hlj p

/-- Explicit and canonical vertex reinsertion agree as heterogeneous simplicial maps. -/
theorem insertVertexPathNerveMap_heq {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    HEq (insertVertexPathNerveMap l hli hlj)
      (CategoryTheory.nerveMap
        (CategoryTheory.SimplicialThickening.functorMap
          (SimplexCategory.δ l).toOrderHom.uliftMap
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up.{u, 0} (deleteFinVertex l i hli)))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up.{u, 0} (deleteFinVertex l j hlj))))) := by
  apply nerveMap_heq_of_pathFunctor_obj_heq
  · apply ULift.ext
    exact (succAbove_deleteFinVertex l i hli).symm
  · apply ULift.ext
    exact (succAbove_deleteFinVertex l j hlj).symm
  · intro p
    exact insertVertexPathFunctor_obj_heq l hli hlj p

/-- An enriched functor's Hom maps respect propositional equality of both endpoint objects. -/
theorem enrichedFunctor_map_heq_of_obj_eq
    {D E : Type u} [Category.{u} D] [Category.{u} E]
    [CategoryTheory.SimplicialCategory D] [CategoryTheory.SimplicialCategory E]
    (F : CategoryTheory.EnrichedFunctor SSet D E)
    {a b a' b' : D} (ha : a = a') (hb : b = b') :
    HEq (F.map a b) (F.map a' b') := by
  subst a'
  subst b'
  rfl

/-- Explicit reinsertion followed by an enriched Hom map is the Hom map of the canonical
restricted enriched functor. -/
theorem insertVertexPathNerveMap_comp_enrichedMap_heq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (F : CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift.{u, 0} (Fin (n + 2)))) C) :
    HEq
      (insertVertexPathNerveMap l hli hlj ≫
        F.map
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j)))
      (((CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ l).toOrderHom.uliftMap).comp (E := C) SSet F).map
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l i hli)))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l j hlj)))) := by
  let a := CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i)
  let b := CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} j)
  let a' := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex l i hli))
  let b' := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex l j hlj))
  let G := CategoryTheory.SimplicialThickening.functor
    (SimplexCategory.δ l).toOrderHom.uliftMap
  have ha : a = G.obj a' := by
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    exact (succAbove_deleteFinVertex l i hli).symm
  have hb : b = G.obj b' := by
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    exact (succAbove_deleteFinVertex l j hlj).symm
  apply CategoryTheory.heq_comp
  · rfl
  · exact nerve_thickPath_eq_of_endpoint_eq
      (congrArg CategoryTheory.SimplicialThickening.as ha)
      (congrArg CategoryTheory.SimplicialThickening.as hb)
  · exact congrArg₂ (fun X Y : C ↦ X ⟶[SSet] Y)
      (congrArg F.obj ha) (congrArg F.obj hb)
  · exact insertVertexPathNerveMap_heq l hli hlj
  · exact enrichedFunctor_map_heq_of_obj_eq F ha hb

/-- The canonical-restriction comparison remains valid after an arbitrary precomposition. -/
theorem precomp_insertVertexPathNerveMap_comp_enrichedMap_heq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (F : CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift.{u, 0} (Fin (n + 2)))) C)
    {X : SSet.{u}}
    (P : X ⟶ CategoryTheory.nerve
      (ThickPath
        (ULift.up.{u, 0} (deleteFinVertex l i hli))
        (ULift.up.{u, 0} (deleteFinVertex l j hlj)))) :
    HEq
      (P ≫ (insertVertexPathNerveMap l hli hlj ≫
        F.map
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))))
      (P ≫
        ((CategoryTheory.SimplicialThickening.functor
          (SimplexCategory.δ l).toOrderHom.uliftMap).comp (E := C) SSet F).map
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex l i hli)))
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex l j hlj)))) := by
  let a := CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i)
  let b := CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} j)
  let a' := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex l i hli))
  let b' := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex l j hlj))
  let G := CategoryTheory.SimplicialThickening.functor
    (SimplexCategory.δ l).toOrderHom.uliftMap
  have ha : a = G.obj a' := by
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    exact (succAbove_deleteFinVertex l i hli).symm
  have hb : b = G.obj b' := by
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    exact (succAbove_deleteFinVertex l j hlj).symm
  apply CategoryTheory.heq_comp
  · rfl
  · rfl
  · exact congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
      (congrArg F.obj ha) (congrArg F.obj hb)
  · rfl
  · exact insertVertexPathNerveMap_comp_enrichedMap_heq C l hli hlj F

/-- Reindex thick paths along deletion of one endpoint-distinct vertex. -/
noncomputable def deleteVertexPathFunctor {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    ThickPath (ULift.up i) (ULift.up j) ⥤
      ThickPath (ULift.up (deleteFinVertex l i hli))
        (ULift.up (deleteFinVertex l j hlj)) where
  obj p := deletePathVertex p l hli hlj
  map f := ⟨⟨⟨fun _ hx ↦ f.1.1.1 hx⟩⟩⟩

/-- The path-nerve map induced by deleting a vertex. -/
noncomputable def deleteVertexPathNerveMap {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    CategoryTheory.nerve (ThickPath (ULift.up i) (ULift.up j)) ⟶
      CategoryTheory.nerve
        (ThickPath (ULift.up (deleteFinVertex l i hli))
          (ULift.up (deleteFinVertex l j hlj))) :=
  CategoryTheory.nerveMap (deleteVertexPathFunctor l hli hlj)

/-- The two double-deletion simplicial maps agree heterogeneously. -/
theorem deleteVertexPathNerveMap_comp_comm_heq
    {n : ℕ} {i j l m : Fin (n + 3)}
    (hlm : l < m) (hli : i ≠ l) (hlj : j ≠ l)
    (hmi : i ≠ m) (hmj : j ≠ m) :
    HEq
      (deleteVertexPathNerveMap.{u} l hli hlj ≫
        deleteVertexPathNerveMap.{u} (deleteFinVertex l m (ne_of_gt hlm))
          (deleteFinVertex_ne l i m hli (ne_of_gt hlm) hmi)
          (deleteFinVertex_ne l j m hlj (ne_of_gt hlm) hmj))
      (deleteVertexPathNerveMap.{u} m hmi hmj ≫
        deleteVertexPathNerveMap.{u} (deleteFinVertex m l (ne_of_lt hlm))
          (deleteFinVertex_ne m i l hmi (ne_of_lt hlm) hli)
          (deleteFinVertex_ne m j l hmj (ne_of_lt hlm) hlj)) := by
  let F := deleteVertexPathFunctor.{u} l hli hlj ⋙
    deleteVertexPathFunctor.{u} (deleteFinVertex l m (ne_of_gt hlm))
      (deleteFinVertex_ne l i m hli (ne_of_gt hlm) hmi)
      (deleteFinVertex_ne l j m hlj (ne_of_gt hlm) hmj)
  let G := deleteVertexPathFunctor.{u} m hmi hmj ⋙
    deleteVertexPathFunctor.{u} (deleteFinVertex m l (ne_of_lt hlm))
      (deleteFinVertex_ne m i l hmi (ne_of_lt hlm) hli)
      (deleteFinVertex_ne m j l hmj (ne_of_lt hlm) hlj)
  change HEq (CategoryTheory.nerveMap F) (CategoryTheory.nerveMap G)
  apply nerveMap_heq_of_pathFunctor_obj_heq
  · apply ULift.ext
    exact deleteFinVertex_delete_comm hlm hli hmi
  · apply ULift.ext
    exact deleteFinVertex_delete_comm hlm hlj hmj
  · intro p
    exact deletePathVertex_delete_heq.{u, u, 0, 0}
      (n := n) p hlm hli hlj hmi hmj

/-- Double-deletion commutation is preserved by an arbitrary precomposition. -/
theorem precomp_deleteVertexPathNerveMap_comp_comm_heq
    {n : ℕ} {i j l m : Fin (n + 3)}
    (hlm : l < m) (hli : i ≠ l) (hlj : j ≠ l)
    (hmi : i ≠ m) (hmj : j ≠ m)
    {X : SSet.{u}}
    (P : X ⟶ CategoryTheory.nerve
      (ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} j))) :
    HEq
      (P ≫ (deleteVertexPathNerveMap l hli hlj ≫
        deleteVertexPathNerveMap (deleteFinVertex l m (ne_of_gt hlm))
          (deleteFinVertex_ne l i m hli (ne_of_gt hlm) hmi)
          (deleteFinVertex_ne l j m hlj (ne_of_gt hlm) hmj)))
      (P ≫ (deleteVertexPathNerveMap m hmi hmj ≫
        deleteVertexPathNerveMap (deleteFinVertex m l (ne_of_lt hlm))
          (deleteFinVertex_ne m i l hmi (ne_of_lt hlm) hli)
          (deleteFinVertex_ne m j l hmj (ne_of_lt hlm) hlj))) := by
  apply CategoryTheory.heq_comp
  · rfl
  · rfl
  · exact nerve_thickPath_eq_of_endpoint_eq
      (congrArg ULift.up (deleteFinVertex_delete_comm hlm hli hmi))
      (congrArg ULift.up (deleteFinVertex_delete_comm hlm hlj hmj))
  · rfl
  · exact deleteVertexPathNerveMap_comp_comm_heq hlm hli hlj hmi hmj

/-- Restriction of a horn face agrees with the corresponding face operator. -/
theorem innerHornFaceFunctor_restrict (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {n : ℕ} {k l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) (a : Fin (n + 2)) :
    σ.app _ ((SSet.horn (n + 2) k : SSet).map (SimplexCategory.δ a).op
      (SSet.horn.face k l hlk)) =
      (CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ a).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hlk) := by
  exact σ.naturality_apply (SimplexCategory.δ a).op (SSet.horn.face k l hlk)

/-- Two available horn faces have equal enriched-functor restrictions on their common face. -/
theorem innerHornFaceFunctor_pairwise_restrict (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {n : ℕ} {k l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) (hmk : m ≠ k) (hlm : l < m) :
    (CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hlk) =
      (CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hmk) := by
  have hface :
      (SSet.horn (n + 2) k : SSet).map
          (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))).op
          (SSet.horn.face k l hlk) =
        (SSet.horn (n + 2) k : SSet).map
          (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))).op
          (SSet.horn.face k m hmk) := by
    apply (SSet.yonedaEquiv (X := (SSet.horn (n + 2) k : SSet))).symm.injective
    rw [← cancel_mono (SSet.horn (n + 2) k).ι]
    change SSet.stdSimplex.map
          (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))) ≫
          SSet.horn.ι k l hlk ≫ (SSet.horn (n + 2) k).ι =
      SSet.stdSimplex.map
          (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))) ≫
          SSet.horn.ι k m hmk ≫ (SSet.horn (n + 2) k).ι
    rw [SSet.horn.ι_ι, SSet.horn.ι_ι]
    change SSet.stdSimplex.map
          (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))) ≫
          SSet.stdSimplex.map (SimplexCategory.δ l) =
      SSet.stdSimplex.map
          (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))) ≫
          SSet.stdSimplex.map (SimplexCategory.δ m)
    rw [← Functor.map_comp, ← Functor.map_comp,
      deleteFinVertex_of_lt hlm, deleteFinVertex_of_gt hlm]
    exact congrArg SSet.stdSimplex.map
      (SimplexCategory.δ_comp_δ' (i := l.castPred (Fin.ne_last_of_lt hlm))
        (j := m) (by simpa using hlm)).symm
  rw [← innerHornFaceFunctor_restrict C σ hlk,
    ← innerHornFaceFunctor_restrict C σ hmk, hface]

/-- Pairwise horn-face compatibility identifies all double-deleted enriched Hom maps. -/
theorem innerHornFaceFunctor_pairwise_restrict_map_heq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) (hmk : m ≠ k) (hlm : l < m)
    (a b : CategoryTheory.SimplicialThickening (ULift.{u, 0} (Fin (n + 1)))) :
    HEq
      (((CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hlk)).map a b)
      (((CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hmk)).map a b) :=
  congr_arg_heq (fun F ↦ F.map a b)
    (innerHornFaceFunctor_pairwise_restrict C σ hlk hmk hlm)

/-- Pairwise restricted horn faces have equal object values at propositionally equal thickening
objects. -/
theorem innerHornFaceFunctor_pairwise_restrict_obj_eq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) (hmk : m ≠ k) (hlm : l < m)
    (a a' : CategoryTheory.SimplicialThickening
      (ULift.{u, 0} (Fin (n + 1)))) (ha : a = a') :
    (((CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))).toOrderHom.uliftMap).comp
        (E := C) SSet (innerHornFaceFunctor C σ hlk)).obj a) =
      (((CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))).toOrderHom.uliftMap).comp
        (E := C) SSet (innerHornFaceFunctor C σ hmk)).obj a') := by
  rw [← ha]
  exact congrArg (fun F ↦ F.obj a)
    (innerHornFaceFunctor_pairwise_restrict C σ hlk hmk hlm)

/-- Pairwise restricted horn-face Hom maps agree at propositionally equal endpoint objects. -/
theorem innerHornFaceFunctor_pairwise_restrict_map_endpoint_heq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) (hmk : m ≠ k) (hlm : l < m)
    (a b a' b' : CategoryTheory.SimplicialThickening
      (ULift.{u, 0} (Fin (n + 1)))) (ha : a = a') (hb : b = b') :
    HEq
      (((CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hlk)).map a b)
      (((CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hmk)).map a' b') := by
  have hsame := innerHornFaceFunctor_pairwise_restrict_map_heq
    C σ hlk hmk hlm a b
  have hargs := enrichedFunctor_map_heq_of_obj_eq
    ((CategoryTheory.SimplicialThickening.functor
      (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))).toOrderHom.uliftMap).comp
        (E := C) SSet (innerHornFaceFunctor C σ hmk)) ha hb
  exact hsame.trans hargs

/-- Pairwise restricted horn-face Hom maps remain compatible after heterogeneously equal
precompositions. -/
theorem precomp_innerHornFaceFunctor_pairwise_restrict_map_endpoint_heq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) (hmk : m ≠ k) (hlm : l < m)
    {X X' : SSet.{u}} (hX : X = X')
    (a b a' b' : CategoryTheory.SimplicialThickening
      (ULift.{u, 0} (Fin (n + 1)))) (ha : a = a') (hb : b = b')
    (P : X ⟶ CategoryTheory.nerve (ThickPath a.as b.as))
    (P' : X' ⟶ CategoryTheory.nerve (ThickPath a'.as b'.as))
    (hP : HEq P P') :
    HEq
      (P ≫
        ((CategoryTheory.SimplicialThickening.functor
          (SimplexCategory.δ (deleteFinVertex l m (ne_of_gt hlm))).toOrderHom.uliftMap).comp
            (E := C) SSet (innerHornFaceFunctor C σ hlk)).map a b)
      (P' ≫
        ((CategoryTheory.SimplicialThickening.functor
          (SimplexCategory.δ (deleteFinVertex m l (ne_of_lt hlm))).toOrderHom.uliftMap).comp
            (E := C) SSet (innerHornFaceFunctor C σ hmk)).map a' b') := by
  apply CategoryTheory.heq_comp hX
  · exact nerve_thickPath_eq_of_endpoint_eq
      (congrArg CategoryTheory.SimplicialThickening.as ha)
      (congrArg CategoryTheory.SimplicialThickening.as hb)
  · exact congrArg₂ (fun A B : C ↦ A ⟶[SSet] B)
      (innerHornFaceFunctor_pairwise_restrict_obj_eq
        C σ hlk hmk hlm a a' ha)
      (innerHornFaceFunctor_pairwise_restrict_obj_eq
        C σ hlk hmk hlm b b' hb)
  · exact hP
  · exact innerHornFaceFunctor_pairwise_restrict_map_endpoint_heq
      C σ hlk hmk hlm a b a' b' ha hb

/-- Composition lands in paths whose least member contains the middle vertex. -/
def pathCompositionToKnownPathSubcomplex {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j)) ⟶
      (knownPathSubcomplex i.as j.as k.as : SSet) :=
  SSet.Subcomplex.lift (CategoryTheory.eComp SSet i k j) (by
    rintro U _ ⟨x, rfl⟩
    change (ofNerveSimplex ((CategoryTheory.eComp SSet i k j).app U x)).KnownAt k.as
    left
    change k.as ∈ (((x.1.prod' x.2) ⋙
      CategoryTheory.SimplicialThickening.compFunctor i k j).obj 0).I
    exact Or.inl (x.1.obj 0).right)

@[reassoc (attr := simp)]
theorem pathCompositionToKnownPathSubcomplex_ι {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    pathCompositionToKnownPathSubcomplex i k j ≫
      (knownPathSubcomplex i.as j.as k.as).ι = CategoryTheory.eComp SSet i k j :=
  rfl

/-- The subcomplex of path chains all of whose paths contain the intermediate vertex. -/
def throughPathSubcomplex {J : Type u} [LinearOrder J] (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex where
  obj U := {x | k ∈ (ofNerveSimplex x).first.I}
  map {U V} f x hx := by
    change k ∈ (ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x)).first.I
    rw [show ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x) =
        (ofNerveSimplex x).reindex f.unop.toOrderHom by
      rw [← toNerveSimplex_ofNerveSimplex x]
      exact ofNerveSimplex_map_toNerveSimplex _ _]
    exact (ofNerveSimplex x).first_le _ hx

/-- The subcomplex of path chains all of whose paths omit a specified vertex. -/
def avoidingPathSubcomplex {J : Type u} [LinearOrder J] (i j l : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex where
  obj U := {x | l ∉ (ofNerveSimplex x).last.I}
  map {U V} f x hx := by
    change l ∉ (ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x)).last.I
    rw [show ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x) =
        (ofNerveSimplex x).reindex f.unop.toOrderHom by
      rw [← toNerveSimplex_ofNerveSimplex x]
      exact ofNerveSimplex_map_toNerveSimplex _ _]
    exact (ofNerveSimplex x).not_mem_of_not_mem_last hx _

/-- Deletion followed by reinsertion is the identity on paths omitting the deleted vertex. -/
@[reassoc]
theorem avoidingPathSubcomplex_delete_insert
    {n : ℕ} {i j l : Fin (n + 2)} (hli : i ≠ l) (hlj : j ≠ l) :
    (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} l)).ι ≫
      deleteVertexPathNerveMap l hli hlj ≫
      insertVertexPathNerveMap l hli hlj =
    (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} l)).ι := by
  ext U x a q
  simp only [NatTrans.comp_app, deleteVertexPathNerveMap,
    insertVertexPathNerveMap, CategoryTheory.nerveMap_app]
  change q ∈ (insertPathVertex l hli hlj
      (deletePathVertex (x.1.obj a) l hli hlj)).I ↔ q ∈ (x.1.obj a).I
  rw [insert_deletePathVertex (x.1.obj a) l hli hlj
    ((ofNerveSimplex x.1).not_mem_of_not_mem_last x.2 a)]

/-- Deleting one of two omitted vertices preserves omission of the other. -/
noncomputable def deleteVertexAvoidingPathMap
    {n : ℕ} {i j l m : Fin (n + 2)}
    (hli : i ≠ l) (hlj : j ≠ l) (hml : m ≠ l) :
    (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j) (ULift.up.{u, 0} l) ⊓
        avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
          (ULift.up.{u, 0} m)).toSSet ⟶
      (avoidingPathSubcomplex
        (ULift.up.{u, 0} (deleteFinVertex l i hli))
        (ULift.up.{u, 0} (deleteFinVertex l j hlj))
        (ULift.up.{u, 0} (deleteFinVertex l m hml))).toSSet :=
  SSet.Subcomplex.lift
    ((avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} l) ⊓ avoidingPathSubcomplex (ULift.up.{u, 0} i)
      (ULift.up.{u, 0} j) (ULift.up.{u, 0} m)).ι ≫
        deleteVertexPathNerveMap l hli hlj) (by
      rintro U _ ⟨x, rfl⟩
      change ULift.up.{u, 0} (deleteFinVertex l m hml) ∉
        (deletePathVertex (ofNerveSimplex x.1).last l hli hlj).I
      intro h
      apply x.2.2
      change ULift.up.{u, 0} (l.succAbove (deleteFinVertex l m hml)) ∈
        (ofNerveSimplex x.1).last.I at h
      rw [succAbove_deleteFinVertex] at h
      exact h)

@[reassoc (attr := simp)]
theorem deleteVertexAvoidingPathMap_ι
    {n : ℕ} {i j l m : Fin (n + 2)}
    (hli : i ≠ l) (hlj : j ≠ l) (hml : m ≠ l) :
    deleteVertexAvoidingPathMap hli hlj hml ≫
      (avoidingPathSubcomplex
        (ULift.up.{u, 0} (deleteFinVertex l i hli))
        (ULift.up.{u, 0} (deleteFinVertex l j hlj))
        (ULift.up.{u, 0} (deleteFinVertex l m hml))).ι =
      (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} l) ⊓ avoidingPathSubcomplex
          (ULift.up.{u, 0} i) (ULift.up.{u, 0} j) (ULift.up.{u, 0} m)).ι ≫
        deleteVertexPathNerveMap l hli hlj :=
  rfl

/-- On paths omitting two vertices, deleting the first and then deleting and reinserting the
second is the same as deleting only the first. -/
theorem inf_avoiding_delete_delete_insert
    {n : ℕ} {i j l m : Fin (n + 3)}
    (hli : i ≠ l) (hlj : j ≠ l) (hml : m ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) :
    (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} l) ⊓
      avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} m)).ι ≫
        deleteVertexPathNerveMap l hli hlj ≫
        deleteVertexPathNerveMap (deleteFinVertex l m hml)
          (deleteFinVertex_ne l i m hli hml him)
          (deleteFinVertex_ne l j m hlj hml hjm) ≫
        insertVertexPathNerveMap (deleteFinVertex l m hml)
          (deleteFinVertex_ne l i m hli hml him)
          (deleteFinVertex_ne l j m hlj hml hjm) =
      (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} l) ⊓
      avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} m)).ι ≫
        deleteVertexPathNerveMap l hli hlj := by
  simp only [← Category.assoc]
  rw [← deleteVertexAvoidingPathMap_ι hli hlj hml]
  simp only [Category.assoc]
  rw [avoidingPathSubcomplex_delete_insert]

/-- The preceding factorization with the second member of a fixed ordered intersection deleted
first. -/
theorem inf_avoiding_delete_delete_insert_right
    {n : ℕ} {i j l m : Fin (n + 3)}
    (hli : i ≠ l) (hlj : j ≠ l) (hml : m ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) :
    (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} l) ⊓
      avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} m)).ι ≫
        deleteVertexPathNerveMap m him hjm ≫
        deleteVertexPathNerveMap (deleteFinVertex m l hml.symm)
          (deleteFinVertex_ne m i l him hml.symm hli)
          (deleteFinVertex_ne m j l hjm hml.symm hlj) ≫
        insertVertexPathNerveMap (deleteFinVertex m l hml.symm)
          (deleteFinVertex_ne m i l him hml.symm hli)
          (deleteFinVertex_ne m j l hjm hml.symm hlj) =
      (avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} l) ⊓
      avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
        (ULift.up.{u, 0} m)).ι ≫
        deleteVertexPathNerveMap m him hjm := by
  ext U x a q
  simp only [NatTrans.comp_app, deleteVertexPathNerveMap,
    insertVertexPathNerveMap, CategoryTheory.nerveMap_app]
  change q ∈ (insertPathVertex (deleteFinVertex m l hml.symm)
      (deleteFinVertex_ne m i l him hml.symm hli)
      (deleteFinVertex_ne m j l hjm hml.symm hlj)
      (deletePathVertex (deletePathVertex (x.1.obj a) m him hjm)
        (deleteFinVertex m l hml.symm)
        (deleteFinVertex_ne m i l him hml.symm hli)
        (deleteFinVertex_ne m j l hjm hml.symm hlj))).I ↔
    q ∈ (deletePathVertex (x.1.obj a) m him hjm).I
  rw [insert_deletePathVertex]
  exact deletePathVertex_not_mem.{u, 0} (x.1.obj a) m l him hjm hml.symm
    ((ofNerveSimplex x.1).not_mem_of_not_mem_last x.2.1 a)

/-- The untransported Hom maps supplied by two ordered horn faces agree on path simplices
omitting both face vertices. -/
theorem innerHornFaceFunctor_avoiding_pairwise_core_heq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hil : i < l) (hlm : l < m) (hmj : m < j) (hlk : l ≠ k) (hmk : m ≠ k) :
    HEq
      ((avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        (deleteVertexPathNerveMap l (ne_of_lt hil) (ne_of_gt (lt_trans hlm hmj)) ≫
          (innerHornFaceFunctor C σ hlk).map
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex l i (ne_of_lt hil))))
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex l j (ne_of_gt (lt_trans hlm hmj)))))))
      ((avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        (deleteVertexPathNerveMap m (ne_of_lt (lt_trans hil hlm)) (ne_of_gt hmj) ≫
          (innerHornFaceFunctor C σ hmk).map
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex m i (ne_of_lt (lt_trans hil hlm)))))
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex m j (ne_of_gt hmj)))))) := by
  let D := avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} l) ⊓
    avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} m)
  let il : i ≠ l := ne_of_lt hil
  let jl : j ≠ l := ne_of_gt (lt_trans hlm hmj)
  let im : i ≠ m := ne_of_lt (lt_trans hil hlm)
  let jm : j ≠ m := ne_of_gt hmj
  let ml := deleteFinVertex l m (ne_of_gt hlm)
  let lm := deleteFinVertex m l (ne_of_lt hlm)
  let ilm := deleteFinVertex_ne l i m il (ne_of_gt hlm) im
  let jlm := deleteFinVertex_ne l j m jl (ne_of_gt hlm) jm
  let iml := deleteFinVertex_ne m i l im (ne_of_lt hlm) il
  let jml := deleteFinVertex_ne m j l jm (ne_of_lt hlm) jl
  let Fl := innerHornFaceFunctor C σ hlk
  let Fm := innerHornFaceFunctor C σ hmk
  let aL := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex ml (deleteFinVertex l i il) ilm))
  let bL := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex ml (deleteFinVertex l j jl) jlm))
  let aR := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex lm (deleteFinVertex m i im) iml))
  let bR := CategoryTheory.SimplicialThickening.mk
    (ULift.up.{u, 0} (deleteFinVertex lm (deleteFinVertex m j jm) jml))
  let PL := D.ι ≫ (deleteVertexPathNerveMap l il jl ≫
    deleteVertexPathNerveMap ml ilm jlm)
  let PR := D.ι ≫ (deleteVertexPathNerveMap m im jm ≫
    deleteVertexPathNerveMap lm iml jml)
  have ha : aL = aR := by
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    exact deleteFinVertex_delete_comm hlm il im
  have hb : bL = bR := by
    apply congrArg CategoryTheory.SimplicialThickening.mk
    apply ULift.ext
    exact deleteFinVertex_delete_comm hlm jl jm
  have hfacL := inf_avoiding_delete_delete_insert
    (n := n) il jl (ne_of_gt hlm) im jm
  have hfacR := inf_avoiding_delete_delete_insert_right
    (n := n) il jl (ne_of_gt hlm) im jm
  have hleft :
      D.ι ≫ (deleteVertexPathNerveMap l il jl ≫
        Fl.map
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l i il)))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l j jl)))) =
      PL ≫ (insertVertexPathNerveMap ml ilm jlm ≫
        Fl.map
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l i il)))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l j jl)))) := by
    dsimp only [D, PL]
    exact congrArg (fun q ↦ q ≫
      Fl.map
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex l i il)))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex l j jl)))) hfacL.symm
  have hright :
      D.ι ≫ (deleteVertexPathNerveMap m im jm ≫
        Fm.map
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex m i im)))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex m j jm)))) =
      PR ≫ (insertVertexPathNerveMap lm iml jml ≫
        Fm.map
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex m i im)))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex m j jm)))) := by
    dsimp only [D, PR]
    exact congrArg (fun q ↦ q ≫
      Fm.map
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex m i im)))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex m j jm)))) hfacR.symm
  have hP : HEq PL PR := by
    exact precomp_deleteVertexPathNerveMap_comp_comm_heq
      hlm il jl im jm D.ι
  change HEq
    (D.ι ≫ (deleteVertexPathNerveMap l il jl ≫
      Fl.map
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex l i il)))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex l j jl)))))
    (D.ι ≫ (deleteVertexPathNerveMap m im jm ≫
      Fm.map
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex m i im)))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex m j jm)))))
  exact HEq.trans (heq_of_eq hleft) <| HEq.trans
    (precomp_insertVertexPathNerveMap_comp_enrichedMap_heq
      C ml ilm jlm Fl PL) <| HEq.trans
    (precomp_innerHornFaceFunctor_pairwise_restrict_map_endpoint_heq
      C σ hlk hmk hlm rfl aL bL aR bR ha hb PL PR hP) <| HEq.trans
    (precomp_insertVertexPathNerveMap_comp_enrichedMap_heq
      C lm iml jml Fm PR).symm
    (heq_of_eq hright.symm)

/-- The mapping-object map carried by an available horn face on paths omitting that face vertex. -/
noncomputable def avoidingPathMapOfInnerHornFace
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    {i j l : Fin (n + 3)} (hil : i < l) (hlj : l < j) (hlk : l ≠ k) :
    (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) : SSet) ⟶
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up i))
        ⟶[SSet]
      innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := by
  let hi : i ≠ l := ne_of_lt hil
  let hj : j ≠ l := ne_of_gt hlj
  let i' := deleteFinVertex l i hi
  let j' := deleteFinVertex l j hj
  let F := innerHornFaceFunctor C σ hlk
  have hobj_i : F.obj (CategoryTheory.SimplicialThickening.mk (ULift.up i')) =
      innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up i)) := by
    simpa [F, i'] using innerHornFaceFunctor_obj C σ hlk
      (CategoryTheory.SimplicialThickening.mk (ULift.up i'))
  have hobj_j : F.obj (CategoryTheory.SimplicialThickening.mk (ULift.up j')) =
      innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up j)) := by
    simpa [F, j'] using innerHornFaceFunctor_obj C σ hlk
      (CategoryTheory.SimplicialThickening.mk (ULift.up j'))
  exact (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).ι ≫
    deleteVertexPathNerveMap l hi hj ≫
    F.map (CategoryTheory.SimplicialThickening.mk (ULift.up i'))
      (CategoryTheory.SimplicialThickening.mk (ULift.up j')) ≫
    eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B) hobj_i hobj_j)

/-- A horn face supplies a full path-map whenever its deleted vertex is distinct from both
interval endpoints. This map is useful when the deleted vertex lies outside the interval. -/
noncomputable def pathMapOfInnerHornFace
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    {i j l : Fin (n + 3)} (hil : i ≠ l) (hjl : j ≠ l) (hlk : l ≠ k) :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)) ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := by
  let i' := deleteFinVertex l i hil
  let j' := deleteFinVertex l j hjl
  let F := innerHornFaceFunctor C σ hlk
  have hobj_i : F.obj (CategoryTheory.SimplicialThickening.mk (ULift.up i')) =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up i)) := by
    simpa [F, i'] using innerHornFaceFunctor_obj C σ hlk
      (CategoryTheory.SimplicialThickening.mk (ULift.up i'))
  have hobj_j : F.obj (CategoryTheory.SimplicialThickening.mk (ULift.up j')) =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up j)) := by
    simpa [F, j'] using innerHornFaceFunctor_obj C σ hlk
      (CategoryTheory.SimplicialThickening.mk (ULift.up j'))
  exact deleteVertexPathNerveMap l hil hjl ≫
    F.map (CategoryTheory.SimplicialThickening.mk (ULift.up i'))
      (CategoryTheory.SimplicialThickening.mk (ULift.up j')) ≫
    eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B) hobj_i hobj_j)

/-- Restricting a full face path-map to paths omitting that face vertex recovers the omitted-face
map. -/
theorem avoidingPathSubcomplex_pathMapOfInnerHornFace
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hil : i < l) (hlj : l < j) (hlk : l ≠ k) :
    (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).ι ≫
        pathMapOfInnerHornFace C σ (ne_of_lt hil) (ne_of_gt hlj) hlk =
      avoidingPathMapOfInnerHornFace C σ hil hlj hlk := by
  rfl

/-- The last available face supplies every full path-map ending at the missing inner-horn
vertex. -/
noncomputable def innerHornLeftPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkLast : k ≠ Fin.last (n + 2)) {i : Fin (n + 3)} (hik : i < k) :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} k)) ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up k))) :=
  pathMapOfInnerHornFace C σ
    (ne_of_lt (lt_trans hik (Fin.lt_last_iff_ne_last.mpr hkLast)))
    hkLast hkLast.symm

/-- The first available face supplies every full path-map starting at the missing inner-horn
vertex. -/
noncomputable def innerHornRightPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) {j : Fin (n + 3)} (hkj : k < j) :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} k) (ULift.up.{u, 0} j)) ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up k)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) :=
  pathMapOfInnerHornFace C σ hkZero
    (ne_of_gt (lt_trans (Fin.pos_iff_ne_zero.mpr hkZero) hkj)) hkZero.symm

/-- Two ordered omitted-vertex face maps agree on paths omitting both vertices. -/
theorem avoidingPathMapOfInnerHornFace_pairwise_of_lt
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hil : i < l) (hlm : l < m) (hmj : m < j) (hlk : l ≠ k) (hmk : m ≠ k) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m) ≤
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)) ≫
        avoidingPathMapOfInnerHornFace C σ hil (lt_trans hlm hmj) hlk =
      SSet.Subcomplex.homOfLE (inf_le_right :
        avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m) ≤
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)) ≫
        avoidingPathMapOfInnerHornFace C σ (lt_trans hil hlm) hmj hmk := by
  apply eq_of_heq
  simp only [avoidingPathMapOfInnerHornFace]
  simp only [← Category.assoc]
  refine (comp_eqToHom_heq (C := SSet) _ _).trans ?_
  refine HEq.trans ?_ (comp_eqToHom_heq (C := SSet) _ _).symm
  change HEq
    ((avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
      (deleteVertexPathNerveMap l (ne_of_lt hil) (ne_of_gt (lt_trans hlm hmj)) ≫
        (innerHornFaceFunctor C σ hlk).map
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l i (ne_of_lt hil))))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex l j (ne_of_gt (lt_trans hlm hmj)))))))
    ((avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
      (deleteVertexPathNerveMap m (ne_of_lt (lt_trans hil hlm)) (ne_of_gt hmj) ≫
        (innerHornFaceFunctor C σ hmk).map
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex m i (ne_of_lt (lt_trans hil hlm)))))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (deleteFinVertex m j (ne_of_gt hmj))))))
  exact innerHornFaceFunctor_avoiding_pairwise_core_heq
    C σ hil hlm hmj hlk hmk

/-- Any two omitted-vertex face maps agree on their binary intersection. -/
theorem avoidingPathMapOfInnerHornFace_pairwise
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hil : i < l) (hlj : l < j) (hlk : l ≠ k)
    (him : i < m) (hmj : m < j) (hmk : m ≠ k) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m) ≤
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)) ≫
        avoidingPathMapOfInnerHornFace C σ hil hlj hlk =
      SSet.Subcomplex.homOfLE (inf_le_right :
        avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m) ≤
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)) ≫
        avoidingPathMapOfInnerHornFace C σ him hmj hmk := by
  rcases lt_trichotomy l m with hlm | rfl | hml
  · exact avoidingPathMapOfInnerHornFace_pairwise_of_lt
      C σ hil hlm hmj hlk hmk
  · rfl
  · ext U x
    have h := congrArg (fun q ↦ q.app U ⟨x.1, ⟨x.2.2, x.2.1⟩⟩)
      (avoidingPathMapOfInnerHornFace_pairwise_of_lt
        C σ him hml hlj hmk hlk)
    exact h.symm

/-- Known paths are through paths or omit a nonmissing vertex. -/
theorem knownPathSubcomplex_eq_through_sup_avoiding {J : Type u} [LinearOrder J]
    (i j k : J) :
    knownPathSubcomplex i j k =
      throughPathSubcomplex i j k ⊔
        ⨆ (l : {l : J // i < l ∧ l < j ∧ l ≠ k}),
          avoidingPathSubcomplex i j l.1 := by
  ext U x
  constructor
  · intro h
    change (ofNerveSimplex x).KnownAt k at h
    rcases h with hk | ⟨l, hil, hlj, hlk, hl⟩
    · exact Or.inl hk
    · apply Or.inr
      simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
      have hli : l ≠ i := fun hli ↦ hl (hli ▸ (ofNerveSimplex x).last.left)
      have hlj' : l ≠ j := fun hlj' ↦ hl (hlj' ▸ (ofNerveSimplex x).last.right)
      exact ⟨⟨l, lt_of_le_of_ne hil hli.symm, lt_of_le_of_ne hlj hlj', hlk⟩, hl⟩
  · intro h
    change (ofNerveSimplex x).KnownAt k
    rcases h with hk | havoid
    · exact Or.inl hk
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at havoid
      obtain ⟨l, hl⟩ := havoid
      exact Or.inr ⟨l.1, l.2.1.le, l.2.2.1.le, l.2.2.2, hl⟩

/-- The union of all known-path pieces obtained by omitting a nonmissing vertex. -/
def avoidingKnownPathSubcomplex {J : Type u} [LinearOrder J] (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  ⨆ (l : {l : J // i < l ∧ l < j ∧ l ≠ k}), avoidingPathSubcomplex i j l.1

section SubcomplexUnionMap

variable {X Y : SSet.{u}} {I : Type u} (A : I → X.Subcomplex)

private noncomputable def iSupSubcomplexWitness
    (U : SimplexCategoryᵒᵖ) (x : (⨆ i, A i : X.Subcomplex).obj U) : I :=
  Classical.choose (by
    simpa only [Subfunctor.iSup_obj, Set.mem_iUnion] using x.2)

private theorem iSupSubcomplexWitness_mem
    (U : SimplexCategoryᵒᵖ) (x : (⨆ i, A i : X.Subcomplex).obj U) :
    x.1 ∈ (A (iSupSubcomplexWitness A U x)).obj U :=
  Classical.choose_spec (by
    simpa only [Subfunctor.iSup_obj, Set.mem_iUnion] using x.2)

/-- Pairwise-compatible maps from subcomplexes glue over their union. -/
noncomputable def mapFromISupSubcomplex
    (f : (i : I) → (A i : SSet) ⟶ Y)
    (hcompat : ∀ i j,
      SSet.Subcomplex.homOfLE (inf_le_left : A i ⊓ A j ≤ A i) ≫ f i =
        SSet.Subcomplex.homOfLE (inf_le_right : A i ⊓ A j ≤ A j) ≫ f j) :
    ((⨆ i, A i : X.Subcomplex) : SSet) ⟶ Y where
  app U := ↾fun x ↦
    f (iSupSubcomplexWitness A U x) |>.app U
      ⟨x.1, iSupSubcomplexWitness_mem A U x⟩
  naturality := by
    intro U V α
    ext x
    let i := iSupSubcomplexWitness A U x
    let y := ((⨆ i, A i : X.Subcomplex) : SSet).map α x
    let j := iSupSubcomplexWitness A V y
    have hxi : x.1 ∈ (A i).obj U := iSupSubcomplexWitness_mem A U x
    have hyi : y.1 ∈ (A i).obj V := (A i).map α hxi
    have hyj : y.1 ∈ (A j).obj V := iSupSubcomplexWitness_mem A V y
    have hover := congrArg (fun q ↦ q.app V ⟨y.1, ⟨hyi, hyj⟩⟩) (hcompat i j)
    change (f i).app V ⟨y.1, hyi⟩ = (f j).app V ⟨y.1, hyj⟩ at hover
    change (f j).app V ⟨y.1, hyj⟩ = Y.map α ((f i).app U ⟨x.1, hxi⟩)
    rw [← hover]
    exact (f i).naturality_apply α ⟨x.1, hxi⟩

/-- The glued map restricts to each member of the compatible family. -/
@[reassoc]
theorem homOfLE_iSup_mapFromISupSubcomplex
    (f : (i : I) → (A i : SSet) ⟶ Y)
    (hcompat : ∀ i j,
      SSet.Subcomplex.homOfLE (inf_le_left : A i ⊓ A j ≤ A i) ≫ f i =
        SSet.Subcomplex.homOfLE (inf_le_right : A i ⊓ A j ≤ A j) ≫ f j)
    (i : I) :
    SSet.Subcomplex.homOfLE (le_iSup A i) ≫
      mapFromISupSubcomplex A f hcompat = f i := by
  ext U x
  let j := iSupSubcomplexWitness A U
    ((SSet.Subcomplex.homOfLE (le_iSup A i)).app U x)
  have hxj : x.1 ∈ (A j).obj U := iSupSubcomplexWitness_mem A U
    ((SSet.Subcomplex.homOfLE (le_iSup A i)).app U x)
  have hover := congrArg (fun q ↦ q.app U ⟨x.1, ⟨x.2, hxj⟩⟩) (hcompat i j)
  change (f j).app U ⟨x.1, hxj⟩ = (f i).app U x
  exact hover.symm

end SubcomplexUnionMap

/-- The compatible omitted-vertex horn faces glue over the entire avoiding-path union. -/
noncomputable def avoidingKnownPathMapOfInnerHorn
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (i j : Fin (n + 3)) :
    (avoidingKnownPathSubcomplex
      (ULift.up.{u, 0} i) (ULift.up.{u, 0} j) (ULift.up.{u, 0} k) : SSet) ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := by
  apply mapFromISupSubcomplex
    (fun l : {l : ULift.{u, 0} (Fin (n + 3)) //
      ULift.up i < l ∧ l < ULift.up j ∧ l ≠ ULift.up k} ↦
        avoidingPathSubcomplex (ULift.up i) (ULift.up j) l.1)
    (fun ⟨⟨l⟩, hil, hlj, hlk⟩ ↦
      avoidingPathMapOfInnerHornFace C σ hil hlj
        (fun h ↦ hlk (congrArg ULift.up h)))
  rintro ⟨⟨l⟩, hil, hlj, hlk⟩ ⟨⟨m⟩, him, hmj, hmk⟩
  exact avoidingPathMapOfInnerHornFace_pairwise
    C σ hil hlj (fun h ↦ hlk (congrArg ULift.up h))
      him hmj (fun h ↦ hmk (congrArg ULift.up h))

/-- The binary through/omitted decomposition of the known-path latching subcomplex. -/
theorem knownPathSubcomplex_eq_through_sup_avoidingKnown {J : Type u}
    [LinearOrder J] (i j k : J) :
    knownPathSubcomplex i j k =
      throughPathSubcomplex i j k ⊔ avoidingKnownPathSubcomplex i j k :=
  knownPathSubcomplex_eq_through_sup_avoiding i j k

/-- Include through paths into known paths. -/
def throughPathSubcomplexToKnown {J : Type u} [LinearOrder J] (i j k : J) :
    (throughPathSubcomplex i j k : SSet) ⟶ (knownPathSubcomplex i j k : SSet) :=
  SSet.Subcomplex.homOfLE (by
    intro U x hx
    exact Or.inl hx)

/-- Include the omitted-vertex union into known paths. -/
def avoidingKnownPathSubcomplexToKnown {J : Type u} [LinearOrder J] (i j k : J) :
    (avoidingKnownPathSubcomplex i j k : SSet) ⟶
      (knownPathSubcomplex i j k : SSet) :=
  SSet.Subcomplex.homOfLE (by
    intro U x hx
    simp only [avoidingKnownPathSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion] at hx
    obtain ⟨l, hl⟩ := hx
    exact Or.inr ⟨l.1, l.2.1.le, l.2.2.1.le, l.2.2.2, hl⟩)

/-- Glue the through and omitted-vertex maps. -/
noncomputable def knownPathMapOfCompatibleParts {J : Type u} [LinearOrder J]
    (i j k : J) {X : SSet.{u}}
    (throughMap : (throughPathSubcomplex i j k : SSet) ⟶ X)
    (avoidingMap : (avoidingKnownPathSubcomplex i j k : SSet) ⟶ X)
    (hcompat :
      SSet.Subcomplex.homOfLE (inf_le_left :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            throughPathSubcomplex i j k) ≫ throughMap =
        SSet.Subcomplex.homOfLE (inf_le_right :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            avoidingKnownPathSubcomplex i j k) ≫ avoidingMap) :
    (knownPathSubcomplex i j k : SSet) ⟶ X :=
  (SSet.Subcomplex.eqToIso
    (knownPathSubcomplex_eq_through_sup_avoidingKnown i j k)).hom ≫
      (SSet.Subcomplex.inf_inclusions_isPushout
        (throughPathSubcomplex i j k) (avoidingKnownPathSubcomplex i j k)).desc
          throughMap avoidingMap hcompat

@[reassoc]
theorem throughPathSubcomplexToKnown_knownPathMapOfCompatibleParts
    {J : Type u} [LinearOrder J] (i j k : J) {X : SSet.{u}}
    (throughMap : (throughPathSubcomplex i j k : SSet) ⟶ X)
    (avoidingMap : (avoidingKnownPathSubcomplex i j k : SSet) ⟶ X)
    (hcompat :
      SSet.Subcomplex.homOfLE (inf_le_left :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            throughPathSubcomplex i j k) ≫ throughMap =
        SSet.Subcomplex.homOfLE (inf_le_right :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            avoidingKnownPathSubcomplex i j k) ≫ avoidingMap) :
    throughPathSubcomplexToKnown i j k ≫
      knownPathMapOfCompatibleParts i j k throughMap avoidingMap hcompat = throughMap := by
  rw [knownPathMapOfCompatibleParts]
  have hinc : throughPathSubcomplexToKnown i j k ≫
      (SSet.Subcomplex.eqToIso
        (knownPathSubcomplex_eq_through_sup_avoidingKnown i j k)).hom =
      SSet.Subcomplex.homOfLE (le_sup_left : throughPathSubcomplex i j k ≤
        throughPathSubcomplex i j k ⊔ avoidingKnownPathSubcomplex i j k) := by
    rfl
  rw [← Category.assoc, hinc]
  exact (SSet.Subcomplex.inf_inclusions_isPushout
    (throughPathSubcomplex i j k) (avoidingKnownPathSubcomplex i j k)).inl_desc _ _ _

/-- Split every path of a through-vertex chain before the intermediate vertex. -/
def Chain.PathChain.beforeAt {J : Type u} [LinearOrder J] {r : ℕ} {i j k : J}
    (c : PathChain r i j) (hk : k ∈ c.first.I) : PathChain r i k where
  path a := beforePath (c.path a) (c.mem_of_mem_first hk a)
  monotone' {_a _b} hab _l hl := ⟨c.monotone' hab hl.1, hl.2⟩

/-- Split every path of a through-vertex chain after the intermediate vertex. -/
def Chain.PathChain.afterAt {J : Type u} [LinearOrder J] {r : ℕ} {i j k : J}
    (c : PathChain r i j) (hk : k ∈ c.first.I) : PathChain r k j where
  path a := afterPath (c.path a) (c.mem_of_mem_first hk a)
  monotone' {_a _b} hab _l hl := ⟨c.monotone' hab hl.1, hl.2⟩

@[simp]
theorem Chain.PathChain.join_beforeAt_afterAt {J : Type u} [LinearOrder J]
    {r : ℕ} {i j k : J} (c : PathChain r i j) (hk : k ∈ c.first.I)
    (a : Fin (r + 1)) :
    join ((c.beforeAt hk).path a) ((c.afterAt hk).path a) = c.path a :=
  beforePath_comp_afterPath (c.path a) (c.mem_of_mem_first hk a)

/-- Split a through-vertex path chain into the two shorter path chains. -/
noncomputable def throughPathSubcomplexToProduct {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (throughPathSubcomplex i.as j.as k.as : SSet) ⟶
      CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j) where
  app U := by
    obtain ⟨⟨r⟩⟩ := U
    exact ↾fun x ↦
      let c := ofNerveSimplex x.1
      ⟨(c.beforeAt x.2).toNerveSimplex, (c.afterAt x.2).toNerveSimplex⟩
  naturality := by
    rintro ⟨⟨r⟩⟩ ⟨⟨s⟩⟩ f
    ext x
    apply Prod.ext
    · exact CategoryTheory.Functor.ext
        (h_obj := fun _ ↦ rfl)
        (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
    · exact CategoryTheory.Functor.ext
        (h_obj := fun _ ↦ rfl)
        (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Compose shorter path chains into the through-path subcomplex. -/
def pathCompositionToThroughPathSubcomplex {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j)) ⟶
      (throughPathSubcomplex i.as j.as k.as : SSet) :=
  SSet.Subcomplex.lift (CategoryTheory.eComp SSet i k j) (by
    rintro U _ ⟨x, rfl⟩
    change k.as ∈ (ofNerveSimplex ((CategoryTheory.eComp SSet i k j).app U x)).first.I
    change k.as ∈ (((x.1.prod' x.2) ⋙
      CategoryTheory.SimplicialThickening.compFunctor i k j).obj 0).I
    exact Or.inl (x.1.obj 0).right)

/-- Composition followed by path splitting is the identity. -/
theorem pathCompositionToThrough_split {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    pathCompositionToThroughPathSubcomplex i k j ≫
        throughPathSubcomplexToProduct i k j = 𝟙 _ := by
  ext U x
  case h_fst =>
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ congrArg Prod.fst
        (splitCritical_joinCritical (x.1.obj a, x.2.obj a)))
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
  case h_snd =>
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ congrArg Prod.snd
        (splitCritical_joinCritical (x.1.obj a, x.2.obj a)))
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Splitting followed by composition is the identity on the through-vertex subcomplex. -/
theorem split_pathCompositionToThrough {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    throughPathSubcomplexToProduct i k j ≫
      pathCompositionToThroughPathSubcomplex i k j = 𝟙 _ := by
  ext U x
  apply Subtype.ext
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ (ofNerveSimplex x.1).join_beforeAt_afterAt x.2 a)
    (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- The through-vertex latching piece is exactly the product of the two shorter path nerves. -/
noncomputable def throughPathSubcomplexProductIso {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j)) ≅
      (throughPathSubcomplex i.as j.as k.as : SSet) where
  hom := pathCompositionToThroughPathSubcomplex i k j
  inv := throughPathSubcomplexToProduct i k j
  hom_inv_id := pathCompositionToThrough_split i k j
  inv_hom_id := split_pathCompositionToThrough i k j

@[reassoc (attr := simp)]
theorem pathCompositionToThrough_toKnown {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    pathCompositionToThroughPathSubcomplex i k j ≫
      throughPathSubcomplexToKnown i.as j.as k.as =
        pathCompositionToKnownPathSubcomplex i k j :=
  rfl

/-- Shorter interval maps force the map on through paths. -/
noncomputable def forcedThroughPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j)) :
    (throughPathSubcomplex i.as j.as k.as : SSet) ⟶ (obj i ⟶[SSet] obj j) :=
  (throughPathSubcomplexProductIso i k j).inv ≫
    (leftMap ⊗ₘ rightMap) ≫ CategoryTheory.eComp SSet (obj i) (obj k) (obj j)

@[reassoc]
theorem pathCompositionToThrough_forcedThroughPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j)) :
    pathCompositionToThroughPathSubcomplex i k j ≫
      forcedThroughPathMap C obj i k j leftMap rightMap =
        (leftMap ⊗ₘ rightMap) ≫
          CategoryTheory.eComp SSet (obj i) (obj k) (obj j) := by
  rw [forcedThroughPathMap, ← Category.assoc]
  change (((throughPathSubcomplexProductIso i k j).hom ≫
      (throughPathSubcomplexProductIso i k j).inv) ≫ _) = _
  rw [(throughPathSubcomplexProductIso i k j).hom_inv_id, Category.id_comp]

/-- A compatible latching map agrees with shorter-interval composition. -/
structure CompatibleKnownPathLatchingMap (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j)) where
  map : (knownPathSubcomplex i.as j.as k.as : SSet) ⟶ (obj i ⟶[SSet] obj j)
  map_comp :
    pathCompositionToKnownPathSubcomplex i k j ≫ map =
      (leftMap ⊗ₘ rightMap) ≫ CategoryTheory.eComp SSet (obj i) (obj k) (obj j)

/-- An overlap equation glues an omitted-vertex map into a compatible latching map. -/
noncomputable def CompatibleKnownPathLatchingMap.ofAvoidingMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j))
    (avoidingMap : (avoidingKnownPathSubcomplex i.as j.as k.as : SSet) ⟶
      (obj i ⟶[SSet] obj j))
    (hcompat :
      SSet.Subcomplex.homOfLE (inf_le_left :
          throughPathSubcomplex i.as j.as k.as ⊓
              avoidingKnownPathSubcomplex i.as j.as k.as ≤
            throughPathSubcomplex i.as j.as k.as) ≫
            forcedThroughPathMap C obj i k j leftMap rightMap =
        SSet.Subcomplex.homOfLE (inf_le_right :
          throughPathSubcomplex i.as j.as k.as ⊓
              avoidingKnownPathSubcomplex i.as j.as k.as ≤
            avoidingKnownPathSubcomplex i.as j.as k.as) ≫ avoidingMap) :
    CompatibleKnownPathLatchingMap C obj i k j leftMap rightMap where
  map := knownPathMapOfCompatibleParts i.as j.as k.as
    (forcedThroughPathMap C obj i k j leftMap rightMap) avoidingMap hcompat
  map_comp := by
    rw [← pathCompositionToThrough_toKnown i k j, Category.assoc,
      throughPathSubcomplexToKnown_knownPathMapOfCompatibleParts]
    exact pathCompositionToThrough_forcedThroughPathMap
      C obj i k j leftMap rightMap

/-- Kan extension preserves the forced composition equation. -/
theorem exists_pathMap_extension_preserving_comp
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J] [Finite J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (hik : i.as < k.as) (hkj : k.as < j.as)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j))
    (latching : CompatibleKnownPathLatchingMap C obj i k j leftMap rightMap)
    [SSet.KanComplex (obj i ⟶[SSet] obj j)] :
    ∃ map : CategoryTheory.nerve (i ⟶ j) ⟶ (obj i ⟶[SSet] obj j),
      (knownPathSubcomplex i.as j.as k.as).ι ≫ map = latching.map ∧
        CategoryTheory.eComp SSet i k j ≫ map =
          (leftMap ⊗ₘ rightMap) ≫
            CategoryTheory.eComp SSet (obj i) (obj k) (obj j) := by
  obtain ⟨map, hmap⟩ := exists_knownPathSubcomplex_extension_of_kan_of_fintype
    hik hkj latching.map
  refine ⟨map, hmap, ?_⟩
  rw [← pathCompositionToKnownPathSubcomplex_ι i k j, Category.assoc, hmap]
  exact latching.map_comp

end LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
