import LeanLCAExactChallenge.Infinity.CoherentNerveKanExtension
import Mathlib.Order.Fin.SuccAboveOrderIso

/-!
# Compatibility of coherent-nerve path latching maps

Composition factors through the known-path latching subcomplex.

The through-vertex piece is the product of the two shorter path nerves.

Kan extension preserves the resulting enriched-composition equation.

Pairwise omitted-face overlap, full horn-face composition, and through/omitted-union
compatibility assemble the known-path latching map for every interval spanning the missing vertex.
-/

set_option autoImplicit false

noncomputable section

universe u v

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

@[simp]
theorem deleteFinVertex_succAbove {n : ℕ} (l : Fin (n + 2)) (a : Fin (n + 1)) :
    deleteFinVertex l (l.succAbove a) (Fin.succAbove_ne l a) = a := by
  apply l.succAbove_right_injective
  rw [succAbove_deleteFinVertex]

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

theorem insertPathVertex_not_mem {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (p : CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u, 0} (deleteFinVertex l i hli))
      (ULift.up.{u, 0} (deleteFinVertex l j hlj))) :
    ULift.up.{u, 0} l ∉ (insertPathVertex l hli hlj p).I := by
  rintro ⟨q, _, hq⟩
  exact Fin.ne_succAbove l q.down (ULift.up_injective hq)

theorem delete_insertPathVertex {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l)
    (p : CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u, 0} (deleteFinVertex l i hli))
      (ULift.up.{u, 0} (deleteFinVertex l j hlj))) :
    deletePathVertex (insertPathVertex l hli hlj p) l hli hlj = p := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  ext q
  constructor
  · rintro ⟨r, hr, hq⟩
    have hqr : q = r := by
      apply ULift.ext
      exact l.succAbove_right_injective (ULift.up_injective hq)
    exact hqr ▸ hr
  · intro hq
    exact ⟨q, hq, rfl⟩

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

/-- Enriched composition is natural under propositional transport of all three objects. -/
theorem eComp_eqToHom_of_obj_eq
    {D : Type u} [Category.{u} D] [CategoryTheory.SimplicialCategory D]
    {a b c a' b' c' : D} (ha : a = a') (hb : b = b') (hc : c = c') :
    CategoryTheory.eComp SSet a b c ≫
        eqToHom (congrArg₂ (fun A C : D ↦ A ⟶[SSet] C) ha hc) =
      (eqToHom (congrArg₂ (fun A B : D ↦ A ⟶[SSet] B) ha hb) ⊗ₘ
          eqToHom (congrArg₂ (fun B C : D ↦ B ⟶[SSet] C) hb hc)) ≫
        CategoryTheory.eComp SSet a' b' c' := by
  subst a'
  subst b'
  subst c'
  simp

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

@[reassoc (attr := simp)]
theorem insertVertexPathNerveMap_deleteVertexPathNerveMap
    {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    insertVertexPathNerveMap l hli hlj ≫
        deleteVertexPathNerveMap l hli hlj = 𝟙 _ := by
  apply CategoryTheory.NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ delete_insertPathVertex l hli hlj (x.obj a))
    (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

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

/-- Vertex deletion commutes with composition of thick paths. -/
theorem pathComposition_deleteVertexPathNerveMap
    {n : ℕ} {i k j l : Fin (n + 2)}
    (hil : i ≠ l) (hkl : k ≠ l) (hjl : j ≠ l) :
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} k))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} j)) ≫
      deleteVertexPathNerveMap l hil hjl =
    (deleteVertexPathNerveMap l hil hkl ⊗ₘ
        deleteVertexPathNerveMap l hkl hjl) ≫
      CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up.{u, 0} (deleteFinVertex l i hil)))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up.{u, 0} (deleteFinVertex l k hkl)))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up.{u, 0} (deleteFinVertex l j hjl))) := by
  ext U x a q
  rfl

/-- Vertex deletion sends the enriched identity path to the enriched identity path. -/
theorem eId_deleteVertexPathNerveMap
    {n : ℕ} {i l : Fin (n + 2)} (hil : i ≠ l) :
    CategoryTheory.eId SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i)) ≫
      deleteVertexPathNerveMap l hil hil =
    CategoryTheory.eId SSet
        (CategoryTheory.SimplicialThickening.mk
        (ULift.up.{u, 0} (deleteFinVertex l i hil))) := by
  exact (Path.homNerveThickPathSelfSubsingleton (𝟙_ SSet)
    (ULift.up.{u, 0} (deleteFinVertex l i hil))).elim _ _

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

noncomputable def insertVertexAvoidingPathMap {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} (deleteFinVertex l i hli))
          (ULift.up.{u, 0} (deleteFinVertex l j hlj))) ⟶
      (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).toSSet :=
  SSet.Subcomplex.lift (insertVertexPathNerveMap l hli hlj) (by
    rintro U _ ⟨x, rfl⟩
    exact insertPathVertex_not_mem l hli hlj (ofNerveSimplex x).last)

@[reassoc (attr := simp)]
theorem insertVertexAvoidingPathMap_ι {n : ℕ} {i j : Fin (n + 2)}
    (l : Fin (n + 2)) (hli : i ≠ l) (hlj : j ≠ l) :
    insertVertexAvoidingPathMap l hli hlj ≫
        (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).ι =
      insertVertexPathNerveMap l hli hlj :=
  rfl

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
    (hlm : l < m) (hil : i ≠ l) (hjl : j ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) (hlk : l ≠ k) (hmk : m ≠ k) :
    HEq
      ((avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        (deleteVertexPathNerveMap l hil hjl ≫
          (innerHornFaceFunctor C σ hlk).map
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex l i hil)))
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex l j hjl)))))
      ((avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        (deleteVertexPathNerveMap m him hjm ≫
          (innerHornFaceFunctor C σ hmk).map
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex m i him)))
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (deleteFinVertex m j hjm))))) := by
  let D := avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} l) ⊓
    avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} m)
  let il : i ≠ l := hil
  let jl : j ≠ l := hjl
  let im : i ≠ m := him
  let jm : j ≠ m := hjm
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

/-- Every full horn-face path-map preserves enriched composition. -/
theorem pathMapOfInnerHornFace_map_comp
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i r j l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hil : i ≠ l) (hrl : r ≠ l) (hjl : j ≠ l) (hlm : l ≠ missing) :
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} r))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} j)) ≫
      pathMapOfInnerHornFace C σ hil hjl hlm =
    (pathMapOfInnerHornFace C σ hil hrl hlm ⊗ₘ
        pathMapOfInnerHornFace C σ hrl hjl hlm) ≫
      CategoryTheory.eComp SSet
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up r)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := by
  let F := innerHornFaceFunctor C σ hlm
  have hi : F.obj (CategoryTheory.SimplicialThickening.mk
      (ULift.up (deleteFinVertex l i hil))) =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up i)) := by
    simpa [F] using innerHornFaceFunctor_obj C σ hlm
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (deleteFinVertex l i hil)))
  have hr : F.obj (CategoryTheory.SimplicialThickening.mk
      (ULift.up (deleteFinVertex l r hrl))) =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up r)) := by
    simpa [F] using innerHornFaceFunctor_obj C σ hlm
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (deleteFinVertex l r hrl)))
  have hj : F.obj (CategoryTheory.SimplicialThickening.mk
      (ULift.up (deleteFinVertex l j hjl))) =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up j)) := by
    simpa [F] using innerHornFaceFunctor_obj C σ hlm
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (deleteFinVertex l j hjl)))
  simp only [pathMapOfInnerHornFace]
  rw [← Category.assoc,
    pathComposition_deleteVertexPathNerveMap hil hrl hjl]
  slice_lhs 2 3 => rw [(innerHornFaceFunctor C σ hlm).map_comp]
  simp only [Category.assoc, tensorHom_comp_tensorHom_assoc]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [eComp_eqToHom_of_obj_eq hi hr hj]
  slice_lhs 1 2 => rw [tensorHom_comp_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rfl

/-- Enriched identities are compatible with transport along an object equality. -/
theorem eId_eqToHom_of_obj_eq
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {X Y : C} (h : X = Y) :
    CategoryTheory.eId SSet X ≫
        eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B) h h) =
      CategoryTheory.eId SSet Y := by
  subst Y
  simp

/-- Every full horn-face path-map preserves the enriched identity. -/
theorem pathMapOfInnerHornFace_map_id
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hil : i ≠ l) (hlm : l ≠ missing) :
    CategoryTheory.eId SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i)) ≫
      pathMapOfInnerHornFace C σ hil hil hlm =
    CategoryTheory.eId SSet
      (innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up i))) := by
  let F := innerHornFaceFunctor C σ hlm
  have hi : F.obj (CategoryTheory.SimplicialThickening.mk
      (ULift.up (deleteFinVertex l i hil))) =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up i)) := by
    simpa [F] using innerHornFaceFunctor_obj C σ hlm
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (deleteFinVertex l i hil)))
  simp only [pathMapOfInnerHornFace]
  rw [← Category.assoc, eId_deleteVertexPathNerveMap hil]
  slice_lhs 1 2 => rw [(innerHornFaceFunctor C σ hlm).map_id]
  exact eId_eqToHom_of_obj_eq C hi

/-- Two ordered endpoint-distinct horn faces induce equal full path-maps on paths omitting both
face vertices. -/
theorem pathMapOfInnerHornFace_pairwise_on_inf_of_lt
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlm : l < m) (hil : i ≠ l) (hjl : j ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) (hlk : l ≠ k) (hmk : m ≠ k) :
    (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        pathMapOfInnerHornFace C σ hil hjl hlk =
      (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ⊓
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        pathMapOfInnerHornFace C σ him hjm hmk := by
  apply eq_of_heq
  simp only [pathMapOfInnerHornFace]
  simp only [← Category.assoc]
  refine (comp_eqToHom_heq (C := SSet) _ _).trans ?_
  refine HEq.trans ?_ (comp_eqToHom_heq (C := SSet) _ _).symm
  simpa only [Category.assoc] using
    (innerHornFaceFunctor_avoiding_pairwise_core_heq
      C σ hlm hil hjl him hjm hlk hmk)

/-- Every path in an interval omits a vertex strictly to the right of the interval. -/
theorem avoidingPathSubcomplex_le_avoiding_of_right
    {J : Type u} [LinearOrder J] {i j l m : J} (hjm : j < m) :
    avoidingPathSubcomplex i j l ≤ avoidingPathSubcomplex i j m := by
  intro U x _ hm
  exact (not_le_of_gt hjm) ((ofNerveSimplex x).last.le_right m hm)

/-- Every path in an interval omits a vertex strictly to the left of the interval. -/
theorem avoidingPathSubcomplex_le_avoiding_of_left
    {J : Type u} [LinearOrder J] {i j l m : J} (hmi : m < i) :
    avoidingPathSubcomplex i j l ≤ avoidingPathSubcomplex i j m := by
  intro U x _ hm
  exact (not_le_of_gt hmi) ((ofNerveSimplex x).last.left_le m hm)

/-- Every path omits a vertex strictly to the right of its interval. -/
theorem avoidingPathSubcomplex_eq_top_of_right
    {J : Type u} [LinearOrder J] {i j l : J} (hjl : j < l) :
    avoidingPathSubcomplex i j l = ⊤ := by
  apply le_antisymm le_top
  intro U x _ hl
  exact (not_le_of_gt hjl) ((ofNerveSimplex x).last.le_right l hl)

/-- Every path omits a vertex strictly to the left of its interval. -/
theorem avoidingPathSubcomplex_eq_top_of_left
    {J : Type u} [LinearOrder J] {i j l : J} (hli : l < i) :
    avoidingPathSubcomplex i j l = ⊤ := by
  apply le_antisymm le_top
  intro U x _ hl
  exact (not_le_of_gt hli) ((ofNerveSimplex x).last.left_le l hl)

/-- An available horn face whose deleted vertex lies outside an interval. -/
structure OutsideAvailableFace {n : ℕ}
    (missing i j : Fin (n + 3)) where
  face : Fin (n + 3)
  face_ne_missing : face ≠ missing
  face_ne_left : face ≠ i
  face_ne_right : face ≠ j
  outside : face < i ∨ j < face

/-- Every proper ordered interval has an available outer face outside it. -/
noncomputable def outsideAvailableFace {n : ℕ}
    {missing i j : Fin (n + 3)}
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hij : i ≤ j) (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2))) :
    OutsideAvailableFace missing i j := by
  by_cases hi : i = 0
  · refine
      { face := Fin.last (n + 2)
        face_ne_missing := fun h ↦ hkLast h.symm
        face_ne_left := ?_
        face_ne_right := ?_
        outside := Or.inr ?_ }
    · rw [hi]
      exact ne_of_gt (Fin.last_pos)
    · intro hj
      exact hproper ⟨hi, hj.symm⟩
    · apply Fin.lt_last_iff_ne_last.mpr
      intro hj
      exact hproper ⟨hi, hj⟩
  · refine
      { face := 0
        face_ne_missing := hkZero.symm
        face_ne_left := fun h ↦ hi h.symm
        face_ne_right := ?_
        outside := Or.inl (Fin.pos_iff_ne_zero.mpr hi) }
    intro hj
    apply hi
    apply Fin.le_zero_iff.mp
    simpa [hj] using hij

/-- A proper ordered interval receives its full path map from an available outer face. -/
noncomputable def properPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hij : i ≤ j) (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2))) :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)) ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) :=
  let l := outsideAvailableFace hkZero hkLast hij hproper
  pathMapOfInnerHornFace C σ
    (fun h ↦ l.face_ne_left h.symm)
    (fun h ↦ l.face_ne_right h.symm)
    l.face_ne_missing

/-- Every path omits a vertex outside its interval. -/
theorem pathChain_not_mem_last_of_outside
    {J : Type u} [LinearOrder J] {r : ℕ} {i j l : J}
    (c : PathChain r i j) (h : l < i ∨ j < l) : l ∉ c.last.I := by
  intro hl
  rcases h with hli | hjl
  · exact (not_le_of_gt hli) (c.last.left_le l hl)
  · exact (not_le_of_gt hjl) (c.last.le_right l hl)

/-- The proper path map agrees with every available face outside the interval. -/
theorem properPathMap_eq_pathMapOf_outsideFace
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i j l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hij : i ≤ j) (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2)))
    (hlout : l < i ∨ j < l) (hlk : l ≠ missing) :
    properPathMap C σ hkZero hkLast hij hproper =
      pathMapOfInnerHornFace C σ
        (by rcases hlout with h | h <;> omega)
        (by rcases hlout with h | h <;> omega) hlk := by
  let q := outsideAvailableFace hkZero hkLast hij hproper
  change pathMapOfInnerHornFace C σ
      (fun h ↦ q.face_ne_left h.symm)
      (fun h ↦ q.face_ne_right h.symm) q.face_ne_missing = _
  rcases lt_trichotomy q.face l with hql | hql | hlq
  · ext U x
    have hxq := pathChain_not_mem_last_of_outside
      (l := ULift.up.{u, 0} q.face) (ofNerveSimplex x) (by
        change q.face < i ∨ j < q.face
        exact q.outside)
    have hxl := pathChain_not_mem_last_of_outside
      (l := ULift.up.{u, 0} l) (ofNerveSimplex x) (by
        change l < i ∨ j < l
        exact hlout)
    have h := congrArg (fun f ↦ f.app U ⟨x, ⟨hxq, hxl⟩⟩)
      (pathMapOfInnerHornFace_pairwise_on_inf_of_lt C σ hql
        (fun h ↦ q.face_ne_left h.symm)
        (fun h ↦ q.face_ne_right h.symm)
        (by rcases hlout with h | h <;> omega)
        (by rcases hlout with h | h <;> omega)
        q.face_ne_missing hlk)
    exact h
  · subst l
    rfl
  · ext U x
    have hxl := pathChain_not_mem_last_of_outside
      (l := ULift.up.{u, 0} l) (ofNerveSimplex x) (by
        change l < i ∨ j < l
        exact hlout)
    have hxq := pathChain_not_mem_last_of_outside
      (l := ULift.up.{u, 0} q.face) (ofNerveSimplex x) (by
        change q.face < i ∨ j < q.face
        exact q.outside)
    have h := congrArg (fun f ↦ f.app U ⟨x, ⟨hxl, hxq⟩⟩)
      (pathMapOfInnerHornFace_pairwise_on_inf_of_lt C σ hlq
        (by rcases hlout with h | h <;> omega)
        (by rcases hlout with h | h <;> omega)
        (fun h ↦ q.face_ne_left h.symm)
        (fun h ↦ q.face_ne_right h.symm)
        hlk q.face_ne_missing)
    exact h.symm

/-- If every path omitting the lower face vertex also omits the higher one, the two full face
path-maps agree on the lower avoiding subcomplex. -/
theorem pathMapOfInnerHornFace_pairwise_on_avoiding_of_lt
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlm : l < m) (hil : i ≠ l) (hjl : j ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) (hlk : l ≠ k) (hmk : m ≠ k)
    (hle : avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} l) ≤
        avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
          (ULift.up.{u, 0} m)) :
    (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).ι ≫
        pathMapOfInnerHornFace C σ hil hjl hlk =
      (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).ι ≫
        pathMapOfInnerHornFace C σ him hjm hmk := by
  ext U x
  have h := congrArg (fun q ↦ q.app U
      ⟨x.1, ⟨x.2, hle U x.2⟩⟩)
    (pathMapOfInnerHornFace_pairwise_on_inf_of_lt
      C σ hlm hil hjl him hjm hlk hmk)
  exact h

/-- The symmetric restriction form when every path omitting the higher face vertex also omits
the lower one. -/
theorem pathMapOfInnerHornFace_pairwise_on_higher_avoiding_of_lt
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j l m : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlm : l < m) (hil : i ≠ l) (hjl : j ≠ l)
    (him : i ≠ m) (hjm : j ≠ m) (hlk : l ≠ k) (hmk : m ≠ k)
    (hle : avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
      (ULift.up.{u, 0} m) ≤
        avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)
          (ULift.up.{u, 0} l)) :
    (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        pathMapOfInnerHornFace C σ hil hjl hlk =
      (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up m)).ι ≫
        pathMapOfInnerHornFace C σ him hjm hmk := by
  ext U x
  have h := congrArg (fun q ↦ q.app U
      ⟨x.1, ⟨hle U x.2, x.2⟩⟩)
    (pathMapOfInnerHornFace_pairwise_on_inf_of_lt
      C σ hlm hil hjl him hjm hlk hmk)
  exact h

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

/-- Proper interval maps recover every available internal horn face. -/
theorem avoidingPathSubcomplex_properPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i l j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hij : i ≤ j) (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2)))
    (hil : i < l) (hlj : l < j) (hlk : l ≠ missing) :
    (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).ι ≫
        properPathMap C σ hkZero hkLast hij hproper =
      avoidingPathMapOfInnerHornFace C σ hil hlj hlk := by
  rw [← avoidingPathSubcomplex_pathMapOfInnerHornFace C σ hil hlj hlk]
  let q := outsideAvailableFace hkZero hkLast hij hproper
  change (avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)).ι ≫
      pathMapOfInnerHornFace C σ
        (fun h ↦ q.face_ne_left h.symm)
        (fun h ↦ q.face_ne_right h.symm) q.face_ne_missing = _
  rcases q.outside with hqi | hjq
  · exact pathMapOfInnerHornFace_pairwise_on_higher_avoiding_of_lt
      C σ (lt_trans hqi hil)
      (fun h ↦ q.face_ne_left h.symm)
      (fun h ↦ q.face_ne_right h.symm)
      (ne_of_lt hil) (ne_of_gt hlj) q.face_ne_missing hlk (by
        rw [avoidingPathSubcomplex_eq_top_of_left
          (show ULift.up.{u, 0} q.face < ULift.up i from hqi)]
        exact le_top)
  · exact (pathMapOfInnerHornFace_pairwise_on_avoiding_of_lt
      C σ (lt_trans hlj hjq)
      (ne_of_lt hil) (ne_of_gt hlj)
      (fun h ↦ q.face_ne_left h.symm)
      (fun h ↦ q.face_ne_right h.symm) hlk q.face_ne_missing (by
        rw [avoidingPathSubcomplex_eq_top_of_right
          (show ULift.up.{u, 0} j < ULift.up q.face from hjq)]
        exact le_top)).symm

/-- A subinterval with the same left endpoint remains proper. -/
theorem proper_left_subinterval {n : ℕ} {i r j : Fin (n + 3)}
    (hrj : r ≤ j)
    (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2))) :
    ¬ (i = 0 ∧ r = Fin.last (n + 2)) := by
  rintro ⟨hi, hr⟩
  apply hproper
  refine ⟨hi, ?_⟩
  apply le_antisymm (Fin.le_last j)
  simpa [hr] using hrj

/-- A subinterval with the same right endpoint remains proper. -/
theorem proper_right_subinterval {n : ℕ} {i r j : Fin (n + 3)}
    (hir : i ≤ r)
    (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2))) :
    ¬ (r = 0 ∧ j = Fin.last (n + 2)) := by
  rintro ⟨hr, hj⟩
  apply hproper
  refine ⟨?_, hj⟩
  apply Fin.le_zero_iff.mp
  simpa [hr] using hir

/-- Proper interval maps preserve every ordered enriched composition. -/
theorem properPathMap_map_comp
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i r j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hir : i ≤ r) (hrj : r ≤ j)
    (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2))) :
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} r))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} j)) ≫
      properPathMap C σ hkZero hkLast (hir.trans hrj) hproper =
    (properPathMap C σ hkZero hkLast hir
          (proper_left_subinterval hrj hproper) ⊗ₘ
        properPathMap C σ hkZero hkLast hrj
          (proper_right_subinterval hir hproper)) ≫
      CategoryTheory.eComp SSet
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up r)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := by
  let q := outsideAvailableFace hkZero hkLast (hir.trans hrj) hproper
  have hqirj : q.face < i ∨ j < q.face := q.outside
  have hqir : q.face < i ∨ r < q.face := by omega
  have hqrj : q.face < r ∨ j < q.face := by omega
  rw [properPathMap_eq_pathMapOf_outsideFace C σ hkZero hkLast
      (hir.trans hrj) hproper hqirj q.face_ne_missing,
    properPathMap_eq_pathMapOf_outsideFace C σ hkZero hkLast
      hir (proper_left_subinterval hrj hproper) hqir q.face_ne_missing,
    properPathMap_eq_pathMapOf_outsideFace C σ hkZero hkLast
      hrj (proper_right_subinterval hir hproper) hqrj q.face_ne_missing]
  exact pathMapOfInnerHornFace_map_comp C σ
    (by omega) (by omega) (by omega) q.face_ne_missing

/-- Proper interval maps preserve the enriched identity. -/
theorem properPathMap_map_id
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hproper : ¬ (i = 0 ∧ i = Fin.last (n + 2))) :
    CategoryTheory.eId SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i)) ≫
      properPathMap C σ hkZero hkLast le_rfl hproper =
    CategoryTheory.eId SSet
      (innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up i))) := by
  exact pathMapOfInnerHornFace_map_id C σ
    (fun h ↦ (outsideAvailableFace hkZero hkLast le_rfl hproper).face_ne_left h.symm)
    (outsideAvailableFace hkZero hkLast le_rfl hproper).face_ne_missing

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

/-- On paths omitting an internal vertex to the left of the missing vertex, the canonical left
interval map agrees with that internal horn face. -/
theorem avoidingPathSubcomplex_innerHornLeftPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkLast : k ≠ Fin.last (n + 2)) (hil : i < l) (hlk : l < k) :
    (avoidingPathSubcomplex (ULift.up i) (ULift.up k) (ULift.up l)).ι ≫
        innerHornLeftPathMap C σ hkLast (lt_trans hil hlk) =
      avoidingPathMapOfInnerHornFace C σ hil hlk (ne_of_lt hlk) := by
  rw [← avoidingPathSubcomplex_pathMapOfInnerHornFace]
  change (avoidingPathSubcomplex (ULift.up i) (ULift.up k) (ULift.up l)).ι ≫
      pathMapOfInnerHornFace C σ
        (ne_of_lt (lt_trans (lt_trans hil hlk)
          (Fin.lt_last_iff_ne_last.mpr hkLast))) hkLast hkLast.symm =
    (avoidingPathSubcomplex (ULift.up i) (ULift.up k) (ULift.up l)).ι ≫
      pathMapOfInnerHornFace C σ (ne_of_lt hil) (ne_of_gt hlk) (ne_of_lt hlk)
  exact (pathMapOfInnerHornFace_pairwise_on_avoiding_of_lt
    C σ (lt_trans hlk (Fin.lt_last_iff_ne_last.mpr hkLast))
    (ne_of_lt hil) (ne_of_gt hlk)
    (ne_of_lt (lt_trans (lt_trans hil hlk)
      (Fin.lt_last_iff_ne_last.mpr hkLast))) hkLast
    (ne_of_lt hlk) hkLast.symm
    (avoidingPathSubcomplex_le_avoiding_of_right
      (show ULift.up.{u, 0} k < ULift.up (Fin.last (n + 2)) from
        Fin.lt_last_iff_ne_last.mpr hkLast))).symm

/-- On paths omitting an internal vertex to the right of the missing vertex, the canonical right
interval map agrees with that internal horn face. -/
theorem avoidingPathSubcomplex_innerHornRightPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k l j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkl : k < l) (hlj : l < j) :
    (avoidingPathSubcomplex (ULift.up k) (ULift.up j) (ULift.up l)).ι ≫
        innerHornRightPathMap C σ hkZero (lt_trans hkl hlj) =
      avoidingPathMapOfInnerHornFace C σ hkl hlj (ne_of_gt hkl) := by
  rw [← avoidingPathSubcomplex_pathMapOfInnerHornFace]
  change (avoidingPathSubcomplex (ULift.up k) (ULift.up j) (ULift.up l)).ι ≫
      pathMapOfInnerHornFace C σ hkZero
        (ne_of_gt (lt_trans (Fin.pos_iff_ne_zero.mpr hkZero) (lt_trans hkl hlj)))
        hkZero.symm =
    (avoidingPathSubcomplex (ULift.up k) (ULift.up j) (ULift.up l)).ι ≫
      pathMapOfInnerHornFace C σ (ne_of_lt hkl) (ne_of_gt hlj) (ne_of_gt hkl)
  exact pathMapOfInnerHornFace_pairwise_on_higher_avoiding_of_lt
    C σ (lt_trans (Fin.pos_iff_ne_zero.mpr hkZero) hkl)
    hkZero
    (ne_of_gt (lt_trans (Fin.pos_iff_ne_zero.mpr hkZero) (lt_trans hkl hlj)))
    (ne_of_lt hkl) (ne_of_gt hlj) hkZero.symm (ne_of_gt hkl)
    (avoidingPathSubcomplex_le_avoiding_of_left
      (show ULift.up.{u, 0} 0 < ULift.up k from Fin.pos_iff_ne_zero.mpr hkZero))

/-- A face vertex to the right of a left interval supplies the same full interval map as the
canonical last face. -/
theorem innerHornLeftPathMap_eq_pathMapOfInnerHornFace_of_right
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkLast : k ≠ Fin.last (n + 2)) (hik : i < k) (hkl : k < l)
    (hlLast : l < Fin.last (n + 2)) :
    innerHornLeftPathMap C σ hkLast hik =
      pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hik hkl))
        (ne_of_lt hkl) (ne_of_gt hkl) := by
  ext U x
  have hx : ULift.up.{u, 0} l ∉ (ofNerveSimplex x).last.I := by
    intro hl
    exact (not_le_of_gt hkl) ((ofNerveSimplex x).last.le_right _ hl)
  have h := congrArg (fun q ↦ q.app U ⟨x, hx⟩)
    (pathMapOfInnerHornFace_pairwise_on_avoiding_of_lt
      C σ hlLast
      (ne_of_lt (lt_trans hik hkl)) (ne_of_lt hkl)
      (ne_of_lt (lt_trans hik (lt_trans hkl hlLast)))
      (ne_of_lt (lt_trans hkl hlLast)) (ne_of_gt hkl) hkLast.symm
      (avoidingPathSubcomplex_le_avoiding_of_right
        (show ULift.up.{u, 0} k < ULift.up (Fin.last (n + 2)) from
          Fin.lt_last_iff_ne_last.mpr hkLast)))
  exact h.symm

/-- A face vertex to the left of a right interval supplies the same full interval map as the
canonical zero face. -/
theorem innerHornRightPathMap_eq_pathMapOfInnerHornFace_of_left
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k l j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hZeroL : 0 < l) (hlk : l < k) (hkj : k < j) :
    innerHornRightPathMap C σ hkZero hkj =
      pathMapOfInnerHornFace C σ (ne_of_gt hlk)
        (ne_of_gt (lt_trans hlk hkj)) (ne_of_lt hlk) := by
  ext U x
  have hx : ULift.up.{u, 0} l ∉ (ofNerveSimplex x).last.I := by
    intro hl
    exact (not_le_of_gt hlk) ((ofNerveSimplex x).last.left_le _ hl)
  have h := congrArg (fun q ↦ q.app U ⟨x, hx⟩)
    (pathMapOfInnerHornFace_pairwise_on_higher_avoiding_of_lt
      C σ hZeroL hkZero
      (ne_of_gt (lt_trans (Fin.pos_iff_ne_zero.mpr hkZero) hkj))
      (ne_of_gt hlk) (ne_of_gt (lt_trans hlk hkj)) hkZero.symm (ne_of_lt hlk)
      (avoidingPathSubcomplex_le_avoiding_of_left
        (show ULift.up.{u, 0} 0 < ULift.up k from Fin.pos_iff_ne_zero.mpr hkZero)))
  exact h

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
    C σ hlm (ne_of_lt hil) (ne_of_gt (lt_trans hlm hmj))
      (ne_of_lt (lt_trans hil hlm)) (ne_of_gt hmj) hlk hmk

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

/-- Full path latching is the union of every through piece and every available face piece. -/
theorem fullyKnownPathSubcomplex_eq_through_sup_avoiding {J : Type u} [LinearOrder J]
    (i j k : J) :
    fullyKnownPathSubcomplex i j k =
      (⨆ m : InteriorVertex i j, throughPathSubcomplex i j m.1) ⊔
        ⨆ l : {l : J // i < l ∧ l < j ∧ l ≠ k},
          avoidingPathSubcomplex i j l.1 := by
  ext U x
  change (ofNerveSimplex x).FullyKnownAt k ↔ _
  constructor
  · rintro (⟨m, hm⟩ | ⟨l, hlk, hl⟩)
    · apply Or.inl
      simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
      exact ⟨m, hm⟩
    · apply Or.inr
      simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
      exact ⟨⟨l.1, l.2.1, l.2.2, hlk⟩, hl⟩
  · intro h
    rcases h with hthrough | havoid
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at hthrough
      obtain ⟨m, hm⟩ := hthrough
      exact Or.inl ⟨m, hm⟩
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at havoid
      obtain ⟨l, hl⟩ := havoid
      exact Or.inr ⟨⟨l.1, l.2.1, l.2.2.1⟩, l.2.2.2, hl⟩

/-- The union of all known-path pieces obtained by omitting a nonmissing vertex. -/
def avoidingKnownPathSubcomplex {J : Type u} [LinearOrder J] (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  ⨆ (l : {l : J // i < l ∧ l < j ∧ l ≠ k}), avoidingPathSubcomplex i j l.1

/-- The binary decomposition of full latching into factorization and face unions. -/
theorem fullyKnownPathSubcomplex_eq_through_sup_avoidingKnown
    {J : Type u} [LinearOrder J] (i j k : J) :
    fullyKnownPathSubcomplex i j k =
      (⨆ m : InteriorVertex i j, throughPathSubcomplex i j m.1) ⊔
        avoidingKnownPathSubcomplex i j k := by
  simpa only [avoidingKnownPathSubcomplex] using
    fullyKnownPathSubcomplex_eq_through_sup_avoiding i j k

section SubcomplexUnionMap

variable {X Y : SSet.{u}} {I : Type v} (A : I → X.Subcomplex)

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

/-- The glued omitted-path map restricts to the map supplied by each individual available
face. -/
@[reassoc]
theorem avoidingPathSubcomplex_avoidingKnownPathMapOfInnerHorn
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i l j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hil : i < l) (hlj : l < j) (hlk : l ≠ k) :
    SSet.Subcomplex.homOfLE
        (show avoidingPathSubcomplex (ULift.up.{u, 0} i) (ULift.up j) (ULift.up l) ≤
          avoidingKnownPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) from
          le_iSup (fun q : {q : ULift.{u, 0} (Fin (n + 3)) //
            ULift.up i < q ∧ q < ULift.up j ∧ q ≠ ULift.up k} ↦
              avoidingPathSubcomplex (ULift.up i) (ULift.up j) q.1)
            ⟨ULift.up l, hil, hlj, fun h ↦ hlk (ULift.up_injective h)⟩) ≫
        avoidingKnownPathMapOfInnerHorn C σ i j =
        avoidingPathMapOfInnerHornFace C σ hil hlj hlk := by
  let A := fun q : {q : ULift.{u, 0} (Fin (n + 3)) //
      ULift.up i < q ∧ q < ULift.up j ∧ q ≠ ULift.up k} ↦
    avoidingPathSubcomplex (ULift.up i) (ULift.up j) q.1
  let f : (q : {q : ULift.{u, 0} (Fin (n + 3)) //
      ULift.up i < q ∧ q < ULift.up j ∧ q ≠ ULift.up k}) →
      (A q : SSet) ⟶
        (innerHornObject C σ
            (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
          innerHornObject C σ
            (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := fun q ↦
    match q with
    | ⟨⟨q⟩, hiq, hqj, hqk⟩ =>
        avoidingPathMapOfInnerHornFace C σ hiq hqj
          (fun h ↦ hqk (congrArg ULift.up h))
  let q : {q : ULift.{u, 0} (Fin (n + 3)) //
      ULift.up i < q ∧ q < ULift.up j ∧ q ≠ ULift.up k} :=
    ⟨ULift.up l, hil, hlj, fun h ↦ hlk (ULift.up_injective h)⟩
  have hcompat : ∀ a b,
      SSet.Subcomplex.homOfLE (inf_le_left : A a ⊓ A b ≤ A a) ≫ f a =
        SSet.Subcomplex.homOfLE (inf_le_right : A a ⊓ A b ≤ A b) ≫ f b := by
    rintro ⟨⟨a⟩, hia, haj, hak⟩ ⟨⟨b⟩, hib, hbj, hbk⟩
    exact avoidingPathMapOfInnerHornFace_pairwise
      C σ hia haj (fun h ↦ hak (congrArg ULift.up h))
        hib hbj (fun h ↦ hbk (congrArg ULift.up h))
  change SSet.Subcomplex.homOfLE (le_iSup A q) ≫
      mapFromISupSubcomplex A f hcompat = f q
  exact homOfLE_iSup_mapFromISupSubcomplex A f hcompat q

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

/-- Splitting a through path and recomposing it gives its ambient path simplex. -/
@[reassoc]
theorem throughPathSubcomplexToProduct_eComp {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    throughPathSubcomplexToProduct i k j ≫ CategoryTheory.eComp SSet i k j =
      (throughPathSubcomplex i.as j.as k.as).ι := by
  change throughPathSubcomplexToProduct i k j ≫
      pathCompositionToThroughPathSubcomplex i k j ≫
        (throughPathSubcomplex i.as j.as k.as).ι = _
  rw [← Category.assoc, split_pathCompositionToThrough, Category.id_comp]

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

/-- On the overlap with a face vertex to the left of the missing vertex, the forced through
map agrees with that face. -/
theorem through_inf_avoiding_forcedThroughPathMap_of_left
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i l j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hil : i < l) (hlk : l < k) (hkj : k < j) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ≤
          throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up k))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))
          (innerHornLeftPathMap C σ hkLast (lt_trans hil hlk))
          (innerHornRightPathMap C σ hkZero hkj) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ≤
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)) ≫
        avoidingPathMapOfInnerHornFace C σ hil (lt_trans hlk hkj) (ne_of_lt hlk) := by
  ext U x
  let c := ofNerveSimplex x.1
  let pair := (throughPathSubcomplexToProduct
    (CategoryTheory.SimplicialThickening.mk (ULift.up i))
    (CategoryTheory.SimplicialThickening.mk (ULift.up k))
    (CategoryTheory.SimplicialThickening.mk (ULift.up j))).app U
      ⟨x.1, x.2.1⟩
  let left := pair.1
  let right := pair.2
  have hleftAvoids : ULift.up.{u, 0} l ∉ (ofNerveSimplex left).last.I := by
    intro hl
    exact x.2.2 hl.1
  have hleftMap := avoidingPathSubcomplex_innerHornLeftPathMap C σ hkLast hil hlk
  rw [← avoidingPathSubcomplex_pathMapOfInnerHornFace] at hleftMap
  have hleft := congrArg (fun q ↦ q.app U ⟨left, hleftAvoids⟩) hleftMap
  have hright := congrArg (fun q ↦ q.app U right)
    (innerHornRightPathMap_eq_pathMapOfInnerHornFace_of_left
      C σ hkZero (lt_of_le_of_lt (Fin.zero_le i) hil) hlk hkj)
  have hcomp := congrArg (fun q ↦ q.app U pair)
    (pathMapOfInnerHornFace_map_comp C σ
      (ne_of_lt hil) (ne_of_gt hlk) (ne_of_gt (lt_trans hlk hkj)) (ne_of_lt hlk))
  change (pathMapOfInnerHornFace C σ (ne_of_lt hil)
      (ne_of_gt (lt_trans hlk hkj)) (ne_of_lt hlk)).app U
        ((CategoryTheory.eComp SSet
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up k))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))).app U pair) =
    (CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up k)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up j)))).app U
        ((pathMapOfInnerHornFace C σ (ne_of_lt hil) (ne_of_gt hlk) (ne_of_lt hlk) ⊗ₘ
          pathMapOfInnerHornFace C σ (ne_of_gt hlk)
            (ne_of_gt (lt_trans hlk hkj)) (ne_of_lt hlk)).app U pair) at hcomp
  change ((CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up k)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up j)))).app U)
      (((innerHornLeftPathMap C σ hkLast (lt_trans hil hlk)) ⊗ₘ
        innerHornRightPathMap C σ hkZero hkj).app U pair) =
    (pathMapOfInnerHornFace C σ (ne_of_lt hil)
      (ne_of_gt (lt_trans hlk hkj)) (ne_of_lt hlk)).app U x.1
  change (innerHornLeftPathMap C σ hkLast (lt_trans hil hlk)).app U left =
    (pathMapOfInnerHornFace C σ (ne_of_lt hil) (ne_of_gt hlk)
      (ne_of_lt hlk)).app U left at hleft
  have hpair : ((innerHornLeftPathMap C σ hkLast (lt_trans hil hlk)) ⊗ₘ
      innerHornRightPathMap C σ hkZero hkj).app U pair =
    ((pathMapOfInnerHornFace C σ (ne_of_lt hil) (ne_of_gt hlk) (ne_of_lt hlk)) ⊗ₘ
      pathMapOfInnerHornFace C σ (ne_of_gt hlk)
        (ne_of_gt (lt_trans hlk hkj)) (ne_of_lt hlk)).app U pair := by
    apply Prod.ext
    · exact hleft
    · exact hright
  rw [hpair]
  rw [← hcomp]
  have hrecompose := congrArg (fun q ↦ q.app U ⟨x.1, x.2.1⟩)
    (throughPathSubcomplexToProduct_eComp
      (CategoryTheory.SimplicialThickening.mk (ULift.up i))
      (CategoryTheory.SimplicialThickening.mk (ULift.up k))
      (CategoryTheory.SimplicialThickening.mk (ULift.up j)))
  change (CategoryTheory.eComp SSet
      (CategoryTheory.SimplicialThickening.mk (ULift.up i))
      (CategoryTheory.SimplicialThickening.mk (ULift.up k))
      (CategoryTheory.SimplicialThickening.mk (ULift.up j))).app U pair = x.1 at hrecompose
  exact congrArg
    (fun y ↦ (pathMapOfInnerHornFace C σ (ne_of_lt hil)
      (ne_of_gt (lt_trans hlk hkj)) (ne_of_lt hlk)).app U y)
    hrecompose

/-- On the overlap with a face vertex to the right of the missing vertex, the forced through
map agrees with that face. -/
theorem through_inf_avoiding_forcedThroughPathMap_of_right
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i l j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkl : k < l) (hlj : l < j) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ≤
          throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up k))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))
          (innerHornLeftPathMap C σ hkLast hik)
          (innerHornRightPathMap C σ hkZero (lt_trans hkl hlj)) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ≤
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)) ≫
        avoidingPathMapOfInnerHornFace C σ (lt_trans hik hkl) hlj (ne_of_gt hkl) := by
  ext U x
  let c := ofNerveSimplex x.1
  let pair := (throughPathSubcomplexToProduct
    (CategoryTheory.SimplicialThickening.mk (ULift.up i))
    (CategoryTheory.SimplicialThickening.mk (ULift.up k))
    (CategoryTheory.SimplicialThickening.mk (ULift.up j))).app U
      ⟨x.1, x.2.1⟩
  let left := pair.1
  let right := pair.2
  have hrightAvoids : ULift.up.{u, 0} l ∉ (ofNerveSimplex right).last.I := by
    intro hl
    exact x.2.2 hl.1
  have hleft := congrArg (fun q ↦ q.app U left)
    (innerHornLeftPathMap_eq_pathMapOfInnerHornFace_of_right C σ hkLast hik hkl
      (lt_of_lt_of_le hlj (Fin.le_last j)))
  have hrightMap := avoidingPathSubcomplex_innerHornRightPathMap C σ hkZero hkl hlj
  rw [← avoidingPathSubcomplex_pathMapOfInnerHornFace] at hrightMap
  have hright := congrArg (fun q ↦ q.app U ⟨right, hrightAvoids⟩) hrightMap
  have hcomp := congrArg (fun q ↦ q.app U pair)
    (pathMapOfInnerHornFace_map_comp C σ
      (ne_of_lt (lt_trans hik hkl)) (ne_of_lt hkl) (ne_of_gt hlj) (ne_of_gt hkl))
  change (pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hik hkl))
      (ne_of_gt hlj) (ne_of_gt hkl)).app U
        ((CategoryTheory.eComp SSet
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up k))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))).app U pair) =
    (CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up k)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up j)))).app U
        ((pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hik hkl))
            (ne_of_lt hkl) (ne_of_gt hkl) ⊗ₘ
          pathMapOfInnerHornFace C σ (ne_of_lt hkl) (ne_of_gt hlj)
            (ne_of_gt hkl)).app U pair) at hcomp
  change ((CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up k)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up j)))).app U)
      (((innerHornLeftPathMap C σ hkLast hik) ⊗ₘ
        innerHornRightPathMap C σ hkZero (lt_trans hkl hlj)).app U pair) =
    (pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hik hkl))
      (ne_of_gt hlj) (ne_of_gt hkl)).app U x.1
  change (innerHornRightPathMap C σ hkZero (lt_trans hkl hlj)).app U right =
    (pathMapOfInnerHornFace C σ (ne_of_lt hkl) (ne_of_gt hlj)
      (ne_of_gt hkl)).app U right at hright
  have hpair : ((innerHornLeftPathMap C σ hkLast hik) ⊗ₘ
      innerHornRightPathMap C σ hkZero (lt_trans hkl hlj)).app U pair =
    ((pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hik hkl))
        (ne_of_lt hkl) (ne_of_gt hkl) ⊗ₘ
      pathMapOfInnerHornFace C σ (ne_of_lt hkl) (ne_of_gt hlj)
        (ne_of_gt hkl)).app U pair) := by
    apply Prod.ext
    · exact hleft
    · exact hright
  rw [hpair]
  rw [← hcomp]
  have hrecompose := congrArg (fun q ↦ q.app U ⟨x.1, x.2.1⟩)
    (throughPathSubcomplexToProduct_eComp
      (CategoryTheory.SimplicialThickening.mk (ULift.up i))
      (CategoryTheory.SimplicialThickening.mk (ULift.up k))
      (CategoryTheory.SimplicialThickening.mk (ULift.up j)))
  change (CategoryTheory.eComp SSet
      (CategoryTheory.SimplicialThickening.mk (ULift.up i))
      (CategoryTheory.SimplicialThickening.mk (ULift.up k))
      (CategoryTheory.SimplicialThickening.mk (ULift.up j))).app U pair = x.1 at hrecompose
  exact congrArg
    (fun y ↦ (pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hik hkl))
      (ne_of_gt hlj) (ne_of_gt hkl)).app U y)
    hrecompose

/-- The forced through map agrees with every individual available internal horn face on their
overlap. -/
theorem through_inf_avoiding_forcedThroughPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i l j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkj : k < j) (hil : i < l) (hlj : l < j) (hlk : l ≠ k) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ≤
          throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up k))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))
          (innerHornLeftPathMap C σ hkLast hik)
          (innerHornRightPathMap C σ hkZero hkj) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l) ≤
          avoidingPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up l)) ≫
        avoidingPathMapOfInnerHornFace C σ hil hlj hlk := by
  rcases lt_or_gt_of_ne hlk with hlk' | hkl
  · simpa only using through_inf_avoiding_forcedThroughPathMap_of_left
      C σ hkZero hkLast hil hlk' hkj
  · simpa only using through_inf_avoiding_forcedThroughPathMap_of_right
      C σ hkZero hkLast hik hkl hlj

/-- The forced through map agrees with the glued union of all available omitted horn faces. -/
theorem through_inf_avoidingKnown_forcedThroughPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkj : k < j) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingKnownPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ≤
          throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up i))
          (CategoryTheory.SimplicialThickening.mk (ULift.up k))
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))
          (innerHornLeftPathMap C σ hkLast hik)
          (innerHornRightPathMap C σ hkZero hkj) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        throughPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ⊓
            avoidingKnownPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k) ≤
          avoidingKnownPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k)) ≫
        avoidingKnownPathMapOfInnerHorn C σ i j := by
  ext U x
  have hx := x.2.2
  simp only [avoidingKnownPathSubcomplex, Subfunctor.iSup_obj,
    Set.mem_iUnion] at hx
  obtain ⟨⟨⟨l⟩, hil, hlj, hlk⟩, havoid⟩ := hx
  let hlk' : l ≠ k := fun h ↦ hlk (congrArg ULift.up h)
  have hforced := congrArg (fun q ↦ q.app U ⟨x.1, ⟨x.2.1, havoid⟩⟩)
    (through_inf_avoiding_forcedThroughPathMap
      C σ hkZero hkLast hik hkj hil hlj hlk')
  have hglued := congrArg (fun q ↦ q.app U ⟨x.1, havoid⟩)
    (avoidingPathSubcomplex_avoidingKnownPathMapOfInnerHorn
      C σ hil hlj hlk')
  exact hforced.trans hglued.symm

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

/-- The available horn faces and forced composition assemble into the compatible known-path
latching map for every interval spanning the missing vertex. -/
noncomputable def compatibleKnownPathLatchingMapOfInnerHorn
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkj : k < j) :
    CompatibleKnownPathLatchingMap C (innerHornObject C σ)
      (CategoryTheory.SimplicialThickening.mk (ULift.up i))
      (CategoryTheory.SimplicialThickening.mk (ULift.up k))
      (CategoryTheory.SimplicialThickening.mk (ULift.up j))
      (innerHornLeftPathMap C σ hkLast hik)
      (innerHornRightPathMap C σ hkZero hkj) :=
  CompatibleKnownPathLatchingMap.ofAvoidingMap C (innerHornObject C σ)
    (CategoryTheory.SimplicialThickening.mk (ULift.up i))
    (CategoryTheory.SimplicialThickening.mk (ULift.up k))
    (CategoryTheory.SimplicialThickening.mk (ULift.up j))
    (innerHornLeftPathMap C σ hkLast hik)
    (innerHornRightPathMap C σ hkZero hkj)
    (avoidingKnownPathMapOfInnerHorn C σ i j)
    (through_inf_avoidingKnown_forcedThroughPathMap
      C σ hkZero hkLast hik hkj)

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

/-- Every interval spanning the missing horn vertex has a full path map extending all known
faces and preserving composition through that vertex. -/
theorem exists_innerHornSpanningPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkj : k < j)
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j)))] :
    ∃ map : CategoryTheory.nerve
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i) ⟶
          CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} j)) ⟶
        (innerHornObject.{u, u} C σ
            (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
          innerHornObject.{u, u} C σ
            (CategoryTheory.SimplicialThickening.mk (ULift.up j))),
      (knownPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k)).ι ≫ map =
          (compatibleKnownPathLatchingMapOfInnerHorn
            C σ hkZero hkLast hik hkj).map ∧
        CategoryTheory.eComp SSet
            (CategoryTheory.SimplicialThickening.mk (ULift.up i))
            (CategoryTheory.SimplicialThickening.mk (ULift.up k))
            (CategoryTheory.SimplicialThickening.mk (ULift.up j)) ≫ map =
          (innerHornLeftPathMap C σ hkLast hik ⊗ₘ
              innerHornRightPathMap C σ hkZero hkj) ≫
            CategoryTheory.eComp SSet
              (innerHornObject.{u, u} C σ
                (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
              (innerHornObject.{u, u} C σ
                (CategoryTheory.SimplicialThickening.mk (ULift.up k)))
              (innerHornObject.{u, u} C σ
                (CategoryTheory.SimplicialThickening.mk (ULift.up j))) :=
  exists_pathMap_extension_preserving_comp (J := ULift.{u, 0} (Fin (n + 3)))
    C (innerHornObject.{u, u} C σ)
    (CategoryTheory.SimplicialThickening.mk (ULift.up i))
    (CategoryTheory.SimplicialThickening.mk (ULift.up k))
    (CategoryTheory.SimplicialThickening.mk (ULift.up j))
    hik hkj
    (innerHornLeftPathMap C σ hkLast hik)
    (innerHornRightPathMap C σ hkZero hkj)
    (compatibleKnownPathLatchingMapOfInnerHorn C σ hkZero hkLast hik hkj)

/-- A chosen full path map for an interval spanning the missing horn vertex. -/
noncomputable def innerHornSpanningPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkj : k < j)
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j)))] :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)) ⟶
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) :=
  Classical.choose
    (exists_innerHornSpanningPathMap.{u} C σ hkZero hkLast hik hkj)

@[reassoc]
theorem innerHornSpanningPathMap_restrict
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkj : k < j)
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j)))] :
    (knownPathSubcomplex (ULift.up i) (ULift.up j) (ULift.up k)).ι ≫
        innerHornSpanningPathMap C σ hkZero hkLast hik hkj =
      (compatibleKnownPathLatchingMapOfInnerHorn
        C σ hkZero hkLast hik hkj).map :=
  (Classical.choose_spec
    (exists_innerHornSpanningPathMap.{u} C σ hkZero hkLast hik hkj)).1

@[reassoc]
theorem innerHornSpanningPathMap_map_comp
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {k i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hkZero : k ≠ 0) (hkLast : k ≠ Fin.last (n + 2))
    (hik : i < k) (hkj : k < j)
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j)))] :
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up i))
        (CategoryTheory.SimplicialThickening.mk (ULift.up k))
        (CategoryTheory.SimplicialThickening.mk (ULift.up j)) ≫
      innerHornSpanningPathMap C σ hkZero hkLast hik hkj =
    (innerHornLeftPathMap C σ hkLast hik ⊗ₘ
        innerHornRightPathMap C σ hkZero hkj) ≫
      CategoryTheory.eComp SSet
        (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
        (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up k)))
        (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) :=
  (Classical.choose_spec
    (exists_innerHornSpanningPathMap.{u} C σ hkZero hkLast hik hkj)).2

/-- A strict internal vertex of the top interval. -/
abbrev TopInternalVertex (n : ℕ) :=
  {r : Fin (n + 3) // 0 < r ∧ r < Fin.last (n + 2)}

/-- An available strict internal face of the top horn. -/
abbrev TopAvailableFace (n : ℕ) (missing : Fin (n + 3)) :=
  {l : TopInternalVertex n // l.1 ≠ missing}

/-- Face pieces and through-vertex pieces indexing the top latching object. -/
abbrev TopPathLatchingIndex (n : ℕ) (missing : Fin (n + 3)) :=
  TopAvailableFace n missing ⊕ TopInternalVertex n

/-- The top latching subcomplex piece selected by an index. -/
def topPathLatchingPiece {n : ℕ} {missing : Fin (n + 3)}
    (a : TopPathLatchingIndex n missing) :
    (CategoryTheory.nerve
      (ThickPath (ULift.up.{u, 0} 0)
        (ULift.up.{u, 0} (Fin.last (n + 2))))).Subcomplex :=
  match a with
  | .inl l => avoidingPathSubcomplex (ULift.up 0)
      (ULift.up (Fin.last (n + 2))) (ULift.up l.1.1)
  | .inr r => throughPathSubcomplex (ULift.up 0)
      (ULift.up (Fin.last (n + 2))) (ULift.up r.1)

/-- Horn data force the map on each top latching piece. -/
noncomputable def topPathLatchingPieceMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (a : TopPathLatchingIndex n missing) :
    (topPathLatchingPiece a : SSet) ⟶
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))) :=
  match a with
  | .inl l => avoidingPathMapOfInnerHornFace C σ
      l.1.2.1 l.1.2.2 l.2
  | .inr r => forcedThroughPathMap C (innerHornObject C σ)
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
      (CategoryTheory.SimplicialThickening.mk (ULift.up r.1))
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2))))
      (properPathMap C σ hkZero hkLast (Fin.zero_le r.1) (by omega))
      (properPathMap C σ hkZero hkLast (Fin.le_last r.1) (by omega))

/-- The indexed top pieces have the full path-latching subcomplex as their union. -/
theorem iSup_topPathLatchingPiece {n : ℕ} {missing : Fin (n + 3)} :
    ⨆ a : TopPathLatchingIndex n missing, topPathLatchingPiece a =
      fullyKnownPathSubcomplex (ULift.up.{u, 0} 0)
        (ULift.up (Fin.last (n + 2))) (ULift.up missing) := by
  ext U x
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, fullyKnownPathSubcomplex]
  change (∃ a, x ∈ (topPathLatchingPiece a).obj U) ↔
    (ofNerveSimplex x).FullyKnownAt (ULift.up missing)
  constructor
  · rintro ⟨a, ha⟩
    rcases a with l | r
    · exact Or.inr ⟨⟨ULift.up l.1.1, by simpa using l.1.2.1,
          by simpa using l.1.2.2⟩,
        fun h ↦ l.2 (ULift.up_injective h), ha⟩
    · exact Or.inl ⟨⟨ULift.up r.1, by simpa using r.2.1,
        by simpa using r.2.2⟩, ha⟩
  · rintro (⟨r, hr⟩ | ⟨l, hlk, hl⟩)
    · let r' := r.1.down
      have hrange := r.2
      change 0 < r.1.down ∧ r.1.down < Fin.last (n + 2) at hrange
      refine ⟨.inr ⟨r', ?_, ?_⟩, ?_⟩
      · exact hrange.1
      · exact hrange.2
      · exact hr
    · let l' := l.1.down
      have hlrange := l.2
      change 0 < l.1.down ∧ l.1.down < Fin.last (n + 2) at hlrange
      refine ⟨.inl ⟨⟨l', ?_, ?_⟩, ?_⟩, ?_⟩
      · exact hlrange.1
      · exact hlrange.2
      · intro h
        apply hlk
        apply ULift.ext
        exact h
      · exact hl

/-- Available top face pieces agree on every binary intersection. -/
theorem topPathLatchingFace_pairwise
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (l m : TopAvailableFace n missing) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        topPathLatchingPiece (Sum.inl l) ⊓ topPathLatchingPiece (Sum.inl m) ≤
          topPathLatchingPiece (Sum.inl l)) ≫
        topPathLatchingPieceMap C σ hkZero hkLast (.inl l) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        topPathLatchingPiece (Sum.inl l) ⊓ topPathLatchingPiece (Sum.inl m) ≤
          topPathLatchingPiece (Sum.inl m)) ≫
        topPathLatchingPieceMap C σ hkZero hkLast (.inl m) := by
  exact avoidingPathMapOfInnerHornFace_pairwise C σ
    l.1.2.1 l.1.2.2 l.2 m.1.2.1 m.1.2.2 m.2

/-- A through piece agrees with an available face lying left of its split vertex. -/
theorem topThroughFace_of_left
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing l r : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hl0 : 0 < l) (hlr : l < r) (hrt : r < Fin.last (n + 2))
    (hlk : l ≠ missing) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r) ⊓
          avoidingPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up l) ≤
          throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
          (CategoryTheory.SimplicialThickening.mk (ULift.up r))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))
          (properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega))
          (properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r) ⊓
          avoidingPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up l) ≤
          avoidingPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up l)) ≫
        avoidingPathMapOfInnerHornFace C σ hl0
          (lt_trans hlr hrt) hlk := by
  ext U x
  let pair := (throughPathSubcomplexToProduct
    (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
    (CategoryTheory.SimplicialThickening.mk (ULift.up r))
    (CategoryTheory.SimplicialThickening.mk
      (ULift.up (Fin.last (n + 2))))).app U ⟨x.1, x.2.1⟩
  let left := pair.1
  let right := pair.2
  have hleftAvoids : ULift.up.{u, 0} l ∉ (ofNerveSimplex left).last.I := by
    intro hl
    exact x.2.2 hl.1
  have hleftMap := avoidingPathSubcomplex_properPathMap C σ hkZero hkLast
    (Fin.zero_le r) (by omega) hl0 hlr hlk
  rw [← avoidingPathSubcomplex_pathMapOfInnerHornFace] at hleftMap
  have hleft := congrArg (fun q ↦ q.app U ⟨left, hleftAvoids⟩) hleftMap
  have hright := congrArg (fun q ↦ q.app U right)
    (properPathMap_eq_pathMapOf_outsideFace C σ hkZero hkLast
      (Fin.le_last r) (by omega) (Or.inl hlr) hlk)
  have hcomp := congrArg (fun q ↦ q.app U pair)
    (pathMapOfInnerHornFace_map_comp C σ
      (ne_of_lt hl0) (ne_of_gt hlr)
      (ne_of_gt (lt_trans hlr hrt)) hlk)
  change (pathMapOfInnerHornFace C σ (ne_of_lt hl0)
      (ne_of_gt (lt_trans hlr hrt)) hlk).app U
        ((CategoryTheory.eComp SSet
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
          (CategoryTheory.SimplicialThickening.mk (ULift.up r))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))).app U pair) =
    (CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up 0)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up r)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2)))))).app U
      ((pathMapOfInnerHornFace C σ (ne_of_lt hl0) (ne_of_gt hlr) hlk ⊗ₘ
        pathMapOfInnerHornFace C σ (ne_of_gt hlr)
          (ne_of_gt (lt_trans hlr hrt)) hlk).app U pair) at hcomp
  change ((CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up 0)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up r)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2)))))).app U)
      (((properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega)) ⊗ₘ
        properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)).app U pair) =
    (pathMapOfInnerHornFace C σ (ne_of_lt hl0)
      (ne_of_gt (lt_trans hlr hrt)) hlk).app U x.1
  have hpair :
      ((properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega) ⊗ₘ
        properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)).app U pair) =
      ((pathMapOfInnerHornFace C σ (ne_of_lt hl0) (ne_of_gt hlr) hlk ⊗ₘ
        pathMapOfInnerHornFace C σ (ne_of_gt hlr)
          (ne_of_gt (lt_trans hlr hrt)) hlk).app U pair) := by
    apply Prod.ext
    · exact hleft
    · exact hright
  rw [hpair, ← hcomp]
  have hrecompose := congrArg (fun q ↦ q.app U ⟨x.1, x.2.1⟩)
    (throughPathSubcomplexToProduct_eComp
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
      (CategoryTheory.SimplicialThickening.mk (ULift.up r))
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2)))))
  change (CategoryTheory.eComp SSet
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
      (CategoryTheory.SimplicialThickening.mk (ULift.up r))
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2))))).app U pair = x.1 at hrecompose
  exact congrArg (fun y ↦
    (pathMapOfInnerHornFace C σ (ne_of_lt hl0)
      (ne_of_gt (lt_trans hlr hrt)) hlk).app U y) hrecompose

/-- A through piece agrees with an available face lying right of its split vertex. -/
theorem topThroughFace_of_right
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing r l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hr0 : 0 < r) (hrl : r < l) (hlt : l < Fin.last (n + 2))
    (hlk : l ≠ missing) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r) ⊓
          avoidingPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up l) ≤
          throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
          (CategoryTheory.SimplicialThickening.mk (ULift.up r))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))
          (properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega))
          (properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r) ⊓
          avoidingPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up l) ≤
          avoidingPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up l)) ≫
        avoidingPathMapOfInnerHornFace C σ (lt_trans hr0 hrl) hlt hlk := by
  ext U x
  let pair := (throughPathSubcomplexToProduct
    (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
    (CategoryTheory.SimplicialThickening.mk (ULift.up r))
    (CategoryTheory.SimplicialThickening.mk
      (ULift.up (Fin.last (n + 2))))).app U ⟨x.1, x.2.1⟩
  let left := pair.1
  let right := pair.2
  have hrightAvoids : ULift.up.{u, 0} l ∉ (ofNerveSimplex right).last.I := by
    intro hl
    exact x.2.2 hl.1
  have hleft := congrArg (fun q ↦ q.app U left)
    (properPathMap_eq_pathMapOf_outsideFace C σ hkZero hkLast
      (Fin.zero_le r) (by omega) (Or.inr hrl) hlk)
  have hrightMap := avoidingPathSubcomplex_properPathMap C σ hkZero hkLast
    (Fin.le_last r) (by omega) hrl hlt hlk
  rw [← avoidingPathSubcomplex_pathMapOfInnerHornFace] at hrightMap
  have hright := congrArg (fun q ↦ q.app U ⟨right, hrightAvoids⟩) hrightMap
  have hcomp := congrArg (fun q ↦ q.app U pair)
    (pathMapOfInnerHornFace_map_comp C σ
      (ne_of_lt (lt_trans hr0 hrl)) (ne_of_lt hrl) (ne_of_gt hlt) hlk)
  change (pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hr0 hrl))
      (ne_of_gt hlt) hlk).app U
        ((CategoryTheory.eComp SSet
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
          (CategoryTheory.SimplicialThickening.mk (ULift.up r))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))).app U pair) =
    (CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up 0)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up r)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2)))))).app U
      ((pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hr0 hrl))
          (ne_of_lt hrl) hlk ⊗ₘ
        pathMapOfInnerHornFace C σ (ne_of_lt hrl) (ne_of_gt hlt) hlk).app U pair)
      at hcomp
  change ((CategoryTheory.eComp SSet
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up 0)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk (ULift.up r)))
      (innerHornObject C σ (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2)))))).app U)
      (((properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega)) ⊗ₘ
        properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)).app U pair) =
    (pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hr0 hrl))
      (ne_of_gt hlt) hlk).app U x.1
  have hpair :
      ((properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega) ⊗ₘ
        properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)).app U pair) =
      ((pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hr0 hrl))
          (ne_of_lt hrl) hlk ⊗ₘ
        pathMapOfInnerHornFace C σ (ne_of_lt hrl) (ne_of_gt hlt) hlk).app U pair) := by
    apply Prod.ext
    · exact hleft
    · exact hright
  rw [hpair, ← hcomp]
  have hrecompose := congrArg (fun q ↦ q.app U ⟨x.1, x.2.1⟩)
    (throughPathSubcomplexToProduct_eComp
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
      (CategoryTheory.SimplicialThickening.mk (ULift.up r))
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2)))))
  change (CategoryTheory.eComp SSet
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
      (CategoryTheory.SimplicialThickening.mk (ULift.up r))
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2))))).app U pair = x.1 at hrecompose
  exact congrArg (fun y ↦
    (pathMapOfInnerHornFace C σ (ne_of_lt (lt_trans hr0 hrl))
      (ne_of_gt hlt) hlk).app U y) hrecompose

/-- Every through piece agrees with every available face piece on their intersection. -/
theorem topPathLatchingThroughFace
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (r : TopInternalVertex n) (l : TopAvailableFace n missing) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        topPathLatchingPiece (Sum.inr r) ⊓ topPathLatchingPiece (Sum.inl l) ≤
          topPathLatchingPiece (Sum.inr r)) ≫
        topPathLatchingPieceMap C σ hkZero hkLast (.inr r) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        topPathLatchingPiece (Sum.inr r) ⊓ topPathLatchingPiece (Sum.inl l) ≤
          topPathLatchingPiece (Sum.inl l)) ≫
        topPathLatchingPieceMap C σ hkZero hkLast (.inl l) := by
  rcases lt_trichotomy l.1.1 r.1 with hlr | hlr | hrl
  · exact topThroughFace_of_left C σ hkZero hkLast
      l.1.2.1 hlr r.2.2 l.2
  · ext U x
    exfalso
    apply x.2.2
    rw [hlr]
    exact (ofNerveSimplex x.1).le_last _ x.2.1
  · exact topThroughFace_of_right C σ hkZero hkLast
      r.2.1 hrl l.1.2.2 l.2

/-- Split paths through two ordered vertices into three consecutive path chains. -/
noncomputable def throughPairSubcomplexToTriple
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) (hrs : r.as ≤ s.as) :
    (throughPathSubcomplex i.as j.as r.as ⊓
        throughPathSubcomplex i.as j.as s.as).toSSet ⟶
      (CategoryTheory.nerve (i ⟶ r) ⊗ CategoryTheory.nerve (r ⟶ s)) ⊗
        CategoryTheory.nerve (s ⟶ j) where
  app U := by
    obtain ⟨⟨d⟩⟩ := U
    exact ↾fun x ↦
      let c := ofNerveSimplex x.1
      let cr := c.afterAt x.2.1
      let hs : s.as ∈ cr.first.I := ⟨x.2.2, hrs⟩
      ⟨⟨(c.beforeAt x.2.1).toNerveSimplex,
          (cr.beforeAt hs).toNerveSimplex⟩,
        (cr.afterAt hs).toNerveSimplex⟩
  naturality := by
    rintro ⟨⟨d⟩⟩ ⟨⟨e⟩⟩ f
    ext x
    apply Prod.ext
    · apply Prod.ext
      · exact CategoryTheory.Functor.ext
          (h_obj := fun _ ↦ rfl)
          (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
      · exact CategoryTheory.Functor.ext
          (h_obj := fun _ ↦ rfl)
          (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
    · exact CategoryTheory.Functor.ext
        (h_obj := fun _ ↦ rfl)
        (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Compose three path chains into the intersection of two through pieces. -/
def pathTripleCompositionToThroughPair
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) :
    (CategoryTheory.nerve (i ⟶ r) ⊗ CategoryTheory.nerve (r ⟶ s)) ⊗
        CategoryTheory.nerve (s ⟶ j) ⟶
      (throughPathSubcomplex i.as j.as r.as ⊓
        throughPathSubcomplex i.as j.as s.as).toSSet :=
  SSet.Subcomplex.lift
    ((α_ (CategoryTheory.nerve (i ⟶ r)) (CategoryTheory.nerve (r ⟶ s))
          (CategoryTheory.nerve (s ⟶ j))).hom ≫
        (CategoryTheory.nerve (i ⟶ r) ◁
          CategoryTheory.eComp SSet r s j) ≫
      CategoryTheory.eComp SSet i r j) (by
        rintro U _ ⟨x, rfl⟩
        constructor
        · change r.as ∈ (((x.1.1.prod' ((x.1.2.prod' x.2) ⋙
            CategoryTheory.SimplicialThickening.compFunctor r s j)) ⋙
              CategoryTheory.SimplicialThickening.compFunctor i r j).obj 0).I
          exact Or.inl (x.1.1.obj 0).right
        · change s.as ∈ (((x.1.1.prod' ((x.1.2.prod' x.2) ⋙
            CategoryTheory.SimplicialThickening.compFunctor r s j)) ⋙
              CategoryTheory.SimplicialThickening.compFunctor i r j).obj 0).I
          exact Or.inr (Or.inl (x.1.2.obj 0).right))

@[reassoc (attr := simp)]
theorem pathTripleCompositionToThroughPair_ι
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) :
    pathTripleCompositionToThroughPair i r s j ≫
      (throughPathSubcomplex i.as j.as r.as ⊓
          throughPathSubcomplex i.as j.as s.as).ι =
      (α_ (CategoryTheory.nerve (i ⟶ r)) (CategoryTheory.nerve (r ⟶ s))
          (CategoryTheory.nerve (s ⟶ j))).hom ≫
        (CategoryTheory.nerve (i ⟶ r) ◁
          CategoryTheory.eComp SSet r s j) ≫
        CategoryTheory.eComp SSet i r j :=
  rfl

/-- Triple composition followed by ordered splitting is the identity. -/
theorem pathTripleCompositionToThroughPair_split
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) (hrs : r.as ≤ s.as) :
    pathTripleCompositionToThroughPair i r s j ≫
      throughPairSubcomplexToTriple i r s j hrs = 𝟙 _ := by
  ext U x
  · exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ congrArg Prod.fst
        (splitCritical_joinCritical
          (x.1.1.obj a, x.1.2.obj a ≫ x.2.obj a)))
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
  · exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        apply CategoryTheory.SimplicialThickening.Path.ext
        ext z
        change ((((z ∈ (x.1.1.obj a).I ∨ z ∈ (x.1.2.obj a).I ∨
          z ∈ (x.2.obj a).I) ∧ r.as ≤ z) ∧ z ≤ s.as) ↔
            z ∈ (x.1.2.obj a).I)
        constructor
        · rintro ⟨⟨hp | hq | ht, hrz⟩, hzs⟩
          · have hzr := (x.1.1.obj a).le_right z hp
            exact (le_antisymm hrz hzr) ▸ (x.1.2.obj a).left
          · exact hq
          · have hsz := (x.2.obj a).left_le z ht
            exact (le_antisymm hzs hsz) ▸ (x.1.2.obj a).right
        · intro hq
          exact ⟨⟨Or.inr (Or.inl hq), (x.1.2.obj a).left_le z hq⟩,
            (x.1.2.obj a).le_right z hq⟩)
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
  · exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        apply CategoryTheory.SimplicialThickening.Path.ext
        ext z
        change ((((z ∈ (x.1.1.obj a).I ∨ z ∈ (x.1.2.obj a).I ∨
          z ∈ (x.2.obj a).I) ∧ r.as ≤ z) ∧ s.as ≤ z) ↔
            z ∈ (x.2.obj a).I)
        constructor
        · rintro ⟨⟨hp | hq | ht, _⟩, hsz⟩
          · have hzr := (x.1.1.obj a).le_right z hp
            have hzs := hzr.trans hrs
            exact (le_antisymm hzs hsz) ▸ (x.2.obj a).left
          · have hzs := (x.1.2.obj a).le_right z hq
            exact (le_antisymm hsz hzs) ▸ (x.2.obj a).left
          · exact ht
        · intro ht
          have hsz := (x.2.obj a).left_le z ht
          exact ⟨⟨Or.inr (Or.inr ht), hrs.trans hsz⟩, hsz⟩)
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Ordered splitting followed by triple composition is the identity. -/
theorem throughPairSubcomplexToTriple_comp
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) (hrs : r.as ≤ s.as) :
    throughPairSubcomplexToTriple i r s j hrs ≫
      pathTripleCompositionToThroughPair i r s j = 𝟙 _ := by
  ext U x
  apply Subtype.ext
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ by
      let c := ofNerveSimplex x.1
      let cr := c.afterAt x.2.1
      let hs : s.as ∈ cr.first.I := ⟨x.2.2, hrs⟩
      change join ((c.beforeAt x.2.1).path a)
          (join ((cr.beforeAt hs).path a) ((cr.afterAt hs).path a)) = c.path a
      rw [cr.join_beforeAt_afterAt hs, c.join_beforeAt_afterAt x.2.1])
    (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- The double-through intersection is the triple product of shorter path nerves. -/
noncomputable def throughPairSubcomplexTripleIso
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) (hrs : r.as ≤ s.as) :
    ((CategoryTheory.nerve (i ⟶ r) ⊗ CategoryTheory.nerve (r ⟶ s)) ⊗
        CategoryTheory.nerve (s ⟶ j)) ≅
      (throughPathSubcomplex i.as j.as r.as ⊓
        throughPathSubcomplex i.as j.as s.as).toSSet where
  hom := pathTripleCompositionToThroughPair i r s j
  inv := throughPairSubcomplexToTriple i r s j hrs
  hom_inv_id := pathTripleCompositionToThroughPair_split i r s j hrs
  inv_hom_id := throughPairSubcomplexToTriple_comp i r s j hrs

/-- Splitting triple composition at the first vertex composes the final two factors. -/
@[reassoc]
theorem pathTripleComposition_first_split
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) :
    pathTripleCompositionToThroughPair i r s j ≫
        SSet.Subcomplex.homOfLE (inf_le_left :
          throughPathSubcomplex i.as j.as r.as ⊓
            throughPathSubcomplex i.as j.as s.as ≤
              throughPathSubcomplex i.as j.as r.as) ≫
        throughPathSubcomplexToProduct i r j =
      (α_ (CategoryTheory.nerve (i ⟶ r)) (CategoryTheory.nerve (r ⟶ s))
          (CategoryTheory.nerve (s ⟶ j))).hom ≫
        (CategoryTheory.nerve (i ⟶ r) ◁ CategoryTheory.eComp SSet r s j) := by
  ext U x
  · exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ congrArg Prod.fst
        (splitCritical_joinCritical
          (x.1.1.obj a, x.1.2.obj a ≫ x.2.obj a)))
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
  · exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ congrArg Prod.snd
        (splitCritical_joinCritical
          (x.1.1.obj a, x.1.2.obj a ≫ x.2.obj a)))
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Splitting triple composition at the second vertex composes the first two factors. -/
@[reassoc]
theorem pathTripleComposition_second_split
    {J : Type u} [LinearOrder J]
    (i r s j : CategoryTheory.SimplicialThickening J) (hrs : r.as ≤ s.as) :
    pathTripleCompositionToThroughPair i r s j ≫
        SSet.Subcomplex.homOfLE (inf_le_right :
          throughPathSubcomplex i.as j.as r.as ⊓
            throughPathSubcomplex i.as j.as s.as ≤
              throughPathSubcomplex i.as j.as s.as) ≫
        throughPathSubcomplexToProduct i s j =
      (CategoryTheory.eComp SSet i r s ▷ CategoryTheory.nerve (s ⟶ j)) := by
  ext U x
  · exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        apply CategoryTheory.SimplicialThickening.Path.ext
        ext z
        change (((z ∈ (x.1.1.obj a).I ∨ z ∈ (x.1.2.obj a).I ∨
          z ∈ (x.2.obj a).I) ∧ z ≤ s.as) ↔
            z ∈ (x.1.1.obj a).I ∨ z ∈ (x.1.2.obj a).I)
        constructor
        · rintro ⟨hp | hq | ht, hzs⟩
          · exact Or.inl hp
          · exact Or.inr hq
          · have hsz := (x.2.obj a).left_le z ht
            exact Or.inr ((le_antisymm hzs hsz) ▸ (x.1.2.obj a).right)
        · rintro (hp | hq)
          · exact ⟨Or.inl hp, ((x.1.1.obj a).le_right z hp).trans hrs⟩
          · exact ⟨Or.inr (Or.inl hq), (x.1.2.obj a).le_right z hq⟩)
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
  · exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ by
        apply CategoryTheory.SimplicialThickening.Path.ext
        ext z
        change (((z ∈ (x.1.1.obj a).I ∨ z ∈ (x.1.2.obj a).I ∨
          z ∈ (x.2.obj a).I) ∧ s.as ≤ z) ↔ z ∈ (x.2.obj a).I)
        constructor
        · rintro ⟨hp | hq | ht, hsz⟩
          · have hzs := ((x.1.1.obj a).le_right z hp).trans hrs
            exact (le_antisymm hzs hsz) ▸ (x.2.obj a).left
          · have hzs := (x.1.2.obj a).le_right z hq
            exact (le_antisymm hzs hsz) ▸ (x.2.obj a).left
          · exact ht
        · intro ht
          exact ⟨Or.inr (Or.inr ht), (x.2.obj a).left_le z ht⟩)
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Forced maps for two ordered through pieces agree on their intersection. -/
theorem topThroughThrough_of_lt
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing r s : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (hr0 : 0 < r) (hrs : r < s) (hst : s < Fin.last (n + 2)) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r) ⊓
          throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up s) ≤
          throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
          (CategoryTheory.SimplicialThickening.mk (ULift.up r))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))
          (properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega))
          (properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up r) ⊓
          throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up s) ≤
          throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
            (ULift.up s)) ≫
        forcedThroughPathMap C (innerHornObject C σ)
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
          (CategoryTheory.SimplicialThickening.mk (ULift.up s))
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))
          (properPathMap C σ hkZero hkLast (Fin.zero_le s) (by omega))
          (properPathMap C σ hkZero hkLast (Fin.le_last s) (by omega)) := by
  apply (cancel_epi (throughPairSubcomplexTripleIso
    (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
    (CategoryTheory.SimplicialThickening.mk (ULift.up r))
    (CategoryTheory.SimplicialThickening.mk (ULift.up s))
    (CategoryTheory.SimplicialThickening.mk
      (ULift.up (Fin.last (n + 2)))) (le_of_lt hrs)).hom).1
  simp only [forcedThroughPathMap, throughPairSubcomplexTripleIso,
    throughPathSubcomplexProductIso]
  rw [pathTripleComposition_first_split_assoc,
    pathTripleComposition_second_split_assoc]
  · ext U x
    let I : CategoryTheory.SimplicialThickening (ULift.{u, 0} (Fin (n + 3))) :=
      CategoryTheory.SimplicialThickening.mk (ULift.up 0)
    let R := CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} r)
    let S := CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} s)
    let T := CategoryTheory.SimplicialThickening.mk
      (ULift.up.{u, 0} (Fin.last (n + 2)))
    let X := innerHornObject C σ
    let M0r := properPathMap C σ hkZero hkLast (Fin.zero_le r) (by omega)
    let Mrs := properPathMap C σ hkZero hkLast (le_of_lt hrs) (by omega)
    let Mst := properPathMap C σ hkZero hkLast (Fin.le_last s) (by omega)
    let M0s := properPathMap C σ hkZero hkLast (Fin.zero_le s) (by omega)
    let Mrt := properPathMap C σ hkZero hkLast (Fin.le_last r) (by omega)
    have hright := congrArg (fun q ↦ q.app U ⟨x.1.2, x.2⟩)
      (properPathMap_map_comp C σ hkZero hkLast
        (le_of_lt hrs) (Fin.le_last s) (by omega))
    have hleft := congrArg (fun q ↦ q.app U x.1)
      (properPathMap_map_comp C σ hkZero hkLast
        (Fin.zero_le r) (le_of_lt hrs) (by omega))
    change (CategoryTheory.eComp SSet (X I) (X R) (X T)).app U
        ⟨M0r.app U x.1.1,
          Mrt.app U ((CategoryTheory.eComp SSet R S T).app U ⟨x.1.2, x.2⟩)⟩ =
      (CategoryTheory.eComp SSet (X I) (X S) (X T)).app U
        ⟨M0s.app U ((CategoryTheory.eComp SSet I R S).app U x.1),
          Mst.app U x.2⟩
    change Mrt.app U ((CategoryTheory.eComp SSet R S T).app U ⟨x.1.2, x.2⟩) =
      (CategoryTheory.eComp SSet (X R) (X S) (X T)).app U
        ⟨Mrs.app U x.1.2, Mst.app U x.2⟩ at hright
    change M0s.app U ((CategoryTheory.eComp SSet I R S).app U x.1) =
      (CategoryTheory.eComp SSet (X I) (X R) (X S)).app U
        ⟨M0r.app U x.1.1, Mrs.app U x.1.2⟩ at hleft
    rw [hright, hleft]
    have hassoc := congrArg (fun q ↦ q.app U
      ⟨⟨M0r.app U x.1.1, Mrs.app U x.1.2⟩, Mst.app U x.2⟩)
      (CategoryTheory.e_assoc' SSet (X I) (X R) (X S) (X T))
    exact hassoc
  · exact le_of_lt hrs

/-- All top through pieces agree on binary intersections. -/
theorem topPathLatchingThrough_pairwise
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (r s : TopInternalVertex n) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        topPathLatchingPiece (Sum.inr r) ⊓ topPathLatchingPiece (Sum.inr s) ≤
          topPathLatchingPiece (Sum.inr r)) ≫
        topPathLatchingPieceMap C σ hkZero hkLast (.inr r) =
      SSet.Subcomplex.homOfLE (inf_le_right :
        topPathLatchingPiece (Sum.inr r) ⊓ topPathLatchingPiece (Sum.inr s) ≤
          topPathLatchingPiece (Sum.inr s)) ≫
        topPathLatchingPieceMap C σ hkZero hkLast (.inr s) := by
  rcases lt_trichotomy r.1 s.1 with hrs | hrs | hsr
  · exact topThroughThrough_of_lt C σ hkZero hkLast r.2.1 hrs s.2.2
  · have h : r = s := Subtype.ext hrs
    subst s
    rfl
  · ext U x
    have h := congrArg (fun q ↦ q.app U ⟨x.1, ⟨x.2.2, x.2.1⟩⟩)
      (topThroughThrough_of_lt C σ hkZero hkLast s.2.1 hsr r.2.2)
    exact h.symm

/-- Every pair of top latching pieces carries compatible forced maps. -/
theorem topPathLatchingPieceMap_pairwise
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (a b : TopPathLatchingIndex n missing) :
    SSet.Subcomplex.homOfLE (inf_le_left :
        topPathLatchingPiece a ⊓ topPathLatchingPiece b ≤ topPathLatchingPiece a) ≫
        topPathLatchingPieceMap C σ hkZero hkLast a =
      SSet.Subcomplex.homOfLE (inf_le_right :
        topPathLatchingPiece a ⊓ topPathLatchingPiece b ≤ topPathLatchingPiece b) ≫
        topPathLatchingPieceMap C σ hkZero hkLast b := by
  rcases a with l | r
  · rcases b with m | s
    · exact topPathLatchingFace_pairwise C σ hkZero hkLast l m
    · ext U x
      have h := congrArg (fun q ↦ q.app U ⟨x.1, ⟨x.2.2, x.2.1⟩⟩)
        (topPathLatchingThroughFace C σ hkZero hkLast s l)
      exact h.symm
  · rcases b with l | s
    · exact topPathLatchingThroughFace C σ hkZero hkLast r l
    · exact topPathLatchingThrough_pairwise C σ hkZero hkLast r s

/-- The compatible top pieces glue over their indexed union. -/
noncomputable def topPathLatchingUnionMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2)) :
    (⨆ a : TopPathLatchingIndex n missing, topPathLatchingPiece a).toSSet ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))) :=
  mapFromISupSubcomplex topPathLatchingPiece
    (topPathLatchingPieceMap C σ hkZero hkLast)
    (topPathLatchingPieceMap_pairwise C σ hkZero hkLast)

/-- The glued top latching map on the semantic full latching subcomplex. -/
noncomputable def topPathLatchingMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2)) :
    (fullyKnownPathSubcomplex (ULift.up.{u, 0} 0)
        (ULift.up (Fin.last (n + 2))) (ULift.up missing) : SSet) ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))) :=
  SSet.Subcomplex.homOfLE (le_of_eq iSup_topPathLatchingPiece.symm) ≫
    topPathLatchingUnionMap C σ hkZero hkLast

/-- The semantic top latching map restricts to every indexed piece. -/
@[reassoc]
theorem topPathLatchingPiece_topPathLatchingMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    (a : TopPathLatchingIndex n missing) :
    SSet.Subcomplex.homOfLE (show topPathLatchingPiece a ≤
        fullyKnownPathSubcomplex (ULift.up.{u, 0} 0)
          (ULift.up (Fin.last (n + 2))) (ULift.up missing) from
      (le_iSup topPathLatchingPiece a).trans
        (le_of_eq iSup_topPathLatchingPiece)) ≫
      topPathLatchingMap C σ hkZero hkLast =
        topPathLatchingPieceMap C σ hkZero hkLast a := by
  simp only [topPathLatchingMap, topPathLatchingUnionMap, ← Category.assoc,
    SSet.Subcomplex.homOfLE_comp]
  exact homOfLE_iSup_mapFromISupSubcomplex topPathLatchingPiece
    (topPathLatchingPieceMap C σ hkZero hkLast)
    (topPathLatchingPieceMap_pairwise C σ hkZero hkLast) a

/-- The full top latching map extends across the complete top path nerve. -/
theorem exists_topPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))] :
    ∃ map : CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} 0)
          (ULift.up.{u, 0} (Fin.last (n + 2)))) ⟶
        (innerHornObject.{u, u} C σ
            (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
          innerHornObject.{u, u} C σ
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (Fin.last (n + 2))))),
      (fullyKnownPathSubcomplex (ULift.up 0)
          (ULift.up (Fin.last (n + 2))) (ULift.up missing)).ι ≫ map =
        topPathLatchingMap C σ hkZero hkLast :=
  exists_fullyKnownPathSubcomplex_extension_of_kan_of_fintype
    (J := ULift.{u, 0} (Fin (n + 3)))
    (X := innerHornObject.{u, u} C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
      innerHornObject.{u, u} C σ
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (Fin.last (n + 2)))))
    (show ULift.up 0 < ULift.up missing from Fin.pos_iff_ne_zero.mpr hkZero)
    (show ULift.up missing < ULift.up (Fin.last (n + 2)) from
      Fin.lt_last_iff_ne_last.mpr hkLast)
    (topPathLatchingMap C σ hkZero hkLast)

/-- A chosen top path map extending every latching piece. -/
noncomputable def topPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))] :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} 0)
          (ULift.up.{u, 0} (Fin.last (n + 2)))) ⟶
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))) :=
  Classical.choose (exists_topPathMap C σ hkZero hkLast)

@[reassoc]
theorem topPathMap_restrict
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))] :
    (fullyKnownPathSubcomplex (ULift.up 0)
        (ULift.up (Fin.last (n + 2))) (ULift.up missing)).ι ≫
      topPathMap C σ hkZero hkLast = topPathLatchingMap C σ hkZero hkLast :=
  Classical.choose_spec (exists_topPathMap C σ hkZero hkLast)

/-- The chosen top map restricts to every forced latching piece. -/
@[reassoc]
theorem topPathMap_restrict_piece
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (a : TopPathLatchingIndex n missing) :
    (topPathLatchingPiece a).ι ≫ topPathMap C σ hkZero hkLast =
      topPathLatchingPieceMap C σ hkZero hkLast a := by
  let hle : topPathLatchingPiece a ≤
      fullyKnownPathSubcomplex (ULift.up.{u, 0} 0)
        (ULift.up (Fin.last (n + 2))) (ULift.up missing) :=
    (le_iSup topPathLatchingPiece a).trans (le_of_eq iSup_topPathLatchingPiece)
  change (SSet.Subcomplex.homOfLE hle ≫
      (fullyKnownPathSubcomplex (ULift.up 0)
        (ULift.up (Fin.last (n + 2))) (ULift.up missing)).ι) ≫
      topPathMap C σ hkZero hkLast = _
  rw [Category.assoc, topPathMap_restrict]
  exact topPathLatchingPiece_topPathLatchingMap C σ hkZero hkLast a

/-- The chosen top map preserves composition through every internal vertex. -/
theorem topPathMap_map_comp
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (r : TopInternalVertex n) :
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} 0))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} r.1))
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up.{u, 0} (Fin.last (n + 2)))) ≫
      topPathMap C σ hkZero hkLast =
    (properPathMap C σ hkZero hkLast (Fin.zero_le r.1) (by omega) ⊗ₘ
        properPathMap C σ hkZero hkLast (Fin.le_last r.1) (by omega)) ≫
      CategoryTheory.eComp SSet
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up r.1)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))) := by
  change (pathCompositionToThroughPathSubcomplex
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
      (CategoryTheory.SimplicialThickening.mk (ULift.up r.1))
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2)))) ≫
    (throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
      (ULift.up r.1)).ι) ≫ topPathMap C σ hkZero hkLast = _
  rw [Category.assoc]
  have hpiece := topPathMap_restrict_piece C σ hkZero hkLast (.inr r)
  change (throughPathSubcomplex (ULift.up 0) (ULift.up (Fin.last (n + 2)))
      (ULift.up r.1)).ι ≫ topPathMap C σ hkZero hkLast =
    forcedThroughPathMap C (innerHornObject C σ)
      (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
      (CategoryTheory.SimplicialThickening.mk (ULift.up r.1))
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (Fin.last (n + 2))))
      (properPathMap C σ hkZero hkLast (Fin.zero_le r.1) (by omega))
      (properPathMap C σ hkZero hkLast (Fin.le_last r.1) (by omega)) at hpiece
  rw [hpiece]
  exact pathCompositionToThrough_forcedThroughPathMap C (innerHornObject C σ)
    (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
    (CategoryTheory.SimplicialThickening.mk (ULift.up r.1))
    (CategoryTheory.SimplicialThickening.mk
      (ULift.up (Fin.last (n + 2))))
    (properPathMap C σ hkZero hkLast (Fin.zero_le r.1) (by omega))
    (properPathMap C σ hkZero hkLast (Fin.le_last r.1) (by omega))

/-- Identity preservation forces composition preservation when the left source interval is
degenerate. -/
theorem map_comp_of_self_left
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i j : CategoryTheory.SimplicialThickening J)
    (mapII : CategoryTheory.nerve (i ⟶ i) ⟶ (obj i ⟶[SSet] obj i))
    (mapIJ : CategoryTheory.nerve (i ⟶ j) ⟶ (obj i ⟶[SSet] obj j))
    (hId : CategoryTheory.eId SSet i ≫ mapII = CategoryTheory.eId SSet (obj i)) :
    CategoryTheory.eComp SSet i i j ≫ mapIJ =
      (mapII ⊗ₘ mapIJ) ≫ CategoryTheory.eComp SSet (obj i) (obj i) (obj j) := by
  letI : IsIso (CategoryTheory.eId SSet i) :=
    (Path.thickPathSelfEIdIso i).isIso_hom
  letI : IsIso (CategoryTheory.eId SSet i ▷ (i ⟶[SSet] j)) :=
    inferInstance
  letI : IsIso ((λ_ (i ⟶[SSet] j)).inv ≫
      CategoryTheory.eId SSet i ▷ (i ⟶[SSet] j)) :=
    inferInstance
  apply (cancel_epi ((λ_ (i ⟶[SSet] j)).inv ≫
    CategoryTheory.eId SSet i ▷ (i ⟶[SSet] j))).1
  simp only [Category.assoc]
  rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc, hId,
    MonoidalCategory.leftUnitor_inv_comp_tensorHom_assoc]
  slice_lhs 1 3 => rw [CategoryTheory.e_id_comp]
  slice_rhs 2 4 => rw [CategoryTheory.e_id_comp]
  simp

/-- Identity preservation forces composition preservation when the right source interval is
degenerate. -/
theorem map_comp_of_self_right
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i j : CategoryTheory.SimplicialThickening J)
    (mapIJ : CategoryTheory.nerve (i ⟶ j) ⟶ (obj i ⟶[SSet] obj j))
    (mapJJ : CategoryTheory.nerve (j ⟶ j) ⟶ (obj j ⟶[SSet] obj j))
    (hId : CategoryTheory.eId SSet j ≫ mapJJ = CategoryTheory.eId SSet (obj j)) :
    CategoryTheory.eComp SSet i j j ≫ mapIJ =
      (mapIJ ⊗ₘ mapJJ) ≫ CategoryTheory.eComp SSet (obj i) (obj j) (obj j) := by
  letI : IsIso (CategoryTheory.eId SSet j) :=
    (Path.thickPathSelfEIdIso j).isIso_hom
  letI : IsIso ((i ⟶[SSet] j) ◁ CategoryTheory.eId SSet j) :=
    inferInstance
  letI : IsIso ((ρ_ (i ⟶[SSet] j)).inv ≫
      (i ⟶[SSet] j) ◁ CategoryTheory.eId SSet j) :=
    inferInstance
  apply (cancel_epi ((ρ_ (i ⟶[SSet] j)).inv ≫
    (i ⟶[SSet] j) ◁ CategoryTheory.eId SSet j)).1
  simp only [Category.assoc]
  rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc, hId,
    MonoidalCategory.rightUnitor_inv_comp_tensorHom_assoc]
  slice_lhs 1 3 => rw [CategoryTheory.e_comp_id]
  slice_rhs 2 4 => rw [CategoryTheory.e_comp_id]
  simp

/-- The total path map uses the single Kan extension on the top interval, an outer face on every
proper ordered interval, and the canonical empty-source map on reversed intervals. -/
noncomputable def innerHornPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (i j : Fin (n + 3)) :
    CategoryTheory.nerve
        (ThickPath (ULift.up.{u, 0} i) (ULift.up.{u, 0} j)) ⟶
      (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)) ⟶[SSet]
        innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := by
  by_cases hij : i ≤ j
  · by_cases htop : i = 0 ∧ j = Fin.last (n + 2)
    · rcases htop with ⟨rfl, rfl⟩
      exact topPathMap C σ hkZero hkLast
    · exact properPathMap C σ hkZero hkLast hij htop
  · exact Path.mapFromNerveThickPathOfNotLE
      (show ¬ ULift.up.{u, 0} i ≤ ULift.up j from
        fun h ↦ hij (by simpa using h)) _

/-- The total path map is the chosen Kan extension on the unique top interval. -/
theorem innerHornPathMap_eq_top
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))] :
    innerHornPathMap C σ hkZero hkLast 0 (Fin.last (n + 2)) =
      topPathMap C σ hkZero hkLast := by
  unfold innerHornPathMap
  rw [dif_pos (Fin.zero_le _), dif_pos (show
    (0 : Fin (n + 3)) = 0 ∧ Fin.last (n + 2) = Fin.last (n + 2) from ⟨rfl, rfl⟩)]

/-- The total path map is the canonical outer-face map on every proper ordered interval. -/
theorem innerHornPathMap_eq_proper
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i j : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (hij : i ≤ j) (hproper : ¬ (i = 0 ∧ j = Fin.last (n + 2))) :
    innerHornPathMap C σ hkZero hkLast i j =
      properPathMap C σ hkZero hkLast hij hproper := by
  simp [innerHornPathMap, hij, hproper]

/-- The total path map preserves every enriched identity. -/
theorem innerHornPathMap_map_id
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (i : Fin (n + 3)) :
    CategoryTheory.eId SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i)) ≫
      innerHornPathMap C σ hkZero hkLast i i =
    CategoryTheory.eId SSet
      (innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up i))) := by
  have hproper : ¬ (i = 0 ∧ i = Fin.last (n + 2)) := by
    rintro ⟨rfl, h⟩
    exact Fin.last_pos.ne h
  rw [innerHornPathMap_eq_proper C σ hkZero hkLast le_rfl hproper]
  exact properPathMap_map_id C σ hkZero hkLast hproper

/-- The total path maps preserve every enriched composition. -/
theorem innerHornPathMap_map_comp
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (i r j : Fin (n + 3)) :
    CategoryTheory.eComp SSet
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} i))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} r))
        (CategoryTheory.SimplicialThickening.mk (ULift.up.{u, 0} j)) ≫
      innerHornPathMap C σ hkZero hkLast i j =
    (innerHornPathMap C σ hkZero hkLast i r ⊗ₘ
        innerHornPathMap C σ hkZero hkLast r j) ≫
      CategoryTheory.eComp SSet
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up i)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up r)))
        (innerHornObject C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up j))) := by
  by_cases hir : i ≤ r
  · by_cases hrj : r ≤ j
    · by_cases htop : i = 0 ∧ j = Fin.last (n + 2)
      · rcases htop with ⟨rfl, rfl⟩
        by_cases hrZero : r = 0
        · subst r
          exact map_comp_of_self_left C (innerHornObject C σ)
            (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
            (CategoryTheory.SimplicialThickening.mk
              (ULift.up (Fin.last (n + 2)))) _ _
            (innerHornPathMap_map_id C σ hkZero hkLast 0)
        · by_cases hrLast : r = Fin.last (n + 2)
          · subst r
            exact map_comp_of_self_right C (innerHornObject C σ)
              (CategoryTheory.SimplicialThickening.mk (ULift.up 0))
              (CategoryTheory.SimplicialThickening.mk
                (ULift.up (Fin.last (n + 2)))) _ _
              (innerHornPathMap_map_id C σ hkZero hkLast (Fin.last (n + 2)))
          · rw [innerHornPathMap_eq_top C σ hkZero hkLast,
              innerHornPathMap_eq_proper C σ hkZero hkLast hir (by omega),
              innerHornPathMap_eq_proper C σ hkZero hkLast hrj (by omega)]
            exact topPathMap_map_comp C σ hkZero hkLast ⟨r, by omega⟩
      · rw [innerHornPathMap_eq_proper C σ hkZero hkLast
              (hir.trans hrj) htop,
            innerHornPathMap_eq_proper C σ hkZero hkLast hir
              (proper_left_subinterval hrj htop),
            innerHornPathMap_eq_proper C σ hkZero hkLast hrj
              (proper_right_subinterval hir htop)]
        exact properPathMap_map_comp C σ hkZero hkLast hir hrj htop
    · ext U x
      have h : ULift.up.{u, 0} r ≤ ULift.up j :=
        CategoryTheory.SimplicialThickening.Path.le (x.2.obj 0)
      exact (hrj (by simpa using h)).elim
  · ext U x
    have h : ULift.up.{u, 0} i ≤ ULift.up r :=
      CategoryTheory.SimplicialThickening.Path.le (x.1.obj 0)
    exact (hir (by simpa using h)).elim

theorem insertVertexPathNerveMap_innerHornPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i j l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (hli : i ≠ l) (hlj : j ≠ l) (hlk : l ≠ missing) :
    insertVertexPathNerveMap l hli hlj ≫
        innerHornPathMap C σ hkZero hkLast i j =
      insertVertexPathNerveMap l hli hlj ≫
        pathMapOfInnerHornFace C σ hli hlj hlk := by
  by_cases hij : i ≤ j
  · by_cases htop : i = 0 ∧ j = Fin.last (n + 2)
    · rcases htop with ⟨rfl, rfl⟩
      have h0l : 0 < l := Fin.pos_iff_ne_zero.mpr hli.symm
      have hlt : l < Fin.last (n + 2) := Fin.lt_last_iff_ne_last.mpr hlj.symm
      let a : TopAvailableFace n missing := ⟨⟨l, h0l, hlt⟩, hlk⟩
      rw [innerHornPathMap_eq_top C σ hkZero hkLast,
        ← insertVertexAvoidingPathMap_ι l hli hlj]
      simp only [Category.assoc]
      have hface := topPathMap_restrict_piece C σ hkZero hkLast (.inl a)
      change (avoidingPathSubcomplex (ULift.up 0)
          (ULift.up (Fin.last (n + 2))) (ULift.up l)).ι ≫
          topPathMap C σ hkZero hkLast =
        avoidingPathMapOfInnerHornFace C σ h0l hlt hlk at hface
      rw [hface]
      change insertVertexAvoidingPathMap l hli hlj ≫
          avoidingPathMapOfInnerHornFace C σ h0l hlt hlk =
        insertVertexAvoidingPathMap l hli hlj ≫
          (avoidingPathSubcomplex (ULift.up 0)
              (ULift.up (Fin.last (n + 2))) (ULift.up l)).ι ≫
            pathMapOfInnerHornFace C σ hli hlj hlk
      rw [avoidingPathSubcomplex_pathMapOfInnerHornFace C σ h0l hlt hlk]
    · rw [innerHornPathMap_eq_proper C σ hkZero hkLast hij htop]
      by_cases hout : l < i ∨ j < l
      · rw [properPathMap_eq_pathMapOf_outsideFace
          C σ hkZero hkLast hij htop hout hlk]
      · have hil : i < l := by omega
        have hlj' : l < j := by omega
        rw [← insertVertexAvoidingPathMap_ι l hli hlj]
        simp only [Category.assoc]
        rw [avoidingPathSubcomplex_properPathMap
            C σ hkZero hkLast hij htop hil hlj' hlk,
          avoidingPathSubcomplex_pathMapOfInnerHornFace C σ hil hlj' hlk]
  · have hdel : ¬ deleteFinVertex l i hli ≤ deleteFinVertex l j hlj := by
      intro h
      apply hij
      have hs := (Fin.succAboveOrderEmb l).monotone h
      change l.succAbove (deleteFinVertex l i hli) ≤
        l.succAbove (deleteFinVertex l j hlj) at hs
      simpa only [succAbove_deleteFinVertex] using hs
    exact (Path.homFromNerveThickPathOfNotLESubsingleton
      (show ¬ ULift.up.{u, 0} (deleteFinVertex l i hli) ≤
          ULift.up (deleteFinVertex l j hlj) from
        fun h ↦ hdel (by simpa using h)) _).elim _ _

theorem innerHornFaceFunctor_obj_delete
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing l a : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ missing) (hal : a ≠ l) :
    (innerHornFaceFunctor C σ hlk).obj
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (deleteFinVertex l a hal))) =
      innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk (ULift.up a)) := by
  simpa only [succAbove_deleteFinVertex] using
    innerHornFaceFunctor_obj C σ hlk
      (CategoryTheory.SimplicialThickening.mk
        (ULift.up (deleteFinVertex l a hal)))

theorem insertVertexPathNerveMap_innerHornPathMap_eq_faceMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing i j l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (hli : i ≠ l) (hlj : j ≠ l) (hlk : l ≠ missing) :
    let a := CategoryTheory.SimplicialThickening.mk
      (ULift.up.{u, 0} (deleteFinVertex l i hli))
    let b := CategoryTheory.SimplicialThickening.mk
      (ULift.up.{u, 0} (deleteFinVertex l j hlj))
    let hi := innerHornFaceFunctor_obj_delete C σ hlk hli
    let hj := innerHornFaceFunctor_obj_delete C σ hlk hlj
    (insertVertexPathNerveMap l hli hlj ≫
        innerHornPathMap C σ hkZero hkLast i j) ≫
        eqToHom (congrArg₂ (fun A B : C ↦ A ⟶[SSet] B) hi.symm hj.symm) =
      (innerHornFaceFunctor C σ hlk).map a b := by
  dsimp only
  rw [insertVertexPathNerveMap_innerHornPathMap C σ hkZero hkLast hli hlj hlk]
  simp only [pathMapOfInnerHornFace, Category.assoc]
  rw [insertVertexPathNerveMap_deleteVertexPathNerveMap_assoc]
  simp

/-- The total horn object and path maps form coherent simplex data. -/
noncomputable def innerHornPartialCoherentSimplexMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))] :
    PartialCoherentSimplexMap C (ULift (Fin (n + 3))) where
  obj := innerHornObject C σ
  map i j := by
    rcases i with ⟨⟨i⟩⟩
    rcases j with ⟨⟨j⟩⟩
    exact innerHornPathMap C σ hkZero hkLast i j
  map_id i := by
    rcases i with ⟨⟨i⟩⟩
    exact innerHornPathMap_map_id C σ hkZero hkLast i
  map_comp i r j := by
    rcases i with ⟨⟨i⟩⟩
    rcases r with ⟨⟨r⟩⟩
    rcases j with ⟨⟨j⟩⟩
    exact innerHornPathMap_map_comp C σ hkZero hkLast i r j

/-- The coherent horn construction as an enriched functor on the full thickened simplex. -/
noncomputable def innerHornEnrichedFunctor
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))] :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift (Fin (n + 3)))) C :=
  partialCoherentSimplexMapEquiv C _
    (innerHornPartialCoherentSimplexMap C σ hkZero hkLast)

theorem innerHornEnrichedFunctor_face
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (hlk : l ≠ missing) :
    (CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ l).toOrderHom.uliftMap).comp (E := C) SSet
          (innerHornEnrichedFunctor C σ hkZero hkLast) =
      innerHornFaceFunctor C σ hlk := by
  let F := (CategoryTheory.SimplicialThickening.functor
    (SimplexCategory.δ l).toOrderHom.uliftMap).comp (E := C) SSet
      (innerHornEnrichedFunctor C σ hkZero hkLast)
  let G := innerHornFaceFunctor C σ hlk
  let hobj : ∀ a, F.obj a = G.obj a := fun a ↦ by
    change innerHornObject C σ
        (CategoryTheory.SimplicialThickening.mk
          (ULift.up (l.succAbove a.as.down))) =
      (innerHornFaceFunctor C σ hlk).obj a
    exact (innerHornFaceFunctor_obj C σ hlk a).symm
  apply CategoryTheory.EnrichedFunctor.ext SSet hobj
  intro a b
  rcases a with ⟨⟨a⟩⟩
  rcases b with ⟨⟨b⟩⟩
  let i := l.succAbove a
  let j := l.succAbove b
  have hli : i ≠ l := Fin.succAbove_ne l a
  have hlj : j ≠ l := Fin.succAbove_ne l b
  have hexp := insertVertexPathNerveMap_innerHornPathMap_eq_faceMap
    C σ hkZero hkLast hli hlj hlk
  have hcanonical := insertVertexPathNerveMap_comp_enrichedMap_heq
    C l hli hlj (innerHornEnrichedFunctor C σ hkZero hkLast)
  dsimp only [i, j] at hexp hcanonical
  dsimp only [innerHornEnrichedFunctor, partialCoherentSimplexMapEquiv,
    innerHornPartialCoherentSimplexMap] at hcanonical
  change HEq
    (insertVertexPathNerveMap l hli hlj ≫
      innerHornPathMap C σ hkZero hkLast (l.succAbove a) (l.succAbove b))
      _ at hcanonical
  have ha : deleteFinVertex l (l.succAbove a) hli = a := by
    apply l.succAbove_right_injective
    rw [succAbove_deleteFinVertex]
  have hb : deleteFinVertex l (l.succAbove b) hlj = b := by
    apply l.succAbove_right_injective
    rw [succAbove_deleteFinVertex]
  apply eq_of_heq
  refine (CategoryTheory.comp_eqToHom_heq _ _).trans ?_
  refine (enrichedFunctor_map_heq_of_obj_eq F
    (congrArg (fun q ↦ CategoryTheory.SimplicialThickening.mk (ULift.up q)) ha.symm)
    (congrArg (fun q ↦ CategoryTheory.SimplicialThickening.mk (ULift.up q)) hb.symm)).trans ?_
  refine hcanonical.symm.trans ?_
  refine (CategoryTheory.comp_eqToHom_heq _ _).symm.trans (heq_of_eq hexp) |>.trans ?_
  exact enrichedFunctor_map_heq_of_obj_eq G
    (congrArg (fun q ↦ CategoryTheory.SimplicialThickening.mk (ULift.up q)) ha)
    (congrArg (fun q ↦ CategoryTheory.SimplicialThickening.mk (ULift.up q)) hb)

/-- The coherent horn construction as the candidate filling simplex. -/
noncomputable def innerHornFillerSimplex
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))] :
    (CategoryTheory.SimplicialNerve C).obj (op (.mk (n + 2))) :=
  innerHornEnrichedFunctor C σ hkZero hkLast

theorem innerHornFillerSimplex_face
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {n : ℕ} {missing l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) missing : SSet.{u}) ⟶
      CategoryTheory.SimplicialNerve C)
    (hkZero : missing ≠ 0) (hkLast : missing ≠ Fin.last (n + 2))
    [SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2)))))]
    (hlk : l ≠ missing) :
    (CategoryTheory.SimplicialNerve C).δ l
        (innerHornFillerSimplex C σ hkZero hkLast) =
      σ.app _ (SSet.horn.face missing l hlk) := by
  change
    (CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ l).toOrderHom.uliftMap).comp (E := C) SSet
          (innerHornEnrichedFunctor C σ hkZero hkLast) =
      innerHornFaceFunctor C σ hlk
  exact innerHornEnrichedFunctor_face C σ hkZero hkLast hlk

/-- The coherent nerve of a simplicial category with Kan mapping spaces is a quasicategory. -/
theorem simplicialNerve_quasicategory
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    [∀ X Y : C, SSet.KanComplex (X ⟶[SSet] Y)] :
    SSet.Quasicategory (CategoryTheory.SimplicialNerve C) := by
  apply SSet.quasicategory_of_filler
  intro n missing σ hkZero hkLast
  letI : SSet.KanComplex
      (innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk (ULift.up 0)) ⟶[SSet]
        innerHornObject.{u, u} C σ
          (CategoryTheory.SimplicialThickening.mk
            (ULift.up (Fin.last (n + 2))))) := inferInstance
  exact ⟨innerHornFillerSimplex C σ (ne_of_gt hkZero) (ne_of_lt hkLast),
    fun l hlk ↦ innerHornFillerSimplex_face C σ
      (ne_of_gt hkZero) (ne_of_lt hkLast) hlk⟩

end LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
