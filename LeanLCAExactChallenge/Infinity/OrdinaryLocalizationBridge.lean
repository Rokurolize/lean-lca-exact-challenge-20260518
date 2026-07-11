import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension
import LeanLCAExactChallenge.Infinity.MetrizableEquivalenceForcingHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
import Mathlib.CategoryTheory.Monoidal.Closed.Functor
import Mathlib.CategoryTheory.Monoidal.Closed.Ideal
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Ordinary localization bridge

This module is reserved for the comparison between the mapping-quasicategory localization
property and its ordinary homotopy-category truncation.  The comparison is not asserted here:
it requires a verified compatibility theorem between the two homotopy-category presentations.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Simplicial

universe u

universe v w x

set_option backward.isDefEq.respectTransparency false in
/-- An edge in a categorical nerve is an equivalence exactly when its underlying morphism is
an isomorphism. -/
theorem edgeIsEquivalence_nerve_iff_isIso
    {C : Type u} [Category.{u} C] {X Y : C} (f : X ⟶ Y) :
    EdgeIsEquivalence (CategoryTheory.nerve.edgeMk f) ↔ IsIso f := by
  constructor
  · intro hf
    letI : IsIso (edgeHomotopyClass (CategoryTheory.nerve.edgeMk f)) := hf
    let G := SSet.Truncated.HomotopyCategory.descOfTruncation
      (𝟙 ((SSet.truncation 2).obj (CategoryTheory.nerve C)))
    haveI : IsIso (G.map (edgeHomotopyClass (CategoryTheory.nerve.edgeMk f))) := by
      infer_instance
    have hedge : (CategoryTheory.nerve.edgeMk f).toTruncated.map
        (𝟙 ((SSet.truncation 2).obj (CategoryTheory.nerve C))) =
        (CategoryTheory.nerve.edgeMk f).toTruncated := by
      ext
      rfl
    have hmap : G.map (edgeHomotopyClass (CategoryTheory.nerve.edgeMk f)) = f := by
      dsimp [G, edgeHomotopyClass]
      rw [SSet.Truncated.HomotopyCategory.descOfTruncation_map_homMk, hedge]
      exact CategoryTheory.nerve.homEquiv_edgeMk f
    change IsIso f
    rw [← hmap]
    infer_instance
  · intro hf
    letI : IsIso f := hf
    exact edgeIsEquivalence_nerve_of_isIso f

private def freeReflVertex {V : Type u} [ReflQuiver V] : Cat.FreeRefl V → V :=
  Cat.FreeRefl.induction id

@[simp]
private theorem freeReflVertex_mk {V : Type u} [ReflQuiver V] (x : V) :
    freeReflVertex (Cat.FreeRefl.mk x) = x := rfl

private theorem freeReflPath_compress
    {V : SSet.Truncated.{u} 2} [V.Quasicategory₂]
    {A B : Cat.FreeRefl (SSet.OneTruncation₂ V)} (p : A ⟶ B) :
    ∀ (x : SSet.OneTruncation₂ V), A = Cat.FreeRefl.mk x →
      ∀ (y : SSet.OneTruncation₂ V), B = Cat.FreeRefl.mk y →
        ∃ e : SSet.Truncated.Edge x y,
          HEq ((SSet.Truncated.HomotopyCategory.quotientFunctor V).map p)
            (SSet.Truncated.HomotopyCategory.homMk e) := by
  induction p using Cat.FreeRefl.hom_induction with
  | id a =>
      intro x hx y hy
      have hax : a = x := congrArg freeReflVertex hx
      have hay : a = y := congrArg freeReflVertex hy
      subst x
      subst y
      refine ⟨SSet.Truncated.Edge.id a, ?_⟩
      exact HEq.trans (heq_of_eq (congrArg
        (SSet.Truncated.HomotopyCategory.quotientFunctor V).map
        (Cat.FreeRefl.homMk_id a))) (HEq.trans
          (heq_of_eq ((SSet.Truncated.HomotopyCategory.quotientFunctor V).map_id _))
          (heq_of_eq (SSet.Truncated.HomotopyCategory.homMk_id a).symm))
  | comp_homMk p g hp =>
      intro x hx z hz
      have hax : _ = x := congrArg freeReflVertex hx
      have hcz : _ = z := congrArg freeReflVertex hz
      subst x
      subst z
      obtain ⟨e, he⟩ := hp _ rfl _ rfl
      refine ⟨e.comp g, ?_⟩
      rw [Functor.map_comp]
      rw [eq_of_heq he]
      exact heq_of_eq (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        (SSet.Truncated.Edge.compStruct e g))

/-- Every morphism between vertex objects in the actual path-quotient homotopy category of a
2-truncated quasicategory has a single-edge representative. -/
theorem homotopyCategory_homMk_surjective_of_quasicategory
    {V : SSet.Truncated.{u} 2} [V.Quasicategory₂]
    {x y : SSet.OneTruncation₂ V} :
    Function.Surjective
      (SSet.Truncated.HomotopyCategory.homMk : SSet.Truncated.Edge x y →
        (SSet.Truncated.HomotopyCategory.mk x ⟶
          SSet.Truncated.HomotopyCategory.mk y)) := by
  intro f
  obtain ⟨p, hp⟩ :=
    (SSet.Truncated.HomotopyCategory.quotientFunctor V).map_surjective f
  obtain ⟨e, he⟩ := freeReflPath_compress p x rfl y rfl
  refine ⟨e, ?_⟩
  exact (eq_of_heq he).symm.trans hp

private instance nerveFunctor_exponentialIdeal : ExponentialIdeal nerveFunctor.{u, u} := by
  letI : Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair)
      (reflector nerveFunctor.{u, u}) := by
    change Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) SSet.hoFunctor.{u}
    infer_instance
  apply exponentialIdeal_of_preservesBinaryProducts

private instance nerveFunctor_monoidalClosedFunctor :
    MonoidalClosedFunctor nerveFunctor.{u, u} := by
  exact cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts
    (F := nerveFunctor.{u, u}) (L := SSet.hoFunctor.{u}) nerveAdjunction

/-- The nerve preserves categorical internal Homs. -/
noncomputable def nerveInternalHomIso (C E : Cat.{u, u}) :
    nerveFunctor.obj ((ihom C).obj E) ≅
      (ihom (nerveFunctor.obj C)).obj (nerveFunctor.obj E) := by
  letI : MonoidalClosedFunctor nerveFunctor.{u, u} :=
    nerveFunctor_monoidalClosedFunctor
  letI : IsIso (expComparison nerveFunctor.{u, u} C).natTrans :=
    MonoidalClosedFunctor.comparison_iso C
  let hApp : IsIso ((expComparison nerveFunctor.{u, u} C).natTrans.app E) :=
    NatIso.isIso_app_of_isIso (expComparison nerveFunctor.{u, u} C).natTrans E
  exact @asIso SSet _ _ _
    ((expComparison nerveFunctor.{u, u} C).natTrans.app E) hApp

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- A functor regarded as a vertex through the nerve exponential comparison uncurries
to its ordinary nerve map. -/
theorem nerveInternalHomIso_vertex_map (C E : Cat.{u, u}) (F : C ⥤ E) :
    internalHomVertexMap (nerveFunctor.obj C) (nerveFunctor.obj E)
      ((nerveInternalHomIso C E).hom.app (Opposite.op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm F)) = nerveFunctor.map F.toCatHom := by
  change MonoidalClosed.uncurry'
    ((SSet.unitHomEquiv (nerveFunctor.obj ((ihom C).obj E))).symm
      (CategoryTheory.nerveEquiv.symm F) ≫
        (expComparison nerveFunctor C).natTrans.app E) = _
  dsimp [MonoidalClosed.uncurry']
  rw [MonoidalClosed.uncurry_natural_left]
  have hh := CategoryTheory.uncurry_expComparison (F := nerveFunctor) C E
  erw [hh]
  ext U s
  let t : (nerveFunctor.obj (C ⊗ (ihom C).obj E)).obj U :=
    Functor.prod' s ((Functor.const _).obj F)
  have ht : (CartesianMonoidalCategory.prodComparison nerveFunctor C ((ihom C).obj E)).app U t =
      (s, (SSet.unitHomEquiv (nerveFunctor.obj ((ihom C).obj E))).symm
        (CategoryTheory.nerveEquiv.symm F) |>.app U PUnit.unit) := by
    change (s, _) = (s, _)
    congr 1
  have hinv : inv ((CartesianMonoidalCategory.prodComparison nerveFunctor C ((ihom C).obj E)).app U)
      (s, (SSet.unitHomEquiv (nerveFunctor.obj ((ihom C).obj E))).symm
        (CategoryTheory.nerveEquiv.symm F) |>.app U PUnit.unit) = t := by
    apply (ConcreteCategory.bijective_of_isIso
      ((CartesianMonoidalCategory.prodComparison nerveFunctor C ((ihom C).obj E)).app U)).1
    rw [ht]
    simp
  have hinv' := hinv
  simp [SSet.unitHomEquiv, CategoryTheory.nerveEquiv] at hinv'
  simp [SSet.unitHomEquiv, CategoryTheory.nerveEquiv]
  have hpair :
      (ConcreteCategory.hom
        ((nerveFunctor.obj C).obj U ◁
          (↾fun _ ↦ (nerveFunctor.obj ((ihom C).obj E)).map
            ((Opposite.unop U).const ⦋0⦌ 0).op
              (ComposableArrows.mk₀ F)))) (s, PUnit.unit) =
        (s, (nerveFunctor.obj ((ihom C).obj E)).map
          ((Opposite.unop U).const ⦋0⦌ 0).op
            (ComposableArrows.mk₀ F)) := by
    rfl
  erw [hpair]
  rw [hinv']
  apply ComposableArrows.ext
  · intro i hi
    dsimp [t, CategoryTheory.nerveMap]
    change (CategoryTheory.evaluationUncurried C E).map (Prod.mkHom _ (𝟙 F)) = _
    simp
  · intro i
    rfl

/-- On homotopy categories, the internal Hom between two nerves is the categorical
functor category. -/
noncomputable def nerveInternalHomHomotopyEquivalence (C E : Cat.{u, u}) :
    SSet.hoFunctor.obj
        ((ihom (nerveFunctor.obj C)).obj (nerveFunctor.obj E)) ≌
      (ihom C).obj E :=
  Cat.equivOfIso ((SSet.hoFunctor.mapIso (nerveInternalHomIso C E)).symm ≪≫
    nerveFunctorCompHoFunctorIso.app ((ihom C).obj E))

/-- Internal Homs into categorical nerves are again categorical nerves up to isomorphism. -/
theorem internalHomNerve_mem_essImage (L : SSet.{u}) (E : Cat.{u, u}) :
    nerveFunctor.{u, u}.essImage ((ihom L).obj (nerveFunctor.obj E)) :=
  ExponentialIdeal.exp_closed (nerveFunctor.obj_mem_essImage E) L

set_option backward.isDefEq.respectTransparency false in
/-- The nerve of a full subcategory maps to the full simplicial subcomplex on its objects. -/
def nerveFullSubcategoryToFullSubcomplex
    {C : Type u} [Category.{u} C] (P : ObjectProperty C) :
    CategoryTheory.nerve P.FullSubcategory ⟶
      (fullSubcomplexOnVertices (CategoryTheory.nerve C)
        (fun v ↦ P (CategoryTheory.nerveEquiv v)) : SSet.{u}) := by
  apply SSet.Subcomplex.lift
    (nerveFunctor.map (ObjectProperty.ι P).toCatHom)
  rintro U _ ⟨s, rfl⟩
  rw [mem_fullSubcomplexOnVertices_iff]
  intro i
  let v := (CategoryTheory.nerve P.FullSubcategory).map
    (SimplexCategory.const ⦋0⦌ U.unop i).op s
  have hv := (CategoryTheory.nerveEquiv v).property
  rw [show CategoryTheory.nerveEquiv
      ((CategoryTheory.nerve C).map
        (SimplexCategory.const ⦋0⦌ U.unop i).op
          ((nerveFunctor.map (ObjectProperty.ι P).toCatHom).app U s)) =
      (CategoryTheory.nerveEquiv v).obj by
    rfl]
  exact hv

@[simp]
theorem nerveFullSubcategoryToFullSubcomplex_app_val
    {C : Type u} [Category.{u} C] (P : ObjectProperty C)
    (U : SimplexCategoryᵒᵖ) (s : (CategoryTheory.nerve P.FullSubcategory).obj U) :
    ((nerveFullSubcategoryToFullSubcomplex P).app U s).val =
      (nerveFunctor.map (ObjectProperty.ι P).toCatHom).app U s :=
  rfl

/-- Package a composable-arrow simplex objectwise in a full subcategory. -/
def composableArrowsToFullSubcategory
    {C : Type u} [Category.{u} C] (P : ObjectProperty C) {n : ℕ}
    (F : ComposableArrows C n) (hF : ∀ i, P (F.obj i)) :
    ComposableArrows P.FullSubcategory n where
  obj i := ⟨F.obj i, hF i⟩
  map f := ObjectProperty.homMk (F.map f)
  map_id i := by ext; exact F.map_id i
  map_comp f g := by ext; exact F.map_comp f g

@[simp]
theorem composableArrowsToFullSubcategory_obj_val
    {C : Type u} [Category.{u} C] (P : ObjectProperty C) {n : ℕ}
    (F : ComposableArrows C n) (hF : ∀ i, P (F.obj i)) (i : Fin (n + 1)) :
    ((composableArrowsToFullSubcategory P F hF).obj i).obj = F.obj i :=
  rfl

/-- Forgetting the packaged chain recovers the original composable-arrow simplex. -/
theorem composableArrowsToFullSubcategory_forget
    {C : Type u} [Category.{u} C] (P : ObjectProperty C) {n : ℕ}
    (F : ComposableArrows C n) (hF : ∀ i, P (F.obj i)) :
    composableArrowsToFullSubcategory P F hF ⋙ ObjectProperty.ι P = F := by
  let hobj : ∀ i, (composableArrowsToFullSubcategory P F hF ⋙
      ObjectProperty.ι P).obj i = F.obj i := fun _ ↦ rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro i j f
  dsimp [composableArrowsToFullSubcategory]
  exact (conj_eqToHom_iff_heq _ _ (hobj i) (hobj j)).2 HEq.rfl

/-- The degreewise inverse to `nerveFullSubcategoryToFullSubcomplex`. -/
def fullSubcomplexToNerveFullSubcategoryApp
    {C : Type u} [Category.{u} C] (P : ObjectProperty C)
    (U : SimplexCategoryᵒᵖ)
    (s : (fullSubcomplexOnVertices (CategoryTheory.nerve C)
      (fun v ↦ P (CategoryTheory.nerveEquiv v)) : SSet.{u}).obj U) :
    (CategoryTheory.nerve P.FullSubcategory).obj U :=
  composableArrowsToFullSubcategory P s.val (fun i ↦ by
    exact s.property i)

/-- The full vertex subcomplex of a categorical nerve maps back to the nerve of the full
subcategory. -/
def fullSubcomplexToNerveFullSubcategory
    {C : Type u} [Category.{u} C] (P : ObjectProperty C) :
    (fullSubcomplexOnVertices (CategoryTheory.nerve C)
      (fun v ↦ P (CategoryTheory.nerveEquiv v)) : SSet.{u}) ⟶
      CategoryTheory.nerve P.FullSubcategory where
  app U := TypeCat.ofHom (fullSubcomplexToNerveFullSubcategoryApp P U)
  naturality {X Y} f := by
    ext s i
    rfl

/-- A categorical full subcategory has nerve equal to the full vertex subcomplex. -/
noncomputable def nerveFullSubcategoryIsoFullSubcomplex
    {C : Type u} [Category.{u} C] (P : ObjectProperty C) :
    CategoryTheory.nerve P.FullSubcategory ≅
      (fullSubcomplexOnVertices (CategoryTheory.nerve C)
        (fun v ↦ P (CategoryTheory.nerveEquiv v)) : SSet.{u}) where
  hom := nerveFullSubcategoryToFullSubcomplex P
  inv := fullSubcomplexToNerveFullSubcategory P
  hom_inv_id := by
    ext U s i
    rfl
  inv_hom_id := by
    ext U s
    apply Subtype.ext
    exact congrArg id (composableArrowsToFullSubcategory_forget P s.val
      (fun i ↦ s.property i))

/-- The reflection unit exhibits an internal Hom into a nerve as the nerve of its homotopy
category. -/
noncomputable def internalHomNerveReflectionIso (L : SSet.{u}) (E : Cat.{u, u}) :
    nerveFunctor.obj (SSet.hoFunctor.obj
      ((ihom L).obj (nerveFunctor.obj E))) ≅
      (ihom L).obj (nerveFunctor.obj E) := by
  haveI := Functor.essImage.unit_isIso (internalHomNerve_mem_essImage L E)
  letI : IsIso (nerveAdjunction.unit.app
      ((ihom L).obj (nerveFunctor.obj E))) := by
    change IsIso ((reflectorAdjunction nerveFunctor).unit.app
      ((ihom L).obj (nerveFunctor.obj E)))
    infer_instance
  exact (asIso (nerveAdjunction.unit.app
    ((ihom L).obj (nerveFunctor.obj E)))).symm

/-- Precomposition along the reflection unit, with a categorical nerve as target. -/
def internalHomReflectionPre (L : SSet.{u}) (E : Cat.{u, u}) :
    (ihom (nerveFunctor.obj (SSet.hoFunctor.obj L))).obj (nerveFunctor.obj E) ⟶
      (ihom L).obj (nerveFunctor.obj E) :=
  (MonoidalClosed.pre (nerveAdjunction.unit.app L)).app (nerveFunctor.obj E)

/-- The Yoneda component used to test internal Homs into categorical nerves. -/
noncomputable def internalHomToNerveYonedaEquiv
    (Z L : SSet.{u}) (E : Cat.{u, u}) :
    (Z ⟶ (ihom L).obj (nerveFunctor.obj E)) ≃
      (SSet.hoFunctor.obj (L ⊗ Z) ⟶ E) :=
  ((ihom.adjunction L).homEquiv Z (nerveFunctor.obj E)).symm.trans
    (nerveAdjunction.homEquiv (L ⊗ Z) E).symm

set_option backward.isDefEq.respectTransparency false in
/-- Applying the reflector to its unit gives an isomorphism. -/
theorem hoFunctor_map_reflectionUnit_isIso (L : SSet.{u}) :
    IsIso (SSet.hoFunctor.map (nerveAdjunction.unit.app L)) := by
  let e := nerveFunctorCompHoFunctorIso.app (SSet.hoFunctor.obj L)
  have h : SSet.hoFunctor.map (nerveAdjunction.unit.app L) = e.inv := by
    calc
      _ = inv e.hom := by
        apply IsIso.eq_inv_of_inv_hom_id
        exact nerveAdjunction.left_triangle_components L
      _ = e.inv := by simp
  rw [h]
  infer_instance

/-- The reflector sends the reflection unit tensored with any object to an isomorphism. -/
theorem hoFunctor_map_reflectionUnit_whiskerRight_isIso (L Z : SSet.{u}) :
    IsIso (SSet.hoFunctor.map (nerveAdjunction.unit.app L ▷ Z)) := by
  letI : IsIso (SSet.hoFunctor.map (nerveAdjunction.unit.app L)) :=
    hoFunctor_map_reflectionUnit_isIso L
  apply IsIso.of_isIso_fac_right
    (CartesianMonoidalCategory.prodComparison_natural_whiskerRight SSet.hoFunctor
      (B := Z) (nerveAdjunction.unit.app L))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Under the Yoneda component, internal-Hom precomposition is ordinary precomposition by
the reflected tensor-unit map. -/
theorem internalHomToNerveYonedaEquiv_postcomp
    (L Z : SSet.{u}) (E : Cat.{u, u})
    (f : Z ⟶ (ihom (nerveFunctor.obj (SSet.hoFunctor.obj L))).obj
      (nerveFunctor.obj E)) :
    internalHomToNerveYonedaEquiv Z L E (f ≫ internalHomReflectionPre L E) =
      SSet.hoFunctor.map (nerveAdjunction.unit.app L ▷ Z) ≫
        internalHomToNerveYonedaEquiv Z
          (nerveFunctor.obj (SSet.hoFunctor.obj L)) E f := by
  dsimp [internalHomToNerveYonedaEquiv, internalHomReflectionPre]
  rw [MonoidalClosed.homEquiv_symm_apply_eq, MonoidalClosed.uncurry_pre_app]
  rw [MonoidalClosed.homEquiv_symm_apply_eq]
  exact nerveAdjunction.homEquiv_naturality_left_symm
    (nerveAdjunction.unit.app L ▷ Z) (MonoidalClosed.uncurry f)

set_option backward.isDefEq.respectTransparency false in
/-- Every Yoneda component of reflection-unit internal-Hom precomposition is bijective. -/
theorem internalHomReflectionPre_yoneda_bijective
    (L : SSet.{u}) (E : Cat.{u, u}) (Z : SSet.{u}) :
    Function.Bijective (fun f : Z ⟶
      (ihom (nerveFunctor.obj (SSet.hoFunctor.obj L))).obj (nerveFunctor.obj E) ↦
        f ≫ internalHomReflectionPre L E) := by
  letI : IsIso (SSet.hoFunctor.map (nerveAdjunction.unit.app L ▷ Z)) :=
    hoFunctor_map_reflectionUnit_whiskerRight_isIso L Z
  constructor
  · intro f g h
    apply (internalHomToNerveYonedaEquiv Z
      (nerveFunctor.obj (SSet.hoFunctor.obj L)) E).injective
    apply (cancel_epi (SSet.hoFunctor.map (nerveAdjunction.unit.app L ▷ Z))).1
    rw [← internalHomToNerveYonedaEquiv_postcomp,
      ← internalHomToNerveYonedaEquiv_postcomp]
    exact congrArg (internalHomToNerveYonedaEquiv Z L E) h
  · intro g
    let f := (internalHomToNerveYonedaEquiv Z
      (nerveFunctor.obj (SSet.hoFunctor.obj L)) E).symm
        (inv (SSet.hoFunctor.map (nerveAdjunction.unit.app L ▷ Z)) ≫
          internalHomToNerveYonedaEquiv Z L E g)
    refine ⟨f, ?_⟩
    apply (internalHomToNerveYonedaEquiv Z L E).injective
    rw [internalHomToNerveYonedaEquiv_postcomp]
    dsimp [f]
    rw [Equiv.apply_symm_apply, IsIso.hom_inv_id_assoc]

/-- Reflection-unit precomposition is an isomorphism of simplicial internal Homs into a
categorical nerve. -/
theorem internalHomReflectionPre_isIso (L : SSet.{u}) (E : Cat.{u, u}) :
    IsIso (internalHomReflectionPre L E) :=
  isIso_of_yoneda_map_bijective (internalHomReflectionPre L E)
    (internalHomReflectionPre_yoneda_bijective L E)

/-- The internal Hom from an arbitrary simplicial set into a categorical nerve is itself the
nerve of the ordinary functor category out of the reflected category. -/
noncomputable def internalHomNerveIso (L : SSet.{u}) (E : Cat.{u, u}) :
    nerveFunctor.obj ((ihom (SSet.hoFunctor.obj L)).obj E) ≅
      (ihom L).obj (nerveFunctor.obj E) := by
  let hPre : IsIso (internalHomReflectionPre L E) :=
    internalHomReflectionPre_isIso L E
  exact nerveInternalHomIso (SSet.hoFunctor.obj L) E ≪≫
    @asIso SSet _ _ _ (internalHomReflectionPre L E) hPre

/-- The marking-inverting vertex predicate transported to the ordinary functor category by
the internal-Hom nerve isomorphism. -/
noncomputable def PulledRelativeFunctorProperty
    {L : SSet.{u}} (W : EdgeMarking L) (E : Cat.{u, u}) :
    ObjectProperty ((ihom (SSet.hoFunctor.obj L)).obj E) :=
  fun F ↦ InvertsMarkedEdges W
    (internalHomVertexMap L (nerveFunctor.obj E)
      ((internalHomNerveIso L E).hom.app (Opposite.op ⦋0⦌)
        (CategoryTheory.nerveEquiv.symm F)))

/-- The morphism property on the simplicial homotopy category represented by marked
edges.  `HEq` records the endpoint transports inherent in the path-quotient
presentation of the homotopy category. -/
def markedHomotopyMorphismProperty {L : SSet.{u}} (W : EdgeMarking L) :
    MorphismProperty (SSet.hoFunctor.obj L) :=
  fun _ _ f ↦ ∃ (x y : L _⦋0⦌) (e : SSet.Edge x y),
    W.marked e.edge ∧ HEq f (edgeHomotopyClass e)

theorem markedHomotopyMorphismProperty_edge_mem
    {L : SSet.{u}} (W : EdgeMarking L) {x y : L _⦋0⦌}
    (e : SSet.Edge x y) (he : W.marked e.edge) :
    markedHomotopyMorphismProperty W (edgeHomotopyClass e) :=
  ⟨x, y, e, he, HEq.rfl⟩

/-- A simplicial isomorphism restricts to the full subcomplexes cut out by a vertex
predicate and its pullback. -/
noncomputable def fullSubcomplexOnVerticesIsoOfIso {X Y : SSet.{u}} (e : X ≅ Y)
    (P : Y.obj (Opposite.op ⦋0⦌) → Prop) :
    (fullSubcomplexOnVertices X (fun v ↦ P (e.hom.app (Opposite.op ⦋0⦌) v)) : SSet.{u}) ≅
      (fullSubcomplexOnVertices Y P : SSet.{u}) where
  hom := SSet.Subcomplex.lift
    ((fullSubcomplexOnVertices X
      (fun v ↦ P (e.hom.app (Opposite.op ⦋0⦌) v))).ι ≫ e.hom) (by
    rintro U _ ⟨s, rfl⟩
    rw [mem_fullSubcomplexOnVertices_iff]
    intro i
    have h := s.property i
    change P (Y.map (SimplexCategory.const ⦋0⦌ U.unop i).op
      (e.hom.app U s.val))
    rw [← NatTrans.naturality_apply e.hom
      (SimplexCategory.const ⦋0⦌ U.unop i).op s.val]
    exact h)
  inv := SSet.Subcomplex.lift
    ((fullSubcomplexOnVertices Y P).ι ≫ e.inv) (by
    rintro U _ ⟨s, rfl⟩
    rw [mem_fullSubcomplexOnVertices_iff]
    intro i
    have h := s.property i
    change P (e.hom.app (Opposite.op ⦋0⦌)
      (X.map (SimplexCategory.const ⦋0⦌ U.unop i).op
        (e.inv.app U s.val)))
    rw [← NatTrans.naturality_apply e.inv
      (SimplexCategory.const ⦋0⦌ U.unop i).op s.val]
    rw [Iso.inv_hom_id_app_apply]
    exact h)
  hom_inv_id := by
    ext U s
    apply Subtype.ext
    exact e.hom_inv_id_app_apply U s.val
  inv_hom_id := by
    ext U s
    apply Subtype.ext
    exact e.inv_hom_id_app_apply U s.val

theorem pulledRelativeFunctorProperty_iff
    {L : SSet.{u}} (W : EdgeMarking L) (E : Cat.{u, u})
    (F : (ihom (SSet.hoFunctor.obj L)).obj E) :
    PulledRelativeFunctorProperty W E F ↔
      InvertsMarkedEdges W
        (internalHomVertexMap L (nerveFunctor.obj E)
          ((internalHomNerveIso L E).hom.app (Opposite.op ⦋0⦌)
            (CategoryTheory.nerveEquiv.symm F))) :=
  Iff.rfl

/-- The relative mapping simplicial set into a categorical nerve is the nerve of the full
subcategory cut out by the transported marking-inversion predicate. -/
noncomputable def relativeInternalHomNerveIso
    {L : SSet.{u}} (W : EdgeMarking L) (E : Cat.{u, u}) :
    CategoryTheory.nerve (PulledRelativeFunctorProperty W E).FullSubcategory ≅
      (relativeInternalHom W (nerveFunctor.obj E) : SSet.{u}) := by
  let P : ((ihom L).obj (nerveFunctor.obj E)).obj (Opposite.op ⦋0⦌) → Prop :=
    fun v ↦ InvertsMarkedEdges W
      (internalHomVertexMap L (nerveFunctor.obj E) v)
  have hsub :
      fullSubcomplexOnVertices
        (nerveFunctor.obj ((ihom (SSet.hoFunctor.obj L)).obj E))
        (fun v ↦ PulledRelativeFunctorProperty W E
          (CategoryTheory.nerveEquiv v)) =
      fullSubcomplexOnVertices
        (nerveFunctor.obj ((ihom (SSet.hoFunctor.obj L)).obj E))
        (fun v ↦ P ((internalHomNerveIso L E).hom.app
          (Opposite.op ⦋0⦌) v)) := by
    ext U s
    simp only [mem_fullSubcomplexOnVertices_iff]
    constructor <;> intro h i
    · simpa [PulledRelativeFunctorProperty, P] using h i
    · simpa [PulledRelativeFunctorProperty, P] using h i
  have hsource := congrArg SSet.Subcomplex.toSSet hsub
  exact nerveFullSubcategoryIsoFullSubcomplex (PulledRelativeFunctorProperty W E) ≪≫
    eqToIso hsource ≪≫
    fullSubcomplexOnVerticesIsoOfIso (internalHomNerveIso L E) P

/-- For an arbitrary simplicial set `L`, mapping into a categorical nerve has homotopy
category the ordinary functor category out of `ho L`. -/
noncomputable def internalHomNerveHomotopyEquivalence (L : SSet.{u}) (E : Cat.{u, u}) :
    SSet.hoFunctor.obj ((ihom L).obj (nerveFunctor.obj E)) ≌
      (ihom (SSet.hoFunctor.obj L)).obj E := by
  exact Cat.equivOfIso ((SSet.hoFunctor.mapIso (internalHomNerveIso L E)).symm ≪≫
    nerveFunctorCompHoFunctorIso.app ((ihom (SSet.hoFunctor.obj L)).obj E))

/-- The homotopy category of the relative mapping simplicial set into a categorical
nerve is the full subcategory of ordinary functors satisfying the transported
marked-edge inversion predicate. -/
noncomputable def relativeInternalHomNerveHomotopyEquivalence
    {L : SSet.{u}} (W : EdgeMarking L) (E : Cat.{u, u}) :
    SSet.hoFunctor.obj (relativeInternalHom W (nerveFunctor.obj E)) ≌
      (PulledRelativeFunctorProperty W E).FullSubcategory := by
  exact Cat.equivOfIso
    ((SSet.hoFunctor.mapIso (relativeInternalHomNerveIso W E)).symm ≪≫
      nerveFunctorCompHoFunctorIso.app
        (Cat.of (PulledRelativeFunctorProperty W E).FullSubcategory))

/-- In a Cat-enriched ordinary category, the transported horizontal composite has the
expected enriched-composition normal form after applying `Hom.base`. -/
theorem catEnrichedOrdinary_base_hComp
    {C : Type x} [Category.{v} C] [EnrichedOrdinaryCategory Cat.{w, u} C]
    {a b c : CategoryTheory.CatEnrichedOrdinary C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} (eta : f ⟶ f') (theta : g ⟶ g') :
    CategoryTheory.CatEnrichedOrdinary.Hom.base
        (CategoryTheory.CatEnrichedOrdinary.hComp eta theta) =
      eqToHom (CategoryTheory.CatEnrichedOrdinary.homEquiv_comp f g) ≫
        CategoryTheory.CatEnriched.hComp
          (CategoryTheory.CatEnrichedOrdinary.Hom.base eta)
          (CategoryTheory.CatEnrichedOrdinary.Hom.base theta) ≫
        eqToHom (CategoryTheory.CatEnrichedOrdinary.homEquiv_comp f' g').symm := by
  rfl

/-- Horizontal composition in the underlying Cat-enriched category is literally the map of
the enriched composition functor. -/
theorem catEnriched_hComp_eq_eComp_map
    {C : Type u} [Category.{v} C] [EnrichedCategory Cat.{w, u} C]
    {a b c : CategoryTheory.CatEnriched C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} (eta : f ⟶ f') (theta : g ⟶ g') :
    CategoryTheory.CatEnriched.hComp eta theta =
      (eComp Cat a b c).toFunctor.map (eta, theta) := by
  rfl

/-- In the self-enrichment of simplicial sets, postcomposition in the enriched Hom object is
the ordinary internal-Hom map. -/
theorem sset_eHomWhiskerLeft_eq_ihom_map
    (A : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y) :
    @eHomWhiskerLeft SSet.{u} _ _ SSet.{u} _
      (MonoidalClosed.enrichedOrdinaryCategorySelf SSet.{u}) A X Y f =
      (ihom A).map f := by
  exact MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft
    (C := SSet.{u}) A f

/-- Postcomposition with the forward map of a bicategorical adjoint equivalence is an
equivalence of ordinary hom-categories. -/
theorem bicategoricalEquivalence_postcomp_isEquivalence
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y) (A : SSet.QCat.{u}) :
    (Bicategory.postcomp A e.hom).IsEquivalence := by
  let G := Bicategory.postcomp A e.inv
  let η :=
    (Bicategory.rightUnitorNatIso A X).symm ≪≫
      (Bicategory.postcomposing A X X).mapIso e.unit ≪≫
        (Bicategory.associatorNatIsoLeft A e.hom e.inv).symm
  let ε :=
    Bicategory.associatorNatIsoLeft A e.inv e.hom ≪≫
      (Bicategory.postcomposing A Y Y).mapIso e.counit ≪≫
        Bicategory.rightUnitorNatIso A Y
  exact Functor.IsEquivalence.mk' G η ε

local instance qcatHomCategory (X Y : SSet.QCat.{u}) : Category (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

/-- The category of strict-bicategory `1`-morphisms is obtained from the enriched
hom-category by transport along the ordinary/enriched Hom equivalence. -/
def qcatHomToEnrichedHom (X Y : SSet.QCat.{u}) :
    (X ⟶ Y) ⥤
      ((CategoryTheory.CatEnrichedOrdinary.toBase X) ⟶
        (CategoryTheory.CatEnrichedOrdinary.toBase Y)) where
  obj := CategoryTheory.CatEnrichedOrdinary.homEquiv
  map := CategoryTheory.CatEnrichedOrdinary.Hom.base

instance qcatHomToEnrichedHom_faithful (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).Faithful where
  map_injective h := CategoryTheory.CatEnrichedOrdinary.Hom.ext _ _ h

instance qcatHomToEnrichedHom_full (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).Full where
  map_surjective f := ⟨CategoryTheory.CatEnrichedOrdinary.Hom.mk f, rfl⟩

instance qcatHomToEnrichedHom_essSurj (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).EssSurj where
  mem_essImage Z := by
    refine ⟨CategoryTheory.CatEnrichedOrdinary.homEquiv.symm Z, ?_⟩
    exact ⟨eqToIso (Equiv.apply_symm_apply
      CategoryTheory.CatEnrichedOrdinary.homEquiv Z)⟩

instance qcatHomToEnrichedHom_isEquivalence (X Y : SSet.QCat.{u}) :
    (qcatHomToEnrichedHom X Y).IsEquivalence where

private instance qcatTensorUnit_quasicategory :
    SSet.Quasicategory (𝟙_ SSet.{u}) := by
  apply SSet.quasicategory_of_hasLiftingProperty _
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u}))
  intro n i h₀ hₙ
  have heq : (SemiCartesianMonoidalCategory.isTerminalTensorUnit
      (C := SSet.{u})).from (𝟙_ SSet) = 𝟙 (𝟙_ SSet) :=
    (SemiCartesianMonoidalCategory.isTerminalTensorUnit (C := SSet.{u})).hom_ext _ _
  rw [heq]
  infer_instance

private def qcatTensorUnit : SSet.QCat.{u} :=
  ⟨𝟙_ SSet, qcatTensorUnit_quasicategory⟩

/-- The strict-bicategory Hom from the tensor unit is explicitly equivalent to the
homotopy category of a quasicategory. -/
noncomputable def qcatUnitHomEquivalence (X : SSet.QCat.{u}) :
    (qcatTensorUnit ⟶ X) ≌ SSet.hoFunctor.obj X.obj :=
  (qcatHomToEnrichedHom qcatTensorUnit X).asEquivalence |>.trans
    (Cat.equivOfIso (SSet.hoFunctor.mapIso
      (MonoidalClosed.unitIsoSelf (C := SSet.{u}) (X := X.obj))))


/-- Transporting enrichment carries enriched postcomposition to the image of the original
postcomposition. -/
theorem transportEnrichment_eHomWhiskerLeft
    {V : Type v} [Category V] [MonoidalCategory V]
    {W : Type w} [Category W] [MonoidalCategory W]
    (F : V ⥤ W) [F.LaxMonoidal]
    (C : Type u) [Category C] [EnrichedOrdinaryCategory V C]
    (e : ∀ v : V, (𝟙_ V ⟶ v) ≃ (𝟙_ W ⟶ F.obj v))
    (h : ∀ v : V, ∀ f : 𝟙_ V ⟶ v,
      e v f = Functor.LaxMonoidal.ε F ≫ F.map f)
    (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    @eHomWhiskerLeft W _ _ (TransportEnrichment F C) _
      (TransportEnrichment.enrichedOrdinaryCategory (F := F) C e h)
      (show TransportEnrichment F C from X) Y Y' g =
      F.map (@eHomWhiskerLeft V _ _ C _ _ X Y Y' g) := by
  letI : EnrichedOrdinaryCategory W (TransportEnrichment F C) :=
    TransportEnrichment.enrichedOrdinaryCategory (F := F) C e h
  dsimp [eHomWhiskerLeft]
  rw [TransportEnrichment.eComp_eq]
  dsimp +instances [TransportEnrichment.enrichedOrdinaryCategory]
  rw [show (@eHomEquiv W _ _ (TransportEnrichment F C) _ _
      (show TransportEnrichment F C from Y)
      (show TransportEnrichment F C from Y') g) =
      Functor.LaxMonoidal.ε F ≫ F.map ((eHomEquiv V) g) by
    exact h _ _]
  change (ρ_ (F.obj (X ⟶[V] Y))).inv ≫
      F.obj (X ⟶[V] Y) ◁
        (Functor.LaxMonoidal.ε F ≫ F.map ((eHomEquiv V) g)) ≫
      Functor.LaxMonoidal.μ F (X ⟶[V] Y) (Y ⟶[V] Y') ≫
        F.map (eComp V X Y Y') =
      F.map ((ρ_ (X ⟶[V] Y)).inv ≫
        (X ⟶[V] Y) ◁ (eHomEquiv V) g ≫ eComp V X Y Y')
  rw [F.map_comp, F.map_comp]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← id_tensorHom]
  rw [← id_tensorHom]
  rw [← F.map_id]
  rw [Functor.LaxMonoidal.μ_natural_assoc]
  rw [tensorHom_def_assoc, whiskerRight_id_assoc, Iso.inv_hom_id_assoc]
  rw [Functor.LaxMonoidal.right_unitality_inv_assoc]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- In the Cat-enrichment of quasicategories, postcomposition is the homotopy-category
image of the internal-Hom postcomposition map. -/
theorem qcat_eHomWhiskerLeft_eq_hoFunctor_map_ihom
    (A : SSet.QCat.{u}) {X Y : SSet.QCat.{u}} (f : X ⟶ Y) :
    @eHomWhiskerLeft Cat _ _ SSet.QCat _ _ A X Y f =
      SSet.hoFunctor.map ((ihom A.obj).map f.hom) := by
  rw [transportEnrichment_eHomWhiskerLeft
    (F := SSet.hoFunctor) SSet.QCat
    (SSet.hoFunctor.unitHomEquiv · |>.trans <| Functor.equivCatHom _ _)
    (congrArg (Functor.toCatHom) <| SSet.hoFunctor.unitHomEquiv_eq · ·)]
  change SSet.hoFunctor.map
      (@eHomWhiskerLeft SSet _ _ SSet _ _ A.obj X.obj Y.obj f.hom) = _
  rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit equivalence from maps out of the tensor unit to the homotopy category
intertwines bicategorical postcomposition with the homotopy-category functor. -/
theorem qcatUnitHomEquivalence_postcomp
    {X Y : SSet.QCat.{u}} (f : X ⟶ Y) :
    Bicategory.postcomp qcatTensorUnit f ⋙ (qcatUnitHomEquivalence Y).functor =
      (qcatUnitHomEquivalence X).functor ⋙ (SSet.hoFunctor.map f.hom).toFunctor := by
  refine CategoryTheory.Functor.ext
    (F := Bicategory.postcomp qcatTensorUnit f ⋙ (qcatUnitHomEquivalence Y).functor)
    (G := (qcatUnitHomEquivalence X).functor ⋙
      (SSet.hoFunctor.map f.hom).toFunctor) (fun g ↦ ?_) ?_
  · rfl
  intro g g' α
  dsimp [qcatUnitHomEquivalence, qcatHomToEnrichedHom,
    CategoryTheory.Equivalence.trans, Cat.equivOfIso, CategoryTheory.Functor.asEquivalence]
  change (SSet.hoFunctor.mapIso
      (MonoidalClosed.unitIsoSelf (C := SSet.{u}) (X := Y.obj))).hom.toFunctor.map
        (CategoryTheory.CatEnrichedOrdinary.Hom.base
          (CategoryTheory.CatEnrichedOrdinary.hComp α
            (CategoryTheory.CatEnrichedOrdinary.Hom.mk
              (f := f) (g := f)
              (𝟙 (CategoryTheory.CatEnrichedOrdinary.homEquiv f))))) = _
  have hcomp := catEnrichedOrdinary_base_hComp α
    (CategoryTheory.CatEnrichedOrdinary.Hom.mk
      (f := f) (g := f)
      (𝟙 (CategoryTheory.CatEnrichedOrdinary.homEquiv f)))
  rw [hcomp]
  simp only [CategoryTheory.CatEnrichedOrdinary.base_mk, Functor.map_comp]
  rw [show CategoryTheory.CatEnriched.hComp
      (CategoryTheory.CatEnrichedOrdinary.Hom.base α)
      (𝟙 (CategoryTheory.CatEnrichedOrdinary.homEquiv f)) =
        (@eHomWhiskerLeft Cat _ _ SSet.QCat _ _ qcatTensorUnit X Y f).toFunctor.map
          (CategoryTheory.CatEnrichedOrdinary.Hom.base α) by rfl]
  rw! (castMode := .all) [qcat_eHomWhiskerLeft_eq_hoFunctor_map_ihom qcatTensorUnit f]
  congr 1
  have hn := congrArg SSet.hoFunctor.map
    ((MonoidalClosed.unitNatIso (C := SSet.{u})).inv.naturality f.hom)
  simp only [SSet.hoFunctor.map_comp] at hn
  dsimp [qcatTensorUnit, MonoidalClosed.unitIsoSelf, CategoryTheory.Functor.mapIso]
  simp
  apply eq_of_heq
  have hn' := congrArg CategoryTheory.Cat.Hom.toFunctor hn
  have hh := CategoryTheory.Functor.hcongr_hom hn'
    (CategoryTheory.CatEnrichedOrdinary.Hom.base α)
  simp [Functor.comp_map] at hh
  exact HEq.trans (by
    congr
    apply eq_of_heq
    exact eqRec_heq_iff_heq.mpr HEq.rfl) (HEq.trans (heq_of_eq hh) (by rfl))

set_option backward.isDefEq.respectTransparency false in
/-- A bicategorical equivalence of quasicategories induces an equivalence on homotopy
categories. -/
theorem IsBicategoricalEquivalence.hoFunctor_isEquivalence
    {X Y : SSet.QCat.{u}} {f : X ⟶ Y} (hf : IsBicategoricalEquivalence f) :
    (SSet.hoFunctor.map f.hom).toFunctor.IsEquivalence := by
  obtain ⟨e, rfl⟩ := hf
  haveI : (Bicategory.postcomp qcatTensorUnit e.hom).IsEquivalence :=
    bicategoricalEquivalence_postcomp_isEquivalence e qcatTensorUnit
  haveI : (qcatUnitHomEquivalence X).functor.IsEquivalence := inferInstance
  haveI : (qcatUnitHomEquivalence Y).functor.IsEquivalence := inferInstance
  haveI : (Bicategory.postcomp qcatTensorUnit e.hom ⋙
      (qcatUnitHomEquivalence Y).functor).IsEquivalence := inferInstance
  haveI : ((qcatUnitHomEquivalence X).functor ⋙
      (SSet.hoFunctor.map e.hom.hom).toFunctor).IsEquivalence := by
    rw [← qcatUnitHomEquivalence_postcomp e.hom]
    infer_instance
  exact CategoryTheory.Functor.isEquivalence_of_comp_left
    (qcatUnitHomEquivalence X).functor (SSet.hoFunctor.map e.hom.hom).toFunctor

/-- Regard a categorical nerve as a quasicategory target. -/
private def categoricalNerveQCat (E : Cat.{u, u}) : SSet.QCat.{u} :=
  ⟨nerveFunctor.obj E, by
    change SSet.Quasicategory (CategoryTheory.nerve E)
    infer_instance⟩

/-- A mapping-quasicategory localization induces, for every ordinary target category,
an equivalence from functors out of its homotopy category to the ordinary full
subcategory selected by marked-edge inversion. -/
noncomputable def mappingLocalizationOrdinaryEquivalence
    {A L : SSet.QCat.{u}} {W : EdgeMarking A.obj} {ell : A ⟶ L}
    (h : MappingQuasicategoryLocalizationProperty W ell) (E : Cat.{u, u}) :
    ((ihom (SSet.hoFunctor.obj L.obj)).obj E) ≌
      (PulledRelativeFunctorProperty W E).FullSubcategory := by
  let d := (h.universal (categoricalNerveQCat E)).some
  haveI : (SSet.hoFunctor.map d.comparison).toFunctor.IsEquivalence :=
    IsBicategoricalEquivalence.hoFunctor_isEquivalence d.isEquivalence
  exact (internalHomNerveHomotopyEquivalence L.obj E).symm |>.trans
    (SSet.hoFunctor.map d.comparison).toFunctor.asEquivalence |>.trans
      (relativeInternalHomNerveHomotopyEquivalence W E)

/-- Maps between nerves are exactly ordinary functors.  This is the fully-faithful
starting point for comparing the mapping localization with its ordinary truncation. -/
noncomputable def nerveFunctorCategoryEquiv (C D : Type u)
    [Category.{u} C] [Category.{u} D] :
    (C ⥤ D) ≃
      (nerveFunctor.obj (Cat.of C) ⟶ nerveFunctor.obj (Cat.of D)) :=
  (Functor.equivCatHom C D).trans nerveFunctor.fullyfaithful.homEquiv

@[simp]
theorem nerveFunctorCategoryEquiv_apply (C D : Type u)
    [Category.{u} C] [Category.{u} D] (F : C ⥤ D) :
    nerveFunctorCategoryEquiv C D F =
      nerveFunctor.map F.toCatHom :=
  rfl

end Infinity
end LeanLCAExactChallenge
