import LeanLCAExactChallenge.Infinity.FunctorQuasicategory
import LeanLCAExactChallenge.Infinity.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# Honest infinity-localization specifications available in pinned mathlib

This file deliberately separates inversion of marked edges, a bicategorical
`2`-localization property, and a mapping-quasicategory localization property.
It does not assert that any concrete equivalence-forcing presentation satisfies
either universal property.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open Opposite
open Simplicial

/-- A marking of a simplicial set is a class of edges containing all identity edges. -/
structure EdgeMarking (X : SSet.{u}) where
  marked : X _⦋1⦌ → Prop
  id_marked : ∀ x : X _⦋0⦌, marked (SSet.Edge.id x).edge

/-- The marking of an ordinary relative nerve by its specified weak equivalences. -/
def relativeNerveEdgeMarking {C : Type u} [Category.{v} C]
    (R : RelativeCategoryData C) : EdgeMarking (CategoryTheory.nerve C) where
  marked e := ∃ (X Y : C) (f : X ⟶ Y),
    R.weakEquivalences f ∧ e = (CategoryTheory.nerve.edgeMk f).edge
  id_marked x := by
    refine ⟨CategoryTheory.nerveEquiv x, CategoryTheory.nerveEquiv x,
      𝟙 _, R.weakEquivalences.id_mem _, ?_⟩
    rw [CategoryTheory.nerve.edgeMk_id]
    simp

/-- A simplicial map inverts a marking when every marked edge becomes an equivalence edge. -/
def InvertsMarkedEdges {X Y : SSet.{u}} (W : EdgeMarking X) (F : X ⟶ Y) : Prop :=
  ∀ e : X _⦋1⦌, W.marked e → EdgeIsEquivalence ((SSet.Edge.mk' e).map F)

/-- The map represented by a vertex of a simplicial internal hom. -/
def internalHomVertexMap (X Y : SSet.{u})
    (v : ((ihom X).obj Y) _⦋0⦌) : X ⟶ Y :=
  MonoidalClosed.uncurry' (SSet.unitHomEquiv ((ihom X).obj Y) |>.symm v)

/-- The full subcomplex of `X` spanned by the vertices satisfying `P`. -/
def fullSubcomplexOnVertices (X : SSet.{u}) (P : X _⦋0⦌ → Prop) : X.Subcomplex where
  obj U := {s | ∀ i : Fin (U.unop.len + 1),
    P (X.map (SimplexCategory.const ⦋0⦌ U.unop i).op s)}
  map {U V} f s hs j := by
    rw [← Functor.map_comp_apply]
    exact hs (f.unop.toOrderHom j)

@[simp]
theorem mem_fullSubcomplexOnVertices_iff (X : SSet.{u})
    (P : X _⦋0⦌ → Prop) {U : SimplexCategoryᵒᵖ} (s : X.obj U) :
    s ∈ (fullSubcomplexOnVertices X P).obj U ↔
      ∀ i : Fin (U.unop.len + 1),
        P (X.map (SimplexCategory.const ⦋0⦌ U.unop i).op s) :=
  Iff.rfl

/-- Vertices of the full subcomplex are exactly the vertices satisfying `P`. -/
@[simp]
theorem mem_fullSubcomplexOnVertices_zero_iff (X : SSet.{u})
    (P : X _⦋0⦌ → Prop) (v : X _⦋0⦌) :
    v ∈ (fullSubcomplexOnVertices X P).obj (op ⦋0⦌) ↔ P v := by
  constructor
  · intro h
    simpa using h 0
  · intro h i
    change Fin 1 at i
    obtain rfl := Subsingleton.elim i 0
    simpa using h

/-- The full mapping subcomplex spanned by functors which invert the marking. -/
def relativeInternalHom {X : SSet.{u}} (W : EdgeMarking X) (Q : SSet.{u}) :
    ((ihom X).obj Q).Subcomplex :=
  fullSubcomplexOnVertices ((ihom X).obj Q) fun v =>
    InvertsMarkedEdges W (internalHomVertexMap X Q v)

/-- The selected vertices are precisely the marking-inverting maps. -/
@[simp]
theorem mem_relativeInternalHom_zero_iff {X : SSet.{u}}
    (W : EdgeMarking X) (Q : SSet.{u})
    (v : ((ihom X).obj Q) _⦋0⦌) :
    v ∈ (relativeInternalHom W Q).obj (op ⦋0⦌) ↔
      InvertsMarkedEdges W (internalHomVertexMap X Q v) :=
  mem_fullSubcomplexOnVertices_zero_iff _ _ _

/-- A full simplicial subcomplex on an arbitrary class of vertices is a quasicategory. -/
theorem fullSubcomplexOnVertices_quasicategory (X : SSet.{u})
    (P : X _⦋0⦌ → Prop) [SSet.Quasicategory X] :
    SSet.Quasicategory (fullSubcomplexOnVertices X P : SSet.{u}) where
  hornFilling' n i σ₀ h₀ hₙ := by
    let A := fullSubcomplexOnVertices X P
    obtain ⟨σ, hσ⟩ := SSet.Quasicategory.hornFilling h₀ hₙ (σ₀ ≫ A.ι)
    have hRange : SSet.Subcomplex.range σ ≤ A := by
      rintro U _ ⟨s, rfl⟩ j
      let vertex : (Λ[n + 2, i] : SSet.{u}).obj (op ⦋0⦌) :=
        ⟨(Δ[n + 2] : SSet.{u}).map
            (SimplexCategory.const ⦋0⦌ U.unop j).op s,
          by rw [SSet.horn_obj_zero n i]; trivial⟩
      have hp : P ((σ₀.app (op ⦋0⦌) vertex).val) :=
        (mem_fullSubcomplexOnVertices_zero_iff X P _).1
          (σ₀.app (op ⦋0⦌) vertex).property
      have hvertex := congrArg (fun f => f.app (op ⦋0⦌) vertex) hσ
      rw [← NatTrans.naturality_apply σ
        (SimplexCategory.const ⦋0⦌ U.unop j).op s]
      change P (σ.app (op ⦋0⦌) vertex.val)
      change (σ₀.app (op ⦋0⦌) vertex).val =
        σ.app (op ⦋0⦌) vertex.val at hvertex
      rw [← hvertex]
      exact hp
    refine ⟨SSet.Subcomplex.lift σ hRange, ?_⟩
    apply (cancel_mono A.ι).1
    rw [Category.assoc, SSet.Subcomplex.lift_ι]
    exact hσ

/-- Relative mapping objects inherit quasicategory closure from the ambient internal Hom. -/
theorem relativeInternalHom_quasicategory {X : SSet.{u}} (W : EdgeMarking X)
    (Q : SSet.{u}) [SSet.Quasicategory ((ihom X).obj Q)] :
    SSet.Quasicategory (relativeInternalHom W Q : SSet.{u}) :=
  fullSubcomplexOnVertices_quasicategory _ _

/-- In mathlib v4.31, relative mapping objects into a quasicategory are unconditionally
quasicategories. -/
theorem relativeInternalHom_quasicategory_of_quasicategory
    {X Q : SSet.{u}} [SSet.Quasicategory Q] (W : EdgeMarking X) :
    SSet.Quasicategory (relativeInternalHom W Q : SSet.{u}) := by
  letI : SSet.Quasicategory ((ihom X).obj Q) := quasicategory_ihom
  exact relativeInternalHom_quasicategory W Q

/-- Precomposition on simplicial internal homs. -/
def internalHomPrecomp {X L : SSet.{u}} (ell : X ⟶ L) (Q : SSet.{u}) :
    (ihom L).obj Q ⟶ (ihom X).obj Q :=
  (MonoidalClosed.pre ell).app Q

/-- Precomposition respects composition of simplicial maps. -/
@[reassoc (attr := simp)]
theorem internalHomPrecomp_comp {X Y L : SSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ L) (Q : SSet.{u}) :
    internalHomPrecomp g Q ≫ internalHomPrecomp f Q =
      internalHomPrecomp (f ≫ g) Q := by
  simp [internalHomPrecomp]

private lemma unitHomEquiv_symm_natural {A B : SSet.{u}}
    (F : A ⟶ B) (a : A _⦋0⦌) :
    (SSet.unitHomEquiv B).symm (F.app _ a) =
      (SSet.unitHomEquiv A).symm a ≫ F := by
  ext U x
  obtain ⟨⟩ := x
  dsimp [SSet.unitHomEquiv]
  rw [← NatTrans.naturality_apply]

/-- A vertex of an internal hom obtained by precomposition represents the
corresponding composite simplicial map. -/
lemma internalHomVertexMap_precomp {X L Q : SSet.{u}}
    (ell : X ⟶ L) (v : ((ihom L).obj Q) _⦋0⦌) :
    internalHomVertexMap X Q ((internalHomPrecomp ell Q).app _ v) =
      ell ≫ internalHomVertexMap L Q v := by
  rw [internalHomVertexMap, internalHomVertexMap, internalHomPrecomp,
    unitHomEquiv_symm_natural]
  simp only [MonoidalClosed.uncurry', MonoidalClosed.uncurry_pre_app]
  simp

/-- Precomposition by a marking-inverting map lands in the relative mapping subcomplex. -/
def internalHomPrecompToRelative {X L : SSet.{u}}
    (W : EdgeMarking X) (ell : X ⟶ L) (Q : SSet.{u})
    (hEll : InvertsMarkedEdges W ell) :
    (ihom L).obj Q ⟶ (relativeInternalHom W Q : SSet.{u}) :=
  SSet.Subcomplex.lift (internalHomPrecomp ell Q) (by
    rintro U _ ⟨s, rfl⟩
    change ∀ i : Fin (U.unop.len + 1),
      InvertsMarkedEdges W
        (internalHomVertexMap X Q
          (((ihom X).obj Q).map
            (SimplexCategory.const ⦋0⦌ U.unop i).op
            ((internalHomPrecomp ell Q).app U s)))
    intro i
    rw [← NatTrans.naturality_apply (internalHomPrecomp ell Q)
      (SimplexCategory.const ⦋0⦌ U.unop i).op s]
    rw [internalHomVertexMap_precomp]
    intro e he
    exact (hEll e he).map (internalHomVertexMap L Q
      (((ihom L).obj Q).map
        (SimplexCategory.const ⦋0⦌ U.unop i).op s)))

/-- Including the relative factor recovers ordinary internal-hom precomposition. -/
@[reassoc (attr := simp)]
theorem internalHomPrecompToRelative_comp_inclusion {X L : SSet.{u}}
    (W : EdgeMarking X) (ell : X ⟶ L) (Q : SSet.{u})
    (hEll : InvertsMarkedEdges W ell) :
    internalHomPrecompToRelative W ell Q hEll ≫ (relativeInternalHom W Q).ι =
      internalHomPrecomp ell Q := by
  apply SSet.Subcomplex.lift_ι

/-- The object property selecting marking-inverting maps in a bicategorical hom-category. -/
def InvertingHomotopyFunctorProperty {X : SSet.{u}}
    (W : EdgeMarking X) (Q : SSet.{u}) :
    ObjectProperty (SSet.hoFunctor.obj ((ihom X).obj Q)) :=
  fun
    z : SSet.hoFunctor.obj ((ihom X).obj Q) =>
      InvertsMarkedEdges W
        (internalHomVertexMap X Q
          (SSet.hoFunctor.obj.equiv ((ihom X).obj Q) z))

/-- The full subcategory of the bicategorical hom-category on marking-inverting maps. -/
abbrev InvertingHomotopyFunctorCategory {X : SSet.{u}}
    (W : EdgeMarking X) (Q : SSet.{u}) :=
  (InvertingHomotopyFunctorProperty W Q).FullSubcategory

/-- The ordinary homotopy-category functor induced by internal-hom precomposition. -/
abbrev homotopyPrecomp {X L : SSet.{u}} (ell : X ⟶ L) (Q : SSet.{u}) :=
  (SSet.hoFunctor.map (internalHomPrecomp ell Q)).toFunctor

/-- Inclusion of the full bicategorical hom-subcategory of marking-inverting maps. -/
abbrev invertingHomotopyFunctorInclusion {X : SSet.{u}}
    (W : EdgeMarking X) (Q : SSet.{u}) :
    InvertingHomotopyFunctorCategory W Q ⥤
      SSet.hoFunctor.obj ((ihom X).obj Q) :=
  ObjectProperty.ι (InvertingHomotopyFunctorProperty W Q)

/-- Data expressing the bicategorical localization comparison at one target. -/
structure BicategoricalTwoLocalizationAt
    {A L : SSet.QCat.{u}} (W : EdgeMarking A.obj) (ell : A ⟶ L)
    (Q : SSet.QCat.{u}) where
  comparison :
    SSet.hoFunctor.obj ((ihom L.obj).obj Q.obj) ⥤
      InvertingHomotopyFunctorCategory W Q.obj
  comparison_comp_inclusion :
    comparison ⋙ invertingHomotopyFunctorInclusion W Q.obj =
      homotopyPrecomp ell.hom Q.obj
  isEquivalence : comparison.IsEquivalence

/--
The explicitly `2`-categorical localization property: precomposition is an equivalence
from the bicategorical hom-category into the full subcategory on marking-inverting maps.

This only controls homotopy categories of mapping objects. It is not by itself the full
mapping-quasicategory universal property.
-/
structure BicategoricalTwoLocalizationProperty
    {A L : SSet.QCat.{u}} (W : EdgeMarking A.obj) (ell : A ⟶ L) : Prop where
  inverts : InvertsMarkedEdges W ell.hom
  universal : ∀ Q : SSet.QCat.{u}, Nonempty (BicategoricalTwoLocalizationAt W ell Q)

/-- Bundle a simplicial internal hom as a quasicategory from explicit evidence. -/
def internalHomQCat (X Q : SSet.{u})
    (h : SSet.Quasicategory ((ihom X).obj Q)) : SSet.QCat.{u} :=
  ⟨(ihom X).obj Q, h⟩

/-- Bundle the full relative mapping subcomplex using explicit quasicategory evidence. -/
def relativeInternalHomQCat {X : SSet.{u}} (W : EdgeMarking X) (Q : SSet.{u})
    (h : SSet.Quasicategory (relativeInternalHom W Q : SSet.{u})) :
    SSet.QCat.{u} :=
  ⟨relativeInternalHom W Q, h⟩

/--
Data expressing the full mapping-quasicategory comparison at one target.

The source and target fields remain explicit so the standalone specification records the exact
quasicategory structures used by its comparison. Mathlib v4.31 supplies canonical inhabitants
for both fields.
-/
structure MappingQuasicategoryLocalizationAt
    {A L : SSet.QCat.{u}} (W : EdgeMarking A.obj) (ell : A ⟶ L)
    (Q : SSet.QCat.{u}) where
  sourceQuasicategory :
    SSet.Quasicategory ((ihom L.obj).obj Q.obj)
  targetQuasicategory :
    SSet.Quasicategory (relativeInternalHom W Q.obj : SSet.{u})
  comparison :
    (ihom L.obj).obj Q.obj ⟶ (relativeInternalHom W Q.obj : SSet.{u})
  comparison_comp_inclusion :
    comparison ≫ (relativeInternalHom W Q.obj).ι =
      internalHomPrecomp ell.hom Q.obj
  isEquivalence :
    IsBicategoricalEquivalence
      (ObjectProperty.homMk comparison :
        internalHomQCat L.obj Q.obj sourceQuasicategory ⟶
          relativeInternalHomQCat W Q.obj targetQuasicategory)

namespace MappingQuasicategoryLocalizationAt

/-- Build the mapping localization data from the canonical relative factor. -/
def ofCanonical {A L : SSet.QCat.{u}}
    (W : EdgeMarking A.obj) (ell : A ⟶ L) (Q : SSet.QCat.{u})
    (hEll : InvertsMarkedEdges W ell.hom)
    [SSet.Quasicategory ((ihom A.obj).obj Q.obj)]
    (sourceQuasicategory :
      SSet.Quasicategory ((ihom L.obj).obj Q.obj))
    (isEquivalence :
      IsBicategoricalEquivalence
        (ObjectProperty.homMk
          (internalHomPrecompToRelative W ell.hom Q.obj hEll) :
            internalHomQCat L.obj Q.obj sourceQuasicategory ⟶
              relativeInternalHomQCat W Q.obj
                (relativeInternalHom_quasicategory W Q.obj))) :
    MappingQuasicategoryLocalizationAt W ell Q where
  sourceQuasicategory := sourceQuasicategory
  targetQuasicategory := relativeInternalHom_quasicategory W Q.obj
  comparison := internalHomPrecompToRelative W ell.hom Q.obj hEll
  comparison_comp_inclusion :=
    internalHomPrecompToRelative_comp_inclusion W ell.hom Q.obj hEll
  isEquivalence := isEquivalence

/-- Build the canonical mapping data using mathlib v4.31's unconditional internal-Hom closure. -/
def ofCanonicalUnconditional {A L : SSet.QCat.{u}}
    (W : EdgeMarking A.obj) (ell : A ⟶ L) (Q : SSet.QCat.{u})
    (hEll : InvertsMarkedEdges W ell.hom)
    (isEquivalence :
      IsBicategoricalEquivalence
        (ObjectProperty.homMk
          (internalHomPrecompToRelative W ell.hom Q.obj hEll) :
            internalHomQCat L.obj Q.obj
                (@quasicategory_ihom L.obj Q.obj Q.property) ⟶
              relativeInternalHomQCat W Q.obj
                (@relativeInternalHom_quasicategory_of_quasicategory
                  A.obj Q.obj Q.property W))) :
    MappingQuasicategoryLocalizationAt W ell Q := by
  letI : SSet.Quasicategory Q.obj := Q.property
  exact ofCanonical W ell Q hEll
    (@quasicategory_ihom L.obj Q.obj Q.property) isEquivalence

end MappingQuasicategoryLocalizationAt

/--
The mapping-quasicategory localization specification. For every quasicategory `Q`, canonical
precomposition must factor through the full subcomplex of marking-inverting maps and induce
an equivalence of quasicategories.

This is a specification only. No concrete localization candidate is given an instance or a
theorem asserting this property.
-/
structure MappingQuasicategoryLocalizationProperty
    {A L : SSet.QCat.{u}} (W : EdgeMarking A.obj) (ell : A ⟶ L) : Prop where
  inverts : InvertsMarkedEdges W ell.hom
  universal : ∀ Q : SSet.QCat.{u},
    Nonempty (MappingQuasicategoryLocalizationAt W ell Q)

end Infinity
end LeanLCAExactChallenge
