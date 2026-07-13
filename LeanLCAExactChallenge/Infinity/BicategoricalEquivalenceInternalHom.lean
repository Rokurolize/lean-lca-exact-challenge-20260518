import LeanLCAExactChallenge.Infinity.InnerAnodyneMapping
import LeanLCAExactChallenge.Infinity.OrdinaryLocalizationBridge

/-!
# Internal homs preserve bicategorical equivalences in the source

A bicategorical equivalence of quasicategories induces a bicategorical equivalence on functor quasicategories by precomposition. Consequently, the full mapping-quasicategory localization property transfers across a bicategorical equivalence of localization carriers.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.EnrichedCategory
  CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped MonoidalCategory MonoidalClosed Bicategory
open Simplicial Opposite

local instance qcatHomCategory' (X Y : SSet.QCat.{u}) : Category (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

private lemma unitHomEquiv_symm_natural' {A B : SSet.{u}}
    (F : A ⟶ B)
    (a : A.obj (op (SimplexCategory.mk 0))) :
    (SSet.unitHomEquiv B).symm (F.app _ a) =
      (SSet.unitHomEquiv A).symm a ≫ F := by
  ext U x
  obtain ⟨⟩ := x
  dsimp [SSet.unitHomEquiv]
  rw [← NatTrans.naturality_apply]

/-- Represent an invertible `2`-cell by an edge in the corresponding functor quasicategory. -/
noncomputable def internalHomEdgeOfTwoIso
    {X Y : SSet.QCat.{u}} {f g : X ⟶ Y} (a : f ≅ g) :
    SSet.Edge
      (SSet.unitHomEquiv ((ihom X.obj).obj Y.obj)
        (MonoidalClosed.curry' f.hom))
      (SSet.unitHomEquiv ((ihom X.obj).obj Y.obj)
        (MonoidalClosed.curry' g.hom)) := by
  letI : SSet.Quasicategory ((ihom X.obj).obj Y.obj) :=
    @quasicategory_ihom X.obj Y.obj Y.property
  let m := CategoryTheory.CatEnrichedOrdinary.Hom.base a.hom
  let s := homotopyCategory_homMk_surjective_of_quasicategory
    (V := (SSet.truncation 2).obj ((ihom X.obj).obj Y.obj)) m
  exact SSet.Edge.ofTruncated s.choose

theorem internalHomEdgeOfTwoIso_isEquivalence
    {X Y : SSet.QCat.{u}} {f g : X ⟶ Y} (a : f ≅ g) :
    EdgeIsEquivalence (internalHomEdgeOfTwoIso a) := by
  letI : SSet.Quasicategory ((ihom X.obj).obj Y.obj) :=
    @quasicategory_ihom X.obj Y.obj Y.property
  let m := CategoryTheory.CatEnrichedOrdinary.Hom.base a.hom
  have hm : IsIso m := by
    refine ⟨⟨CategoryTheory.CatEnrichedOrdinary.Hom.base a.inv, ?_, ?_⟩⟩
    · rw [← CategoryTheory.CatEnrichedOrdinary.Hom.base_comp]
      exact (congrArg CategoryTheory.CatEnrichedOrdinary.Hom.base
        a.hom_inv_id).trans
          (CategoryTheory.CatEnrichedOrdinary.Hom.base_id f)
    · rw [← CategoryTheory.CatEnrichedOrdinary.Hom.base_comp]
      exact (congrArg CategoryTheory.CatEnrichedOrdinary.Hom.base
        a.inv_hom_id).trans
          (CategoryTheory.CatEnrichedOrdinary.Hom.base_id g)
  let s := homotopyCategory_homMk_surjective_of_quasicategory
    (V := (SSet.truncation 2).obj ((ihom X.obj).obj Y.obj)) m
  change IsIso (edgeHomotopyClass (SSet.Edge.ofTruncated s.choose))
  change IsIso (SSet.Truncated.HomotopyCategory.homMk s.choose)
  rw [s.choose_spec]
  exact hm

/-- A self-map acts contravariantly on the associated functor quasicategory. -/
def internalHomPrecompositionAction (X Q : SSet.{u}) :
    (ihom X).obj X ⟶
      (ihom ((ihom X).obj Q)).obj ((ihom X).obj Q) :=
  MonoidalClosed.curry
    ((β_ ((ihom X).obj Q) ((ihom X).obj X)).hom ≫
      MonoidalClosed.comp X X Q)

lemma internalHomPrecompositionAction_vertex
    (X Q : SSet.{u}) (f : X ⟶ X) :
    (internalHomPrecompositionAction X Q).app (op (SimplexCategory.mk 0))
        (SSet.unitHomEquiv ((ihom X).obj X)
          (MonoidalClosed.curry' f)) =
      SSet.unitHomEquiv
        ((ihom ((ihom X).obj Q)).obj ((ihom X).obj Q))
        (MonoidalClosed.curry' (internalHomPrecomp f Q)) := by
  apply (SSet.unitHomEquiv
    ((ihom ((ihom X).obj Q)).obj ((ihom X).obj Q))).symm.injective
  rw [Equiv.symm_apply_apply, unitHomEquiv_symm_natural']
  simp only [internalHomPrecompositionAction, internalHomPrecomp]
  rw [Equiv.symm_apply_apply, ← MonoidalClosed.curry_natural_left]
  unfold MonoidalClosed.curry'
  congr 1

/-- Apply precomposition to an invertible `2`-cell represented by an internal-hom edge. -/
noncomputable def internalHomPrecompEdgeOfTwoIso
    {X : SSet.QCat.{u}} {f g : X ⟶ X} (a : f ≅ g)
    (Q : SSet.QCat.{u}) :
    SSet.Edge
      (SSet.unitHomEquiv
        ((ihom ((ihom X.obj).obj Q.obj)).obj ((ihom X.obj).obj Q.obj))
        (MonoidalClosed.curry' (internalHomPrecomp f.hom Q.obj)))
      (SSet.unitHomEquiv
        ((ihom ((ihom X.obj).obj Q.obj)).obj ((ihom X.obj).obj Q.obj))
        (MonoidalClosed.curry' (internalHomPrecomp g.hom Q.obj))) :=
  SSet.Edge.castEndpoints
    (internalHomPrecompositionAction_vertex X.obj Q.obj f.hom).symm
    (internalHomPrecompositionAction_vertex X.obj Q.obj g.hom).symm
    ((internalHomEdgeOfTwoIso a).map
      (internalHomPrecompositionAction X.obj Q.obj))

theorem internalHomPrecompEdgeOfTwoIso_isEquivalence
    {X : SSet.QCat.{u}} {f g : X ⟶ X} (a : f ≅ g)
    (Q : SSet.QCat.{u}) :
    EdgeIsEquivalence (internalHomPrecompEdgeOfTwoIso a Q) :=
  (internalHomEdgeOfTwoIso_isEquivalence a).map
      (internalHomPrecompositionAction X.obj Q.obj) |>.castEndpoints
        (internalHomPrecompositionAction_vertex X.obj Q.obj f.hom).symm
        (internalHomPrecompositionAction_vertex X.obj Q.obj g.hom).symm

/-- Precomposition carries an invertible `2`-cell to an invertible `2`-cell. -/
noncomputable def internalHomPrecompTwoIso
    {X : SSet.QCat.{u}} {f g : X ⟶ X} (a : f ≅ g)
    (Q : SSet.QCat.{u}) :
    (ObjectProperty.homMk (internalHomPrecomp f.hom Q.obj) :
      internalHomQCat X.obj Q.obj
          (@quasicategory_ihom X.obj Q.obj Q.property) ⟶
        internalHomQCat X.obj Q.obj
          (@quasicategory_ihom X.obj Q.obj Q.property)) ≅
      ObjectProperty.homMk (internalHomPrecomp g.hom Q.obj) :=
  twoIsoOfInternalHomEquivalenceEdge
    (internalHomPrecompEdgeOfTwoIso a Q)
    (internalHomPrecompEdgeOfTwoIso_isEquivalence a Q)

/-- Precomposition by the forward map of an adjoint equivalence is an adjoint equivalence of functor quasicategories. -/
noncomputable def internalHomPrecompBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y)
    (Q : SSet.QCat.{u}) :
    Bicategory.Equivalence
      (internalHomQCat Y.obj Q.obj
        (@quasicategory_ihom Y.obj Q.obj Q.property))
      (internalHomQCat X.obj Q.obj
        (@quasicategory_ihom X.obj Q.obj Q.property)) := by
  let HY := internalHomQCat Y.obj Q.obj
    (@quasicategory_ihom Y.obj Q.obj Q.property)
  let HX := internalHomQCat X.obj Q.obj
    (@quasicategory_ihom X.obj Q.obj Q.property)
  let p : HY ⟶ HX :=
    ObjectProperty.homMk (internalHomPrecomp e.hom.hom Q.obj)
  let s : HX ⟶ HY :=
    ObjectProperty.homMk (internalHomPrecomp e.inv.hom Q.obj)
  let preYId : HY ⟶ HY :=
    ObjectProperty.homMk (internalHomPrecomp (𝟙 Y.obj) Q.obj)
  let preYCounit : HY ⟶ HY :=
    ObjectProperty.homMk
      (internalHomPrecomp (e.inv ≫ e.hom).hom Q.obj)
  let preXId : HX ⟶ HX :=
    ObjectProperty.homMk (internalHomPrecomp (𝟙 X.obj) Q.obj)
  let preXUnit : HX ⟶ HX :=
    ObjectProperty.homMk
      (internalHomPrecomp (e.hom ≫ e.inv).hom Q.obj)
  have hp_comp_s : p ≫ s = preYCounit := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    exact internalHomPrecomp_comp e.inv.hom e.hom.hom Q.obj
  have hs_comp_p : s ≫ p = preXUnit := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    exact internalHomPrecomp_comp e.hom.hom e.inv.hom Q.obj
  have hpreYId : preYId = 𝟙 HY := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    simp [preYId, internalHomPrecomp]
    rfl
  have hpreXId : preXId = 𝟙 HX := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    simp [preXId, internalHomPrecomp]
    rfl
  letI : Category (HY ⟶ HY) := SSet.QCat.bicategory.homCategory HY HY
  letI : Category (HX ⟶ HX) := SSet.QCat.bicategory.homCategory HX HX
  let counitPreIso : preYCounit ≅ preYId :=
    internalHomPrecompTwoIso e.counit Q
  let unitPreIso : preXId ≅ preXUnit :=
    internalHomPrecompTwoIso e.unit Q
  let unit : 𝟙 HY ≅ p ≫ s :=
    (eqToIso hpreYId.symm).trans
      (counitPreIso.symm.trans (eqToIso hp_comp_s.symm))
  let counit : s ≫ p ≅ 𝟙 HX :=
    (eqToIso hs_comp_p).trans
      (unitPreIso.symm.trans (eqToIso hpreXId))
  exact Bicategory.Equivalence.mkOfAdjointifyCounit unit counit

/-- Precomposition by a bicategorical equivalence is a bicategorical equivalence of functor quasicategories. -/
theorem internalHomPrecomp_isBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} {f : X ⟶ Y}
    (hf : IsBicategoricalEquivalence f) (Q : SSet.QCat.{u}) :
    IsBicategoricalEquivalence
      (ObjectProperty.homMk (internalHomPrecomp f.hom Q.obj) :
        internalHomQCat Y.obj Q.obj
            (@quasicategory_ihom Y.obj Q.obj Q.property) ⟶
          internalHomQCat X.obj Q.obj
            (@quasicategory_ihom X.obj Q.obj Q.property)) := by
  obtain ⟨e, rfl⟩ := hf
  exact ⟨internalHomPrecompBicategoricalEquivalence e Q, rfl⟩

/-- The full mapping-localization property transfers after postcomposing its carrier map with a bicategorical equivalence. -/
theorem MappingQuasicategoryLocalizationProperty.postcomp_of_bicategoricalEquivalence
    {A L D : SSet.QCat.{u}} (W : EdgeMarking A.obj)
    (ell : A ⟶ L) (b : L ⟶ D)
    (h : MappingQuasicategoryLocalizationProperty W ell)
    (hb : IsBicategoricalEquivalence b) :
    MappingQuasicategoryLocalizationProperty W (ell ≫ b) where
  inverts := by
    intro e he
    change EdgeIsEquivalence
      (((SSet.Edge.mk' e).map ell.hom).map b.hom)
    exact (h.inverts e he).map b.hom
  universal := by
    intro Q
    let d := (h.universal Q).some
    refine ⟨{
      sourceQuasicategory := @quasicategory_ihom D.obj Q.obj Q.property
      targetQuasicategory := d.targetQuasicategory
      comparison := internalHomPrecomp b.hom Q.obj ≫ d.comparison
      comparison_comp_inclusion := ?_
      isEquivalence := ?_ }⟩
    · rw [Category.assoc, d.comparison_comp_inclusion]
      exact internalHomPrecomp_comp ell.hom b.hom Q.obj
    · let c : internalHomQCat L.obj Q.obj
            (@quasicategory_ihom L.obj Q.obj Q.property) ⟶
          relativeInternalHomQCat W Q.obj d.targetQuasicategory :=
        ObjectProperty.homMk d.comparison
      change IsBicategoricalEquivalence
        ((ObjectProperty.homMk (internalHomPrecomp b.hom Q.obj) :
            internalHomQCat D.obj Q.obj
                (@quasicategory_ihom D.obj Q.obj Q.property) ⟶
              internalHomQCat L.obj Q.obj
                (@quasicategory_ihom L.obj Q.obj Q.property)) ≫ c)
      exact (internalHomPrecomp_isBicategoricalEquivalence hb Q).comp
        d.isEquivalence

end LeanLCAExactChallenge.Infinity
