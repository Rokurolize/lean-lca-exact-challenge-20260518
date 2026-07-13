import LeanLCAExactChallenge.Infinity.InnerAnodyneMapping
import LeanLCAExactChallenge.Infinity.OrdinaryLocalizationBridge

/-!
# Internal homs preserve bicategorical equivalences in the source

A bicategorical equivalence induces equivalences on functor quasicategories.

This transfers mapping localization across equivalent carriers.
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

/-- Precomposition by an adjoint equivalence is an equivalence. -/
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

/-- Precomposition preserves bicategorical equivalences. -/
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

/-- A self-map acts covariantly on every functor quasicategory by postcomposition. -/
def internalHomPostcompositionAction (K X : SSet.{u}) :
    (ihom X).obj X ⟶
      (ihom ((ihom K).obj X)).obj ((ihom K).obj X) :=
  MonoidalClosed.curry (MonoidalClosed.comp K X X)

lemma internalHomPostcompositionAction_vertex
    (K X : SSet.{u}) (f : X ⟶ X) :
    (internalHomPostcompositionAction K X).app (op (SimplexCategory.mk 0))
        (SSet.unitHomEquiv ((ihom X).obj X)
          (MonoidalClosed.curry' f)) =
      SSet.unitHomEquiv
        ((ihom ((ihom K).obj X)).obj ((ihom K).obj X))
        (MonoidalClosed.curry' ((ihom K).map f)) := by
  apply (SSet.unitHomEquiv
    ((ihom ((ihom K).obj X)).obj ((ihom K).obj X))).symm.injective
  rw [Equiv.symm_apply_apply, unitHomEquiv_symm_natural']
  rw [Equiv.symm_apply_apply]
  simp only [internalHomPostcompositionAction]
  rw [← MonoidalClosed.curry_natural_left,
    MonoidalClosed.whiskerLeft_curry'_comp]
  rfl

/-- Apply postcomposition to an invertible `2`-cell represented by an internal-hom edge. -/
noncomputable def internalHomPostcompEdgeOfTwoIso
    {X : SSet.QCat.{u}} {f g : X ⟶ X} (a : f ≅ g)
    (K : SSet.{u}) :
    SSet.Edge
      (SSet.unitHomEquiv
        ((ihom ((ihom K).obj X.obj)).obj ((ihom K).obj X.obj))
        (MonoidalClosed.curry' ((ihom K).map f.hom)))
      (SSet.unitHomEquiv
        ((ihom ((ihom K).obj X.obj)).obj ((ihom K).obj X.obj))
        (MonoidalClosed.curry' ((ihom K).map g.hom))) :=
  SSet.Edge.castEndpoints
    (internalHomPostcompositionAction_vertex K X.obj f.hom).symm
    (internalHomPostcompositionAction_vertex K X.obj g.hom).symm
    ((internalHomEdgeOfTwoIso a).map
      (internalHomPostcompositionAction K X.obj))

theorem internalHomPostcompEdgeOfTwoIso_isEquivalence
    {X : SSet.QCat.{u}} {f g : X ⟶ X} (a : f ≅ g)
    (K : SSet.{u}) :
    EdgeIsEquivalence (internalHomPostcompEdgeOfTwoIso a K) :=
  (internalHomEdgeOfTwoIso_isEquivalence a).map
      (internalHomPostcompositionAction K X.obj) |>.castEndpoints
        (internalHomPostcompositionAction_vertex K X.obj f.hom).symm
        (internalHomPostcompositionAction_vertex K X.obj g.hom).symm

/-- Postcomposition carries an invertible `2`-cell to an invertible `2`-cell. -/
noncomputable def internalHomPostcompTwoIso
    {X : SSet.QCat.{u}} {f g : X ⟶ X} (a : f ≅ g)
    (K : SSet.{u}) :
    (ObjectProperty.homMk ((ihom K).map f.hom) :
      internalHomQCat K X.obj
          (@quasicategory_ihom K X.obj X.property) ⟶
        internalHomQCat K X.obj
          (@quasicategory_ihom K X.obj X.property)) ≅
      ObjectProperty.homMk ((ihom K).map g.hom) :=
  twoIsoOfInternalHomEquivalenceEdge
    (internalHomPostcompEdgeOfTwoIso a K)
    (internalHomPostcompEdgeOfTwoIso_isEquivalence a K)

/-- Postcomposition by an adjoint equivalence is an equivalence. -/
noncomputable def internalHomPostcompBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y)
    (K : SSet.{u}) :
    Bicategory.Equivalence
      (internalHomQCat K X.obj (@quasicategory_ihom K X.obj X.property))
      (internalHomQCat K Y.obj (@quasicategory_ihom K Y.obj Y.property)) := by
  let HX := internalHomQCat K X.obj (@quasicategory_ihom K X.obj X.property)
  let HY := internalHomQCat K Y.obj (@quasicategory_ihom K Y.obj Y.property)
  let p : HX ⟶ HY := ObjectProperty.homMk ((ihom K).map e.hom.hom)
  let s : HY ⟶ HX := ObjectProperty.homMk ((ihom K).map e.inv.hom)
  let preXId : HX ⟶ HX := ObjectProperty.homMk ((ihom K).map (𝟙 X.obj))
  let preXUnit : HX ⟶ HX :=
    ObjectProperty.homMk ((ihom K).map (e.hom ≫ e.inv).hom)
  let preYId : HY ⟶ HY := ObjectProperty.homMk ((ihom K).map (𝟙 Y.obj))
  let preYCounit : HY ⟶ HY :=
    ObjectProperty.homMk ((ihom K).map (e.inv ≫ e.hom).hom)
  have hp_comp_s : p ≫ s = preXUnit := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    exact ((ihom K).map_comp e.hom.hom e.inv.hom).symm
  have hs_comp_p : s ≫ p = preYCounit := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    exact ((ihom K).map_comp e.inv.hom e.hom.hom).symm
  have hpreXId : preXId = 𝟙 HX := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    exact (ihom K).map_id X.obj
  have hpreYId : preYId = 𝟙 HY := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    exact (ihom K).map_id Y.obj
  letI : Category (HX ⟶ HX) := SSet.QCat.bicategory.homCategory HX HX
  letI : Category (HY ⟶ HY) := SSet.QCat.bicategory.homCategory HY HY
  let unitPreIso : preXId ≅ preXUnit := internalHomPostcompTwoIso e.unit K
  let counitPreIso : preYCounit ≅ preYId := internalHomPostcompTwoIso e.counit K
  let unit : 𝟙 HX ≅ p ≫ s :=
    (eqToIso hpreXId.symm).trans
      (unitPreIso.trans (eqToIso hp_comp_s.symm))
  let counit : s ≫ p ≅ 𝟙 HY :=
    (eqToIso hs_comp_p).trans
      (counitPreIso.trans (eqToIso hpreYId))
  exact Bicategory.Equivalence.mkOfAdjointifyCounit unit counit

/-- Postcomposition preserves bicategorical equivalences. -/
theorem internalHomPostcomp_isBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} {f : X ⟶ Y}
    (hf : IsBicategoricalEquivalence f) (K : SSet.{u}) :
    IsBicategoricalEquivalence
      (ObjectProperty.homMk ((ihom K).map f.hom) :
        internalHomQCat K X.obj (@quasicategory_ihom K X.obj X.property) ⟶
          internalHomQCat K Y.obj (@quasicategory_ihom K Y.obj Y.property)) := by
  obtain ⟨e, rfl⟩ := hf
  exact ⟨internalHomPostcompBicategoricalEquivalence e K, rfl⟩

/-- Mapping localization transfers after an equivalent carrier change. -/
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
