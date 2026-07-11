import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension
import LeanLCAExactChallenge.Infinity.MetrizableEquivalenceForcingHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

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

universe u

universe v w x

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
