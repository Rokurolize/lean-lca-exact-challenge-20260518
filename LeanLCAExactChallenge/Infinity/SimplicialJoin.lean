import Mathlib.AlgebraicTopology.SimplexCategory.Augmented.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Monoidal.DayConvolution
import Mathlib.CategoryTheory.Monoidal.DayConvolution.Closed
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Types.End
import Mathlib.Data.Finset.Sort

/-!
# The join of simplicial sets

This file constructs the simplicial join as Day convolution for ordinal sum on
the augmented simplex category.  Ordinary simplicial sets are first extended
by the empty `(-1)`-simplices and the convolution is then restricted back to
the ordinary simplex category.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity


open CategoryTheory Limits
open scoped CategoryTheory.MonoidalCategory.DayConvolution MonoidalCategory.ExternalProduct
  MonoidalCategory Simplicial Prod

abbrev AugmentedSSet : Type (u + 1) :=
  (AugmentedSimplexCategoryᵒᵖ ⥤ Type u)

/-- The linear-order multispan indexing a nonempty family of objects is
connected: every pair of right vertices is joined through their pair object,
and every left object maps to either endpoint. -/
theorem walkingMultispanOfLinearOrder_isConnected
    (ι : Type u) [LinearOrder ι] [Nonempty ι] :
    CategoryTheory.IsConnected
      (Limits.WalkingMultispan (Limits.MultispanShape.ofLinearOrder ι)) := by
  let rightZigzag (i j : ι) : CategoryTheory.Zigzag
      (Limits.WalkingMultispan.right
        (J := Limits.MultispanShape.ofLinearOrder ι) i)
      (Limits.WalkingMultispan.right
        (J := Limits.MultispanShape.ofLinearOrder ι) j) := by
    by_cases h : i = j
    · subst j
      exact CategoryTheory.Zigzag.refl _
    · rcases lt_or_gt_of_ne h with hij | hji
      · let p : (Limits.MultispanShape.ofLinearOrder ι).L :=
          ⟨(i, j), hij⟩
        exact CategoryTheory.Zigzag.of_inv_hom
          (Limits.WalkingMultispan.Hom.fst
            (J := Limits.MultispanShape.ofLinearOrder ι) p)
          (Limits.WalkingMultispan.Hom.snd
            (J := Limits.MultispanShape.ofLinearOrder ι) p)
      · let p : (Limits.MultispanShape.ofLinearOrder ι).L :=
          ⟨(j, i), hji⟩
        exact CategoryTheory.Zigzag.of_inv_hom
          (Limits.WalkingMultispan.Hom.snd
            (J := Limits.MultispanShape.ofLinearOrder ι) p)
          (Limits.WalkingMultispan.Hom.fst
            (J := Limits.MultispanShape.ofLinearOrder ι) p)
  let ⟨i₀⟩ := (inferInstance : Nonempty ι)
  letI : Nonempty
      (Limits.WalkingMultispan (Limits.MultispanShape.ofLinearOrder ι)) :=
    ⟨Limits.WalkingMultispan.right
      (J := Limits.MultispanShape.ofLinearOrder ι) i₀⟩
  apply CategoryTheory.zigzag_isConnected
  intro x y
  rcases x with a | i <;> rcases y with b | j
  · exact (CategoryTheory.Zigzag.of_hom
      (Limits.WalkingMultispan.Hom.fst a)).trans
        ((rightZigzag a.1.1 b.1.1).trans
          (CategoryTheory.Zigzag.of_hom
            (Limits.WalkingMultispan.Hom.fst b)).symm)
  · exact (CategoryTheory.Zigzag.of_hom
      (Limits.WalkingMultispan.Hom.fst a)).trans
        (rightZigzag a.1.1 j)
  · exact (rightZigzag i b.1.1).trans
      (CategoryTheory.Zigzag.of_hom
        (Limits.WalkingMultispan.Hom.fst b)).symm
  · exact rightZigzag i j

/-- The linearized multicoequalizer index of a positive-dimensional horn is
connected. -/
theorem hornMulticoequalizerIndex_isConnected {n : ℕ}
    (i : Fin (n + 1)) (hn : 0 < n) :
    CategoryTheory.IsConnected
      (Limits.WalkingMultispan
        (Limits.MultispanShape.ofLinearOrder ({i}ᶜ : Set (Fin (n + 1))))) := by
  letI : Nontrivial (Fin (n + 1)) :=
    Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨j, hj⟩ := exists_ne i
  letI : Nonempty ({i}ᶜ : Set (Fin (n + 1))) :=
    ⟨⟨j, by simpa⟩⟩
  exact walkingMultispanOfLinearOrder_isConnected _

/-- At augmented degree, the horn multicoequalizer becomes the constant
singleton cocone, which is colimiting by connectedness. -/
noncomputable def hornIndexPUnitIsColimit {n : ℕ}
    (i : Fin (n + 1)) (hn : 0 < n) :
    Limits.IsColimit
      (Limits.Types.pUnitCocone.{u}
        (Limits.WalkingMultispan
          (Limits.MultispanShape.ofLinearOrder ({i}ᶜ : Set (Fin (n + 1)))))) := by
  letI : CategoryTheory.IsConnected
      (Limits.WalkingMultispan
        (Limits.MultispanShape.ofLinearOrder ({i}ᶜ : Set (Fin (n + 1))))) :=
    hornMulticoequalizerIndex_isConnected i hn
  exact Limits.Types.isColimitPUnitCocone _

/-- Equip a simplicial set with its canonical augmentation to the terminal
set.  This is the augmentation used by the ordinary simplicial join. -/
def terminalAugmentedSSet : SSet.{u} ⥤ SSet.Augmented.{u} where
  obj X :=
    { left := X
      right := Limits.terminal (Type u)
      hom :=
        { app := fun _ ↦ Limits.terminal.from _
          naturality := by intros; apply Limits.terminal.hom_ext } }
  map f :=
    { left := f
      right := 𝟙 _
      w := by
        apply NatTrans.ext
        funext n
        apply Limits.terminal.hom_ext }
  map_id _ := by ext <;> rfl
  map_comp _ _ := by ext <;> rfl

/-- The canonical singleton augmentation, expressed as a presheaf on the
augmented simplex category. -/
def singletonAugmentation : SSet.{u} ⥤ AugmentedSSet.{u} :=
  terminalAugmentedSSet ⋙
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.inverse

/-- A strict normal form of singleton augmentation.  Ordinary degrees are
literally those of `X`, while augmented degree is the chosen terminal type. -/
def strictSingletonAugmentation : SSet.{u} ⥤ AugmentedSSet.{u} where
  obj X :=
    (WithInitial.opEquiv SimplexCategory).functor ⋙
      WithTerminal.liftToTerminal X (Limits.terminalIsTerminal (C := Type u))
  map {X Y} f := Functor.whiskerLeft (WithInitial.opEquiv SimplexCategory).functor
    { app := fun j ↦ match j with
        | .of _ => f.app _
        | .star => 𝟙 _
      naturality := by
        rintro (j | _) (k | _) g
        · exact f.naturality g
        · apply Limits.terminal.hom_ext
        · exact g.elim
        · apply Limits.terminal.hom_ext }
  map_id X := by
    apply NatTrans.ext
    funext j
    rcases j with ⟨(j | _)⟩ <;> rfl
  map_comp {X Y Z} f g := by
    apply NatTrans.ext
    funext j
    rcases j with ⟨(j | _)⟩ <;> rfl

/-- The strict and comma-equivalence presentations of singleton augmentation
are canonically isomorphic. -/
def strictSingletonAugmentationIso :
    strictSingletonAugmentation.{u} ≅ singletonAugmentation.{u} :=
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  NatIso.ofComponents (fun X ↦ E.unitIso.app (strictSingletonAugmentation.obj X))
    (fun f ↦ E.unitIso.hom.naturality (strictSingletonAugmentation.map f))

/-- Evaluation of strict singleton augmentation at an ordinary degree. -/
def strictSingletonAugmentationEvalOfIso (j : SimplexCategory) :
    strictSingletonAugmentation.{u} ⋙
        (evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
          (Opposite.op (WithInitial.of j)) ≅
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op j) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- Evaluation of strict singleton augmentation at augmented degree is the
constant singleton functor. -/
def strictSingletonAugmentationEvalStarIso :
    strictSingletonAugmentation.{u} ⋙
      (evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
          (Opposite.op WithInitial.star) ≅
      (Functor.const SSet.{u}).obj PUnit.{u + 1} :=
  NatIso.ofComponents
    (fun _ ↦ (Limits.terminalIsTerminal (C := Type u)).uniqueUpToIso
      Limits.Types.isTerminalPUnit)
    (fun _ ↦ by apply Limits.Types.isTerminalPUnit.hom_ext)

/-- The horn multicofork after strict singleton augmentation. -/
noncomputable def strictSingletonAugmentationHornCocone {n : ℕ}
    (i : Fin (n + 1)) :
    Cocone
      (((SSet.horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
        (SSet.Subcomplex.toSSetFunctor)).multispan ⋙ strictSingletonAugmentation.{u}) :=
  strictSingletonAugmentation.{u}.mapCocone
    ((SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor)

/-- Strict singleton augmentation preserves the horn multicoequalizer. -/
noncomputable def strictSingletonAugmentationHornIsColimit {n : ℕ}
    (i : Fin (n + 1)) (hn : 0 < n) :
    IsColimit (strictSingletonAugmentationHornCocone.{u} i) := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨(j | _)⟩
  · let c := (SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor
    let e := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op j)
    have hc : IsColimit (e.mapCocone c) :=
      isColimitOfPreserves e (SSet.horn.isColimit.{u} i)
    exact IsColimit.ofIsoColimit
      (IsColimit.mapCoconeEquiv
        (strictSingletonAugmentationEvalOfIso.{u} j).symm hc)
      (Functor.mapCoconeMapCocone c).symm

  · let c := (SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor
    letI : CategoryTheory.IsConnected
        (Limits.WalkingMultispan
          (Limits.MultispanShape.ofLinearOrder ({i}ᶜ : Set (Fin (n + 1))))) :=
      hornMulticoequalizerIndex_isConnected i hn
    have hc : IsColimit
        (((Functor.const SSet.{u}).obj PUnit.{u + 1}).mapCocone c) := by
      refine
        { desc := fun s ↦ s.ι.app Classical.ofNonempty
          fac := fun s j ↦ ?_
          uniq := fun s m h ↦ ?_ }
      · ext ⟨⟩
        refine constant_of_preserves_morphisms (α := s.pt)
          (fun k ↦ s.ι.app k PUnit.unit) ?_ Classical.ofNonempty j
        intro X Y f
        exact ConcreteCategory.congr_hom (s.ι.naturality f).symm PUnit.unit
      · ext ⟨⟩
        have hh := h Classical.ofNonempty
        simp [c] at hh
        change m = s.ι.app Classical.ofNonempty at hh
        exact ConcreteCategory.congr_hom hh PUnit.unit
    exact IsColimit.ofIsoColimit
      (IsColimit.mapCoconeEquiv strictSingletonAugmentationEvalStarIso.symm hc)
      (Functor.mapCoconeMapCocone c).symm

/-- The horn multicofork after canonical singleton augmentation. -/
noncomputable def singletonAugmentationHornCocone {n : ℕ}
    (i : Fin (n + 1)) :
    Cocone
      (((SSet.horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
        (SSet.Subcomplex.toSSetFunctor)).multispan ⋙ singletonAugmentation.{u}) :=
  singletonAugmentation.{u}.mapCocone
    ((SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor)

/-- Canonical singleton augmentation preserves positive-dimensional horn
multicoequalizers. -/
noncomputable def singletonAugmentationHornIsColimit {n : ℕ}
    (i : Fin (n + 1)) (hn : 0 < n) :
    IsColimit (singletonAugmentationHornCocone.{u} i) :=
  IsColimit.mapCoconeEquiv strictSingletonAugmentationIso
    (strictSingletonAugmentationHornIsColimit.{u} i hn)

/-- Diagnostic left Kan extension along the inclusion of ordinary degrees.
Its augmented degree records a colimit of the simplicial set and it is not the
augmentation used for the ordinary join. -/
def componentAugmentation : SSet.{u} ⥤ AugmentedSSet.{u} :=
  AugmentedSimplexCategory.inclusion.op.lan

/-- The canonical singleton augmentation used for the ordinary join. -/
abbrev emptyAugmentation : SSet.{u} ⥤ AugmentedSSet.{u} :=
  singletonAugmentation

/-- Restriction of an augmented simplicial set to ordinary simplicial degrees. -/
def forgetAugmentation : AugmentedSSet.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ (Type u)).obj
    AugmentedSimplexCategory.inclusion.op

/-- Forgetting the canonical singleton augmentation recovers the original
simplicial set. -/
def forgetSingletonAugmentationIso :
    singletonAugmentation.{u} ⋙ forgetAugmentation.{u} ≅ 𝟭 SSet.{u} :=
  Iso.refl _

/-- The distinguished object in the pointwise Kan-extension category computing
Day convolution in augmented degree `-1`. -/
def tensorCostructuredStar :
    CostructuredArrow
      (CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ)
      (Opposite.op WithInitial.star) :=
  CostructuredArrow.mk (Y :=
    (Opposite.op WithInitial.star, Opposite.op WithInitial.star)) (𝟙 _)

/-- The pair `(star, star)` is terminal in the category computing the
augmented-degree value of Day convolution. -/
def tensorCostructuredStarIsTerminal : Limits.IsTerminal tensorCostructuredStar := by
  apply Limits.IsTerminal.ofUniqueHom
    (fun s ↦ CostructuredArrow.homMk
        ((WithInitial.starInitial.to s.left.1.unop).op ×ₘ
          (WithInitial.starInitial.to s.left.2.unop).op) (by
            apply Quiver.Hom.unop_inj
            apply WithInitial.starInitial.hom_ext))
  intro s f
  apply CostructuredArrow.hom_ext
  ext
  · apply Quiver.Hom.unop_inj
    apply WithInitial.starInitial.hom_ext
  · apply Quiver.Hom.unop_inj
    apply WithInitial.starInitial.hom_ext

/-- The augmented-degree value of the canonical singleton augmentation is a
terminal set. -/
def emptyAugmentationStarIsTerminal (X : SSet.{u}) :
    Limits.IsTerminal
      ((emptyAugmentation.{u}.obj X).obj (Opposite.op WithInitial.star)) := by
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  let e : E.functor.obj (E.inverse.obj (terminalAugmentedSSet.obj X)) ≅
      terminalAugmentedSSet.obj X := E.counitIso.app _
  exact Limits.IsTerminal.ofIso Limits.terminalIsTerminal
    (SimplicialObject.Augmented.point.mapIso e).symm

/-- The chosen Day convolution on augmented simplicial sets. -/
@[implicit_reducible]
def augmentedDayConvolution (X Y : AugmentedSSet.{u}) :
    CategoryTheory.MonoidalCategory.DayConvolution X Y where
  convolution :=
    (CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ).leftKanExtension
      (X ⊠ Y)
  unit :=
    (CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ).leftKanExtensionUnit
      (X ⊠ Y)
  isPointwiseLeftKanExtensionUnit :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _

/-- Day convolution of two singleton-augmented simplicial sets again has a
terminal augmented-degree value. -/
def augmentedDayConvolutionStarIsTerminal (X Y : SSet.{u}) :
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj X) (emptyAugmentation.{u}.obj Y)
    Limits.IsTerminal
      ((CategoryTheory.MonoidalCategory.DayConvolution.convolution
        (emptyAugmentation.{u}.obj X) (emptyAugmentation.{u}.obj Y)).obj
          (Opposite.op WithInitial.star)) := by
  let F := emptyAugmentation.{u}.obj X
  let G := emptyAugmentation.{u}.obj Y
  letI := augmentedDayConvolution F G
  let T := CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ
  let D := CostructuredArrow.proj T (Opposite.op WithInitial.star) ⋙ (F ⊠ G)
  let e₁ := T.leftKanExtensionObjIsoColimit (F ⊠ G)
    (Opposite.op WithInitial.star)
  let e₂ : Limits.colimit D ≅ D.obj tensorCostructuredStar :=
    Limits.IsColimit.coconePointUniqueUpToIso (Limits.colimit.isColimit D)
      (Limits.colimitOfDiagramTerminal tensorCostructuredStarIsTerminal D)
  let uF : Unique (F.obj (Opposite.op WithInitial.star)) :=
    (Limits.Types.isTerminalEquivUnique _)
      (emptyAugmentationStarIsTerminal X)
  let uG : Unique (G.obj (Opposite.op WithInitial.star)) :=
    (Limits.Types.isTerminalEquivUnique _)
      (emptyAugmentationStarIsTerminal Y)
  let uprod : Unique (F.obj (Opposite.op WithInitial.star) ×
      G.obj (Opposite.op WithInitial.star)) :=
    { default := (uF.default, uG.default)
      uniq := fun p ↦ Prod.ext (uF.uniq p.1) (uG.uniq p.2) }
  let hprod : Limits.IsTerminal (D.obj tensorCostructuredStar) := by
    change Limits.IsTerminal
      (F.obj (Opposite.op WithInitial.star) ×
        G.obj (Opposite.op WithInitial.star))
    exact (Limits.Types.isTerminalEquivUnique _).symm uprod
  exact Limits.IsTerminal.ofIso hprod (e₁ ≪≫ e₂).symm

/-- The join of two simplicial sets. -/
def simplicialJoin (X Y : SSet.{u}) : SSet.{u} :=
  letI := augmentedDayConvolution.{u}
    (emptyAugmentation.{u}.obj X) (emptyAugmentation.{u}.obj Y)
  forgetAugmentation.{u}.obj
    (CategoryTheory.MonoidalCategory.DayConvolution.convolution
      (emptyAugmentation.{u}.obj X) (emptyAugmentation.{u}.obj Y))

/-- The augmented Day convolution of singleton augmentations is the singleton
augmentation of its ordinary restriction. -/
def convolutionSingletonAugmentationIso (X Y : SSet.{u}) :
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj X) (emptyAugmentation.{u}.obj Y)
    emptyAugmentation.{u}.obj (simplicialJoin X Y) ≅
      CategoryTheory.MonoidalCategory.DayConvolution.convolution
        (emptyAugmentation.{u}.obj X) (emptyAugmentation.{u}.obj Y) := by
  let F := emptyAugmentation.{u}.obj X
  let G := emptyAugmentation.{u}.obj Y
  letI := augmentedDayConvolution F G
  let H := CategoryTheory.MonoidalCategory.DayConvolution.convolution F G
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  let hH := augmentedDayConvolutionStarIsTerminal X Y
  let uH : Unique (H.obj (Opposite.op WithInitial.star)) :=
    (Limits.Types.isTerminalEquivUnique _) hH
  let e : terminalAugmentedSSet.obj (simplicialJoin X Y) ≅ E.functor.obj H :=
    Comma.isoMk (Iso.refl _) (Limits.terminalIsTerminal.uniqueUpToIso hH) (by
      apply NatTrans.ext
      funext j
      apply ConcreteCategory.hom_ext
      intro x
      change (_ : H.obj (Opposite.op WithInitial.star)) = _
      exact (uH.uniq _).trans (uH.uniq _).symm)
  exact E.inverse.mapIso e ≪≫ (E.unitIso.app H).symm

scoped infixr:70 " ⋆ˢ " => simplicialJoin

/-- Functoriality of the simplicial join in both variables. -/
def simplicialJoinMap {X X' Y Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') : X ⋆ˢ Y ⟶ X' ⋆ˢ Y' := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj X) (emptyAugmentation.{u}.obj Y)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj X') (emptyAugmentation.{u}.obj Y')
  exact Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op
    (CategoryTheory.MonoidalCategory.DayConvolution.map
      (emptyAugmentation.{u}.map f) (emptyAugmentation.{u}.map g))

/-- Extending a standard simplex to augmented degree is the augmented
representable at the same finite ordinal. -/
def emptyAugmentationStdSimplexIso (n : SimplexCategory) :
    emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n) ≅
      (CategoryTheory.uliftYoneda.{u}.obj
        (AugmentedSimplexCategory.inclusion.obj n) : AugmentedSSet.{u}) :=
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  let R := E.functor.obj (CategoryTheory.uliftYoneda.{u}.obj
    (AugmentedSimplexCategory.inclusion.obj n))
  letI : Unique R.right :=
    { default := ULift.up (WithInitial.starInitial.to _)
      uniq := by
        intro x
        rcases x with ⟨x⟩
        apply ULift.ext
        apply WithInitial.starInitial.hom_ext }
  let hR : Limits.IsTerminal R.right :=
    (Limits.Types.isTerminalEquivUnique R.right).symm inferInstance
  let e : terminalAugmentedSSet.obj (SSet.stdSimplex.obj n) ≅
      R :=
    Comma.isoMk (Iso.refl _)
      (Limits.terminalIsTerminal.uniqueUpToIso hR) (by
        apply NatTrans.ext
        funext j
        apply ConcreteCategory.hom_ext
        intro x
        change (_ : R.right) = _
        exact (this.uniq _).trans (this.uniq _).symm)
  E.inverse.mapIso e ≪≫ (E.unitIso.app _).symm

set_option backward.isDefEq.respectTransparency false in
lemma emptyAugmentationStdSimplexIso_naturality
    {m n : SimplexCategory} (f : m ⟶ n) :
    emptyAugmentation.{u}.map (SSet.stdSimplex.map f) ≫
        (emptyAugmentationStdSimplexIso.{u} n).hom =
      (emptyAugmentationStdSimplexIso.{u} m).hom ≫
        CategoryTheory.uliftYoneda.{u}.map
          (AugmentedSimplexCategory.inclusion.map f) := by
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  apply E.functor.map_injective
  apply CommaMorphism.ext
  · rfl
  · apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply WithInitial.starInitial.hom_ext

/-- The product representable, written on the product of opposite categories
used by the Day convolution API. -/
@[reducible]
def productULiftYoneda (x y : AugmentedSimplexCategory) :
    AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ ⥤ Type u where
  obj z := ULift ((z.1.unop ⟶ x) × (z.2.unop ⟶ y))
  map {X Y} f := ConcreteCategory.ofHom (TypeCat.Fun.mk fun p :
      ULift.{u} ((X.1.unop ⟶ x) × (X.2.unop ⟶ y)) ↦
    (ULift.up (f.1.unop ≫ p.down.1, f.2.unop ≫ p.down.2) :
      ULift.{u} ((Y.1.unop ⟶ x) × (Y.2.unop ⟶ y))))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨⟨a, b⟩⟩
    ext <;> simp
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨⟨a, b⟩⟩
    ext <;> simp [Category.assoc]

/-- The external product of two representables is the product representable. -/
def externalProductULiftYonedaIso (x y : AugmentedSimplexCategory) :
    (CategoryTheory.uliftYoneda.{u}.obj x ⊠
      CategoryTheory.uliftYoneda.{u}.obj y) ≅ productULiftYoneda.{u} x y :=
  NatIso.ofComponents (fun z ↦ Equiv.toIso
    { toFun := fun p ↦ ULift.up (p.1.down, p.2.down)
      invFun := fun p ↦ (ULift.up p.down.1, ULift.up p.down.2)
      left_inv := by rintro ⟨⟨a⟩, ⟨b⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, b⟩⟩; rfl }) (by
        intro z z' f
        rw [CategoryTheory.MonoidalCategory.externalProductBifunctor_obj_map]
        ext ⟨⟨a⟩, ⟨b⟩⟩ <;> rfl)

/-- The canonical multiplication map from the external product of two
representables to the representable at their ordinal sum. -/
def representableConvolutionUnit (x y : AugmentedSimplexCategory) :
    (CategoryTheory.uliftYoneda.{u}.obj x ⊠
      CategoryTheory.uliftYoneda.{u}.obj y) ⟶
      CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ ⋙
        CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y) where
  app z := ConcreteCategory.ofHom (TypeCat.Fun.mk fun p ↦
    (ULift.up (p.1.down ⊗ₘ p.2.down) :
      ULift.{u} (z.1.unop ⊗ z.2.unop ⟶ x ⊗ y)))
  naturality {z z'} f := by
    rw [CategoryTheory.MonoidalCategory.externalProductBifunctor_obj_map]
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨⟨a⟩, ⟨b⟩⟩
    apply ULift.ext
    change (f.1.unop ≫ a) ⊗ₘ (f.2.unop ≫ b) =
      (f.1 ⊗ₘ f.2).unop ≫ (a ⊗ₘ b)
    simp

/-- The same representable multiplication, obtained by precomposing the
Yoneda left-Kan-extension unit with the product/opposite equivalence. -/
def representableConvolutionUnitViaLan (x y : AugmentedSimplexCategory) :
    (CategoryTheory.prodOpEquiv (C := AugmentedSimplexCategory)
      (D := AugmentedSimplexCategory)).inverse ⋙
      CategoryTheory.uliftYoneda.{u}.obj (x, y) ⟶
      ((CategoryTheory.prodOpEquiv (C := AugmentedSimplexCategory)
        (D := AugmentedSimplexCategory)).inverse ⋙
        (CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategory).op) ⋙
          CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y) :=
  Functor.whiskerLeft
      (CategoryTheory.prodOpEquiv (C := AugmentedSimplexCategory)
        (D := AugmentedSimplexCategory)).inverse
      (CategoryTheory.uliftYonedaMap.{u}
        (CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategory) (x, y)) ≫
    (Functor.associator _ _ _).inv

theorem representableConvolutionUnitViaLan_isLeftKanExtension
    (x y : AugmentedSimplexCategory) :
    (CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y)).IsLeftKanExtension
      (representableConvolutionUnitViaLan.{u} x y) := by
  exact (Functor.isLeftKanExtension_iff_precomp
    (G := (CategoryTheory.prodOpEquiv (C := AugmentedSimplexCategory)
      (D := AugmentedSimplexCategory)).inverse)
    (α := CategoryTheory.uliftYonedaMap.{u}
      (CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategory) (x, y))).mp
        (by infer_instance)

/-- The explicit product representable agrees with restriction of the
representable on the product category along `prodOpEquiv.inverse`. -/
def productULiftYonedaIsoViaProdOp (x y : AugmentedSimplexCategory) :
    productULiftYoneda.{u} x y ≅
      (CategoryTheory.prodOpEquiv (C := AugmentedSimplexCategory)
        (D := AugmentedSimplexCategory)).inverse ⋙
          CategoryTheory.uliftYoneda.{u}.obj (x, y) :=
  Iso.refl _

/-- Tensoring in the opposite augmented simplex category is ordinal sum
precomposed by the product/opposite equivalence. -/
def tensorOppositeIso :
    (CategoryTheory.prodOpEquiv (C := AugmentedSimplexCategory)
      (D := AugmentedSimplexCategory)).inverse ⋙
        (CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategory).op ≅
      CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ :=
  Iso.refl _

/-- The canonical representable multiplication is a left Kan extension along
ordinal sum on the opposite augmented simplex category. -/
theorem representableConvolutionUnit_isLeftKanExtension
    (x y : AugmentedSimplexCategory) :
    (CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y)).IsLeftKanExtension
      (representableConvolutionUnit.{u} x y) := by
  let e :
      ((CategoryTheory.prodOpEquiv (C := AugmentedSimplexCategory)
        (D := AugmentedSimplexCategory)).inverse ⋙
          CategoryTheory.uliftYoneda.{u}.obj (x, y)) ≅
        (CategoryTheory.uliftYoneda.{u}.obj x ⊠
          CategoryTheory.uliftYoneda.{u}.obj y) :=
    (productULiftYonedaIsoViaProdOp.{u} x y).symm ≪≫
      (externalProductULiftYonedaIso.{u} x y).symm
  apply (Functor.isLeftKanExtension_iff_of_iso₂
    (representableConvolutionUnitViaLan.{u} x y)
    (representableConvolutionUnit.{u} x y) e (Iso.refl _) ?_).mp
  · exact representableConvolutionUnitViaLan_isLeftKanExtension.{u} x y
  · ext z p
    rcases p with ⟨p⟩
    apply ULift.ext
    rfl

/-- Day convolution of augmented representables is represented by ordinal sum. -/
@[implicit_reducible]
def representableDayConvolution (x y : AugmentedSimplexCategory) :
    CategoryTheory.MonoidalCategory.DayConvolution
      (CategoryTheory.uliftYoneda.{u}.obj x)
      (CategoryTheory.uliftYoneda.{u}.obj y) where
  convolution := CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y)
  unit := representableConvolutionUnit.{u} x y
  isPointwiseLeftKanExtensionUnit := by
    letI : (CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y)).IsLeftKanExtension
        (representableConvolutionUnit.{u} x y) :=
      representableConvolutionUnit_isLeftKanExtension.{u} x y
    exact Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On representables, the morphism induced by Day convolution is the
representable morphism induced by tensoring the indexing arrows. -/
theorem representableDayConvolution_map
    {x x' y y' : AugmentedSimplexCategory}
    (f : x ⟶ x') (g : y ⟶ y') :
    letI := representableDayConvolution.{u} x y
    letI := representableDayConvolution.{u} x' y'
    CategoryTheory.MonoidalCategory.DayConvolution.map
        (CategoryTheory.uliftYoneda.{u}.map f)
        (CategoryTheory.uliftYoneda.{u}.map g) =
      CategoryTheory.uliftYoneda.{u}.map (f ⊗ₘ g) := by
  letI := representableDayConvolution.{u} x y
  letI := representableDayConvolution.{u} x' y'
  letI : (CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y)).IsLeftKanExtension
      (representableConvolutionUnit.{u} x y) :=
    representableConvolutionUnit_isLeftKanExtension.{u} x y
  apply Functor.hom_ext_of_isLeftKanExtension _
    (representableConvolutionUnit.{u} x y)
  unfold CategoryTheory.MonoidalCategory.DayConvolution.map
  change representableConvolutionUnit.{u} x y ≫
      Functor.whiskerLeft (CategoryTheory.MonoidalCategory.tensor _)
        (Functor.descOfIsLeftKanExtension
          (CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y))
          (representableConvolutionUnit.{u} x y)
          (CategoryTheory.uliftYoneda.{u}.obj (x' ⊗ y'))
          ((CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).map
              (CategoryTheory.uliftYoneda.{u}.map f ×ₘ
                CategoryTheory.uliftYoneda.{u}.map g) ≫
            representableConvolutionUnit.{u} x' y')) = _
  rw [Functor.descOfIsLeftKanExtension_fac]
  ext z p
  rcases p with ⟨p, q⟩
  apply ULift.ext
  simp only [representableConvolutionUnit, NatTrans.comp_app]
  change (CategoryTheory.MonoidalCategory.tensor _).map
      ((p.down ×ₘ q.down) ≫ (f ×ₘ g)) =
    (CategoryTheory.MonoidalCategory.tensor _).map (p.down ×ₘ q.down) ≫
      (CategoryTheory.MonoidalCategory.tensor _).map (f ×ₘ g)
  rw [Functor.map_comp]

theorem representableConvolutionUnit_naturality
    {x x' y y' : AugmentedSimplexCategory}
    (f : x ⟶ x') (g : y ⟶ y') :
    (CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).map
        (CategoryTheory.uliftYoneda.{u}.map f ×ₘ
          CategoryTheory.uliftYoneda.{u}.map g) ≫
      representableConvolutionUnit.{u} x' y' =
    representableConvolutionUnit.{u} x y ≫
      Functor.whiskerLeft (CategoryTheory.MonoidalCategory.tensor _)
        (CategoryTheory.uliftYoneda.{u}.map (f ⊗ₘ g)) := by
  ext z p
  rcases p with ⟨p, q⟩
  apply ULift.ext
  simp only [representableConvolutionUnit, NatTrans.comp_app]
  change (CategoryTheory.MonoidalCategory.tensor _).map
      ((p.down ×ₘ q.down) ≫ (f ×ₘ g)) =
    (CategoryTheory.MonoidalCategory.tensor _).map (p.down ×ₘ q.down) ≫
      (CategoryTheory.MonoidalCategory.tensor _).map (f ×ₘ g)
  rw [Functor.map_comp]

/-- The chosen left-Kan Day convolution agrees with the representable at
ordinal sum whenever both inputs are representable. -/
def augmentedDayConvolutionRepresentablesIso (x y : AugmentedSimplexCategory) :
    letI := augmentedDayConvolution
      (CategoryTheory.uliftYoneda.{u}.obj x)
      (CategoryTheory.uliftYoneda.{u}.obj y)
    CategoryTheory.MonoidalCategory.DayConvolution.convolution
        (CategoryTheory.uliftYoneda.{u}.obj x)
        (CategoryTheory.uliftYoneda.{u}.obj y) ≅
      CategoryTheory.uliftYoneda.{u}.obj (x ⊗ y) :=
  let h := augmentedDayConvolution
    (CategoryTheory.uliftYoneda.{u}.obj x)
    (CategoryTheory.uliftYoneda.{u}.obj y)
  let h' := representableDayConvolution.{u} x y
  h.uniqueUpToIso h'

/-- Transport a Day convolution structure backwards along isomorphisms of its
two input functors. -/
@[implicit_reducible]
def dayConvolutionOfInputIsos
    {F F' G G' : AugmentedSSet.{u}} (eF : F ≅ F') (eG : G ≅ G')
    (h : CategoryTheory.MonoidalCategory.DayConvolution F' G') :
    CategoryTheory.MonoidalCategory.DayConvolution F G where
  convolution := h.convolution
  unit :=
    (CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).map
        (eF.hom ×ₘ eG.hom) ≫ h.unit
  isPointwiseLeftKanExtensionUnit := by
    let e := (CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).mapIso
      (eF.prod eG)
    have hlan : h.convolution.IsLeftKanExtension h.unit :=
      h.isPointwiseLeftKanExtensionUnit.isLeftKanExtension
    have hlan' : h.convolution.IsLeftKanExtension
        (e.hom ≫ h.unit) := by
      exact (Functor.isLeftKanExtension_iff_of_iso₂ h.unit (e.hom ≫ h.unit)
        e.symm (Iso.refl _) (by simp)).mp hlan
    letI : h.convolution.IsLeftKanExtension
        ((CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).map
          (eF.hom ×ₘ eG.hom) ≫ h.unit) := hlan'
    exact Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ _

/-- A representable model for the Day convolution of two augmented standard
simplices. -/
@[implicit_reducible]
def standardSimplexDayConvolution (m n : SimplexCategory) :=
  dayConvolutionOfInputIsos
    (emptyAugmentationStdSimplexIso.{u} m)
    (emptyAugmentationStdSimplexIso.{u} n)
    (representableDayConvolution.{u}
      (AugmentedSimplexCategory.inclusion.obj m)
      (AugmentedSimplexCategory.inclusion.obj n))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem standardSimplexDayConvolution_map
    {m m' n n' : SimplexCategory} (f : m ⟶ m') (g : n ⟶ n') :
    letI := standardSimplexDayConvolution.{u} m n
    letI := standardSimplexDayConvolution.{u} m' n'
    CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.{u}.map (SSet.stdSimplex.map f))
        (emptyAugmentation.{u}.map (SSet.stdSimplex.map g)) =
      CategoryTheory.uliftYoneda.{u}.map
        (AugmentedSimplexCategory.inclusion.map f ⊗ₘ
          AugmentedSimplexCategory.inclusion.map g) := by
  letI := standardSimplexDayConvolution.{u} m n
  letI := standardSimplexDayConvolution.{u} m' n'
  apply Functor.hom_ext_of_isLeftKanExtension _
    (CategoryTheory.MonoidalCategory.DayConvolution.unit
      (emptyAugmentation.obj (SSet.stdSimplex.obj m))
      (emptyAugmentation.obj (SSet.stdSimplex.obj n)))
  unfold CategoryTheory.MonoidalCategory.DayConvolution.map
  rw [Functor.descOfIsLeftKanExtension_fac]
  change
    (CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).map
        (emptyAugmentation.map (SSet.stdSimplex.map f) ×ₘ
          emptyAugmentation.map (SSet.stdSimplex.map g)) ≫
      ((CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).map
          ((emptyAugmentationStdSimplexIso.{u} m').hom ×ₘ
            (emptyAugmentationStdSimplexIso.{u} n').hom) ≫
        representableConvolutionUnit _ _) =
    ((CategoryTheory.MonoidalCategory.externalProductBifunctor _ _ _).map
        ((emptyAugmentationStdSimplexIso.{u} m).hom ×ₘ
          (emptyAugmentationStdSimplexIso.{u} n).hom) ≫
      representableConvolutionUnit _ _) ≫
      Functor.whiskerLeft (CategoryTheory.MonoidalCategory.tensor _)
        (CategoryTheory.uliftYoneda.{u}.map
          (AugmentedSimplexCategory.inclusion.map f ⊗ₘ
            AugmentedSimplexCategory.inclusion.map g))
  have hfg :
      (emptyAugmentation.map (SSet.stdSimplex.map f) ×ₘ
          emptyAugmentation.map (SSet.stdSimplex.map g)) ≫
        ((emptyAugmentationStdSimplexIso.{u} m').hom ×ₘ
          (emptyAugmentationStdSimplexIso.{u} n').hom) =
      ((emptyAugmentationStdSimplexIso.{u} m).hom ×ₘ
          (emptyAugmentationStdSimplexIso.{u} n).hom) ≫
        (CategoryTheory.uliftYoneda.{u}.map
            (AugmentedSimplexCategory.inclusion.map f) ×ₘ
          CategoryTheory.uliftYoneda.{u}.map
            (AugmentedSimplexCategory.inclusion.map g)) := by
    ext <;> simp [emptyAugmentationStdSimplexIso_naturality]
  rw [← Category.assoc, ← Functor.map_comp, hfg, Functor.map_comp,
    Category.assoc, representableConvolutionUnit_naturality]
  simp only [Category.assoc]

/-- The chosen convolution of augmented standard simplices is the augmented
representable at their ordinal sum. -/
def augmentedDayConvolutionStdSimplexIso (m n : SimplexCategory) :
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj m))
      (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n))
    CategoryTheory.MonoidalCategory.DayConvolution.convolution
        (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj m))
        (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n)) ≅
      CategoryTheory.uliftYoneda.{u}.obj
        (AugmentedSimplexCategory.inclusion.obj m ⊗
          AugmentedSimplexCategory.inclusion.obj n) :=
  let h := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj m))
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n))
  let h' := standardSimplexDayConvolution.{u} m n
  h.uniqueUpToIso h'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem augmentedDayConvolutionStdSimplexIso_naturality
    {m m' n n' : SimplexCategory} (f : m ⟶ m') (g : n ⟶ n') :
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj m))
      (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n))
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj m'))
      (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n'))
    CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.{u}.map (SSet.stdSimplex.map f))
        (emptyAugmentation.{u}.map (SSet.stdSimplex.map g)) ≫
      (augmentedDayConvolutionStdSimplexIso.{u} m' n').hom =
    (augmentedDayConvolutionStdSimplexIso.{u} m n).hom ≫
      CategoryTheory.uliftYoneda.{u}.map
        (AugmentedSimplexCategory.inclusion.map f ⊗ₘ
          AugmentedSimplexCategory.inclusion.map g) := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj m))
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n))
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj m'))
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.obj n'))
  apply Functor.hom_ext_of_isLeftKanExtension _
    (CategoryTheory.MonoidalCategory.DayConvolution.unit
      (emptyAugmentation.obj (SSet.stdSimplex.obj m))
      (emptyAugmentation.obj (SSet.stdSimplex.obj n)))
  unfold CategoryTheory.MonoidalCategory.DayConvolution.map
  rw [Functor.whiskerLeft_comp, ← Category.assoc,
    Functor.descOfIsLeftKanExtension_fac]
  simp only [augmentedDayConvolutionStdSimplexIso]
  slice_lhs 2 3 =>
    rw [CategoryTheory.MonoidalCategory.DayConvolution.unit_uniqueUpToIso_hom]
  rw [Functor.whiskerLeft_comp]
  slice_rhs 1 2 =>
    rw [CategoryTheory.MonoidalCategory.DayConvolution.unit_uniqueUpToIso_hom]
  rw [← standardSimplexDayConvolution_map f g]
  unfold CategoryTheory.MonoidalCategory.DayConvolution.map
  symm
  apply Functor.descOfIsLeftKanExtension_fac

/-- Restricting the preceding augmented isomorphism gives the representable
calculation for the ordinary simplicial join. -/
def simplicialJoinStdSimplexIsoRaw (m n : SimplexCategory) :
    simplicialJoin (SSet.stdSimplex.obj m) (SSet.stdSimplex.obj n) ≅
      forgetAugmentation.{u}.obj
        (CategoryTheory.uliftYoneda.{u}.obj
          (AugmentedSimplexCategory.inclusion.obj m ⊗
            AugmentedSimplexCategory.inclusion.obj n)) :=
  forgetAugmentation.{u}.mapIso (augmentedDayConvolutionStdSimplexIso.{u} m n)

theorem simplicialJoinStdSimplexIsoRaw_naturality
    {m m' n n' : SimplexCategory} (f : m ⟶ m') (g : n ⟶ n') :
    simplicialJoinMap (SSet.stdSimplex.map f) (SSet.stdSimplex.map g) ≫
        (simplicialJoinStdSimplexIsoRaw.{u} m' n').hom =
      (simplicialJoinStdSimplexIsoRaw.{u} m n).hom ≫
        forgetAugmentation.{u}.map
          (CategoryTheory.uliftYoneda.{u}.map
            (AugmentedSimplexCategory.inclusion.map f ⊗ₘ
              AugmentedSimplexCategory.inclusion.map g)) := by
  convert congrArg (fun k ↦ forgetAugmentation.{u}.map k)
      (augmentedDayConvolutionStdSimplexIso_naturality.{u} f g) using 1 <;>
    rfl

/-- Naturality for a right-block coface, the form used in the join-horn
filtration. -/
theorem simplicialJoinStdSimplexIsoRaw_naturality_rightCoface
    (m n : ℕ) (j : Fin (n + 2)) :
    simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
        (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
        (simplicialJoinStdSimplexIsoRaw.{u}
          (SimplexCategory.mk m) (SimplexCategory.mk (n + 1))).hom =
      (simplicialJoinStdSimplexIsoRaw.{u}
          (SimplexCategory.mk m) (SimplexCategory.mk n)).hom ≫
        forgetAugmentation.{u}.map
          (CategoryTheory.uliftYoneda.{u}.map
            (AugmentedSimplexCategory.inclusion.map (𝟙 _) ⊗ₘ
              AugmentedSimplexCategory.inclusion.map
                (SimplexCategory.δ j))) := by
  simpa using simplicialJoinStdSimplexIsoRaw_naturality.{u}
    (𝟙 (SimplexCategory.mk m)) (SimplexCategory.δ j)

lemma augmentedInclusion_tensor_rightCoface (m n : ℕ) (j : Fin (n + 2)) :
    AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk m)) ⊗ₘ
        AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ j) =
      AugmentedSimplexCategory.inclusion.map
        (SimplexCategory.δ
          (⟨m + 1 + j.val, by omega⟩ : Fin (m + n + 3))) := by
  change AugmentedSimplexCategory.tensorHomOf (𝟙 (SimplexCategory.mk m))
      (SimplexCategory.δ j) = _
  apply SimplexCategory.Hom.ext
  ext k
  change Fin (m + n + 2) at k
  by_cases hk : k.val < m + 1
  · have hkm : k.val ≤ m := by omega
    have hlt : k.castSucc <
        (⟨m + 1 + j.val, by omega⟩ : Fin (m + n + 3)) := by
      apply Fin.mk_lt_mk.mpr
      omega
    simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
      Fin.addCases, Fin.succAbove, hkm, hlt]
  · let b : Fin (n + 1) := ⟨k.val - (m + 1), by omega⟩
    have hkm : ¬ k.val ≤ m := by omega
    have hbval : b.castSucc.val = k.val - (m + 1) := rfl
    have hkval : k.castSucc.val = k.val := rfl
    have hcastval : (Fin.cast (by omega) k :
        Fin ((m + 1) + (n + 1))).val = k.val := rfl
    let kc : Fin ((n + 1) + (m + 1)) := Fin.cast (by omega) k
    have hkc : kc.val = k.val := rfl
    have hkcast : m + 1 ≤ kc.val := by
      simpa [kc] using (Nat.le_of_not_gt hk)
    have hsubFin :
        (Fin.subNat (m + 1) kc hkcast : Fin (n + 1)) = b := by
      apply Fin.ext
      change kc.val - (m + 1) = k.val - (m + 1)
      rw [hkc]
    dsimp [kc] at hsubFin
    by_cases hb : b.castSucc < j
    · have hb' : k.val - (m + 1) < j.val := by
        exact Fin.mk_lt_mk.mp hb
      have hlt : k.castSucc <
          (⟨m + 1 + j.val, by omega⟩ : Fin (m + n + 3)) := by
        apply Fin.mk_lt_mk.mpr
        omega
      simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hkm, hsubFin, hb, hlt]
      simp only [Fin.val_cast, Fin.val_mk, Fin.val_castSucc] at *
      omega
    · have hb' : ¬ k.val - (m + 1) < j.val := by
        simpa [b, Fin.lt_def] using hb
      have hlt : ¬ k.castSucc <
          (⟨m + 1 + j.val, by omega⟩ : Fin (m + n + 3)) := by
        simp only [Fin.lt_def]
        omega
      simp [AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hkm, hsubFin, hb, hlt]
      simp only [Fin.val_cast, Fin.val_mk, Fin.val_castSucc] at *
      omega

/-- Restriction of an augmented representable at an ordinary simplex is the
ordinary standard simplex. -/
def forgetAugmentationULiftYonedaInclusionIso (n : SimplexCategory) :
    forgetAugmentation.{u}.obj
        (CategoryTheory.uliftYoneda.{u}.obj
          (AugmentedSimplexCategory.inclusion.obj n)) ≅
      SSet.stdSimplex.obj n :=
  Iso.refl _

lemma forgetAugmentationULiftYonedaInclusionIso_naturality
    {m n : SimplexCategory} (f : m ⟶ n) :
    forgetAugmentation.{u}.map
          (CategoryTheory.uliftYoneda.{u}.map
            (AugmentedSimplexCategory.inclusion.map f)) ≫
        (forgetAugmentationULiftYonedaInclusionIso.{u} n).hom =
      (forgetAugmentationULiftYonedaInclusionIso.{u} m).hom ≫
        SSet.stdSimplex.map f := by
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨x⟩
  rfl

/-- Join of standard simplices is the standard simplex on ordinal sum. -/
def simplicialJoinStdSimplexIso (m n : SimplexCategory) :
    simplicialJoin (SSet.stdSimplex.obj m) (SSet.stdSimplex.obj n) ≅
      SSet.stdSimplex.obj (AugmentedSimplexCategory.tensorObjOf m n) :=
  simplicialJoinStdSimplexIsoRaw.{u} m n ≪≫
    forgetAugmentationULiftYonedaInclusionIso.{u}
      (AugmentedSimplexCategory.tensorObjOf m n)

/-- Numerical form of `simplicialJoinStdSimplexIso`. -/
def simplicialJoinStdSimplexIsoNat (m n : ℕ) :
    simplicialJoin (Δ[m] : SSet.{u}) Δ[n] ≅ Δ[m + n + 1] :=
  simplicialJoinStdSimplexIso.{u} (SimplexCategory.mk m) (SimplexCategory.mk n)

theorem simplicialJoinStdSimplexIsoNat_naturality_rightCoface
    (m n : ℕ) (j : Fin (n + 2)) :
    simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
        (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
        (simplicialJoinStdSimplexIsoNat m (n + 1)).hom =
      (simplicialJoinStdSimplexIsoNat m n).hom ≫
        SSet.stdSimplex.map
          (SimplexCategory.δ
            (⟨m + 1 + j.val, by omega⟩ : Fin (m + n + 3))) := by
  unfold simplicialJoinStdSimplexIsoNat simplicialJoinStdSimplexIso
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc,
    simplicialJoinStdSimplexIsoRaw_naturality_rightCoface]
  rw [augmentedInclusion_tensor_rightCoface]
  simp only [Category.assoc]
  apply (cancel_epi (simplicialJoinStdSimplexIsoRaw.{u}
    (SimplexCategory.mk m) (SimplexCategory.mk n)).hom).2
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨x⟩
  rfl

lemma stdSimplex_range_map_delta {n : ℕ} (j : Fin (n + 2)) :
    SSet.Subcomplex.range (SSet.stdSimplex.map (SimplexCategory.δ j) :
      (Δ[n] : SSet.{u}) ⟶ Δ[n + 1]) = SSet.stdSimplex.face {j}ᶜ := by
  rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.stdSimplex.yonedaEquiv_map,
    ← SSet.stdSimplex.face_singleton_compl]

lemma representableJoin_rightCoface_range (m n : ℕ) (j : Fin (n + 2)) :
    SSet.Subcomplex.range
        (simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
            (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
          (simplicialJoinStdSimplexIsoNat m (n + 1)).hom) =
      SSet.stdSimplex.face
        ({(⟨m + 1 + j.val, by omega⟩ : Fin (m + n + 3))}ᶜ) := by
  rw [simplicialJoinStdSimplexIsoNat_naturality_rightCoface]
  rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top,
    SSet.Subcomplex.image_top, stdSimplex_range_map_delta]

lemma subcomplex_range_eq_of_precomp_iso {X Y Z : SSet.{u}}
    (e : X ⟶ Y) [IsIso e] (f : Y ⟶ Z) (g : X ⟶ Z) (h : e ≫ f = g) :
    SSet.Subcomplex.range f = SSet.Subcomplex.range g := by
  calc
    SSet.Subcomplex.range f = (⊤ : Y.Subcomplex).image f := by
      rw [SSet.Subcomplex.image_top]
    _ = (SSet.Subcomplex.range e).image f := by
      rw [SSet.Subcomplex.range_eq_top]
    _ = SSet.Subcomplex.range (e ≫ f) :=
      (SSet.Subcomplex.range_comp e f).symm
    _ = SSet.Subcomplex.range g := congrArg SSet.Subcomplex.range h

lemma isColimit_range_desc_component {J : Type*} [Category J]
    {D : J ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c)
    (t : Cocone D) (j : J) :
    SSet.Subcomplex.range (c.ι.app j ≫ hc.desc t) =
      SSet.Subcomplex.range (t.ι.app j) := by
  exact congrArg SSet.Subcomplex.range (hc.fac t j)

lemma isColimit_desc_extend_self {J : Type*} [Category J]
    {D : J ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c)
    {X : SSet.{u}} (f : c.pt ⟶ X) : hc.desc (c.extend f) = f := by
  apply hc.hom_ext
  intro j
  rw [hc.fac]
  rfl

/-! ## The paired simplices in the representable join-horn filtration -/

/-- Vertices in the first block selected by `T`. -/
def joinFirstVertices (m n : ℕ) (T : Finset (Fin (m + 1))) :
    Finset (Fin (m + n + 2)) :=
  T.map (Fin.castLEEmb (by omega))

/-- The complete second block of vertices. -/
def joinSecondVertices (m n : ℕ) : Finset (Fin (m + n + 2)) :=
  Finset.univ.map
    ⟨fun j : Fin (n + 1) ↦ ⟨m + 1 + j, by omega⟩, by
      intro a b h
      apply Fin.ext
      simpa using congrArg Fin.val h⟩

/-- Vertex set of the upper simplex in the pair indexed by `T`. -/
def joinSigmaOneVertices (m n : ℕ) (T : Finset (Fin (m + 1))) :
    Finset (Fin (m + n + 2)) :=
  joinFirstVertices m n T ∪ joinSecondVertices m n

/-- The shifted copy of the distinguished horn vertex. -/
def joinShiftedVertex (m n : ℕ) (i : Fin (n + 1)) : Fin (m + n + 2) :=
  ⟨m + 1 + i, by omega⟩

/-- Vertex set of the missing face paired with the upper simplex. -/
def joinSigmaZeroVertices (m n : ℕ) (i : Fin (n + 1))
    (T : Finset (Fin (m + 1))) : Finset (Fin (m + n + 2)) :=
  (joinSigmaOneVertices m n T).erase (joinShiftedVertex m n i)

lemma disjoint_joinFirstVertices_joinSecondVertices
    (m n : ℕ) (T : Finset (Fin (m + 1))) :
    Disjoint (joinFirstVertices m n T) (joinSecondVertices m n) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [joinFirstVertices, Finset.mem_map] at hx₁
  simp only [joinSecondVertices, Finset.mem_map, Finset.mem_univ, true_and] at hx₂
  obtain ⟨a, _, rfl⟩ := hx₁
  obtain ⟨b, hb⟩ := hx₂
  have := congrArg Fin.val hb
  simp at this
  omega

@[simp] lemma card_joinFirstVertices
    (m n : ℕ) (T : Finset (Fin (m + 1))) :
    (joinFirstVertices m n T).card = T.card := by
  simp [joinFirstVertices]

@[simp] lemma card_joinSecondVertices (m n : ℕ) :
    (joinSecondVertices m n).card = n + 1 := by
  simp [joinSecondVertices]

@[simp] lemma card_joinSigmaOneVertices
    (m n : ℕ) (T : Finset (Fin (m + 1))) :
    (joinSigmaOneVertices m n T).card = T.card + (n + 1) := by
  rw [joinSigmaOneVertices, Finset.card_union_of_disjoint
    (disjoint_joinFirstVertices_joinSecondVertices m n T)]
  simp

lemma joinShiftedVertex_mem_joinSigmaOneVertices
    (m n : ℕ) (i : Fin (n + 1)) (T : Finset (Fin (m + 1))) :
    joinShiftedVertex m n i ∈ joinSigmaOneVertices m n T := by
  simp [joinSigmaOneVertices, joinSecondVertices, joinShiftedVertex]

@[simp] lemma card_joinSigmaZeroVertices
    (m n : ℕ) (i : Fin (n + 1)) (T : Finset (Fin (m + 1))) :
    (joinSigmaZeroVertices m n i T).card = T.card + n := by
  rw [joinSigmaZeroVertices, Finset.card_erase_of_mem
    (joinShiftedVertex_mem_joinSigmaOneVertices m n i T),
    card_joinSigmaOneVertices]
  omega

/-- Ordered embedding classifying the upper simplex of the pair. -/
def joinSigmaOne (m n : ℕ) (T : Finset (Fin (m + 1))) :
    Fin (T.card + n + 1) ↪o Fin (m + n + 2) :=
  (joinSigmaOneVertices m n T).orderEmbOfFin (by
    rw [card_joinSigmaOneVertices]
    omega)

def explicitJoinSigmaOneFun (m n : ℕ) (T : Finset (Fin (m + 1)))
    (k : Fin (T.card + n + 1)) : Fin (m + n + 2) :=
  if h : k.val < T.card then
    Fin.castLE (by omega) (T.orderEmbOfFin rfl ⟨k.val, h⟩)
  else ⟨m + 1 + (k.val - T.card), by omega⟩

lemma explicitJoinSigmaOneFun_strictMono (m n : ℕ)
    (T : Finset (Fin (m + 1))) :
    StrictMono (explicitJoinSigmaOneFun m n T) := by
  intro a b hab
  simp only [Fin.lt_def] at hab ⊢
  simp only [explicitJoinSigmaOneFun]
  split_ifs with ha hb
  · exact (T.orderEmbOfFin rfl).strictMono hab
  · have hx : (T.orderEmbOfFin rfl ⟨a.val, ha⟩).val < m + 1 :=
      (T.orderEmbOfFin rfl ⟨a.val, ha⟩).isLt
    change (T.orderEmbOfFin rfl ⟨a.val, ha⟩).val <
      m + 1 + (b.val - T.card)
    omega
  · omega
  · change m + 1 + (a.val - T.card) < m + 1 + (b.val - T.card)
    omega

def explicitJoinSigmaOne (m n : ℕ) (T : Finset (Fin (m + 1))) :
    Fin (T.card + n + 1) ↪o Fin (m + n + 2) where
  toFun := explicitJoinSigmaOneFun m n T
  inj' := (explicitJoinSigmaOneFun_strictMono m n T).injective
  map_rel_iff' := (explicitJoinSigmaOneFun_strictMono m n T).le_iff_le

lemma explicitJoinSigmaOne_mem (m n : ℕ) (T : Finset (Fin (m + 1)))
    (k : Fin (T.card + n + 1)) :
    explicitJoinSigmaOne m n T k ∈ joinSigmaOneVertices m n T := by
  change explicitJoinSigmaOneFun m n T k ∈ joinSigmaOneVertices m n T
  simp only [explicitJoinSigmaOneFun]
  split_ifs with h
  · apply Finset.mem_union_left
    simp [joinFirstVertices]
  · apply Finset.mem_union_right
    simp only [joinSecondVertices, Finset.mem_map, Finset.mem_univ, true_and]
    refine ⟨⟨k.val - T.card, by omega⟩, ?_⟩
    apply Fin.ext
    simp

lemma joinSigmaOne_eq_explicitJoinSigmaOne (m n : ℕ)
    (T : Finset (Fin (m + 1))) :
    joinSigmaOne m n T = explicitJoinSigmaOne m n T := by
  symm
  apply Finset.orderEmbOfFin_unique'
  exact explicitJoinSigmaOne_mem m n T

lemma joinSigmaOne_nth_second (m n : ℕ) (T : Finset (Fin (m + 1)))
    (i : Fin (n + 1)) :
    joinSigmaOne m n T ⟨T.card + i.val, by omega⟩ =
      joinShiftedVertex m n i := by
  rw [joinSigmaOne_eq_explicitJoinSigmaOne]
  simp [explicitJoinSigmaOne, explicitJoinSigmaOneFun, joinShiftedVertex]

/-- Ordered embedding classifying the missing distinguished face. -/
def joinSigmaZero (m n : ℕ) (i : Fin (n + 1))
    (T : Finset (Fin (m + 1))) :
    Fin (T.card + n) ↪o Fin (m + n + 2) :=
  (joinSigmaZeroVertices m n i T).orderEmbOfFin
    (card_joinSigmaZeroVertices m n i T)

/-- The upper simplex, regarded as a simplex of the ambient standard simplex. -/
def joinSigmaOneSimplex (m n : ℕ) (T : Finset (Fin (m + 1))) :
    (Δ[m + n + 1] : SSet.{u}) _⦋T.card + n⦌ :=
  SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.mkHom (joinSigmaOne m n T))

lemma joinSigmaOneFace_eq_ofSimplex (m n : ℕ)
    (T : Finset (Fin (m + 1))) :
    SSet.stdSimplex.face.{u} (joinSigmaOneVertices m n T) =
      SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T) := by
  rw [SSet.stdSimplex.face_eq_ofSimplex.{u}
    (joinSigmaOneVertices m n T) (T.card + n)
    ((joinSigmaOneVertices m n T).orderIsoOfFin (by
      rw [card_joinSigmaOneVertices]
      omega))]
  congr 1

/-- Local index of the distinguished second-block vertex in `σ₁(T)`. -/
def joinSigmaOneDistinguishedIndex {m : ℕ} (n : ℕ) (T : Finset (Fin (m + 1)))
    (i : Fin (n + 1)) : Fin (T.card + n + 1) :=
  ⟨T.card + i.val, by omega⟩

lemma joinSigmaOneDistinguishedIndex_pos {m n : ℕ}
    (T : Finset (Fin (m + 1))) (i : Fin (n + 1)) (hi : 0 < i) :
    0 < joinSigmaOneDistinguishedIndex n T i := by
  apply Fin.mk_lt_mk.mpr
  change 0 < T.card + i.val
  have := Fin.mk_lt_mk.mp hi
  omega

lemma joinSigmaOneDistinguishedIndex_lt_last {m n : ℕ}
    (T : Finset (Fin (m + 1))) (i : Fin (n + 1))
    (hi : i < Fin.last n) :
    joinSigmaOneDistinguishedIndex n T i < Fin.last (T.card + n) := by
  apply Fin.mk_lt_mk.mpr
  exact Nat.add_lt_add_left (Fin.mk_lt_mk.mp hi) _

/-- The face carried by `σ₁(T)` is representable. -/
def joinSigmaOneFaceIso (m n : ℕ) (T : Finset (Fin (m + 1))) :
    (Δ[T.card + n] : SSet.{u}) ≅
      SSet.stdSimplex.face (joinSigmaOneVertices m n T) :=
  SSet.stdSimplex.isoOfRepresentableBy
    (SSet.stdSimplex.faceRepresentableBy
      (joinSigmaOneVertices m n T) (T.card + n)
      ((joinSigmaOneVertices m n T).orderIsoOfFin (by
        rw [card_joinSigmaOneVertices]
        omega)))

/-- The distinguished horn transported into the ambient join simplex. -/
def joinSigmaOneHornMap (m n : ℕ) (T : Finset (Fin (m + 1)))
    (i : Fin (n + 1)) :
    (Λ[T.card + n, joinSigmaOneDistinguishedIndex n T i] : SSet.{u}) ⟶
      (Δ[m + n + 1] : SSet.{u}) :=
  (SSet.horn (T.card + n) (joinSigmaOneDistinguishedIndex n T i)).ι ≫
    (joinSigmaOneFaceIso m n T).hom ≫
    (SSet.stdSimplex.face (joinSigmaOneVertices m n T)).ι

def joinSigmaOneHornRange (m n : ℕ) (T : Finset (Fin (m + 1)))
    (i : Fin (n + 1)) :
    (Δ[m + n + 1] : SSet.{u}).Subcomplex :=
  SSet.Subcomplex.range (joinSigmaOneHornMap m n T i)

lemma joinSigmaOneHornRange_eq_image (m n : ℕ)
    (T : Finset (Fin (m + 1))) (i : Fin (n + 1)) :
    joinSigmaOneHornRange m n T i =
      (SSet.horn (T.card + n) (joinSigmaOneDistinguishedIndex n T i)).image
        ((joinSigmaOneFaceIso m n T).hom ≫
          (SSet.stdSimplex.face (joinSigmaOneVertices m n T)).ι) := by
  rw [joinSigmaOneHornRange, joinSigmaOneHornMap,
    SSet.Subcomplex.range_comp]
  congr 1
  exact Subfunctor.range_ι _

lemma joinSigmaOneHornRange_le_face (m n : ℕ)
    (T : Finset (Fin (m + 1))) (i : Fin (n + 1)) :
    joinSigmaOneHornRange m n T i ≤
      SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T) := by
  rw [← joinSigmaOneFace_eq_ofSimplex]
  rw [joinSigmaOneHornRange, joinSigmaOneHornMap,
    SSet.Subcomplex.range_comp]
  rw [SSet.Subcomplex.image_comp]
  simpa using SSet.Subcomplex.image_le_range
    ((SSet.Subcomplex.range
      (SSet.horn (T.card + n) (joinSigmaOneDistinguishedIndex n T i)).ι).image
        (joinSigmaOneFaceIso m n T).hom)
    (SSet.stdSimplex.face (joinSigmaOneVertices m n T)).ι

/-- Join of a representable with the specified horn, as a map to the ambient
representable join simplex. -/
def representableJoinHornMap (m n : ℕ) (i : Fin (n + 1)) :
    simplicialJoin (Δ[m] : SSet.{u}) Λ[n, i] ⟶ Δ[m + n + 1] :=
  simplicialJoinMap (X := (Δ[m] : SSet.{u})) (X' := Δ[m])
      (Y := Λ[n, i]) (Y' := Δ[n]) (𝟙 _) (SSet.horn n i).ι ≫
    (simplicialJoinStdSimplexIsoNat m n).hom

/-- The initial term of the paired-simplex filtration. -/
def representableJoinHornInitial (m n : ℕ) (i : Fin (n + 1)) :
    (Δ[m + n + 1] : SSet.{u}).Subcomplex :=
  SSet.Subcomplex.range (representableJoinHornMap m n i)

/-- Cardinal filtration obtained by adjoining all paired upper simplices with
at most `r` selected first-block vertices. -/
def representableJoinHornStage (m n : ℕ) (i : Fin (n + 1)) (r : ℕ) :
    (Δ[m + n + 1] : SSet.{u}).Subcomplex :=
  representableJoinHornInitial m n i ⊔
    ⨆ (T : Finset (Fin (m + 1))), ⨆ (_ : T.card ≤ r),
      SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T)

lemma representableJoinHornStage_monotone (m n : ℕ) (i : Fin (n + 1)) :
    Monotone (representableJoinHornStage m n i) := by
  intro r s hrs
  rw [representableJoinHornStage, representableJoinHornStage]
  apply sup_le_sup_left
  apply iSup_mono
  intro T
  apply iSup_mono'
  intro hT
  exact ⟨le_trans hT hrs, le_rfl⟩

lemma representableJoinHornStage_zero_le (m n : ℕ) (i : Fin (n + 1)) :
    representableJoinHornInitial m n i ≤ representableJoinHornStage m n i 0 := by
  exact le_sup_left

lemma joinSigmaOne_of_card_le_stage (m n : ℕ) (i : Fin (n + 1))
    (r : ℕ) (T : Finset (Fin (m + 1))) (hT : T.card ≤ r) :
    SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T) ≤
      representableJoinHornStage m n i r := by
  rw [representableJoinHornStage]
  exact le_sup_of_le_right (le_iSup_of_le T (le_iSup_of_le hT le_rfl))

lemma joinSigmaOneVertices_univ (m n : ℕ) :
    joinSigmaOneVertices m n (Finset.univ : Finset (Fin (m + 1))) =
      Finset.univ := by
  ext x
  simp only [joinSigmaOneVertices, Finset.mem_union, joinFirstVertices,
    joinSecondVertices, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro _
    simp
  · intro _
    by_cases hx : x.val < m + 1
    · left
      exact ⟨⟨x.val, hx⟩, by ext; simp⟩
    · right
      refine ⟨⟨x.val - (m + 1), by omega⟩, ?_⟩
      ext
      simp
      omega

/-- The cardinal filtration is exhaustive after all first-block vertices have
been admitted. -/
lemma representableJoinHornStage_eq_top (m n : ℕ) (i : Fin (n + 1)) :
    representableJoinHornStage m n i (m + 1) = ⊤ := by
  apply top_unique
  have h := joinSigmaOne_of_card_le_stage m n i (m + 1)
    (Finset.univ : Finset (Fin (m + 1))) (by simp)
  rw [← joinSigmaOneFace_eq_ofSimplex] at h
  simpa [joinSigmaOneVertices_univ] using h

/-- The lattice square which adjoins one paired upper simplex to a filtration
term.  Its upper-left corner is the actual intersection, so this statement is
independent of the later horn identification. -/
lemma representableJoinHornStage_adjoin_bicartSq
    (m n r : ℕ) (i : Fin (n + 1)) (T : Finset (Fin (m + 1))) :
    SSet.Subcomplex.BicartSq
      (representableJoinHornStage m n i r ⊓
        SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T))
      (representableJoinHornStage m n i r)
      (SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T))
      (representableJoinHornStage m n i r ⊔
        SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T)) where
  sup_eq := rfl
  inf_eq := rfl

/-- Adjoining a paired upper simplex is an actual pushout along its
intersection with the preceding filtration term. -/
lemma representableJoinHornStage_adjoin_isPushout
    (m n r : ℕ) (i : Fin (n + 1)) (T : Finset (Fin (m + 1))) :
    IsPushout
      (SSet.Subcomplex.homOfLE (inf_le_left :
        representableJoinHornStage m n i r ⊓
          SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T) ≤
            representableJoinHornStage m n i r))
      (SSet.Subcomplex.homOfLE (inf_le_right :
        representableJoinHornStage m n i r ⊓
          SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T) ≤
            SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m n T)))
      (SSet.Subcomplex.homOfLE le_sup_left)
      (SSet.Subcomplex.homOfLE le_sup_right) :=
  (representableJoinHornStage_adjoin_bicartSq m n r i T).isPushout

/-- The chosen internal hom for Day convolution on augmented simplicial sets,
obtained by taking the explicit Type-valued end pointwise. -/
def augmentedDayInternalHom (F G : AugmentedSSet.{u}) : AugmentedSSet.{u} :=
  (CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor F).obj G ⋙
    Limits.chosenEndFunctor (J := AugmentedSimplexCategoryᵒᵖ) (C := Type u)

/-- The chosen pointwise end has the universal structure required of the Day
convolution internal hom. -/
def augmentedDayInternalHomStructure (F G : AugmentedSSet.{u}) :
    CategoryTheory.MonoidalCategory.DayConvolutionInternalHom F G
      (augmentedDayInternalHom F G) where
  π c j := Limits.chosenEnd.π
    ((CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor F).obj G |>.obj c) j
  hπ c _ _ f := Limits.chosenEnd.condition _ f
  isLimitWedge c := Limits.ChosenEndsOfShape.isEnd _
  map_comp_π f j := by
    change Limits.chosenEnd.map
        ((CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor F).obj G |>.map f) ≫
          Limits.chosenEnd.π _ j = _
    rw [Limits.chosenEnd.map_π]
    rfl

theorem dayConvolutionMap_comp
    {F F' F'' G G' G'' : AugmentedSSet.{u}}
    [CategoryTheory.MonoidalCategory.DayConvolution F G]
    [CategoryTheory.MonoidalCategory.DayConvolution F' G']
    [CategoryTheory.MonoidalCategory.DayConvolution F'' G'']
    (f : F ⟶ F') (f' : F' ⟶ F'') (g : G ⟶ G') (g' : G' ⟶ G'') :
    CategoryTheory.MonoidalCategory.DayConvolution.map f g ≫
        CategoryTheory.MonoidalCategory.DayConvolution.map f' g' =
      CategoryTheory.MonoidalCategory.DayConvolution.map (f ≫ f') (g ≫ g') := by
  apply Functor.hom_ext_of_isLeftKanExtension _
    (CategoryTheory.MonoidalCategory.DayConvolution.unit F G)
  unfold CategoryTheory.MonoidalCategory.DayConvolution.map
  rw [Functor.whiskerLeft_comp, ← Category.assoc]
  rw [Functor.descOfIsLeftKanExtension_fac]
  rw [Category.assoc, Functor.descOfIsLeftKanExtension_fac]
  rw [Functor.descOfIsLeftKanExtension_fac]
  rw [← Category.assoc]
  rw [← Functor.map_comp]
  congr 2

@[simp]
theorem dayConvolutionMap_id
    (F G : AugmentedSSet.{u})
    [CategoryTheory.MonoidalCategory.DayConvolution F G] :
    CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F) (𝟙 G) = 𝟙 _ := by
  apply Functor.hom_ext_of_isLeftKanExtension _
    (CategoryTheory.MonoidalCategory.DayConvolution.unit F G)
  unfold CategoryTheory.MonoidalCategory.DayConvolution.map
  rw [Functor.descOfIsLeftKanExtension_fac]
  have h : (𝟙 F ×ₘ 𝟙 G) = 𝟙 (F, G) := by ext <;> simp
  rw [h]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.whiskerLeft_id', Category.comp_id]

/-- The ordinary simplicial join as an actual bifunctor.  Its object formula
is the restriction of the chosen augmented Day convolution. -/
def ordinaryJoinBifunctor : SSet.{u} × SSet.{u} ⥤ SSet.{u} where
  obj X := simplicialJoin X.1 X.2
  map f := simplicialJoinMap f.1 f.2
  map_id X := by
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj X.1) (emptyAugmentation.{u}.obj X.2)
    apply NatTrans.ext
    funext U
    change (CategoryTheory.MonoidalCategory.DayConvolution.map
      (emptyAugmentation.{u}.map (𝟙 X.1))
      (emptyAugmentation.{u}.map (𝟙 X.2))).app _ = _
    rw [emptyAugmentation.map_id, emptyAugmentation.map_id,
      dayConvolutionMap_id]
    rfl
  map_comp {X Y Z} f g := by
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj X.1) (emptyAugmentation.{u}.obj X.2)
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj Y.1) (emptyAugmentation.{u}.obj Y.2)
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj Z.1) (emptyAugmentation.{u}.obj Z.2)
    apply NatTrans.ext
    funext U
    change (CategoryTheory.MonoidalCategory.DayConvolution.map
      (emptyAugmentation.{u}.map (f.1 ≫ g.1))
      (emptyAugmentation.{u}.map (f.2 ≫ g.2))).app _ = _
    rw [emptyAugmentation.map_comp, emptyAugmentation.map_comp,
      ← dayConvolutionMap_comp]
    rfl

/-- The bifunctor object is the previously defined simplicial join. -/
def ordinaryJoinBifunctorObjIso (X Y : SSet.{u}) :
    ordinaryJoinBifunctor.{u}.obj (X, Y) ≅ simplicialJoin X Y :=
  Iso.refl _

lemma ordinaryJoinBifunctor_map_isIso {X X' Y Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') [IsIso f] [IsIso g] :
    IsIso (ordinaryJoinBifunctor.{u}.map
      ((f, g) : (X, Y) ⟶ (X', Y'))) := by
  let fg : (X, Y) ⟶ (X', Y') := (f, g)
  letI : IsIso fg := by
    apply IsIso.mk
    refine ⟨(inv f, inv g), ?_, ?_⟩ <;> ext <;> simp [fg]
  change IsIso (ordinaryJoinBifunctor.{u}.map fg)
  infer_instance

theorem dayInternalHomMap_comp
    {F G G' G'' H H' H'' : AugmentedSSet.{u}}
    (ℓ : CategoryTheory.MonoidalCategory.DayConvolutionInternalHom F G H)
    (ℓ' : CategoryTheory.MonoidalCategory.DayConvolutionInternalHom F G' H')
    (ℓ'' : CategoryTheory.MonoidalCategory.DayConvolutionInternalHom F G'' H'')
    (f : G ⟶ G') (g : G' ⟶ G'') :
    ℓ.map (f ≫ g) ℓ'' = ℓ.map f ℓ' ≫ ℓ'.map g ℓ'' := by
  apply NatTrans.ext
  funext c
  apply Wedge.IsLimit.hom_ext (ℓ''.isLimitWedge c)
  rintro (j | j)
  · change (ℓ.map (f ≫ g) ℓ'').app c ≫
      ℓ''.π c (Opposite.op (WithInitial.of j)) =
        (ℓ.map f ℓ').app c ≫ (ℓ'.map g ℓ'').app c ≫
          ℓ''.π c (Opposite.op (WithInitial.of j))
    rw [ℓ.map_app_comp_π, NatTrans.comp_app,
      ℓ'.map_app_comp_π, ← Category.assoc, ℓ.map_app_comp_π]
    simp
  · change (ℓ.map (f ≫ g) ℓ'').app c ≫
      ℓ''.π c (Opposite.op WithInitial.star) =
        (ℓ.map f ℓ').app c ≫ (ℓ'.map g ℓ'').app c ≫
          ℓ''.π c (Opposite.op WithInitial.star)
    rw [ℓ.map_app_comp_π, NatTrans.comp_app,
      ℓ'.map_app_comp_π, ← Category.assoc, ℓ.map_app_comp_π]
    simp

/-- Day convolution by a fixed augmented simplicial set, as a functor in the
right variable. -/
def augmentedDayTensorLeft (F : AugmentedSSet.{u}) :
    AugmentedSSet.{u} ⥤ AugmentedSSet.{u} where
  obj K :=
    letI := augmentedDayConvolution F K
    CategoryTheory.MonoidalCategory.DayConvolution.convolution F K
  map {K K'} f := by
    letI := augmentedDayConvolution F K
    letI := augmentedDayConvolution F K'
    exact CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F) f
  map_id K := by
    letI := augmentedDayConvolution F K
    exact dayConvolutionMap_id F K
  map_comp {K K' K''} f g := by
    letI := augmentedDayConvolution F K
    letI := augmentedDayConvolution F K'
    letI := augmentedDayConvolution F K''
    exact (dayConvolutionMap_comp (𝟙 F) (𝟙 F) f g).symm

set_option backward.isDefEq.respectTransparency false in
/-- The chosen Day internal hom, functorial in its target. -/
def augmentedDayInternalHomFunctor (F : AugmentedSSet.{u}) :
    AugmentedSSet.{u} ⥤ AugmentedSSet.{u} where
  obj G := augmentedDayInternalHom F G
  map {G G'} f :=
    (augmentedDayInternalHomStructure F G).map f
      (augmentedDayInternalHomStructure F G')
  map_id G := by
    apply NatTrans.ext
    funext c
    apply Wedge.IsLimit.hom_ext
      ((augmentedDayInternalHomStructure F G).isLimitWedge c)
    rintro (j | j)
    · change ((augmentedDayInternalHomStructure F G).map (𝟙 G)
          (augmentedDayInternalHomStructure F G)).app c ≫
          (augmentedDayInternalHomStructure F G).π c
            (Opposite.op (WithInitial.of j)) = _
      rw [(augmentedDayInternalHomStructure F G).map_app_comp_π]
      simp
    · change ((augmentedDayInternalHomStructure F G).map (𝟙 G)
          (augmentedDayInternalHomStructure F G)).app c ≫
          (augmentedDayInternalHomStructure F G).π c
            (Opposite.op WithInitial.star) = _
      rw [(augmentedDayInternalHomStructure F G).map_app_comp_π]
      simp
  map_comp f g :=
    dayInternalHomMap_comp
      (augmentedDayInternalHomStructure F _)
      (augmentedDayInternalHomStructure F _)
      (augmentedDayInternalHomStructure F _) f g
/-- The tensor-hom correspondence for augmented Day convolution. -/
def augmentedDayHomEquiv (F K G : AugmentedSSet.{u}) :
    letI := augmentedDayConvolution F K
    (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K ⟶ G) ≃
      (K ⟶ augmentedDayInternalHom F G) := by
  letI hFK := augmentedDayConvolution F K
  letI hFH := augmentedDayConvolution F (augmentedDayInternalHom F G)
  let ℓG := augmentedDayInternalHomStructure F G
  let ℓFK := augmentedDayInternalHomStructure F
    (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K)
  letI hFHK := augmentedDayConvolution F (augmentedDayInternalHom F
    (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K))
  let ℓFH := augmentedDayInternalHomStructure F
    (CategoryTheory.MonoidalCategory.DayConvolution.convolution F
      (augmentedDayInternalHom F G))
  exact
    { toFun := fun φ ↦ ℓFK.coev_app ≫ ℓFK.map φ ℓG
      invFun := fun ψ ↦
        CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F) ψ ≫ ℓG.ev_app
      left_inv := by
        intro φ
        change CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F)
          (ℓFK.coev_app ≫ ℓFK.map φ ℓG) ≫ ℓG.ev_app = φ
        have hm := dayConvolutionMap_comp (𝟙 F) (𝟙 F)
          ℓFK.coev_app (ℓFK.map φ ℓG)
        simp only [Category.comp_id] at hm
        rw [← hm, Category.assoc, ℓFK.ev_naturality_app ℓG φ]
        rw [← Category.assoc,
          CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.left_triangle_components]
        simp
      right_inv := by
        intro ψ
        change ℓFK.coev_app ≫
          ℓFK.map
            (CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F) ψ ≫
              ℓG.ev_app) ℓG = ψ
        rw [dayInternalHomMap_comp ℓFK ℓFH ℓG]
        rw [← Category.assoc, ← ℓFK.coev_naturality_app ψ ℓFH]
        rw [Category.assoc]
        rw [CategoryTheory.MonoidalCategory.DayConvolutionInternalHom.right_triangle_components]
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- Convolution by `F` is left adjoint to the chosen Day internal hom. -/
def augmentedDayAdjunction (F : AugmentedSSet.{u}) :
    augmentedDayTensorLeft F ⊣ augmentedDayInternalHomFunctor F :=
  CategoryTheory.Adjunction.mkOfHomEquiv
    { homEquiv := fun K G ↦ augmentedDayHomEquiv F K G
      homEquiv_naturality_left_symm := by
        intro K' K G f g
        letI := augmentedDayConvolution F K'
        letI := augmentedDayConvolution F K
        letI := augmentedDayConvolution F
          ((augmentedDayInternalHomFunctor F).obj G)
        letI := augmentedDayConvolution F (augmentedDayInternalHom F G)
        change CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F)
            (f ≫ g) ≫ (augmentedDayInternalHomStructure F G).ev_app =
          CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F) f ≫
            (CategoryTheory.MonoidalCategory.DayConvolution.map (𝟙 F) g ≫
              (augmentedDayInternalHomStructure F G).ev_app)
        rw [← Category.assoc, dayConvolutionMap_comp]
        simp
      homEquiv_naturality_right := by
        intro K G G' f g
        letI := augmentedDayConvolution F K
        letI := augmentedDayConvolution F
          (augmentedDayInternalHom F
            (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K))
        let f' : CategoryTheory.MonoidalCategory.DayConvolution.convolution F K ⟶ G := f
        change (augmentedDayInternalHomStructure F
            (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K)).coev_app ≫
              (augmentedDayInternalHomStructure F
                (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K)).map (f' ≫ g)
                (augmentedDayInternalHomStructure F G') =
          ((augmentedDayInternalHomStructure F
              (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K)).coev_app ≫
            (augmentedDayInternalHomStructure F
              (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K)).map f'
              (augmentedDayInternalHomStructure F G)) ≫
            (augmentedDayInternalHomStructure F G).map g
              (augmentedDayInternalHomStructure F G')
        rw [dayInternalHomMap_comp
          (augmentedDayInternalHomStructure F
            (CategoryTheory.MonoidalCategory.DayConvolution.convolution F K))
          (augmentedDayInternalHomStructure F G)
          (augmentedDayInternalHomStructure F G')]
        simp only [Category.assoc] }

noncomputable instance augmentedDayTensorLeft_preservesColimits
    (F : AugmentedSSet.{u}) : PreservesColimits (augmentedDayTensorLeft F) :=
  (augmentedDayAdjunction F).leftAdjoint_preservesColimits

/-- The horn multicofork after singleton augmentation and convolution on the
left by an augmented standard simplex. -/
noncomputable def augmentedRepresentableJoinHornCocone (m : ℕ) {n : ℕ}
    (i : Fin (n + 1)) :
    Cocone
      ((((SSet.horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
          SSet.Subcomplex.toSSetFunctor).multispan ⋙ singletonAugmentation.{u}) ⋙
        augmentedDayTensorLeft
          (emptyAugmentation.{u}.obj (Δ[m] : SSet.{u}))) :=
  (augmentedDayTensorLeft (emptyAugmentation.{u}.obj (Δ[m] : SSet.{u}))).mapCocone
    (singletonAugmentationHornCocone.{u} i)

/-- Convolution on the left by an augmented standard simplex preserves the
positive-dimensional horn multicofork. -/
noncomputable def augmentedRepresentableJoinHornIsColimit (m : ℕ) {n : ℕ}
    (i : Fin (n + 1)) (hn : 0 < n) :
    IsColimit (augmentedRepresentableJoinHornCocone.{u} m i) := by
  let F := emptyAugmentation.{u}.obj (Δ[m] : SSet.{u})
  letI : PreservesColimitsOfSize.{0, 0} (augmentedDayTensorLeft F) :=
    (augmentedDayAdjunction F).leftAdjoint_preservesColimits
  exact isColimitOfPreserves (augmentedDayTensorLeft F)
    (singletonAugmentationHornIsColimit.{u} i hn)

/-- The ordinary simplicial cocone underlying the convolved horn
multicofork. -/
noncomputable def representableJoinHornCocone (m : ℕ) {n : ℕ}
    (i : Fin (n + 1)) :
    Cocone
      (((((SSet.horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
            SSet.Subcomplex.toSSetFunctor).multispan ⋙ singletonAugmentation.{u}) ⋙
          augmentedDayTensorLeft
            (emptyAugmentation.{u}.obj (Δ[m] : SSet.{u}))) ⋙
        forgetAugmentation.{u}) :=
  forgetAugmentation.{u}.mapCocone
    (augmentedRepresentableJoinHornCocone.{u} m i)

/-- The ordinary convolved horn multicofork is colimiting. -/
noncomputable def representableJoinHornIsColimit (m : ℕ) {n : ℕ}
    (i : Fin (n + 1)) (hn : 0 < n) :
    IsColimit (representableJoinHornCocone.{u} m i) := by
  apply evaluationJointlyReflectsColimits
  intro j
  let e := (evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
    (AugmentedSimplexCategory.inclusion.op.obj j)
  exact IsColimit.ofIsoColimit
    (isColimitOfPreserves e
      (augmentedRepresentableJoinHornIsColimit.{u} m i hn))
    (Functor.mapCoconeMapCocone _)

/-- The initial representable join-horn subcomplex is the union of the ranges
of the convolved codimension-one face pieces. -/
lemma representableJoinHornInitial_eq_iSup_multicoforkRanges
    (m n : ℕ) (i : Fin (n + 1)) (hn : 0 < n) :
    representableJoinHornInitial m n i =
      ⨆ j, SSet.Subcomplex.range
        ((representableJoinHornCocone.{u} m i).ι.app j ≫
          representableJoinHornMap m n i) := by
  exact SSet.range_eq_iSup_of_isColimit
    (representableJoinHornIsColimit.{u} m i hn)
    (representableJoinHornMap m n i)

/-- The ordinary simplicial slice underlying the augmented Day internal hom. -/
def simplicialSlice (X Q : SSet.{u}) : SSet.{u} :=
  forgetAugmentation.{u}.obj
    (augmentedDayInternalHom (emptyAugmentation.{u}.obj X)
      (emptyAugmentation.{u}.obj Q))

/-- The relative join-slice over a fixed augmented-degree point.  The point
records the base map which would be lost by merely forgetting augmentation. -/
def dayInternalHomAugmentedObject (F G : AugmentedSSet.{u}) :
    SSet.Augmented.{u} :=
  AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj
    (augmentedDayInternalHom F G)

def dayInternalHomConstantPoint (F G : AugmentedSSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) :
    (SimplicialObject.const (Type u)).obj (Limits.terminal (Type u)) ⟶
      (SimplicialObject.const (Type u)).obj
        (dayInternalHomAugmentedObject F G).right :=
  (SimplicialObject.const (Type u)).map
    (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v)))

def relativeDaySlice (F G : AugmentedSSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) :
    SSet.{u} :=
  Limits.pullback (dayInternalHomAugmentedObject F G).hom
    (dayInternalHomConstantPoint F G v)

/-- The relative slice includes into the underlying absolute Day internal hom. -/
def relativeDaySlice.ι (F G : AugmentedSSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) :
    relativeDaySlice F G v ⟶ forgetAugmentation.{u}.obj (augmentedDayInternalHom F G) :=
  Limits.pullback.fst _ _

/-- The structure map of the relative slice to the constant singleton. -/
def relativeDaySlice.toPoint (F G : AugmentedSSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) :
    relativeDaySlice F G v ⟶
      (SimplicialObject.const (Type u)).obj (Limits.terminal (Type u)) :=
  Limits.pullback.snd _ _

/-- Once the augmentation of the absolute internal hom is an inner fibration,
the relative slice is a quasicategory by base-change stability. -/
theorem relativeDaySlice_quasicategory_of_innerFibration
    (F G : AugmentedSSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star))
    [SSet.InnerFibration (dayInternalHomAugmentedObject F G).hom] :
    SSet.Quasicategory (relativeDaySlice F G v) := by
  haveI : SSet.InnerFibration (relativeDaySlice.toPoint F G v) := by
    rw [SSet.innerFibration_iff]
    exact SSet.innerFibrations.pullback_snd _ _ SSet.InnerFibration.mem
  have hT : Limits.IsTerminal
      ((SimplicialObject.const (Type u)).obj (Limits.terminal (Type u))) := by
    let t : ∀ K : SSet.{u}, K ⟶
        (SimplicialObject.const (Type u)).obj (Limits.terminal (Type u)) :=
      fun K ↦
        { app := fun _ ↦ Limits.terminal.from _
          naturality := by intros; apply Limits.terminal.hom_ext }
    apply Limits.IsTerminal.ofUniqueHom t
    intro K f
    apply NatTrans.ext
    funext n
    apply Limits.terminal.hom_ext
  exact (SSet.quasicategory_iff_of_isTerminal
    (relativeDaySlice.toPoint F G v) hT).2 inferInstance

/-- A map of augmented simplicial sets determines the distinguished
augmented-degree point of its Day internal hom. -/
def dayInternalHomStarOfMap {F G : AugmentedSSet.{u}} (a : F ⟶ G) :
    (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star) := by
  change (augmentedDayInternalHom F G).obj
    (𝟙_ AugmentedSimplexCategoryᵒᵖ)
  change Limits.Types.end_
    (((CategoryTheory.MonoidalCategory.dayConvolutionInternalHomDiagramFunctor F).obj G).obj
      (𝟙_ AugmentedSimplexCategoryᵒᵖ))
  refine ⟨?_, ?_⟩
  · intro j
    change (ihom (F.obj j)).obj (G.obj (j ⊗ 𝟙_ AugmentedSimplexCategoryᵒᵖ))
    exact MonoidalClosed.curry
      ((ρ_ (F.obj j)).hom ≫ a.app j ≫ G.map (ρ_ j).inv) PUnit.unit
  intro i j f
  dsimp
  change (ihom (F.obj i)).map (G.map (f ▷ 𝟙_ AugmentedSimplexCategoryᵒᵖ)) _ =
    (MonoidalClosed.pre (F.map f)).app (G.obj (j ⊗ 𝟙_ AugmentedSimplexCategoryᵒᵖ)) _
  rw [← comp_apply, ← comp_apply]
  apply ConcreteCategory.congr_hom
  rw [← MonoidalClosed.curry_natural_right,
    MonoidalClosed.curry_pre_app]
  congr 1
  simp only [Category.assoc, ← G.map_comp]
  rw [← a.naturality]
  simp

/-- The relative Day slice whose base point is induced by a specified map. -/
abbrev relativeDaySliceOverMap (F G : AugmentedSSet.{u}) (a : F ⟶ G) :
    SSet.{u} :=
  relativeDaySlice F G (dayInternalHomStarOfMap a)

/-- The unique map from a simplicial set to the constant simplicial singleton. -/
def toConstantTerminal (K : SSet.{u}) :
    K ⟶ (SimplicialObject.const (Type u)).obj (Limits.terminal (Type u)) where
  app _ := Limits.terminal.from _
  naturality := by intros; apply Limits.terminal.hom_ext

set_option backward.isDefEq.respectTransparency false in
/-- Maps into the relative Day slice are precisely maps into the absolute
internal hom whose augmentation is constantly the prescribed base point. -/
def relativeDaySliceHomEquiv (F G : AugmentedSSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star))
    (K : SSet.{u}) :
    (K ⟶ relativeDaySlice F G v) ≃
      { ψ : K ⟶ forgetAugmentation.{u}.obj (augmentedDayInternalHom F G) //
        ψ ≫ (dayInternalHomAugmentedObject F G).hom =
          toConstantTerminal K ≫ dayInternalHomConstantPoint F G v } := by
  exact
    { toFun := fun h ↦ ⟨h ≫ Limits.pullback.fst
          (dayInternalHomAugmentedObject F G).hom
          (dayInternalHomConstantPoint F G v), by
          dsimp
          change (h ≫ Limits.pullback.fst
            (dayInternalHomAugmentedObject F G).hom
            (dayInternalHomConstantPoint F G v)) ≫
              (dayInternalHomAugmentedObject F G).hom = _
          rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
          congr 1
          apply NatTrans.ext
          funext n
          apply Limits.terminal.hom_ext⟩
      invFun := fun ψ ↦ Limits.pullback.lift ψ.1 (toConstantTerminal K) ψ.2
      left_inv := by
        intro h
        change Limits.pullback.lift
          (h ≫ Limits.pullback.fst
            (dayInternalHomAugmentedObject F G).hom
            (dayInternalHomConstantPoint F G v)) (toConstantTerminal K) _ = h
        apply Limits.pullback.hom_ext
        · rw [Limits.pullback.lift_fst]
        · rw [Limits.pullback.lift_snd]
          apply NatTrans.ext
          funext n
          apply Limits.terminal.hom_ext
      right_inv := by
        intro ψ
        apply Subtype.ext
        change Limits.pullback.lift ψ.1 (toConstantTerminal K) _ ≫
          Limits.pullback.fst (dayInternalHomAugmentedObject F G).hom
            (dayInternalHomConstantPoint F G v) = ψ.1
        rw [Limits.pullback.lift_fst] }

/-- Fixed-base form of `relativeDaySliceHomEquiv`. -/
def relativeDaySliceOverMapHomEquiv (F G : AugmentedSSet.{u})
    (a : F ⟶ G) (K : SSet.{u}) :
    (K ⟶ relativeDaySliceOverMap F G a) ≃
      { ψ : K ⟶ forgetAugmentation.{u}.obj (augmentedDayInternalHom F G) //
        ψ ≫ (dayInternalHomAugmentedObject F G).hom =
          toConstantTerminal K ≫
            dayInternalHomConstantPoint F G (dayInternalHomStarOfMap a) } :=
  relativeDaySliceHomEquiv F G (dayInternalHomStarOfMap a) K

/-- Reassemble an augmented map from its ordinary part and its fixed value in
augmented degree.  The compatibility hypothesis is exactly the comma-square
condition for augmented simplicial objects. -/
def augmentedMapOfFixedUnderlying (K : SSet.{u}) (H : AugmentedSSet.{u})
    (v : H.obj (Opposite.op WithInitial.star))
    (ψ : K ⟶ forgetAugmentation.{u}.obj H)
    (hψ : ψ ≫
        (AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj H).hom =
      toConstantTerminal K ≫
        (SimplicialObject.const (Type u)).map
          (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v)))) :
    emptyAugmentation.{u}.obj K ⟶ H := by
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  let m : terminalAugmentedSSet.obj K ⟶ E.functor.obj H :=
    { left := ψ
      right := ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v))
      w := hψ }
  exact E.fullyFaithfulFunctor.preimage m

@[simp]
theorem forgetAugmentation_augmentedMapOfFixedUnderlying
    (K : SSet.{u}) (H : AugmentedSSet.{u})
    (v : H.obj (Opposite.op WithInitial.star))
    (ψ : K ⟶ forgetAugmentation.{u}.obj H)
    (hψ : ψ ≫
        (AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj H).hom =
      toConstantTerminal K ≫
        (SimplicialObject.const (Type u)).map
          (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v)))) :
    forgetAugmentation.{u}.map
      (augmentedMapOfFixedUnderlying K H v ψ hψ) = ψ := by
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  let m : terminalAugmentedSSet.obj K ⟶ E.functor.obj H :=
    { left := ψ
      right := ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v))
      w := hψ }
  have hm : E.functor.map (augmentedMapOfFixedUnderlying K H v ψ hψ) = m := by
    simp [augmentedMapOfFixedUnderlying, m]
  exact congrArg CommaMorphism.left hm

/-- A canonical inhabitant of the augmented degree of a singleton-augmented
simplicial set. -/
def emptyAugmentationStarPoint (K : SSet.{u}) :
    (emptyAugmentation.{u}.obj K).obj (Opposite.op WithInitial.star) :=
  Limits.terminal.from (ULift.{u} PUnit) (ULift.up PUnit.unit)

@[simp]
theorem augmentedMapOfFixedUnderlying_star
    (K : SSet.{u}) (H : AugmentedSSet.{u})
    (v : H.obj (Opposite.op WithInitial.star))
    (ψ : K ⟶ forgetAugmentation.{u}.obj H)
    (hψ : ψ ≫
        (AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj H).hom =
      toConstantTerminal K ≫
        (SimplicialObject.const (Type u)).map
          (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v)))) :
    (augmentedMapOfFixedUnderlying K H v ψ hψ).app
      (Opposite.op WithInitial.star) (emptyAugmentationStarPoint K) = v := by
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  let m : terminalAugmentedSSet.obj K ⟶ E.functor.obj H :=
    { left := ψ
      right := ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v))
      w := hψ }
  have hm : E.functor.map (augmentedMapOfFixedUnderlying K H v ψ hψ) = m := by
    simp [augmentedMapOfFixedUnderlying, m]
  have hr := congrArg CommaMorphism.right hm
  exact ConcreteCategory.congr_hom hr (emptyAugmentationStarPoint K)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of an augmented map turns a prescribed augmented-degree value
into the pullback compatibility equation on ordinary degrees. -/
theorem fixedUnderlyingConditionOfAugmentedMap
    (K : SSet.{u}) (H : AugmentedSSet.{u})
    (v : H.obj (Opposite.op WithInitial.star))
    (τ : emptyAugmentation.{u}.obj K ⟶ H)
    (hv : τ.app (Opposite.op WithInitial.star) (emptyAugmentationStarPoint K) = v) :
    forgetAugmentation.{u}.map τ ≫
        (AugmentedSimplexCategory.equivAugmentedSimplicialObject.functor.obj H).hom =
      toConstantTerminal K ≫
        (SimplicialObject.const (Type u)).map
          (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v))) := by
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  let m := E.functor.map τ
  have hr : m.right = ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v)) := by
    apply ConcreteCategory.hom_ext
    intro x
    have hx : x = emptyAugmentationStarPoint K := by
      let fx : (E.functor.obj (emptyAugmentation.obj K)).right ⟶
          (E.functor.obj (emptyAugmentation.obj K)).right :=
        ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ x))
      let ft : (E.functor.obj (emptyAugmentation.obj K)).right ⟶
          (E.functor.obj (emptyAugmentation.obj K)).right :=
        ConcreteCategory.ofHom
          (TypeCat.Fun.mk (fun _ ↦ emptyAugmentationStarPoint K))
      exact ConcreteCategory.congr_hom (Limits.terminal.hom_ext fx ft) x
    rw [hx]
    exact hv
  change m.left ≫ (E.functor.obj H).hom =
    (E.functor.obj (emptyAugmentation.obj K)).hom ≫
      (SimplicialObject.const (Type u)).map
        (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ v)))
  rw [← hr]
  exact m.w

/-- Day-convolution maps whose transpose has a prescribed augmented-degree
value.  Unlike an equation only on ordinary degrees, this definition remains
correct for the empty simplicial set. -/
def FixedBaseDayConvolutionMap (F G : AugmentedSSet.{u}) (K : SSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) :
    Type u := by
  letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj K)
  exact { φ : CategoryTheory.MonoidalCategory.DayConvolution.convolution F
      (emptyAugmentation.{u}.obj K) ⟶ G //
    ((augmentedDayHomEquiv F (emptyAugmentation.{u}.obj K) G φ).app
      (Opposite.op WithInitial.star))
        (emptyAugmentationStarPoint K) = v }

/-- Fixed-base convolution maps associated to a specified base map. -/
abbrev FixedBaseDayConvolutionMapOver (F G : AugmentedSSet.{u})
    (K : SSet.{u}) (a : F ⟶ G) : Type u :=
  FixedBaseDayConvolutionMap F G K (dayInternalHomStarOfMap a)

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-base tensor-hom correspondence: maps to the relative slice are the
Day-convolution maps whose transpose has the prescribed augmented value. -/
def relativeDaySliceFixedBaseEquiv (F G : AugmentedSSet.{u}) (K : SSet.{u})
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) :
    (K ⟶ relativeDaySlice F G v) ≃ FixedBaseDayConvolutionMap F G K v := by
  letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj K)
  let H := augmentedDayInternalHom F G
  let e := relativeDaySliceHomEquiv F G v K
  let c := augmentedDayHomEquiv F (emptyAugmentation.{u}.obj K) G
  exact
    { toFun := fun h ↦ by
        let ψ := e h
        let τ := augmentedMapOfFixedUnderlying K H v ψ.1 ψ.2
        refine ⟨c.symm τ, ?_⟩
        rw [c.apply_symm_apply]
        exact augmentedMapOfFixedUnderlying_star K H v ψ.1 ψ.2
      invFun := fun φ ↦ by
        let τ := c φ.1
        exact e.symm ⟨forgetAugmentation.map τ,
          fixedUnderlyingConditionOfAugmentedMap K H v τ φ.2⟩
      left_inv := by
        intro h
        apply e.injective
        dsimp only
        simp only [Equiv.apply_symm_apply]
        let ψ := e h
        apply Subtype.ext
        exact forgetAugmentation_augmentedMapOfFixedUnderlying K H v ψ.1 ψ.2
      right_inv := by
        intro φ
        apply Subtype.ext
        apply c.injective
        dsimp only
        simp only [Equiv.apply_symm_apply]
        let τ := c φ.1
        let hτ := fixedUnderlyingConditionOfAugmentedMap K H v τ φ.2
        change augmentedMapOfFixedUnderlying K H v
          (forgetAugmentation.map τ) hτ = τ
        let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
        apply E.functor.map_injective
        apply CommaMorphism.ext
        · exact forgetAugmentation_augmentedMapOfFixedUnderlying K H v
            (forgetAugmentation.map τ) hτ
        · apply ConcreteCategory.hom_ext
          intro x
          have hx : x = emptyAugmentationStarPoint K := by
            let fx : (E.functor.obj (emptyAugmentation.obj K)).right ⟶
                (E.functor.obj (emptyAugmentation.obj K)).right :=
              ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ x))
            let ft : (E.functor.obj (emptyAugmentation.obj K)).right ⟶
                (E.functor.obj (emptyAugmentation.obj K)).right :=
              ConcreteCategory.ofHom
                (TypeCat.Fun.mk (fun _ ↦ emptyAugmentationStarPoint K))
            exact ConcreteCategory.congr_hom (Limits.terminal.hom_ext fx ft) x
          rw [hx]
          exact augmentedMapOfFixedUnderlying_star K H v
            (forgetAugmentation.map τ) hτ |>.trans φ.2.symm }

/-- Fixed-base tensor-hom correspondence at the point induced by `a`. -/
def relativeDaySliceOverMapFixedBaseEquiv (F G : AugmentedSSet.{u})
    (K : SSet.{u}) (a : F ⟶ G) :
    (K ⟶ relativeDaySliceOverMap F G a) ≃
      FixedBaseDayConvolutionMapOver F G K a :=
  relativeDaySliceFixedBaseEquiv F G K (dayInternalHomStarOfMap a)

noncomputable def terminalAugmentedSSetFullyFaithful :
    terminalAugmentedSSet.{u}.FullyFaithful where
  preimage f := f.left
  map_preimage f := by
    apply CommaMorphism.ext
    · rfl
    · apply Limits.terminal.hom_ext
  preimage_map f := rfl

noncomputable def emptyAugmentationFullyFaithful :
    emptyAugmentation.{u}.FullyFaithful :=
  terminalAugmentedSSetFullyFaithful.{u}.comp
    AugmentedSimplexCategory.equivAugmentedSimplicialObject.fullyFaithfulInverse

noncomputable instance emptyAugmentation_full : emptyAugmentation.{u}.Full :=
  emptyAugmentationFullyFaithful.{u}.full

noncomputable instance emptyAugmentation_faithful : emptyAugmentation.{u}.Faithful :=
  emptyAugmentationFullyFaithful.{u}.faithful

end Infinity
end LeanLCAExactChallenge
