import LeanLCAExactChallenge.Infinity.LeftOuterHornBoundary
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Join boundary-horn corners -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution MonoidalCategory

/-- Arithmetic reassociation of the target of a left-block coface. -/
noncomputable def leftJoinTargetIso (m n : ℕ) :
    (Δ[m + n + 2] : SSet.{u}) ≅ Δ[(m + 1) + n + 1] :=
  SSet.stdSimplex.mapIso (eqToIso (by
    apply SimplexCategory.ext
    simp
    omega))

/-- The left-block coface in an ordinal sum, with its target arithmetic
transport made explicit. -/
def leftJoinCoface (m n : ℕ) (i : Fin (m + 2)) :
    SimplexCategory.mk (m + n + 1) ⟶
      SimplexCategory.mk ((m + 1) + n + 1) :=
  SimplexCategory.δ (Fin.castLE (by omega) i : Fin (m + n + 3)) ≫
    (eqToIso (by
      apply SimplexCategory.ext
      simp
      omega)).hom

/-- Tensoring a left coface with an identity preserves its index in the
ordinal sum, up to the canonical arithmetic transport of the target. -/
lemma augmentedInclusion_leftCoface_tensor (m n : ℕ) (i : Fin (m + 2)) :
    AugmentedSimplexCategory.inclusion.map (SimplexCategory.δ i) ⊗ₘ
        AugmentedSimplexCategory.inclusion.map (𝟙 (SimplexCategory.mk n)) =
      leftJoinCoface m n i := by
  change AugmentedSimplexCategory.tensorHomOf (SimplexCategory.δ i)
      (𝟙 (SimplexCategory.mk n)) = _
  apply SimplexCategory.Hom.ext
  ext k
  change Fin (m + n + 2) at k
  by_cases hk : k.val ≤ m
  · let kl : Fin (m + 1) := ⟨k.val, by omega⟩
    let kc : Fin ((m + 1) + (n + 1)) := Fin.cast (by omega) k
    have hkc : kc.val = k.val := rfl
    have hklt : kc.val < m + 1 := by omega
    have hkl : kc.castLT hklt = kl := by
      ext
      exact hkc
    by_cases hki : kl.castSucc < i
    · have hc : k.castSucc < Fin.castLE (by omega) i := by
        simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE] using hki
      have hcond : (⟨k.val, by omega⟩ : Fin (m + 2)) < i := by
        simpa [kl] using hki
      simp [leftJoinCoface, AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hk, kc, kl, hkl, hcond, hc]
    · have hc : ¬ k.castSucc < Fin.castLE (by omega) i := by
        simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE] using hki
      have hcond : ¬ (⟨k.val, by omega⟩ : Fin (m + 2)) < i := by
        simpa [kl] using hki
      simp [leftJoinCoface, AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
        Fin.addCases, Fin.succAbove, hk, kc, kl, hkl, hcond, hc]
  · have hc : ¬ k.castSucc < Fin.castLE (by omega) i := by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_castLE]
      omega
    simp [leftJoinCoface, AugmentedSimplexCategory.tensorHomOf, SimplexCategory.δ,
      Fin.addCases, Fin.succAbove, hk, hc]
    omega

/-- Naturality of the standard-simplex join isomorphism for a coface in the
left block. -/
theorem simplicialJoinStdSimplexIsoNat_naturality_leftCoface
    (m n : ℕ) (i : Fin (m + 2)) :
    simplicialJoinMap (SSet.stdSimplex.map (SimplexCategory.δ i))
        (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom =
      (simplicialJoinStdSimplexIsoNat m n).hom ≫
        SSet.stdSimplex.map (leftJoinCoface m n i) := by
  unfold simplicialJoinStdSimplexIsoNat simplicialJoinStdSimplexIso
  rw [Iso.trans_hom, Iso.trans_hom, ← Category.assoc]
  rw [← SSet.stdSimplex.map_id]
  have hid : (SimplexCategory.Hom.mk OrderHom.id :
      SimplexCategory.mk n ⟶ SimplexCategory.mk n) =
      𝟙 (SimplexCategory.mk n) := by
    apply SimplexCategory.Hom.ext
    rfl
  rw [hid]
  have hraw := simplicialJoinStdSimplexIsoRaw_naturality.{u}
    (SimplexCategory.δ i) (𝟙 (SimplexCategory.mk n))
  rw [hraw]
  rw [augmentedInclusion_leftCoface_tensor]
  rw [Category.assoc, Category.assoc]
  apply (cancel_epi (simplicialJoinStdSimplexIsoRaw.{u}
    (SimplexCategory.mk m) (SimplexCategory.mk n)).hom).2
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro x
  rcases x with ⟨x⟩
  rfl

lemma stdSimplex_range_map_leftJoinCoface
    (m n : ℕ) (i : Fin (m + 2)) :
    SSet.Subcomplex.range (SSet.stdSimplex.map (leftJoinCoface m n i) :
      (Δ[m + n + 1] : SSet.{u}) ⟶ Δ[(m + 1) + n + 1]) =
      (SSet.stdSimplex.face
        ({(Fin.castLE (by omega) i : Fin (m + n + 3))}ᶜ)).image
          (leftJoinTargetIso.{u} m n).hom := by
  rw [SSet.Subcomplex.range_eq_ofSimplex,
    SSet.stdSimplex.face_singleton_compl,
    SSet.Subcomplex.image_ofSimplex]
  congr 1

lemma representableJoin_leftCoface_range
    (m n : ℕ) (i : Fin (m + 2)) :
    SSet.Subcomplex.range
        (simplicialJoinMap
            (SSet.stdSimplex.map (SimplexCategory.δ i))
            (𝟙 (Δ[n] : SSet.{u})) ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) n).hom) =
      (SSet.stdSimplex.face
        ({(Fin.castLE (by omega) i : Fin (m + n + 3))}ᶜ)).image
          (leftJoinTargetIso.{u} m n).hom := by
  rw [simplicialJoinStdSimplexIsoNat_naturality_leftCoface]
  rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top,
    SSet.Subcomplex.image_top, stdSimplex_range_map_leftJoinCoface]

/-- Identify a left codimension-one face with the smaller standard simplex
before joining on the right. -/
noncomputable def ordinaryJoinLeftFaceIso
    (m n : ℕ) (j : Fin (m + 2)) :
    ordinaryJoinBifunctor.{u}.obj
        ((Δ[m] : SSet.{u}), Δ[n]) ≅
  ordinaryJoinBifunctor.{u}.obj
        ((SSet.stdSimplex.face {j}ᶜ : SSet.{u}), Δ[n]) := by
  let e := SSet.stdSimplex.faceSingletonComplIso.{u} j
  exact ordinaryJoinBifunctor.mapIso (e.prod (Iso.refl _))

@[simp]
lemma ordinaryJoinLeftFaceIso_inv
    (m n : ℕ) (j : Fin (m + 2)) :
    (ordinaryJoinLeftFaceIso.{u} m n j).inv =
      simplicialJoinMap (SSet.stdSimplex.faceSingletonComplIso j).inv
        (𝟙 (Δ[n] : SSet.{u})) := rfl

set_option maxHeartbeats 800000 in
/-- A transported left face of a representable join. -/
noncomputable def ordinaryJoinTransportedLeftLeg
    (m n : ℕ) (j : Fin (m + 2)) :
  ordinaryJoinBifunctor.{u}.obj
        ((SSet.stdSimplex.face {j}ᶜ : SSet.{u}), Δ[n]) ⟶
      Δ[(m + 1) + n + 1] :=
  (ordinaryJoinLeftFaceIso m n j).inv ≫
    simplicialJoinMap (SSet.stdSimplex.δ j) (𝟙 (Δ[n] : SSet.{u})) ≫
    (simplicialJoinStdSimplexIsoNat (m + 1) n).hom

lemma ordinaryJoinTransportedLeftLeg_range
    (m n : ℕ) (j : Fin (m + 2)) :
    SSet.Subcomplex.range (ordinaryJoinTransportedLeftLeg.{u} m n j) =
      (SSet.stdSimplex.face
        ({(Fin.castLE (by omega) j : Fin (m + n + 3))}ᶜ)).image
          (leftJoinTargetIso.{u} m n).hom := by
  let f := simplicialJoinMap (SSet.stdSimplex.δ j)
    (𝟙 (Δ[n] : SSet.{u})) ≫
      (simplicialJoinStdSimplexIsoNat (m + 1) n).hom
  have hr := subcomplex_range_eq_of_precomp_iso
    (ordinaryJoinLeftFaceIso.{u} m n j).inv f
    ((ordinaryJoinLeftFaceIso m n j).inv ≫ f) rfl
  rw [ordinaryJoinTransportedLeftLeg]
  change SSet.Subcomplex.range
    ((ordinaryJoinLeftFaceIso m n j).inv ≫ f) = _
  rw [← hr]
  exact representableJoin_leftCoface_range m n j

/-- The ordinary join, curried for the pushout-product API. -/
abbrev ordinaryJoinCurried : SSet.{u} ⥤ SSet.{u} ⥤ SSet.{u} :=
  Functor.curryObj ordinaryJoinBifunctor

/-- The canonical join pushout-product square of a boundary and a horn. -/
noncomputable def joinBoundaryHornCornerSq
    (m n : ℕ) (i : Fin (n + 1)) :=
  Functor.PushoutObjObj.ofHasPushout ordinaryJoinCurried
    ((SSet.boundary m).ι : (SSet.boundary m : SSet.{u}) ⟶ Δ[m])
    ((SSet.horn n i).ι : (Λ[n, i] : SSet.{u}) ⟶ Δ[n])

/-- The pushout-product corner map of a simplex boundary and a horn under join. -/
noncomputable def joinBoundaryHornCornerMap
    (m n : ℕ) (i : Fin (n + 1)) :
    (joinBoundaryHornCornerSq m n i).pt ⟶
      simplicialJoin (Δ[m] : SSet.{u}) Δ[n] :=
  (joinBoundaryHornCornerSq m n i).ι

@[reassoc (attr := simp)]
lemma joinBoundaryHornCornerMap_inl
    (m n : ℕ) (i : Fin (n + 1)) :
    (joinBoundaryHornCornerSq m n i).inl ≫
      joinBoundaryHornCornerMap m n i =
        simplicialJoinMap (𝟙 (Δ[m] : SSet.{u}))
          (SSet.horn n i).ι :=
  (joinBoundaryHornCornerSq m n i).inl_ι

@[reassoc (attr := simp)]
lemma joinBoundaryHornCornerMap_inr
    (m n : ℕ) (i : Fin (n + 1)) :
    (joinBoundaryHornCornerSq m n i).inr ≫
      joinBoundaryHornCornerMap m n i =
        simplicialJoinMap (SSet.boundary m).ι
          (𝟙 (Δ[n] : SSet.{u})) :=
  (joinBoundaryHornCornerSq m n i).inr_ι

/-- The boundary-join inclusion transported to the standard ambient simplex. -/
noncomputable def joinBoundaryStandardMap (m n : ℕ) :
    simplicialJoin (SSet.boundary m : SSet.{u}) Δ[n] ⟶ Δ[m + n + 1] :=
  simplicialJoinMap (SSet.boundary m).ι (𝟙 (Δ[n] : SSet.{u})) ≫
    (simplicialJoinStdSimplexIsoNat m n).hom

/-- The join boundary-horn corner transported to its standard ambient simplex. -/
noncomputable def joinBoundaryHornStandardCornerMap
    (m n : ℕ) (i : Fin (n + 1)) :
    (joinBoundaryHornCornerSq m n i).pt ⟶ Δ[m + n + 1] :=
  joinBoundaryHornCornerMap m n i ≫
    (simplicialJoinStdSimplexIsoNat m n).hom

@[reassoc (attr := simp)]
lemma joinBoundaryHornStandardCornerMap_inl
    (m n : ℕ) (i : Fin (n + 1)) :
    (joinBoundaryHornCornerSq m n i).inl ≫
      joinBoundaryHornStandardCornerMap m n i =
        representableJoinHornMap m n i := by
  unfold joinBoundaryHornStandardCornerMap
  exact joinBoundaryHornCornerMap_inl_assoc m n i _

@[reassoc (attr := simp)]
lemma joinBoundaryHornStandardCornerMap_inr
    (m n : ℕ) (i : Fin (n + 1)) :
    (joinBoundaryHornCornerSq m n i).inr ≫
      joinBoundaryHornStandardCornerMap m n i =
        joinBoundaryStandardMap m n := by
  unfold joinBoundaryHornStandardCornerMap joinBoundaryStandardMap
  exact joinBoundaryHornCornerMap_inr_assoc m n i _

/-- The range of a map from an arbitrary pushout object is the union of the
ranges of its restrictions to the two pushout legs. -/
lemma range_isPushout_map_eq_sup
    {A B C P D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P}
    (sq : IsPushout f g inl inr) (h : P ⟶ D) :
    SSet.Subcomplex.range h =
      SSet.Subcomplex.range (inl ≫ h) ⊔
        SSet.Subcomplex.range (inr ≫ h) := by
  let R := SSet.Subcomplex.range (inl ≫ h) ⊔
    SSet.Subcomplex.range (inr ≫ h)
  let h' : B ⟶ (R : SSet.{u}) :=
    SSet.Subcomplex.toRange (inl ≫ h) ≫
      SSet.Subcomplex.homOfLE le_sup_left
  let k' : C ⟶ (R : SSet.{u}) :=
    SSet.Subcomplex.toRange (inr ≫ h) ≫
      SSet.Subcomplex.homOfLE le_sup_right
  have w' : f ≫ h' = g ≫ k' := by
    apply (cancel_mono R.ι).mp
    simp only [h', k', Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι]
    rw [← Category.assoc, sq.w, Category.assoc]
  let q : P ⟶ (R : SSet.{u}) := sq.desc h' k' w'
  have hfac : q ≫ R.ι = h := by
    apply sq.hom_ext
    · dsimp only [q]
      rw [← Category.assoc, sq.inl_desc]
      dsimp only [h']
      rw [Category.assoc, SSet.Subcomplex.homOfLE_ι,
        SSet.Subcomplex.toRange_ι]
    · dsimp only [q]
      rw [← Category.assoc, sq.inr_desc]
      dsimp only [k']
      rw [Category.assoc, SSet.Subcomplex.homOfLE_ι,
        SSet.Subcomplex.toRange_ι]
  apply le_antisymm
  · calc
      SSet.Subcomplex.range h = SSet.Subcomplex.range (q ≫ R.ι) :=
        congrArg SSet.Subcomplex.range hfac.symm
      _ = (SSet.Subcomplex.range q).image R.ι :=
        SSet.Subcomplex.range_comp _ _
      _ ≤ R := (SSet.Subcomplex.image_le_range _ _).trans (by simp [R])
  · apply sup_le
    · calc
        SSet.Subcomplex.range (inl ≫ h) =
            (SSet.Subcomplex.range inl).image h :=
          SSet.Subcomplex.range_comp _ _
        _ ≤ SSet.Subcomplex.range h :=
          SSet.Subcomplex.image_le_range _ _
    · calc
        SSet.Subcomplex.range (inr ≫ h) =
            (SSet.Subcomplex.range inr).image h :=
          SSet.Subcomplex.range_comp _ _
        _ ≤ SSet.Subcomplex.range h :=
          SSet.Subcomplex.image_le_range _ _

lemma joinBoundaryHornStandardCornerMap_range
    (m n : ℕ) (i : Fin (n + 1)) :
    SSet.Subcomplex.range (joinBoundaryHornStandardCornerMap.{u} m n i) =
      representableJoinHornInitial m n i ⊔
        SSet.Subcomplex.range (joinBoundaryStandardMap m n) := by
  rw [range_isPushout_map_eq_sup
    (joinBoundaryHornCornerSq m n i).isPushout]
  rw [joinBoundaryHornStandardCornerMap_inl,
    joinBoundaryHornStandardCornerMap_inr]
  rfl

/-- External product with a fixed right augmented simplicial set. -/
def augmentedExternalProductRight (G : AugmentedSSet.{u}) :
    AugmentedSSet.{u} ⥤
      (AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ ⥤ Type u) :=
  (Functor.curryObj
    (CategoryTheory.MonoidalCategory.externalProductBifunctor
      AugmentedSimplexCategoryᵒᵖ AugmentedSimplexCategoryᵒᵖ (Type u))).flip.obj G

noncomputable instance augmentedExternalProductRight_preservesColimits
    (G : AugmentedSSet.{u}) :
    PreservesColimits (augmentedExternalProductRight G) := by
  apply preservesColimits_of_evaluation
  intro cd
  let X := G.obj cd.2
  letI : PreservesColimits (MonoidalCategory.tensorLeft X) :=
    (CategoryTheory.ihom.adjunction X).leftAdjoint_preservesColimits
  letI : PreservesColimits (MonoidalCategory.tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  dsimp [augmentedExternalProductRight, Functor.curryObj, Functor.flip]
  change PreservesColimits
    ((evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj cd.1 ⋙
      MonoidalCategory.tensorRight X)
  infer_instance

/-- Day convolution with a fixed right input. -/
noncomputable def augmentedDayTensorRight (G : AugmentedSSet.{u}) :
    AugmentedSSet.{u} ⥤ AugmentedSSet.{u} :=
  augmentedExternalProductRight G ⋙
    (CategoryTheory.MonoidalCategory.tensor
      AugmentedSimplexCategoryᵒᵖ).lan

noncomputable instance augmentedDayTensorRight_preservesColimits
    (G : AugmentedSSet.{u}) : PreservesColimits (augmentedDayTensorRight G) := by
  let T := CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ
  let L :
      (AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ ⥤ Type u) ⥤
        AugmentedSSet.{u} := T.lan
  letI : PreservesColimits L := (T.lanAdjunction (Type u)).leftAdjoint_preservesColimits
  dsimp only [augmentedDayTensorRight]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma augmentedDayTensorRight_map
    (G : AugmentedSSet.{u}) {F F' : AugmentedSSet.{u}} (f : F ⟶ F') :
    (augmentedDayTensorRight G).map f =
      (letI := augmentedDayConvolution F G
       letI := augmentedDayConvolution F' G
       CategoryTheory.MonoidalCategory.DayConvolution.map f (𝟙 G)) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma simplicialJoinRight_map_isPushout
    (Y : SSet.{u}) {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k : C ⟶ D}
    (sq : IsPushout f g h k) :
    IsPushout (simplicialJoinMap f (𝟙 Y))
      (simplicialJoinMap g (𝟙 Y))
      (simplicialJoinMap h (𝟙 Y))
      (simplicialJoinMap k (𝟙 Y)) := by
  let G := emptyAugmentation.{u}.obj Y
  have hs₀ := emptyAugmentation_map_isPushout sq
  have hs₁ := hs₀.map (augmentedDayTensorRight G)
  have hs : IsPushout
      (forgetAugmentation.map ((augmentedDayTensorRight G).map
        (emptyAugmentation.map f)))
      (forgetAugmentation.map ((augmentedDayTensorRight G).map
        (emptyAugmentation.map g)))
      (forgetAugmentation.map ((augmentedDayTensorRight G).map
        (emptyAugmentation.map h)))
      (forgetAugmentation.map ((augmentedDayTensorRight G).map
        (emptyAugmentation.map k))) := by
    apply IsPushout.of_forall_isPushout_app
    intro U
    exact hs₁.app (AugmentedSimplexCategory.inclusion.op.obj U)
  letI := augmentedDayConvolution (emptyAugmentation.obj A) G
  letI := augmentedDayConvolution (emptyAugmentation.obj B) G
  letI := augmentedDayConvolution (emptyAugmentation.obj C) G
  letI := augmentedDayConvolution (emptyAugmentation.obj D) G
  change IsPushout
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map f) (𝟙 G)))
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map g) (𝟙 G)))
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map h) (𝟙 G)))
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map k) (𝟙 G))) at hs
  change IsPushout
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map f) (emptyAugmentation.map (𝟙 Y))))
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map g) (emptyAugmentation.map (𝟙 Y))))
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map h) (emptyAugmentation.map (𝟙 Y))))
    (forgetAugmentation.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map k) (emptyAugmentation.map (𝟙 Y))))
  simpa only [emptyAugmentation.map_id] using hs

noncomputable instance forgetAugmentation_preservesColimits :
    PreservesColimits (forgetAugmentation.{u}) := by
  apply preservesColimits_of_evaluation
  intro U
  change PreservesColimits
    ((evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
      (AugmentedSimplexCategory.inclusion.op.obj U))
  infer_instance

/-- The horn face multicofork after joining on the right by a fixed simplicial
set. -/
noncomputable def rightTensorHornCocone
    (Y : SSet.{u}) {n : ℕ} (i : Fin (n + 1)) :=
  forgetAugmentation.{u}.mapCocone
    ((augmentedDayTensorRight (emptyAugmentation.{u}.obj Y)).mapCocone
      (singletonAugmentationHornCocone.{u} i))

@[implicit_reducible]
noncomputable def augmentedDayTensorRight_preservesSmallColimits
    (G : AugmentedSSet.{u}) :
    PreservesColimitsOfSize.{0, 0} (augmentedDayTensorRight G) := by
  let E := augmentedExternalProductRight G
  letI : PreservesColimitsOfSize.{0, 0} E := by
    apply preservesColimits_of_evaluation
    intro cd
    let X := G.obj cd.2
    letI : PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorLeft X) :=
      (CategoryTheory.ihom.adjunction X).leftAdjoint_preservesColimits
    letI : PreservesColimitsOfSize.{0, 0}
        (MonoidalCategory.tensorRight X) :=
      preservesColimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight X)
    letI : PreservesColimitsOfSize.{0, 0}
        ((evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj cd.1) :=
      { preservesColimitsOfShape := inferInstance }
    dsimp [E, augmentedExternalProductRight, Functor.curryObj, Functor.flip]
    change PreservesColimitsOfSize.{0, 0}
      ((evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj cd.1 ⋙
        MonoidalCategory.tensorRight X)
    infer_instance
  let T := CategoryTheory.MonoidalCategory.tensor AugmentedSimplexCategoryᵒᵖ
  let L :
      (AugmentedSimplexCategoryᵒᵖ × AugmentedSimplexCategoryᵒᵖ ⥤ Type u) ⥤
        AugmentedSSet.{u} := T.lan
  letI : PreservesColimitsOfSize.{0, 0} L :=
    (T.lanAdjunction (Type u)).leftAdjoint_preservesColimits
  change PreservesColimitsOfSize.{0, 0} (E ⋙ L)
  infer_instance

@[implicit_reducible]
noncomputable def forgetAugmentation_preservesSmallColimits :
    PreservesColimitsOfSize.{0, 0} (forgetAugmentation.{u}) := by
  apply preservesColimits_of_evaluation
  intro U
  letI : PreservesColimitsOfSize.{0, 0}
      ((evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
        (AugmentedSimplexCategory.inclusion.op.obj U)) :=
    { preservesColimitsOfShape := inferInstance }
  change PreservesColimitsOfSize.{0, 0}
    ((evaluation AugmentedSimplexCategoryᵒᵖ (Type u)).obj
      (AugmentedSimplexCategory.inclusion.op.obj U))
  infer_instance

noncomputable def rightTensorHornIsColimit
    (Y : SSet.{u}) {n : ℕ} (i : Fin (n + 1)) (hn : 0 < n) :
    IsColimit (rightTensorHornCocone Y i) := by
  let T := augmentedDayTensorRight (emptyAugmentation.{u}.obj Y)
  letI : PreservesColimitsOfSize.{0, 0} T :=
    augmentedDayTensorRight_preservesSmallColimits _
  letI : PreservesColimitsOfSize.{0, 0} forgetAugmentation.{u} :=
    forgetAugmentation_preservesSmallColimits
  exact isColimitOfPreserves forgetAugmentation.{u}
    (isColimitOfPreserves T
      (singletonAugmentationHornIsColimit.{u} i hn))

/-- A horn in the left block joined with a representable right block. -/
def leftRepresentableJoinHornMap
    (m n : ℕ) (i : Fin (m + 1)) :
    simplicialJoin (Λ[m, i] : SSet.{u}) Δ[n] ⟶ Δ[m + n + 1] :=
  simplicialJoinMap (SSet.horn m i).ι (𝟙 (Δ[n] : SSet.{u})) ≫
    (simplicialJoinStdSimplexIsoNat m n).hom

lemma leftRepresentableJoinHornRange_eq_iSup_multicoforkRanges
    (m n : ℕ) (i : Fin (m + 1)) (hm : 0 < m) :
    SSet.Subcomplex.range (leftRepresentableJoinHornMap.{u} m n i) =
      ⨆ j, SSet.Subcomplex.range
        ((rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app j ≫
          leftRepresentableJoinHornMap m n i) := by
  exact SSet.range_eq_iSup_of_isColimit
    (rightTensorHornIsColimit (Δ[n] : SSet.{u}) i hm)
    (leftRepresentableJoinHornMap m n i)

set_option maxHeartbeats 600000 in
lemma leftHornFaceJoin_comp
    (m n : ℕ) (i : Fin (m + 2))
    (j : Fin (m + 2)) (hji : j ≠ i) :
    simplicialJoinMap (SSet.horn.faceι i j hji)
        (𝟙 (Δ[n] : SSet.{u})) ≫
        leftRepresentableJoinHornMap (m + 1) n i =
      ordinaryJoinTransportedLeftLeg.{u} m n j := by
  rw [leftRepresentableJoinHornMap, ordinaryJoinTransportedLeftLeg]
  rw [← Category.assoc]
  change (_ ≫ _) ≫ (simplicialJoinStdSimplexIsoNat (m + 1) n).hom =
    (_ ≫ _) ≫ (simplicialJoinStdSimplexIsoNat (m + 1) n).hom
  apply (cancel_mono (simplicialJoinStdSimplexIsoNat (m + 1) n).hom).mpr
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.face {j}ᶜ : SSet.{u}))
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (Λ[m + 1, i] : SSet.{u}))
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (Δ[m] : SSet.{u}))
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  rw [← SSet.horn.faceSingletonComplIso_inv_ι i j hji]
  rw [ordinaryJoinLeftFaceIso_inv]
  simp only [ordinaryJoinBifunctor, simplicialJoinMap,
    emptyAugmentation.map_id]
  change Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op
        (CategoryTheory.MonoidalCategory.DayConvolution.map
          (emptyAugmentation.{u}.map
            ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫
              SSet.horn.ι i j hji))
          (𝟙 (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u})))) ≫ _ = _
  rw [emptyAugmentation.map_comp]
  change Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op (_ ≫ _) =
    Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op (_ ≫ _)
  congr 1
  rw [dayConvolutionMap_comp, dayConvolutionMap_comp]
  simp only [Category.comp_id]
  rw [← emptyAugmentation.map_comp, ← emptyAugmentation.map_comp]
  rw [Category.assoc, SSet.horn.ι_ι]
  rw [← emptyAugmentation.map_comp]

set_option maxHeartbeats 400000 in
lemma rightTensorHornCocone_right_app
    (m n : ℕ) (i : Fin (m + 2))
    (j : ({i}ᶜ : Set (Fin (m + 2)))) :
    (rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.right j) =
      simplicialJoinMap (SSet.horn.faceι i j.1 (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.2))
        (𝟙 (Δ[n] : SSet.{u})) := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (SSet.stdSimplex.face {j.1}ᶜ : SSet.{u}))
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj (Λ[m + 1, i] : SSet.{u}))
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  have hji : j.1 ≠ i := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.2
  have hface :
      (((SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
          SSet.Subcomplex.toSSetFunctor).ι.app (.right j)) =
        SSet.horn.faceι i j.1 hji := by
    rfl
  simp only [rightTensorHornCocone, singletonAugmentationHornCocone,
    Functor.mapCocone_ι_app, augmentedDayTensorRight_map]
  rw [hface]
  unfold simplicialJoinMap
  rw [emptyAugmentation.map_id]
  change Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op _ =
    Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op _
  congr 2

lemma rightTensorHornCocone_left_comp
    (m n : ℕ) (i : Fin (m + 2))
    (j : ({i}ᶜ : Set (Fin (m + 2)))) :
    (rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.right j) ≫
        leftRepresentableJoinHornMap (m + 1) n i =
      ordinaryJoinTransportedLeftLeg.{u} m n j.1 := by
  rw [rightTensorHornCocone_right_app]
  exact leftHornFaceJoin_comp m n i j.1 (by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using j.2)

lemma leftRepresentableJoinHornRange_eq_iSup_leftFaces
    (m n : ℕ) (i : Fin (m + 2)) :
    SSet.Subcomplex.range
        (leftRepresentableJoinHornMap.{u} (m + 1) n i) =
      ⨆ (j : ({i}ᶜ : Set (Fin (m + 2)))),
        SSet.Subcomplex.range
          ((rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.right j) ≫
            leftRepresentableJoinHornMap (m + 1) n i) := by
  rw [leftRepresentableJoinHornRange_eq_iSup_multicoforkRanges
    (m + 1) n i (by omega)]
  let c := rightTensorHornCocone (Δ[n] : SSet.{u}) i
  apply le_antisymm
  · apply iSup_le
    rintro (a | j)
    · let j₀ := (Limits.MultispanShape.ofLinearOrder
          ({i}ᶜ : Set (Fin (m + 2)))).fst a
      refine le_iSup_of_le j₀ ?_
      let f := Limits.WalkingMultispan.Hom.fst
        (J := Limits.MultispanShape.ofLinearOrder
          ({i}ᶜ : Set (Fin (m + 2)))) a
      let D := (((((SSet.horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
            SSet.Subcomplex.toSSetFunctor).multispan ⋙ singletonAugmentation.{u}) ⋙
          augmentedDayTensorRight (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))) ⋙
        forgetAugmentation.{u})
      let d := D.map f
      have hnat := c.ι.naturality f
      have hleg := hnat.trans (Category.comp_id _)
      rw [← hleg]
      rw [SSet.Subcomplex.range_comp]
      rw [SSet.Subcomplex.range_comp (c.ι.app (.right j₀))
        (leftRepresentableJoinHornMap (m + 1) n i)]
      apply SSet.Subcomplex.image_monotone
      change SSet.Subcomplex.range (d ≫ c.ι.app (.right j₀)) ≤ _
      rw [SSet.Subcomplex.range_comp]
      exact SSet.Subcomplex.image_le_range _ _
    · exact le_iSup (fun k ↦ SSet.Subcomplex.range
        (c.ι.app (.right k) ≫
          leftRepresentableJoinHornMap (m + 1) n i)) j
  · apply iSup_le
    intro j
    exact le_iSup (fun k ↦ SSet.Subcomplex.range
      (c.ι.app k ≫ leftRepresentableJoinHornMap (m + 1) n i)) (.right j)

lemma leftRepresentableJoinHornRange_eq_iSup_transportedLeftFaces
    (m n : ℕ) (i : Fin (m + 2)) :
    SSet.Subcomplex.range
        (leftRepresentableJoinHornMap.{u} (m + 1) n i) =
      ⨆ (j : ({i}ᶜ : Set (Fin (m + 2)))),
        SSet.Subcomplex.range
          (ordinaryJoinTransportedLeftLeg.{u} m n j.1) := by
  rw [leftRepresentableJoinHornRange_eq_iSup_leftFaces]
  congr 1
  funext j
  rw [rightTensorHornCocone_left_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma simplicialJoinMap_comp_right_id
    {A B C Y : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    simplicialJoinMap f (𝟙 Y) ≫ simplicialJoinMap g (𝟙 Y) =
      simplicialJoinMap (f ≫ g) (𝟙 Y) := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj A) (emptyAugmentation.{u}.obj Y)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj B) (emptyAugmentation.{u}.obj Y)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj C) (emptyAugmentation.{u}.obj Y)
  simp only [simplicialJoinMap, emptyAugmentation.map_id]
  change Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op (_ ≫ _) = _
  congr 1
  rw [dayConvolutionMap_comp]
  rw [← emptyAugmentation.map_comp]
  simp

lemma joinBoundaryStandardMap_range_succ
    (m n : ℕ) :
    SSet.Subcomplex.range (joinBoundaryStandardMap.{u} (m + 1) n) =
      SSet.Subcomplex.range
          (leftRepresentableJoinHornMap.{u} (m + 1) n (Fin.last (m + 1))) ⊔
        SSet.Subcomplex.range
          (ordinaryJoinTransportedLeftLeg.{u} m n (Fin.last (m + 1))) := by
  let b := boundaryLastFaceBicartSq (m + 1)
  have sq := simplicialJoinRight_map_isPushout (Δ[n] : SSet.{u}) b.isPushout
  have hr := range_isPushout_map_eq_sup sq
    (joinBoundaryStandardMap (m + 1) n)
  rw [hr]
  congr 1
  · apply congrArg SSet.Subcomplex.range
    unfold joinBoundaryStandardMap leftRepresentableJoinHornMap
    rw [← Category.assoc, simplicialJoinMap_comp_right_id,
      SSet.Subcomplex.homOfLE_ι]
  · apply congrArg SSet.Subcomplex.range
    unfold joinBoundaryStandardMap ordinaryJoinTransportedLeftLeg
    rw [ordinaryJoinLeftFaceIso_inv]
    rw [← Category.assoc, simplicialJoinMap_comp_right_id,
      SSet.Subcomplex.homOfLE_ι]
    have hf := SSet.stdSimplex.faceSingletonComplIso_hom_ι
      (Fin.last (m + 1))
    have hi : (SSet.stdSimplex.face
          ({Fin.last (m + 1)}ᶜ) :
            (Δ[m + 1] : SSet.{u}).Subcomplex).ι =
        (SSet.stdSimplex.faceSingletonComplIso (Fin.last (m + 1))).inv ≫
          SSet.stdSimplex.δ (Fin.last (m + 1)) := by
      apply (cancel_epi
        (SSet.stdSimplex.faceSingletonComplIso.{u} (Fin.last (m + 1))).hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hf
    rw [hi]
    have hc := simplicialJoinMap_comp_right_id
      (Y := (Δ[n] : SSet.{u}))
      (SSet.stdSimplex.faceSingletonComplIso (Fin.last (m + 1))).inv
      (SSet.stdSimplex.δ (Fin.last (m + 1)))
    calc
      _ = (simplicialJoinMap
            (SSet.stdSimplex.faceSingletonComplIso (Fin.last (m + 1))).inv
            (𝟙 (Δ[n] : SSet.{u})) ≫
          simplicialJoinMap (SSet.stdSimplex.δ (Fin.last (m + 1)))
            (𝟙 (Δ[n] : SSet.{u}))) ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) n).hom :=
        congrArg (fun q ↦ q ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) n).hom) hc.symm
      _ = _ := Category.assoc _ _ _

end LeanLCAExactChallenge.Infinity
