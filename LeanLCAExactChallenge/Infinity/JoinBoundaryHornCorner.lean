import LeanLCAExactChallenge.Infinity.LeftOuterHornBoundary
import LeanLCAExactChallenge.Infinity.MultispanRangeMono
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

/-- Transporting a standard simplex along equality preserves vertex values. -/
lemma stdSimplex_map_eqToHom_val
    {a b d : ℕ} (h : SimplexCategory.mk a = SimplexCategory.mk b)
    (x : (Δ[a] : SSet.{u}).obj (Opposite.op (SimplexCategory.mk d)))
    (k : Fin (d + 1)) :
    ((((SSet.stdSimplex.map (eqToHom h)).app _ x) k).val) = (x k).val := by
  cases h
  rfl

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
-- This finite combinatorial normalization exceeds the default elaboration budget.
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

noncomputable instance ordinaryJoinTransportedLeftLeg_mono
    (m n : ℕ) (j : Fin (m + 2)) :
    Mono (ordinaryJoinTransportedLeftLeg.{u} m n j) := by
  let q := simplicialJoinMap (SSet.stdSimplex.δ j)
      (𝟙 (Δ[n] : SSet.{u})) ≫
    (simplicialJoinStdSimplexIsoNat (m + 1) n).hom
  haveI : Mono q := by
    change Mono (simplicialJoinMap
      (SSet.stdSimplex.map (SimplexCategory.δ j))
      (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom)
    rw [simplicialJoinStdSimplexIsoNat_naturality_leftCoface]
    haveI : Mono (SSet.stdSimplex.map (leftJoinCoface m n j)) := by
      let e : SimplexCategory.mk (m + n + 2) ≅
          SimplexCategory.mk ((m + 1) + n + 1) :=
        eqToIso (by
          apply SimplexCategory.ext
          simp
          omega)
      change Mono (SSet.stdSimplex.map
        (SimplexCategory.δ
          (Fin.castLE (show m + 2 ≤ m + n + 3 by omega) j) ≫ e.hom))
      rw [Functor.map_comp]
      haveI : Mono (SSet.stdSimplex.map
          (SimplexCategory.δ
            (Fin.castLE (show m + 2 ≤ m + n + 3 by omega) j))) := by
        change Mono (SSet.stdSimplex.δ
          (Fin.castLE (show m + 2 ≤ m + n + 3 by omega) j))
        infer_instance
      haveI : IsIso (SSet.stdSimplex.map e.hom) := inferInstance
      haveI : Mono (SSet.stdSimplex.map e.hom) := inferInstance
      infer_instance
    infer_instance
  unfold ordinaryJoinTransportedLeftLeg
  change Mono ((ordinaryJoinLeftFaceIso m n j).inv ≫ q)
  haveI : IsIso (ordinaryJoinLeftFaceIso m n j).inv := inferInstance
  haveI : Mono (ordinaryJoinLeftFaceIso m n j).inv := inferInstance
  exact mono_comp _ q

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

/-- A simplicial pushout map is monic when its two component images meet exactly
at the image of the overlap.  The proof is degreewise, using the corresponding
criterion for pushouts of types. -/
lemma mono_of_pushout_range_inter
    {A B C X : SSet.{u}} {a : A ⟶ B} {b : A ⟶ C}
    {h : B ⟶ X} {k : C ⟶ X} (w : a ≫ h = b ≫ k)
    [Mono a] [Mono b] [Mono h] [Mono k]
    (hr : SSet.Subcomplex.range (a ≫ h) =
      SSet.Subcomplex.range h ⊓ SSet.Subcomplex.range k) :
    Mono (pushout.desc h k w) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [mono_iff_injective]
  let G := (evaluation SimplexCategoryᵒᵖ (Type u)).obj U
  have hmapcol : IsColimit
      (Functor.mapCocone G (PushoutCocone.mk (pushout.inl a b)
        (pushout.inr a b) pushout.condition)) :=
    isColimitOfPreserves G (pushoutIsPushout a b)
  have hp0 := (isColimitMapCoconePushoutCoconeEquiv G pushout.condition).1 hmapcol
  have hp : IsPushout (a.app U) (b.app U)
      ((pushout.inl a b).app U) ((pushout.inr a b).app U) := by
    refine ⟨?_, ⟨hp0⟩⟩
    refine ⟨?_⟩
    have hw0 : a ≫ pushout.inl a b = b ≫ pushout.inr a b :=
      pushout.condition
    simpa only [NatTrans.comp_app] using
      congrArg (fun q : A ⟶ pushout a b => q.app U) hw0
  have hw : (a.app U) ≫ h.app U = (b.app U) ≫ k.app U := by
    simpa only [NatTrans.comp_app] using congrArg (fun q => q.app U) w
  let h₂ : IsPullback (a.app U) (b.app U) (h.app U) (k.app U) := by
    rw [Types.isPullback_iff]
    refine ⟨hw, ?_, ?_⟩
    · intro x y he
      exact (mono_iff_injective _).mp (inferInstance : Mono (b.app U)) he.2
    · intro x₂ x₃ he
      have hx : (h.app U) x₂ ∈
          (SSet.Subcomplex.range h ⊓ SSet.Subcomplex.range k).obj U := by
        exact ⟨⟨x₂, rfl⟩, ⟨x₃, he.symm⟩⟩
      rw [← hr] at hx
      obtain ⟨x₁, hx₁⟩ := hx
      change (h.app U) ((a.app U) x₁) = (h.app U) x₂ at hx₁
      have hx₁' : (a.app U) x₁ = x₂ :=
        (mono_iff_injective _).mp (inferInstance : Mono (h.app U)) hx₁
      have hx₃' : (b.app U) x₁ = x₃ :=
        (mono_iff_injective _).mp (inferInstance : Mono (k.app U))
          (by
            calc
              (k.app U) ((b.app U) x₁) = (h.app U) ((a.app U) x₁) := by
                exact (congrArg (fun q => q x₁) hw).symm
              _ = (h.app U) x₂ := hx₁
              _ = (k.app U) x₃ := he)
      exact ⟨x₁, hx₁', hx₃'⟩
  have hmap : ((pushout.inl a b).app U) ≫
      ((pushout.desc h k w).app U) = h.app U := by
    simpa only [NatTrans.comp_app] using
      congrArg (fun q => q.app U) (pushout.inl_desc h k w)
  have hmap' : ((pushout.inr a b).app U) ≫
      ((pushout.desc h k w).app U) = k.app U := by
    simpa only [NatTrans.comp_app] using
      congrArg (fun q => q.app U) (pushout.inr_desc h k w)
  have hm : Mono ((pushout.desc h k w).app U) := by
    apply Types.mono_of_isPushout_of_isPullback hp h₂ hmap hmap'
    intro x y hx hy he
    exact (mono_iff_injective _).mp (inferInstance : Mono (k.app U)) he
  exact (mono_iff_injective _).mp hm

/-- The boundary is the linear multicoequalizer of its codimension-one faces. -/
def boundaryMulticoequalizerDiagram (n : ℕ) :
    SSet.Subcomplex.MulticoequalizerDiagram
      (SSet.boundary n)
      (fun j : Fin (n + 1) => SSet.stdSimplex.face {j}ᶜ)
      (fun j k => SSet.stdSimplex.face {j, k}ᶜ) where
  iSup_eq := (SSet.boundary_eq_iSup n).symm
  eq_inf j k := by
    rw [SSet.stdSimplex.face_inter_face]
    congr 1
    ext x
    simp

noncomputable def boundaryMulticoequalizerIsColimit (n : ℕ) :
    IsColimit
      ((boundaryMulticoequalizerDiagram n).multicofork.toLinearOrder.map
        SSet.Subcomplex.toSSetFunctor) :=
  (boundaryMulticoequalizerDiagram n).isColimit'

theorem boundaryMulticoequalizerIndex_isConnected (n : ℕ) :
    CategoryTheory.IsConnected
      (Limits.WalkingMultispan
        (Limits.MultispanShape.ofLinearOrder (Fin (n + 1)))) := by
  letI : Nonempty (Fin (n + 1)) := ⟨0⟩
  exact walkingMultispanOfLinearOrder_isConnected _

noncomputable def strictSingletonAugmentationBoundaryCocone (n : ℕ) :
    Cocone
      (((boundaryMulticoequalizerDiagram n).multispanIndex.toLinearOrder.map
        SSet.Subcomplex.toSSetFunctor).multispan ⋙ strictSingletonAugmentation.{u}) :=
  strictSingletonAugmentation.{u}.mapCocone
    ((boundaryMulticoequalizerDiagram n).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor)

noncomputable def strictSingletonAugmentationBoundaryIsColimit (n : ℕ) :
    IsColimit (strictSingletonAugmentationBoundaryCocone.{u} n) := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨(j | _)⟩
  · let c := (boundaryMulticoequalizerDiagram n).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor
    let e := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op j)
    have hc : IsColimit (e.mapCocone c) :=
      isColimitOfPreserves e (boundaryMulticoequalizerIsColimit n)
    exact IsColimit.ofIsoColimit
      (IsColimit.mapCoconeEquiv
        (strictSingletonAugmentationEvalOfIso.{u} j).symm hc)
      (Functor.mapCoconeMapCocone c).symm
  · let c := (boundaryMulticoequalizerDiagram n).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor
    letI : CategoryTheory.IsConnected
        (Limits.WalkingMultispan
          (Limits.MultispanShape.ofLinearOrder (Fin (n + 1)))) :=
      boundaryMulticoequalizerIndex_isConnected n
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
        change m = s.ι.app Classical.ofNonempty at hh
        exact ConcreteCategory.congr_hom hh PUnit.unit
    exact IsColimit.ofIsoColimit
      (IsColimit.mapCoconeEquiv strictSingletonAugmentationEvalStarIso.symm hc)
      (Functor.mapCoconeMapCocone c).symm

noncomputable def singletonAugmentationBoundaryCocone (n : ℕ) :
    Cocone
      (((boundaryMulticoequalizerDiagram n).multispanIndex.toLinearOrder.map
        SSet.Subcomplex.toSSetFunctor).multispan ⋙ singletonAugmentation.{u}) :=
  singletonAugmentation.{u}.mapCocone
    ((boundaryMulticoequalizerDiagram n).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor)

noncomputable def singletonAugmentationBoundaryIsColimit (n : ℕ) :
    IsColimit (singletonAugmentationBoundaryCocone.{u} n) :=
  IsColimit.mapCoconeEquiv strictSingletonAugmentationIso
    (strictSingletonAugmentationBoundaryIsColimit.{u} n)

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

lemma simplicialJoinMap_right_id_eq_augmentedDayTensorRight_map
    {X X' : SSet.{u}} (f : X ⟶ X') (Y : SSet.{u}) :
    simplicialJoinMap f (𝟙 Y) =
      forgetAugmentation.{u}.map
        ((augmentedDayTensorRight (emptyAugmentation.{u}.obj Y)).map
          (emptyAugmentation.{u}.map f)) := by
  unfold simplicialJoinMap augmentedDayTensorRight
  rw [emptyAugmentation.map_id]
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

abbrev rightTensorBoundaryDiagram (m n : ℕ) :=
  (((((boundaryMulticoequalizerDiagram (m + 1)).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor).multispan ⋙ singletonAugmentation.{u}) ⋙
    augmentedDayTensorRight
      (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))) ⋙
    forgetAugmentation.{u})

noncomputable def rightTensorBoundaryCocone (m n : ℕ) :
    Cocone (rightTensorBoundaryDiagram.{u} m n) :=
  forgetAugmentation.{u}.mapCocone
    ((augmentedDayTensorRight (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))).mapCocone
      (singletonAugmentationBoundaryCocone.{u} (m + 1)))

noncomputable def rightTensorBoundaryIsColimit (m n : ℕ) :
    IsColimit (rightTensorBoundaryCocone.{u} m n) := by
  let T := augmentedDayTensorRight (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  letI : PreservesColimitsOfSize.{0, 0} T :=
    augmentedDayTensorRight_preservesSmallColimits _
  letI : PreservesColimitsOfSize.{0, 0} forgetAugmentation.{u} :=
    forgetAugmentation_preservesSmallColimits
  exact isColimitOfPreserves forgetAugmentation.{u}
    (isColimitOfPreserves T
      (singletonAugmentationBoundaryIsColimit.{u} (m + 1)))

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
-- This finite combinatorial normalization exceeds the default elaboration budget.
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
-- This finite combinatorial normalization exceeds the default elaboration budget.
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
set_option maxHeartbeats 1200000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
lemma rightTensorHornCocone_left_comp_eq_doubleLeftCoface
    (r n : ℕ) (i : Fin (r + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (r + 3)))).L) :
    let j := a.1.1
    let k := a.1.2
    let kp := k.1.pred (Fin.ne_zero_of_lt a.2)
    let e := ordinaryJoinBifunctor.{u}.map
      (((SSet.stdSimplex.facePairComplIso.{u} j.1 k.1 a.2).hom,
        𝟙 (Δ[n] : SSet.{u})) :
        ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
          ((SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u}), Δ[n]))
    e ≫
        (rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a) ≫
          leftRepresentableJoinHornMap (r + 2) n i =
      (simplicialJoinStdSimplexIsoNat r n).hom ≫
        SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
        SSet.stdSimplex.map (leftJoinCoface (r + 1) n j.1) := by
  dsimp
  let j := a.1.1
  let k := a.1.2
  have hjk : j.1 < k.1 := a.2
  let kp := k.1.pred (Fin.ne_zero_of_lt hjk)
  let e := ordinaryJoinBifunctor.{u}.map
    (((SSet.stdSimplex.facePairComplIso.{u} j.1 k.1 hjk).hom,
      𝟙 (Δ[n] : SSet.{u})) :
      ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u}), Δ[n]))
  change e ≫ _ ≫ _ = _
  conv_rhs => rw [← Category.assoc]
  rw [← simplicialJoinStdSimplexIsoNat_naturality_leftCoface.{u}
    r n kp]
  rw [Category.assoc,
    ← simplicialJoinStdSimplexIsoNat_naturality_leftCoface.{u}
      (r + 1) n j.1]
  rw [leftRepresentableJoinHornMap, ← Category.assoc]
  change ((e ≫
      (rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a)) ≫
      simplicialJoinMap (SSet.horn (r + 2) i).ι
        (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (r + 2) n).hom =
    (simplicialJoinMap (SSet.stdSimplex.map (SimplexCategory.δ kp))
        (𝟙 (Δ[n] : SSet.{u})) ≫
      simplicialJoinMap (SSet.stdSimplex.map (SimplexCategory.δ j.1))
        (𝟙 (Δ[n] : SSet.{u}))) ≫
      (simplicialJoinStdSimplexIsoNat (r + 2) n).hom)
  rw [← Category.assoc]
  apply (cancel_mono (simplicialJoinStdSimplexIsoNat (r + 2) n).hom).mpr
  simp only [e, ordinaryJoinBifunctor, rightTensorHornCocone,
    singletonAugmentationHornCocone, Functor.mapCocone_ι_app]
  let l := (((SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
    SSet.Subcomplex.toSSetFunctor).ι.app (.left a))
  have hface : l ≫ (SSet.horn (r + 2) i).ι =
      (SSet.stdSimplex.face {j.1, k.1}ᶜ).ι := by
    rfl
  let T := augmentedDayTensorRight
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  have hT : T.map (emptyAugmentation.{u}.map l) ≫
        T.map (emptyAugmentation.{u}.map (SSet.horn (r + 2) i).ι) =
      T.map (emptyAugmentation.{u}.map
        (SSet.stdSimplex.face {j.1, k.1}ᶜ).ι) := by
    rw [← T.map_comp, ← emptyAugmentation.map_comp, hface]
  have hforget := congrArg forgetAugmentation.{u}.map hT
  simp only [forgetAugmentation.map_comp] at hforget
  dsimp [T, l] at hforget
  simp_rw [simplicialJoinMap_right_id_eq_augmentedDayTensorRight_map]
  slice_lhs 2 3 => rw [hforget]
  rw [← forgetAugmentation.map_comp, ← forgetAugmentation.map_comp]
  congr 1
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  rw [← emptyAugmentation.map_comp, ← emptyAugmentation.map_comp]
  congr 1
  exact SSet.stdSimplex.facePairComplIso_hom_ι' j.1 k.1 hjk

set_option maxHeartbeats 800000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
noncomputable def leftJoinPairTargetIso (r n : ℕ) :
    (Δ[r + n + 3] : SSet.{u}) ≅ Δ[(r + 2) + n + 1] :=
  SSet.stdSimplex.mapIso (eqToIso (by
    apply SimplexCategory.ext
    simp
    omega))

set_option maxHeartbeats 800000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
lemma doubleLeftCoface_std_map_eq_facePair
    (r n : ℕ) (j k : Fin (r + 3)) (hjk : j < k) :
    let kp := k.pred (Fin.ne_zero_of_lt hjk)
    let J := (Fin.castLE (by omega) j : Fin (r + n + 4))
    let K := (Fin.castLE (by omega) k : Fin (r + n + 4))
    SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
        SSet.stdSimplex.map (leftJoinCoface (r + 1) n j) =
      (SSet.stdSimplex.facePairComplIso.{u} J K (by
        simp only [Fin.lt_def]
        exact hjk)).hom ≫
        (SSet.stdSimplex.face {J, K}ᶜ).ι ≫
        (leftJoinPairTargetIso r n).hom := by
  dsimp
  let kp := k.pred (Fin.ne_zero_of_lt hjk)
  let J := (Fin.castLE (by omega) j : Fin (r + n + 4))
  let K := (Fin.castLE (by omega) k : Fin (r + n + 4))
  have hJK : J < K := by
    simp only [Fin.lt_def, J, K, Fin.val_castLE]
    exact hjk
  change SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
      SSet.stdSimplex.map (leftJoinCoface (r + 1) n j) =
    (SSet.stdSimplex.facePairComplIso J K hJK).hom ≫
      (SSet.stdSimplex.face {J, K}ᶜ).ι ≫
      (leftJoinPairTargetIso r n).hom
  rw [← Category.assoc,
    SSet.stdSimplex.facePairComplIso_hom_ι' J K hJK]
  rw [← Functor.map_comp]
  unfold leftJoinPairTargetIso
  change SSet.stdSimplex.map
      (leftJoinCoface r n kp ≫ leftJoinCoface (r + 1) n j) =
    (SSet.stdSimplex.map (SimplexCategory.δ (K.pred (Fin.ne_zero_of_lt hJK))) ≫
      SSet.stdSimplex.map (SimplexCategory.δ J)) ≫
        SSet.stdSimplex.map (eqToHom (by
          apply SimplexCategory.ext
          simp
          omega))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  have hkp :
      (Fin.castLE (show r + 2 ≤ r + n + 3 by omega) kp : Fin (r + n + 3)) =
        K.pred (Fin.ne_zero_of_lt hJK) := by
    apply Fin.ext
    simp [kp, K]
  apply SimplexCategory.Hom.ext
  ext x
  simp [leftJoinCoface, SimplexCategory.δ, Fin.succAbove, kp, J, K, hkp]
  split <;> split <;> split <;> simp_all
  all_goals
    simp only [Fin.lt_def, Fin.le_def, Fin.val_cast, Fin.val_castLE,
      Fin.val_castSucc, Fin.val_pred, Fin.val_succ] at *
    omega

lemma rightTensorHornCocone_left_comp_range
    (r n : ℕ) (i : Fin (r + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (r + 3)))).L) :
    let j := a.1.1
    let k := a.1.2
    let J := (Fin.castLE (by omega) j.1 : Fin (r + n + 4))
    let K := (Fin.castLE (by omega) k.1 : Fin (r + n + 4))
    SSet.Subcomplex.range
        ((rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a) ≫
          leftRepresentableJoinHornMap (r + 2) n i) =
      (SSet.stdSimplex.face {J, K}ᶜ).image
        (leftJoinPairTargetIso r n).hom := by
  dsimp
  let j := a.1.1
  let k := a.1.2
  have hjk : j.1 < k.1 := a.2
  let kp := k.1.pred (Fin.ne_zero_of_lt hjk)
  let J := (Fin.castLE (by omega) j.1 : Fin (r + n + 4))
  let K := (Fin.castLE (by omega) k.1 : Fin (r + n + 4))
  have hJK : J < K := by
    simp only [Fin.lt_def, J, K, Fin.val_castLE]
    exact hjk
  let e := ordinaryJoinBifunctor.{u}.map
    (((SSet.stdSimplex.facePairComplIso.{u} j.1 k.1 hjk).hom,
      𝟙 (Δ[n] : SSet.{u})) :
      ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u}), Δ[n]))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let f := (rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a) ≫
    leftRepresentableJoinHornMap (r + 2) n i
  let g := (simplicialJoinStdSimplexIsoNat r n).hom ≫
    SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
    SSet.stdSimplex.map (leftJoinCoface (r + 1) n j.1)
  have heq : e ≫ f = g := by
    exact rightTensorHornCocone_left_comp_eq_doubleLeftCoface r n i a
  calc
    SSet.Subcomplex.range f = SSet.Subcomplex.range g :=
      subcomplex_range_eq_of_precomp_iso e f g heq
    _ = SSet.Subcomplex.range
        (SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
          SSet.stdSimplex.map (leftJoinCoface (r + 1) n j.1)) := by
      symm
      apply subcomplex_range_eq_of_precomp_iso
        (simplicialJoinStdSimplexIsoNat r n).hom
      rfl
    _ = SSet.Subcomplex.range
        ((SSet.stdSimplex.facePairComplIso J K hJK).hom ≫
          (SSet.stdSimplex.face {J, K}ᶜ).ι ≫
          (leftJoinPairTargetIso r n).hom) := by
      apply congrArg SSet.Subcomplex.range
      exact doubleLeftCoface_std_map_eq_facePair r n j.1 k.1 hjk
    _ = (SSet.stdSimplex.face {J, K}ᶜ).image
        (leftJoinPairTargetIso r n).hom := by
      have hr := subcomplex_range_eq_of_precomp_iso
        (SSet.stdSimplex.facePairComplIso.{u} J K hJK).hom
        ((SSet.stdSimplex.face {J, K}ᶜ).ι ≫
          (leftJoinPairTargetIso r n).hom)
        ((SSet.stdSimplex.facePairComplIso J K hJK).hom ≫
          ((SSet.stdSimplex.face {J, K}ᶜ).ι ≫
            (leftJoinPairTargetIso r n).hom)) rfl
      rw [← hr, SSet.Subcomplex.range_comp]
      congr 1
      ext U x
      simp [SSet.Subcomplex.range]

lemma rightTensorHornCocone_left_comp_mono
    (r n : ℕ) (i : Fin (r + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (r + 3)))).L) :
    Mono ((rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a) ≫
      leftRepresentableJoinHornMap (r + 2) n i) := by
  let j := a.1.1
  let k := a.1.2
  have hjk : j.1 < k.1 := a.2
  let J := (Fin.castLE (by omega) j.1 : Fin (r + n + 4))
  let K := (Fin.castLE (by omega) k.1 : Fin (r + n + 4))
  have hJK : J < K := by
    simp only [Fin.lt_def, J, K, Fin.val_castLE]
    exact hjk
  let e := ordinaryJoinBifunctor.{u}.map
    (((SSet.stdSimplex.facePairComplIso.{u} j.1 k.1 hjk).hom,
      𝟙 (Δ[n] : SSet.{u})) :
      ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u}), Δ[n]))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let f := (rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a) ≫
    leftRepresentableJoinHornMap (r + 2) n i
  let fn := f ≫ (leftJoinPairTargetIso r n).inv
  have hr : SSet.Subcomplex.range fn =
      SSet.stdSimplex.face {J, K}ᶜ := by
    unfold fn
    rw [SSet.Subcomplex.range_comp,
      rightTensorHornCocone_left_comp_range]
    rw [← SSet.Subcomplex.image_comp]
    simp
    rfl
  let E := (asIso e).symm ≪≫ simplicialJoinStdSimplexIsoNat r n ≪≫
    SSet.stdSimplex.facePairComplIso J K hJK ≪≫
      SSet.Subcomplex.toSSetFunctor.mapIso (eqToIso hr.symm)
  haveI : Mono (SSet.Subcomplex.toRange fn) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    rw [mono_iff_injective]
    letI : Finite ((SSet.Subcomplex.toSSetFunctor.obj
        (SSet.Subcomplex.range fn)).obj U) :=
      Finite.of_injective ((SSet.Subcomplex.range fn).ι.app U)
        ((mono_iff_injective _).mp inferInstance)
    letI : Finite ((ordinaryJoinBifunctor.{u}.obj
        ((SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u}),
          (Δ[n] : SSet.{u}))).obj U) :=
      Finite.of_injective (E.app U).toEquiv (E.app U).toEquiv.injective
    apply (Finite.injective_iff_surjective_of_equiv ((E.app U).toEquiv)).2
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  haveI : Mono fn := by
    rw [← SSet.Subcomplex.toRange_ι (f := fn)]
    infer_instance
  change Mono f
  have hf : f = fn ≫ (leftJoinPairTargetIso r n).hom := by
    simp [fn]
  rw [hf]
  infer_instance

lemma ordinaryJoinTransportedLeftLeg_range_pairNormalized
    (r n : ℕ) (j : Fin (r + 3)) :
    SSet.Subcomplex.range
        (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n j ≫
          (leftJoinPairTargetIso r n).inv) =
      SSet.stdSimplex.face
        ({(Fin.castLE (by omega) j : Fin (r + n + 4))}ᶜ) := by
  rw [SSet.Subcomplex.range_comp,
    ordinaryJoinTransportedLeftLeg_range]
  rw [← SSet.Subcomplex.image_comp]
  have hi : IsIso ((leftJoinTargetIso.{u} (r + 1) n).hom ≫
      (leftJoinPairTargetIso r n).inv) := inferInstance
  rw [show (SSet.stdSimplex.face
      ({(Fin.castLE (by omega) j : Fin ((r + 1) + n + 3))}ᶜ)).image
        ((leftJoinTargetIso (r + 1) n).hom ≫
          (leftJoinPairTargetIso r n).inv) =
      SSet.stdSimplex.face
        ({(Fin.castLE (by omega) j : Fin (r + n + 4))}ᶜ) by
    ext U x
    rcases U with ⟨⟨d⟩⟩
    rw [show (leftJoinTargetIso (r + 1) n).hom ≫
        (leftJoinPairTargetIso r n).inv =
      inv ((leftJoinPairTargetIso r n).hom ≫
        (leftJoinTargetIso (r + 1) n).inv) by simp]
    rw [SSet.Subcomplex.image_inv]
    change (((leftJoinPairTargetIso r n).hom ≫
        (leftJoinTargetIso (r + 1) n).inv).app _ x ∈
          (SSet.stdSimplex.face _).obj _) ↔
      x ∈ (SSet.stdSimplex.face _).obj _
    rw [SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff]
    simp only [Finset.mem_compl, Finset.mem_singleton]
    have hval (k : Fin (d + 1)) :
        ((((leftJoinPairTargetIso r n).hom ≫
          (leftJoinTargetIso (r + 1) n).inv).app _ x) k).val =
            (x k).val := by
      simp only [leftJoinPairTargetIso, leftJoinTargetIso, Functor.mapIso_hom,
        Functor.mapIso_inv, eqToIso.hom, eqToIso.inv]
      rw [← Functor.map_comp]
      simp only [eqToHom_trans]
      exact stdSimplex_map_eqToHom_val _ x k
    constructor
    · intro h k hk
      apply h k
      apply Fin.ext
      have hv := congrArg Fin.val hk
      rw [hval]
      exact hv
    · intro h k hk
      apply h k
      apply Fin.ext
      have hv := congrArg Fin.val hk
      rw [hval] at hv
      exact hv]

noncomputable def leftRepresentableJoinHornMapPairNormalized
    (r n : ℕ) (i : Fin (r + 3)) :
    simplicialJoin (Λ[r + 2, i] : SSet.{u}) Δ[n] ⟶ Δ[r + n + 3] :=
  leftRepresentableJoinHornMap (r + 2) n i ≫
    (leftJoinPairTargetIso r n).inv

lemma rightTensorHornCocone_left_comp_range_pairNormalized
    (r n : ℕ) (i : Fin (r + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (r + 3)))).L) :
    let j := a.1.1
    let k := a.1.2
    let J := (Fin.castLE (by omega) j.1 : Fin (r + n + 4))
    let K := (Fin.castLE (by omega) k.1 : Fin (r + n + 4))
    SSet.Subcomplex.range
        ((rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a) ≫
          leftRepresentableJoinHornMapPairNormalized r n i) =
      SSet.stdSimplex.face {J, K}ᶜ := by
  dsimp
  unfold leftRepresentableJoinHornMapPairNormalized
  change SSet.Subcomplex.range
    (((rightTensorHornCocone (Δ[n] : SSet.{u}) i).ι.app (.left a) ≫
      leftRepresentableJoinHornMap (r + 2) n i) ≫
        (leftJoinPairTargetIso r n).inv) = _
  rw [SSet.Subcomplex.range_comp,
    rightTensorHornCocone_left_comp_range]
  rw [← SSet.Subcomplex.image_comp]
  simp

set_option synthInstance.maxHeartbeats 200000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
noncomputable instance leftRepresentableJoinHornMapPairNormalized_mono
    (r n : ℕ) (i : Fin (r + 3)) :
    Mono (leftRepresentableJoinHornMapPairNormalized.{u} r n i) := by
  let c := rightTensorHornCocone (Δ[n] : SSet.{u}) i
  let hc := rightTensorHornIsColimit (Δ[n] : SSet.{u}) i (by omega)
  apply mono_of_linearMultispan_ranges c
    (leftRepresentableJoinHornMapPairNormalized r n i) hc
  · rintro (a | j)
    · change Mono (((c.ι.app (.left a) ≫
          leftRepresentableJoinHornMap (r + 2) n i)) ≫
        (leftJoinPairTargetIso r n).inv)
      haveI : Mono (c.ι.app (.left a) ≫
          leftRepresentableJoinHornMap (r + 2) n i) :=
        rightTensorHornCocone_left_comp_mono r n i a
      infer_instance
    · have hj := rightTensorHornCocone_left_comp (r + 1) n i j
      change Mono (c.ι.app (.right j) ≫
        (leftRepresentableJoinHornMap (r + 2) n i ≫
          (leftJoinPairTargetIso r n).inv))
      rw [← Category.assoc, hj]
      change Mono (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n j.1 ≫
        (leftJoinPairTargetIso r n).inv)
      haveI : Mono (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n j.1) :=
        ordinaryJoinTransportedLeftLeg_mono (r + 1) n j.1
      haveI : Mono (leftJoinPairTargetIso r n).inv := inferInstance
      exact mono_comp _ _
  · intro a
    rw [rightTensorHornCocone_left_comp_range_pairNormalized]
    let j := (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (r + 3)))).fst a
    let k := (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (r + 3)))).snd a
    have hj := rightTensorHornCocone_left_comp (r + 1) n i j
    have hk := rightTensorHornCocone_left_comp (r + 1) n i k
    have hj' : c.ι.app (.right j) ≫
        leftRepresentableJoinHornMapPairNormalized r n i =
      ordinaryJoinTransportedLeftLeg (r + 1) n j.1 ≫
        (leftJoinPairTargetIso r n).inv := by
      unfold leftRepresentableJoinHornMapPairNormalized
      calc
        _ = (c.ι.app (.right j) ≫
            leftRepresentableJoinHornMap (r + 2) n i) ≫
              (leftJoinPairTargetIso r n).inv :=
          (Category.assoc _ _ _).symm
        _ = _ := congrArg (fun q ↦ q ≫
          (leftJoinPairTargetIso r n).inv) hj
    have hk' : c.ι.app (.right k) ≫
        leftRepresentableJoinHornMapPairNormalized r n i =
      ordinaryJoinTransportedLeftLeg (r + 1) n k.1 ≫
        (leftJoinPairTargetIso r n).inv := by
      unfold leftRepresentableJoinHornMapPairNormalized
      calc
        _ = (c.ι.app (.right k) ≫
            leftRepresentableJoinHornMap (r + 2) n i) ≫
              (leftJoinPairTargetIso r n).inv :=
          (Category.assoc _ _ _).symm
        _ = _ := congrArg (fun q ↦ q ≫
          (leftJoinPairTargetIso r n).inv) hk
    rw [hj', hk']
    calc
      SSet.stdSimplex.face {Fin.castLE (by omega) j.1,
          Fin.castLE (by omega) k.1}ᶜ =
        SSet.stdSimplex.face {Fin.castLE (by omega) j.1}ᶜ ⊓
          SSet.stdSimplex.face {Fin.castLE (by omega) k.1}ᶜ := by
            rw [SSet.stdSimplex.face_inter_face]
            congr 1
            ext x
            simp
      _ = SSet.Subcomplex.range
            (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n j.1 ≫
              (leftJoinPairTargetIso r n).inv) ⊓
          SSet.Subcomplex.range
            (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n k.1 ≫
              (leftJoinPairTargetIso r n).inv) := by
            rw [ordinaryJoinTransportedLeftLeg_range_pairNormalized,
              ordinaryJoinTransportedLeftLeg_range_pairNormalized]

lemma leftRepresentableJoinHornMap_mono_of_pairNormalized
    (r n : ℕ) (i : Fin (r + 3)) :
    Mono (leftRepresentableJoinHornMap.{u} (r + 2) n i) := by
  haveI : Mono (leftRepresentableJoinHornMapPairNormalized.{u} r n i) :=
    leftRepresentableJoinHornMapPairNormalized_mono r n i
  haveI : Mono (leftJoinPairTargetIso.{u} r n).hom := inferInstance
  have hf : leftRepresentableJoinHornMap.{u} (r + 2) n i =
      leftRepresentableJoinHornMapPairNormalized r n i ≫
        (leftJoinPairTargetIso r n).hom := by
    unfold leftRepresentableJoinHornMapPairNormalized
    simp
  rw [hf]
  infer_instance

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

lemma joinBoundaryStandardMap_range_eq_iSup_leftFaces
    (m n : ℕ) :
    SSet.Subcomplex.range (joinBoundaryStandardMap.{u} (m + 1) n) =
      ⨆ j : Fin (m + 2), SSet.Subcomplex.range
        (ordinaryJoinTransportedLeftLeg.{u} m n j) := by
  rw [joinBoundaryStandardMap_range_succ,
    leftRepresentableJoinHornRange_eq_iSup_transportedLeftFaces]
  apply le_antisymm
  · apply sup_le
    · apply iSup_le
      rintro ⟨j, hj⟩
      exact le_iSup
        (fun q : Fin (m + 2) ↦ SSet.Subcomplex.range
          (ordinaryJoinTransportedLeftLeg.{u} m n q)) j
    · exact le_iSup
        (fun q : Fin (m + 2) ↦ SSet.Subcomplex.range
          (ordinaryJoinTransportedLeftLeg.{u} m n q)) (Fin.last (m + 1))
  · apply iSup_le
    intro j
    by_cases hj : j = Fin.last (m + 1)
    · subst j
      exact le_sup_right
    · exact le_sup_of_le_left (le_iSup
        (fun q : ({Fin.last (m + 1)}ᶜ : Set (Fin (m + 2))) ↦
          SSet.Subcomplex.range
            (ordinaryJoinTransportedLeftLeg.{u} m n q.1))
        ⟨j, by simpa using hj⟩)

/-- The joined boundary map, with the harmless arithmetic transport on its
target removed. -/
noncomputable def normalizedJoinBoundaryStandardMap (m n : ℕ) :
    simplicialJoin (SSet.boundary (m + 1) : SSet.{u}) Δ[n] ⟶
      Δ[m + n + 2] :=
  joinBoundaryStandardMap (m + 1) n ≫ (leftJoinTargetIso m n).inv

lemma rightTensorBoundaryCocone_left_app
    (m n : ℕ)
    (a : (Limits.MultispanShape.ofLinearOrder (Fin (m + 2))).L) :
    (rightTensorBoundaryCocone.{u} m n).ι.app (.left a) =
      simplicialJoinMap
        (((boundaryMulticoequalizerDiagram (m + 1)).multicofork.toLinearOrder.map
          SSet.Subcomplex.toSSetFunctor).ι.app (.left a))
        (𝟙 (Δ[n] : SSet.{u})) := by
  simp only [rightTensorBoundaryCocone,
    singletonAugmentationBoundaryCocone,
    Functor.mapCocone_ι_app, augmentedDayTensorRight_map]
  unfold simplicialJoinMap
  rw [emptyAugmentation.map_id]
  rfl

lemma rightTensorBoundaryCocone_right_comp
    (m n : ℕ) (j : Fin (m + 2)) :
    (rightTensorBoundaryCocone.{u} m n).ι.app (.right j) ≫
      normalizedJoinBoundaryStandardMap m n =
        ordinaryJoinTransportedLeftLeg m n j ≫ (leftJoinTargetIso m n).inv := by
  let b :=
    ((boundaryMulticoequalizerDiagram (m + 1)).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor).ι.app (.right j)
  have hobj :
      (((boundaryMulticoequalizerDiagram (m + 1)).multispanIndex.toLinearOrder.map
        SSet.Subcomplex.toSSetFunctor).multispan.obj (.right j) : SSet.{u}) =
        (SSet.stdSimplex.face {j}ᶜ : SSet.{u}) := by
    rfl
  have happ : (rightTensorBoundaryCocone.{u} m n).ι.app (.right j) =
      simplicialJoinMap b (𝟙 (Δ[n] : SSet.{u})) := by
    dsimp [rightTensorBoundaryCocone, singletonAugmentationBoundaryCocone, b]
    simp only [Functor.mapCocone_ι_app, augmentedDayTensorRight_map]
    unfold simplicialJoinMap
    rw [emptyAugmentation.map_id]
    change Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op _ =
      Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op _
    congr 2
  rw [happ]
  have hface : b ≫ (SSet.boundary (m + 1)).ι =
      (SSet.stdSimplex.face {j}ᶜ : (Δ[m + 1] : SSet.{u}).Subcomplex).ι := by
    rfl
  have hface' :
      (SSet.stdSimplex.face {j}ᶜ : (Δ[m + 1] : SSet.{u}).Subcomplex).ι =
        (SSet.stdSimplex.faceSingletonComplIso j).inv ≫ SSet.stdSimplex.δ j := by
    apply (cancel_epi (SSet.stdSimplex.faceSingletonComplIso.{u} j).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact SSet.stdSimplex.faceSingletonComplIso_hom_ι j
  cases hobj
  unfold normalizedJoinBoundaryStandardMap joinBoundaryStandardMap
  have hcomp :
      simplicialJoinMap b (𝟙 (Δ[n] : SSet.{u})) ≫
          simplicialJoinMap ((SSet.boundary (m + 1)).ι)
            (𝟙 (Δ[n] : SSet.{u})) =
        simplicialJoinMap
          ((SSet.stdSimplex.face {j}ᶜ :
            (Δ[m + 1] : SSet.{u}).Subcomplex).ι)
          (𝟙 (Δ[n] : SSet.{u})) := by
    exact (simplicialJoinMap_comp_right_id
      (Y := (Δ[n] : SSet.{u})) b (SSet.boundary (m + 1)).ι).trans
        (congrArg (fun q ↦ simplicialJoinMap q (𝟙 (Δ[n] : SSet.{u}))) hface)
  unfold ordinaryJoinTransportedLeftLeg
  rw [ordinaryJoinLeftFaceIso_inv]
  have hnat := simplicialJoinMap_comp_right_id
    (Y := (Δ[n] : SSet.{u}))
    (SSet.stdSimplex.faceSingletonComplIso j).inv
    (SSet.stdSimplex.δ j)
  calc
    _ = (simplicialJoinMap b (𝟙 (Δ[n] : SSet.{u})) ≫
          simplicialJoinMap ((SSet.boundary (m + 1)).ι)
            (𝟙 (Δ[n] : SSet.{u}))) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
        (leftJoinTargetIso m n).inv := by rfl
    _ = simplicialJoinMap
          ((SSet.stdSimplex.face {j}ᶜ :
            (Δ[m + 1] : SSet.{u}).Subcomplex).ι)
          (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
        (leftJoinTargetIso m n).inv :=
      congrArg (fun q ↦ q ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
          (leftJoinTargetIso m n).inv) hcomp
    _ = simplicialJoinMap
          ((SSet.stdSimplex.faceSingletonComplIso j).inv ≫
            SSet.stdSimplex.δ j)
          (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
        (leftJoinTargetIso m n).inv :=
      congrArg (fun q ↦ simplicialJoinMap q (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
          (leftJoinTargetIso m n).inv) hface'
    _ = (simplicialJoinMap
          (SSet.stdSimplex.faceSingletonComplIso j).inv
          (𝟙 (Δ[n] : SSet.{u})) ≫
        simplicialJoinMap (SSet.stdSimplex.δ j)
          (𝟙 (Δ[n] : SSet.{u}))) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
        (leftJoinTargetIso m n).inv := by
          exact congrArg (fun q ↦ q ≫
            (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
              (leftJoinTargetIso m n).inv) hnat.symm
    _ = _ := by rfl

lemma rightTensorBoundaryCocone_right_comp_range
    (m n : ℕ) (j : Fin (m + 2)) :
    SSet.Subcomplex.range
        ((rightTensorBoundaryCocone.{u} m n).ι.app (.right j) ≫
          normalizedJoinBoundaryStandardMap m n) =
      SSet.stdSimplex.face
        ({(Fin.castLE (by omega) j : Fin (m + n + 3))}ᶜ) := by
  calc
    _ = SSet.Subcomplex.range
        (ordinaryJoinTransportedLeftLeg.{u} m n j ≫
          (leftJoinTargetIso m n).inv) :=
      congrArg SSet.Subcomplex.range
        (rightTensorBoundaryCocone_right_comp m n j)
    _ = (SSet.Subcomplex.range
        (ordinaryJoinTransportedLeftLeg.{u} m n j)).image
          (leftJoinTargetIso m n).inv :=
      SSet.Subcomplex.range_comp _ _
    _ = ((SSet.stdSimplex.face
          ({(Fin.castLE (by omega) j : Fin (m + n + 3))}ᶜ)).image
        (leftJoinTargetIso.{u} m n).hom).image
          (leftJoinTargetIso m n).inv := by
      rw [ordinaryJoinTransportedLeftLeg_range]
    _ = _ := by
      rw [← SSet.Subcomplex.image_comp]
      simp

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- Unfolding the two preserved colimit legs and the Day convolution maps is expensive.
lemma rightTensorBoundaryCocone_left_comp_eq_doubleLeftCoface
    (r n : ℕ)
    (a : (Limits.MultispanShape.ofLinearOrder (Fin (r + 3))).L) :
    let j := a.1.1
    let k := a.1.2
    let kp := k.pred (Fin.ne_zero_of_lt a.2)
    let e := ordinaryJoinBifunctor.{u}.map
      (((SSet.stdSimplex.facePairComplIso.{u} j k a.2).hom,
        𝟙 (Δ[n] : SSet.{u})) :
        ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
          ((SSet.stdSimplex.face {j, k}ᶜ : SSet.{u}), Δ[n]))
    e ≫
        (rightTensorBoundaryCocone (r + 1) n).ι.app (.left a) ≫
          joinBoundaryStandardMap (r + 2) n =
      (simplicialJoinStdSimplexIsoNat r n).hom ≫
        SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
        SSet.stdSimplex.map (leftJoinCoface (r + 1) n j) := by
  dsimp
  let j := a.1.1
  let k := a.1.2
  have hjk : j < k := a.2
  let kp := k.pred (Fin.ne_zero_of_lt hjk)
  let e := ordinaryJoinBifunctor.{u}.map
    (((SSet.stdSimplex.facePairComplIso.{u} j k hjk).hom,
      𝟙 (Δ[n] : SSet.{u})) :
      ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.stdSimplex.face {j, k}ᶜ : SSet.{u}), Δ[n]))
  change e ≫ _ ≫ _ = _
  conv_rhs => rw [← Category.assoc]
  rw [← simplicialJoinStdSimplexIsoNat_naturality_leftCoface.{u}
    r n kp]
  rw [Category.assoc,
    ← simplicialJoinStdSimplexIsoNat_naturality_leftCoface.{u}
      (r + 1) n j]
  rw [joinBoundaryStandardMap, ← Category.assoc]
  change ((e ≫
      (rightTensorBoundaryCocone (r + 1) n).ι.app (.left a)) ≫
      simplicialJoinMap (SSet.boundary (r + 2)).ι
        (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinStdSimplexIsoNat (r + 2) n).hom =
    (simplicialJoinMap (SSet.stdSimplex.map (SimplexCategory.δ kp))
        (𝟙 (Δ[n] : SSet.{u})) ≫
      simplicialJoinMap (SSet.stdSimplex.map (SimplexCategory.δ j))
        (𝟙 (Δ[n] : SSet.{u}))) ≫
      (simplicialJoinStdSimplexIsoNat (r + 2) n).hom)
  rw [← Category.assoc]
  apply (cancel_mono (simplicialJoinStdSimplexIsoNat (r + 2) n).hom).mpr
  simp only [e, ordinaryJoinBifunctor, rightTensorBoundaryCocone,
    singletonAugmentationBoundaryCocone, Functor.mapCocone_ι_app]
  let l := (((boundaryMulticoequalizerDiagram (r + 2)).multicofork.toLinearOrder.map
    SSet.Subcomplex.toSSetFunctor).ι.app (.left a))
  have hface : l ≫ (SSet.boundary (r + 2)).ι =
      (SSet.stdSimplex.face {j, k}ᶜ).ι := by
    rfl
  let T := augmentedDayTensorRight
    (emptyAugmentation.{u}.obj (Δ[n] : SSet.{u}))
  have hT : T.map (emptyAugmentation.{u}.map l) ≫
        T.map (emptyAugmentation.{u}.map (SSet.boundary (r + 2)).ι) =
      T.map (emptyAugmentation.{u}.map
        (SSet.stdSimplex.face {j, k}ᶜ).ι) := by
    rw [← T.map_comp, ← emptyAugmentation.map_comp, hface]
  have hforget := congrArg forgetAugmentation.{u}.map hT
  simp only [forgetAugmentation.map_comp] at hforget
  dsimp [T, l] at hforget
  simp_rw [simplicialJoinMap_right_id_eq_augmentedDayTensorRight_map]
  slice_lhs 2 3 => rw [hforget]
  rw [← forgetAugmentation.map_comp, ← forgetAugmentation.map_comp]
  congr 1
  rw [← T.map_comp, ← T.map_comp]
  congr 1
  rw [← emptyAugmentation.map_comp, ← emptyAugmentation.map_comp]
  congr 1
  exact SSet.stdSimplex.facePairComplIso_hom_ι' j k hjk

lemma rightTensorBoundaryCocone_right_comp_unnormalized
    (m n : ℕ) (j : Fin (m + 2)) :
    (rightTensorBoundaryCocone.{u} m n).ι.app (.right j) ≫
        joinBoundaryStandardMap (m + 1) n =
      ordinaryJoinTransportedLeftLeg m n j := by
  apply (cancel_mono (leftJoinTargetIso.{u} m n).inv).mp
  exact rightTensorBoundaryCocone_right_comp.{u} m n j

/-- The joined boundary map in the strict coordinates used for intersections
of two left faces. -/
noncomputable def joinBoundaryStandardMapPairNormalized (r n : ℕ) :
    simplicialJoin (SSet.boundary (r + 2) : SSet.{u}) Δ[n] ⟶
      Δ[r + n + 3] :=
  joinBoundaryStandardMap (r + 2) n ≫
    (leftJoinPairTargetIso r n).inv

lemma rightTensorBoundaryCocone_right_comp_pairNormalized
    (r n : ℕ) (j : Fin (r + 3)) :
    (rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.right j) ≫
        joinBoundaryStandardMapPairNormalized r n =
      ordinaryJoinTransportedLeftLeg (r + 1) n j ≫
        (leftJoinPairTargetIso r n).inv := by
  unfold joinBoundaryStandardMapPairNormalized
  exact congrArg (fun q ↦ q ≫ (leftJoinPairTargetIso r n).inv)
    (rightTensorBoundaryCocone_right_comp_unnormalized.{u} (r + 1) n j)

lemma rightTensorBoundaryCocone_right_comp_range_pairNormalized
    (r n : ℕ) (j : Fin (r + 3)) :
    SSet.Subcomplex.range
        ((rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.right j) ≫
          joinBoundaryStandardMapPairNormalized r n) =
      SSet.stdSimplex.face
        ({(Fin.castLE (by omega) j : Fin (r + n + 4))}ᶜ) := by
  calc
    _ = SSet.Subcomplex.range
        (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n j ≫
          (leftJoinPairTargetIso r n).inv) :=
      congrArg SSet.Subcomplex.range
        (rightTensorBoundaryCocone_right_comp_pairNormalized r n j)
    _ = _ := ordinaryJoinTransportedLeftLeg_range_pairNormalized r n j

lemma rightTensorBoundaryCocone_left_comp_range
    (r n : ℕ)
    (a : (Limits.MultispanShape.ofLinearOrder (Fin (r + 3))).L) :
    let j := a.1.1
    let k := a.1.2
    let J := (Fin.castLE (by omega) j : Fin (r + n + 4))
    let K := (Fin.castLE (by omega) k : Fin (r + n + 4))
    SSet.Subcomplex.range
        ((rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.left a) ≫
          joinBoundaryStandardMap.{u} (r + 2) n) =
      (SSet.stdSimplex.face {J, K}ᶜ).image
        (leftJoinPairTargetIso.{u} r n).hom := by
  dsimp
  let j := a.1.1
  let k := a.1.2
  have hjk : j < k := a.2
  let kp := k.pred (Fin.ne_zero_of_lt hjk)
  let J := (Fin.castLE (by omega) j : Fin (r + n + 4))
  let K := (Fin.castLE (by omega) k : Fin (r + n + 4))
  have hJK : J < K := by
    simp only [Fin.lt_def, J, K, Fin.val_castLE]
    exact hjk
  let e := ordinaryJoinBifunctor.{u}.map
    (((SSet.stdSimplex.facePairComplIso.{u} j k hjk).hom,
      𝟙 (Δ[n] : SSet.{u})) :
      ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.stdSimplex.face {j, k}ᶜ : SSet.{u}), Δ[n]))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let f := (rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.left a) ≫
    joinBoundaryStandardMap.{u} (r + 2) n
  let g := (simplicialJoinStdSimplexIsoNat r n).hom ≫
    SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
    SSet.stdSimplex.map (leftJoinCoface (r + 1) n j)
  have heq : e ≫ f = g := by
    exact rightTensorBoundaryCocone_left_comp_eq_doubleLeftCoface r n a
  calc
    SSet.Subcomplex.range f = SSet.Subcomplex.range g :=
      subcomplex_range_eq_of_precomp_iso e f g heq
    _ = SSet.Subcomplex.range
        (SSet.stdSimplex.map (leftJoinCoface r n kp) ≫
          SSet.stdSimplex.map (leftJoinCoface (r + 1) n j)) := by
      symm
      apply subcomplex_range_eq_of_precomp_iso
        (simplicialJoinStdSimplexIsoNat r n).hom
      rfl
    _ = SSet.Subcomplex.range
        ((SSet.stdSimplex.facePairComplIso J K hJK).hom ≫
          (SSet.stdSimplex.face {J, K}ᶜ).ι ≫
          (leftJoinPairTargetIso r n).hom) := by
      apply congrArg SSet.Subcomplex.range
      exact doubleLeftCoface_std_map_eq_facePair r n j k hjk
    _ = (SSet.stdSimplex.face {J, K}ᶜ).image
        (leftJoinPairTargetIso r n).hom := by
      have hr := subcomplex_range_eq_of_precomp_iso
        (SSet.stdSimplex.facePairComplIso.{u} J K hJK).hom
        ((SSet.stdSimplex.face {J, K}ᶜ).ι ≫
          (leftJoinPairTargetIso r n).hom)
        ((SSet.stdSimplex.facePairComplIso J K hJK).hom ≫
          ((SSet.stdSimplex.face {J, K}ᶜ).ι ≫
            (leftJoinPairTargetIso r n).hom)) rfl
      rw [← hr, SSet.Subcomplex.range_comp]
      congr 1
      ext U x
      simp [SSet.Subcomplex.range]

lemma rightTensorBoundaryCocone_left_comp_range_pairNormalized
    (r n : ℕ)
    (a : (Limits.MultispanShape.ofLinearOrder (Fin (r + 3))).L) :
    let j := a.1.1
    let k := a.1.2
    let J := (Fin.castLE (by omega) j : Fin (r + n + 4))
    let K := (Fin.castLE (by omega) k : Fin (r + n + 4))
    SSet.Subcomplex.range
        ((rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.left a) ≫
          joinBoundaryStandardMapPairNormalized.{u} r n) =
      SSet.stdSimplex.face {J, K}ᶜ := by
  dsimp
  unfold joinBoundaryStandardMapPairNormalized
  change SSet.Subcomplex.range
    (((rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.left a) ≫
      joinBoundaryStandardMap.{u} (r + 2) n) ≫
        (leftJoinPairTargetIso.{u} r n).inv) = _
  rw [SSet.Subcomplex.range_comp,
    rightTensorBoundaryCocone_left_comp_range]
  rw [← SSet.Subcomplex.image_comp]
  simp

lemma rightTensorBoundaryCocone_left_comp_mono_pairNormalized
    (r n : ℕ)
    (a : (Limits.MultispanShape.ofLinearOrder (Fin (r + 3))).L) :
    Mono ((rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.left a) ≫
      joinBoundaryStandardMapPairNormalized r n) := by
  let j := a.1.1
  let k := a.1.2
  have hjk : j < k := a.2
  let J := (Fin.castLE (by omega) j : Fin (r + n + 4))
  let K := (Fin.castLE (by omega) k : Fin (r + n + 4))
  have hJK : J < K := by
    simp only [Fin.lt_def, J, K, Fin.val_castLE]
    exact hjk
  let e := ordinaryJoinBifunctor.{u}.map
    (((SSet.stdSimplex.facePairComplIso.{u} j k hjk).hom,
      𝟙 (Δ[n] : SSet.{u})) :
      ((Δ[r] : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.stdSimplex.face {j, k}ᶜ : SSet.{u}), Δ[n]))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let f := (rightTensorBoundaryCocone.{u} (r + 1) n).ι.app (.left a) ≫
    joinBoundaryStandardMapPairNormalized r n
  have hr : SSet.Subcomplex.range f =
      SSet.stdSimplex.face {J, K}ᶜ := by
    exact rightTensorBoundaryCocone_left_comp_range_pairNormalized r n a
  let E := (asIso e).symm ≪≫ simplicialJoinStdSimplexIsoNat r n ≪≫
    SSet.stdSimplex.facePairComplIso J K hJK ≪≫
      SSet.Subcomplex.toSSetFunctor.mapIso (eqToIso hr.symm)
  haveI : Mono (SSet.Subcomplex.toRange f) := by
    rw [NatTrans.mono_iff_mono_app]
    intro U
    rw [mono_iff_injective]
    letI : Finite ((SSet.Subcomplex.toSSetFunctor.obj
        (SSet.Subcomplex.range f)).obj U) :=
      Finite.of_injective ((SSet.Subcomplex.range f).ι.app U)
        ((mono_iff_injective _).mp inferInstance)
    letI : Finite ((ordinaryJoinBifunctor.{u}.obj
        ((SSet.stdSimplex.face {j, k}ᶜ : SSet.{u}),
          (Δ[n] : SSet.{u}))).obj U) :=
      Finite.of_injective (E.app U).toEquiv (E.app U).toEquiv.injective
    apply (Finite.injective_iff_surjective_of_equiv ((E.app U).toEquiv)).2
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  change Mono f
  rw [← SSet.Subcomplex.toRange_ι (f := f)]
  infer_instance

set_option synthInstance.maxHeartbeats 200000 in
-- The multispan mono synthesis repeatedly unfolds the convolved boundary diagram.
noncomputable instance joinBoundaryStandardMapPairNormalized_mono
    (r n : ℕ) :
    Mono (joinBoundaryStandardMapPairNormalized.{u} r n) := by
  let c := rightTensorBoundaryCocone.{u} (r + 1) n
  let hc := rightTensorBoundaryIsColimit.{u} (r + 1) n
  apply mono_of_linearMultispan_ranges c
    (joinBoundaryStandardMapPairNormalized r n) hc
  · rintro (a | j)
    · exact rightTensorBoundaryCocone_left_comp_mono_pairNormalized r n a
    · have hj := rightTensorBoundaryCocone_right_comp_pairNormalized.{u} r n j
      have hleg : Mono (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n j) :=
        ordinaryJoinTransportedLeftLeg_mono (r + 1) n j
      have hinv : Mono (leftJoinPairTargetIso.{u} r n).inv := inferInstance
      have hcomp : Mono (ordinaryJoinTransportedLeftLeg.{u} (r + 1) n j ≫
          (leftJoinPairTargetIso r n).inv) := by
        letI := hleg
        letI := hinv
        exact mono_comp _ _
      exact hj.symm ▸ hcomp
  · intro a
    rw [rightTensorBoundaryCocone_left_comp_range_pairNormalized]
    let j := (Limits.MultispanShape.ofLinearOrder (Fin (r + 3))).fst a
    let k := (Limits.MultispanShape.ofLinearOrder (Fin (r + 3))).snd a
    calc
      SSet.stdSimplex.face {Fin.castLE (by omega) j,
          Fin.castLE (by omega) k}ᶜ =
        SSet.stdSimplex.face {Fin.castLE (by omega) j}ᶜ ⊓
          SSet.stdSimplex.face {Fin.castLE (by omega) k}ᶜ := by
            rw [SSet.stdSimplex.face_inter_face]
            congr 1
            ext x
            simp
      _ = SSet.Subcomplex.range
            (c.ι.app (.right j) ≫
              joinBoundaryStandardMapPairNormalized r n) ⊓
          SSet.Subcomplex.range
            (c.ι.app (.right k) ≫
              joinBoundaryStandardMapPairNormalized r n) := by
            rw [rightTensorBoundaryCocone_right_comp_range_pairNormalized,
              rightTensorBoundaryCocone_right_comp_range_pairNormalized]

lemma joinBoundaryStandardMap_succ_mono (r n : ℕ) :
    Mono (joinBoundaryStandardMap.{u} (r + 2) n) := by
  haveI : Mono (joinBoundaryStandardMapPairNormalized.{u} r n) :=
    joinBoundaryStandardMapPairNormalized_mono r n
  apply mono_of_mono_fac (h := joinBoundaryStandardMapPairNormalized r n)
  rfl

lemma normalizedJoinBoundaryStandardMap_succ_mono (r n : ℕ) :
    Mono (normalizedJoinBoundaryStandardMap.{u} (r + 1) n) := by
  unfold normalizedJoinBoundaryStandardMap
  haveI : Mono (joinBoundaryStandardMap.{u} (r + 2) n) :=
    joinBoundaryStandardMap_succ_mono r n
  haveI : Mono (leftJoinTargetIso.{u} (r + 1) n).inv := inferInstance
  exact mono_comp _ _

lemma standardJoinRightOperator_one_range (n : ℕ) :
    SSet.Subcomplex.range
        (SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
          (leftJoinTargetIso.{u} 0 n).inv) =
      SSet.stdSimplex.face
        ({(0 : Fin (0 + n + 3)), (1 : Fin (0 + n + 3))}ᶜ) := by
  let i : Fin (0 + n + 3) := 0
  let j : Fin (0 + n + 3) := 1
  have hij : i < j := by simp [i, j]
  let e0 : (Δ[n] : SSet.{u}) ≅ Δ[0 + n] :=
    SSet.stdSimplex.mapIso (eqToIso (by
      apply SimplexCategory.ext
      simp))
  let e := e0 ≪≫ SSet.stdSimplex.facePairComplIso.{u} i j hij
  have hmap : e.hom ≫
        (SSet.stdSimplex.face {i, j}ᶜ :
          (Δ[0 + n + 2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
        (leftJoinTargetIso.{u} 0 n).inv := by
    simp only [e, Iso.trans_hom, Category.assoc]
    rw [SSet.stdSimplex.facePairComplIso_hom_ι]
    dsimp [e0, leftJoinTargetIso]
    rw [Functor.mapIso_hom, Functor.mapIso_inv]
    change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ ≫
        SSet.stdSimplex.map _ =
      SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply SimplexCategory.Hom.ext
    ext k
    simp only [eqToIso.hom, SimplexCategory.comp_toOrderHom,
      SimplexCategory.eqToHom_toOrderHom, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
      Function.comp_apply, Fin.castOrderIso_apply, eqToIso.inv, Fin.val_cast]
    let kc : Fin (0 + n + 1) := Fin.cast (by simp) k
    change (if kc.castSucc.succ < 1 then kc.castSucc.succ
      else kc.succ.succ).val = 2 + k.val
    have hkc : kc.val = k.val := by simp [kc]
    by_cases h : kc.castSucc.succ < 1
    · have hh : kc.castSucc.succ.val < 1 := h
      have hv : kc.castSucc.succ.val = kc.val + 1 := rfl
      omega
    · rw [if_neg h]
      have hv : kc.succ.succ.val = kc.val + 2 := rfl
      rw [hv, hkc]
      omega
  simpa only [Subfunctor.range_ι, i, j] using
    (subcomplex_range_eq_of_precomp_iso e.hom
      (SSet.stdSimplex.face {i, j}ᶜ :
        (Δ[0 + n + 2] : SSet.{u}).Subcomplex).ι
      (SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
        (leftJoinTargetIso.{u} 0 n).inv) hmap).symm

lemma standardJoinRightOperator_one_mono (n : ℕ) :
    Mono (SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
      (leftJoinTargetIso.{u} 0 n).inv) := by
  let i : Fin (0 + n + 3) := 0
  let j : Fin (0 + n + 3) := 1
  have hij : i < j := by simp [i, j]
  let e0 : (Δ[n] : SSet.{u}) ≅ Δ[0 + n] :=
    SSet.stdSimplex.mapIso (eqToIso (by
      apply SimplexCategory.ext
      simp))
  let e := e0 ≪≫ SSet.stdSimplex.facePairComplIso.{u} i j hij
  have hmap : e.hom ≫
        (SSet.stdSimplex.face {i, j}ᶜ :
          (Δ[0 + n + 2] : SSet.{u}).Subcomplex).ι =
      SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
        (leftJoinTargetIso.{u} 0 n).inv := by
    simp only [e, Iso.trans_hom, Category.assoc]
    rw [SSet.stdSimplex.facePairComplIso_hom_ι]
    dsimp [e0, leftJoinTargetIso]
    rw [Functor.mapIso_hom, Functor.mapIso_inv]
    change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ ≫
        SSet.stdSimplex.map _ =
      SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply SimplexCategory.Hom.ext
    ext k
    simp only [eqToIso.hom, SimplexCategory.comp_toOrderHom,
      SimplexCategory.eqToHom_toOrderHom, OrderHom.comp_coe,
      OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
      Function.comp_apply, Fin.castOrderIso_apply, eqToIso.inv, Fin.val_cast]
    let kc : Fin (0 + n + 1) := Fin.cast (by simp) k
    change (if kc.castSucc.succ < 1 then kc.castSucc.succ
      else kc.succ.succ).val = 2 + k.val
    have hkc : kc.val = k.val := by simp [kc]
    by_cases h : kc.castSucc.succ < 1
    · have hh : kc.castSucc.succ.val < 1 := h
      have hv : kc.castSucc.succ.val = kc.val + 1 := rfl
      omega
    · rw [if_neg h]
      have hv : kc.succ.succ.val = kc.val + 2 := rfl
      rw [hv, hkc]
      omega
  rw [← hmap]
  infer_instance

def baseJoinBoundaryLeftToBoundary
    (n : ℕ) (a : (Limits.MultispanShape.ofLinearOrder (Fin 2)).L) :
    (Δ[n] : SSet.{u}) ⟶
      simplicialJoin (SSet.boundary 1 : SSet.{u}) Δ[n] :=
  simplicialJoinRightInclusion
      (SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ : SSet.{u}) Δ[n] ≫
    (rightTensorBoundaryCocone.{u} 0 n).ι.app (.left a)

lemma baseJoinBoundaryLeftToBoundary_eq_rightInclusion
    (n : ℕ) (a : (Limits.MultispanShape.ofLinearOrder (Fin 2)).L) :
    baseJoinBoundaryLeftToBoundary.{u} n a =
      simplicialJoinRightInclusion (SSet.boundary 1 : SSet.{u}) Δ[n] := by
  unfold baseJoinBoundaryLeftToBoundary
  rw [rightTensorBoundaryCocone_left_app]
  exact simplicialJoinRightInclusion_naturality_left
    (((boundaryMulticoequalizerDiagram 1).multicofork.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor).ι.app (.left a))

lemma baseJoinBoundaryOverlap_comp_normalized
    (n : ℕ) (a : (Limits.MultispanShape.ofLinearOrder (Fin 2)).L) :
    baseJoinBoundaryLeftToBoundary.{u} n a ≫
        normalizedJoinBoundaryStandardMap 0 n =
      SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
        (leftJoinTargetIso.{u} 0 n).inv := by
  rw [baseJoinBoundaryLeftToBoundary_eq_rightInclusion]
  unfold normalizedJoinBoundaryStandardMap joinBoundaryStandardMap
  slice_lhs 1 2 => rw [simplicialJoinRightInclusion_naturality_left]
  rw [simplicialJoinRightInclusion_stdSimplex]

set_option synthInstance.maxHeartbeats 200000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
lemma baseJoinBoundaryLeft_comp_mono
    (n : ℕ) (a : (Limits.MultispanShape.ofLinearOrder (Fin 2)).L) :
    Mono ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.left a) ≫
      normalizedJoinBoundaryStandardMap 0 n) := by
  let e := simplicialJoinRightInclusion
    (SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ : SSet.{u}) Δ[n]
  let f := (rightTensorBoundaryCocone.{u} 0 n).ι.app (.left a) ≫
    normalizedJoinBoundaryStandardMap 0 n
  have heq : e ≫ f =
      SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
        (leftJoinTargetIso.{u} 0 n).inv := by
    change simplicialJoinRightInclusion
        (SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ : SSet.{u}) Δ[n] ≫
      ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.left a) ≫
        normalizedJoinBoundaryStandardMap 0 n) = _
    rw [← Category.assoc]
    exact baseJoinBoundaryOverlap_comp_normalized n a
  have hmono :
      Mono (SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
        (leftJoinTargetIso.{u} 0 n).inv) :=
    standardJoinRightOperator_one_mono n
  haveI : Mono (e ≫ f) := heq.symm ▸ hmono
  have hj : a.1.1 = 0 := by
    apply Fin.ext
    have ha : a.1.1.val < a.1.2.val := a.2
    have hlt := a.1.1.isLt
    omega
  have hk : a.1.2 = 1 := by
    apply Fin.ext
    have ha : a.1.1.val < a.1.2.val := a.2
    have hlt := a.1.2.isLt
    omega
  have hface : SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ =
      (⊥ : (Δ[1] : SSet.{u}).Subcomplex) := by
    rw [hj, hk]
    have hfin : ({(0 : Fin 2), (1 : Fin 2)} : Finset (Fin 2)) =
        Finset.univ := by decide
    rw [hfin]
    simp
  have hinit : Limits.IsInitial
      (SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ : SSet.{u}) := by
    rw [hface]
    exact SSet.Subcomplex.isInitialBot
  let E := simplicialJoinInitialIso
    (SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ : SSet.{u}) hinit
      (Δ[n] : SSet.{u})
  have he : e = E.inv := by
    apply (cancel_mono E.hom).mp
    rw [simplicialJoinRightInclusion_initial_iso_hom, Iso.inv_hom_id]
  change Mono f
  have hf : f = E.hom ≫ (e ≫ f) := by
    rw [he, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hf]
  haveI : Mono E.hom := inferInstance
  exact mono_comp _ _

lemma baseJoinBoundaryLeft_comp_range
    (n : ℕ) (a : (Limits.MultispanShape.ofLinearOrder (Fin 2)).L) :
    SSet.Subcomplex.range
        ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.left a) ≫
          normalizedJoinBoundaryStandardMap 0 n) =
      SSet.Subcomplex.range
          ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.right a.1.1) ≫
            normalizedJoinBoundaryStandardMap 0 n) ⊓
        SSet.Subcomplex.range
          ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.right a.1.2) ≫
            normalizedJoinBoundaryStandardMap 0 n) := by
  let c := rightTensorBoundaryCocone.{u} 0 n
  let M := normalizedJoinBoundaryStandardMap.{u} 0 n
  let f := c.ι.app (.left a) ≫ M
  let e := simplicialJoinRightInclusion
    (SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ : SSet.{u}) Δ[n]
  have hj : a.1.1 = 0 := by
    apply Fin.ext
    have ha : a.1.1.val < a.1.2.val := a.2
    have hlt := a.1.1.isLt
    omega
  have hk : a.1.2 = 1 := by
    apply Fin.ext
    have ha : a.1.1.val < a.1.2.val := a.2
    have hlt := a.1.2.isLt
    omega
  have heq : e ≫ f =
      SSet.stdSimplex.map (standardJoinRightOperator 1 n) ≫
        (leftJoinTargetIso.{u} 0 n).inv := by
    change simplicialJoinRightInclusion
        (SSet.stdSimplex.face {a.1.1, a.1.2}ᶜ : SSet.{u}) Δ[n] ≫
      ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.left a) ≫
        normalizedJoinBoundaryStandardMap 0 n) = _
    rw [← Category.assoc]
    exact baseJoinBoundaryOverlap_comp_normalized n a
  have hpre : SSet.Subcomplex.range (e ≫ f) =
      SSet.stdSimplex.face
        ({(0 : Fin (0 + n + 3)), (1 : Fin (0 + n + 3))}ᶜ) := by
    rw [heq, standardJoinRightOperator_one_range]
  have hrightinf :
      SSet.Subcomplex.range (c.ι.app (.right a.1.1) ≫ M) ⊓
          SSet.Subcomplex.range (c.ι.app (.right a.1.2) ≫ M) =
        SSet.stdSimplex.face
          ({(0 : Fin (0 + n + 3)), (1 : Fin (0 + n + 3))}ᶜ) := by
    have hzero :
        (Fin.castLE (by omega) (0 : Fin 2) : Fin (0 + n + 3)) = 0 := by
      rfl
    have hone :
        (Fin.castLE (by omega) (1 : Fin 2) : Fin (0 + n + 3)) = 1 := by
      apply Fin.ext
      rfl
    change SSet.Subcomplex.range
        ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.right a.1.1) ≫
          normalizedJoinBoundaryStandardMap 0 n) ⊓
      SSet.Subcomplex.range
        ((rightTensorBoundaryCocone.{u} 0 n).ι.app (.right a.1.2) ≫
          normalizedJoinBoundaryStandardMap 0 n) = _
    rw [rightTensorBoundaryCocone_right_comp_range,
      rightTensorBoundaryCocone_right_comp_range, hj, hk,
      hzero, hone, SSet.stdSimplex.face_inter_face]
    congr 1
    ext x
    simp
  apply le_antisymm
  · have hfst := (c.ι.naturality
        (Limits.WalkingMultispan.Hom.fst a)).trans (Category.comp_id _)
    have hsnd := (c.ι.naturality
        (Limits.WalkingMultispan.Hom.snd a)).trans (Category.comp_id _)
    apply le_inf
    · change SSet.Subcomplex.range (c.ι.app (.left a) ≫ M) ≤
        SSet.Subcomplex.range (c.ι.app (.right a.1.1) ≫ M)
      have hfst' :
          (rightTensorBoundaryDiagram.{u} 0 n).map
                (Limits.WalkingMultispan.Hom.fst a) ≫
              c.ι.app (.right a.1.1) =
            c.ι.app (.left a) := hfst
      have hfac : c.ι.app (.left a) ≫ M =
          (rightTensorBoundaryDiagram.{u} 0 n).map
              (Limits.WalkingMultispan.Hom.fst a) ≫
            (c.ι.app (.right a.1.1) ≫ M) := by
        calc
          _ = ((rightTensorBoundaryDiagram.{u} 0 n).map
                (Limits.WalkingMultispan.Hom.fst a) ≫
              c.ι.app (.right a.1.1)) ≫ M :=
            congrArg (fun q ↦ q ≫ M) hfst'.symm
          _ = _ := Category.assoc _ _ _
      calc
        SSet.Subcomplex.range (c.ι.app (.left a) ≫ M) =
            SSet.Subcomplex.range
              ((rightTensorBoundaryDiagram.{u} 0 n).map
                  (Limits.WalkingMultispan.Hom.fst a) ≫
                (c.ι.app (.right a.1.1) ≫ M)) :=
          congrArg SSet.Subcomplex.range hfac
        _ = (SSet.Subcomplex.range
              ((rightTensorBoundaryDiagram.{u} 0 n).map
                (Limits.WalkingMultispan.Hom.fst a))).image
              (c.ι.app (.right a.1.1) ≫ M) :=
          SSet.Subcomplex.range_comp _ _
        _ ≤ _ := SSet.Subcomplex.image_le_range _ _
    · change SSet.Subcomplex.range (c.ι.app (.left a) ≫ M) ≤
        SSet.Subcomplex.range (c.ι.app (.right a.1.2) ≫ M)
      have hsnd' :
          (rightTensorBoundaryDiagram.{u} 0 n).map
                (Limits.WalkingMultispan.Hom.snd a) ≫
              c.ι.app (.right a.1.2) =
            c.ι.app (.left a) := hsnd
      have hfac : c.ι.app (.left a) ≫ M =
          (rightTensorBoundaryDiagram.{u} 0 n).map
              (Limits.WalkingMultispan.Hom.snd a) ≫
            (c.ι.app (.right a.1.2) ≫ M) := by
        calc
          _ = ((rightTensorBoundaryDiagram.{u} 0 n).map
                (Limits.WalkingMultispan.Hom.snd a) ≫
              c.ι.app (.right a.1.2)) ≫ M :=
            congrArg (fun q ↦ q ≫ M) hsnd'.symm
          _ = _ := Category.assoc _ _ _
      calc
        SSet.Subcomplex.range (c.ι.app (.left a) ≫ M) =
            SSet.Subcomplex.range
              ((rightTensorBoundaryDiagram.{u} 0 n).map
                  (Limits.WalkingMultispan.Hom.snd a) ≫
                (c.ι.app (.right a.1.2) ≫ M)) :=
          congrArg SSet.Subcomplex.range hfac
        _ = (SSet.Subcomplex.range
              ((rightTensorBoundaryDiagram.{u} 0 n).map
                (Limits.WalkingMultispan.Hom.snd a))).image
              (c.ι.app (.right a.1.2) ≫ M) :=
          SSet.Subcomplex.range_comp _ _
        _ ≤ _ := SSet.Subcomplex.image_le_range _ _
  · rw [hrightinf]
    rw [← hpre, SSet.Subcomplex.range_comp]
    exact SSet.Subcomplex.image_le_range _ _

set_option synthInstance.maxHeartbeats 200000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
noncomputable instance normalizedJoinBoundaryStandardMap_zero_mono
    (n : ℕ) :
    Mono (normalizedJoinBoundaryStandardMap.{u} 0 n) := by
  let c := rightTensorBoundaryCocone.{u} 0 n
  let hc := rightTensorBoundaryIsColimit.{u} 0 n
  apply mono_of_linearMultispan_ranges c
    (normalizedJoinBoundaryStandardMap 0 n) hc
  · rintro (a | j)
    · exact baseJoinBoundaryLeft_comp_mono n a
    · have hj := rightTensorBoundaryCocone_right_comp.{u} 0 n j
      have hleg : Mono (ordinaryJoinTransportedLeftLeg.{u} 0 n j) :=
        ordinaryJoinTransportedLeftLeg_mono 0 n j
      have hinv : Mono (leftJoinTargetIso.{u} 0 n).inv := inferInstance
      have hcomp : Mono (ordinaryJoinTransportedLeftLeg.{u} 0 n j ≫
          (leftJoinTargetIso 0 n).inv) := by
        letI := hleg
        letI := hinv
        exact mono_comp _ _
      exact hj.symm ▸ hcomp
  · intro a
    exact baseJoinBoundaryLeft_comp_range n a

noncomputable instance normalizedJoinBoundaryStandardMap_mono
    (m n : ℕ) :
    Mono (normalizedJoinBoundaryStandardMap.{u} m n) := by
  cases m with
  | zero => exact normalizedJoinBoundaryStandardMap_zero_mono n
  | succ r => exact normalizedJoinBoundaryStandardMap_succ_mono r n

lemma normalizedJoinBoundaryStandardMap_range (m n : ℕ) :
    SSet.Subcomplex.range (normalizedJoinBoundaryStandardMap.{u} m n) =
      ⨆ j : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) j : Fin (m + n + 3))}ᶜ) := by
  unfold normalizedJoinBoundaryStandardMap
  rw [SSet.Subcomplex.range_comp,
    joinBoundaryStandardMap_range_eq_iSup_leftFaces,
    SSet.Subcomplex.image_iSup]
  apply iSup_congr
  intro j
  rw [ordinaryJoinTransportedLeftLeg_range]
  rw [← SSet.Subcomplex.image_comp]
  simp

abbrev boundaryJoinHornDiagram (m : ℕ) {n : ℕ} (i : Fin (n + 1)) :=
  (((((SSet.horn.multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
      SSet.Subcomplex.toSSetFunctor).multispan ⋙ singletonAugmentation.{u}) ⋙
    augmentedDayTensorLeft
      (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))) ⋙
    forgetAugmentation.{u})

noncomputable def boundaryJoinHornCocone (m : ℕ) {n : ℕ} (i : Fin (n + 1)) :
    Cocone (boundaryJoinHornDiagram.{u} m i) :=
  forgetAugmentation.{u}.mapCocone
    ((augmentedDayTensorLeft
      (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))).mapCocone
        (singletonAugmentationHornCocone.{u} i))

noncomputable def boundaryJoinHornIsColimit (m : ℕ) {n : ℕ}
    (i : Fin (n + 1)) (hn : 0 < n) :
    IsColimit (boundaryJoinHornCocone.{u} m i) := by
  let F := emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u})
  letI : PreservesColimitsOfSize.{0, 0} (augmentedDayTensorLeft F) :=
    (augmentedDayAdjunction F).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} forgetAugmentation.{u} :=
    forgetAugmentation_preservesSmallColimits
  exact isColimitOfPreserves forgetAugmentation.{u}
    (isColimitOfPreserves (augmentedDayTensorLeft F)
      (singletonAugmentationHornIsColimit.{u} i hn))

noncomputable def normalizedJoinBoundaryHornOverlapMap
    (m n : ℕ) (i : Fin (n + 2)) :
    simplicialJoin (SSet.boundary (m + 1) : SSet.{u}) Λ[n + 1, i] ⟶
      Δ[m + (n + 1) + 2] :=
  simplicialJoinMap (SSet.boundary (m + 1)).ι (SSet.horn (n + 1) i).ι ≫
    (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom ≫
    (leftJoinTargetIso m (n + 1)).inv

def normalizedJoinRightCoface (m n : ℕ) (j : Fin (n + 2)) :
    (Δ[m + n + 2] : SSet.{u}) ⟶ Δ[m + (n + 1) + 2] :=
  SSet.stdSimplex.map (SimplexCategory.δ
    (⟨m + 2 + j.val, by omega⟩ : Fin (m + (n + 1) + 3)))

lemma leftJoinTargetIso_inv_comp_normalizedJoinRightCoface
    (m n : ℕ) (j : Fin (n + 2)) :
    (leftJoinTargetIso.{u} m n).inv ≫ normalizedJoinRightCoface m n j =
      SSet.stdSimplex.map (SimplexCategory.δ
        (⟨(m + 1) + 1 + j.val, by omega⟩ : Fin ((m + 1) + n + 3))) ≫
        (leftJoinTargetIso.{u} m (n + 1)).inv := by
  unfold normalizedJoinRightCoface leftJoinTargetIso
  rw [Functor.mapIso_inv, Functor.mapIso_inv]
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply SimplexCategory.Hom.ext
  ext k
  simp [SimplexCategory.δ, Fin.succAbove]
  split_ifs <;> simp_all [Fin.lt_def]; omega

set_option backward.isDefEq.respectTransparency false in
lemma simplicialJoinMap_comp_general
    {A B C X Y Z : SSet.{u}} (f : A ⟶ B) (f' : B ⟶ C)
    (g : X ⟶ Y) (g' : Y ⟶ Z) :
    simplicialJoinMap f g ≫ simplicialJoinMap f' g' =
      simplicialJoinMap (f ≫ f') (g ≫ g') := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj A) (emptyAugmentation.{u}.obj X)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj B) (emptyAugmentation.{u}.obj Y)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj C) (emptyAugmentation.{u}.obj Z)
  unfold simplicialJoinMap
  change Functor.whiskerLeft AugmentedSimplexCategory.inclusion.op (_ ≫ _) = _
  congr 1
  rw [dayConvolutionMap_comp]
  rw [← emptyAugmentation.map_comp, ← emptyAugmentation.map_comp]

lemma normalizedSimplicialJoinMap_rightCoface
    {X Y : SSet.{u}} (m n : ℕ)
    (f : X ⟶ (Δ[m + 1] : SSet.{u})) (g : Y ⟶ Δ[n])
    (j : Fin (n + 2)) :
    (simplicialJoinMap f g ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
          (leftJoinTargetIso m n).inv) ≫
        normalizedJoinRightCoface m n j =
      simplicialJoinMap f (g ≫ SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom ≫
        (leftJoinTargetIso m (n + 1)).inv := by
  calc
    (simplicialJoinMap f g ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
          (leftJoinTargetIso m n).inv) ≫
        normalizedJoinRightCoface m n j =
      simplicialJoinMap f g ≫
        ((simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
          SSet.stdSimplex.map (SimplexCategory.δ
            (⟨(m + 1) + 1 + j.val, by omega⟩ : Fin ((m + 1) + n + 3)))) ≫
        (leftJoinTargetIso m (n + 1)).inv := by
          simp only [Category.assoc]
          rw [leftJoinTargetIso_inv_comp_normalizedJoinRightCoface]
    _ = simplicialJoinMap f g ≫
        (simplicialJoinMap (𝟙 (Δ[m + 1] : SSet.{u}))
          (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom) ≫
        (leftJoinTargetIso m (n + 1)).inv := by
          rw [simplicialJoinStdSimplexIsoNat_naturality_rightCoface]
    _ = (simplicialJoinMap f g ≫
          simplicialJoinMap (𝟙 (Δ[m + 1] : SSet.{u}))
            (SSet.stdSimplex.map (SimplexCategory.δ j))) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom ≫
        (leftJoinTargetIso m (n + 1)).inv := by simp only [Category.assoc]
    _ = _ := by
      rw [simplicialJoinMap_comp_general]
      simp

lemma normalizedJoinBoundaryStandardMap_rightCoface
    (m n : ℕ) (j : Fin (n + 2)) :
    normalizedJoinBoundaryStandardMap.{u} m n ≫
        normalizedJoinRightCoface m n j =
      simplicialJoinMap (SSet.boundary (m + 1)).ι
          (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom ≫
        (leftJoinTargetIso m (n + 1)).inv := by
  calc
    normalizedJoinBoundaryStandardMap.{u} m n ≫
        normalizedJoinRightCoface m n j =
      simplicialJoinMap (SSet.boundary (m + 1)).ι (𝟙 (Δ[n] : SSet.{u})) ≫
        ((simplicialJoinStdSimplexIsoNat (m + 1) n).hom ≫
          SSet.stdSimplex.map (SimplexCategory.δ
            (⟨(m + 1) + 1 + j.val, by omega⟩ : Fin ((m + 1) + n + 3)))) ≫
        (leftJoinTargetIso m (n + 1)).inv := by
          unfold normalizedJoinBoundaryStandardMap joinBoundaryStandardMap
          simp only [Category.assoc]
          rw [leftJoinTargetIso_inv_comp_normalizedJoinRightCoface]
    _ = simplicialJoinMap (SSet.boundary (m + 1)).ι (𝟙 (Δ[n] : SSet.{u})) ≫
        (simplicialJoinMap (𝟙 (Δ[m + 1] : SSet.{u}))
          (SSet.stdSimplex.map (SimplexCategory.δ j)) ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom) ≫
        (leftJoinTargetIso m (n + 1)).inv := by
          rw [simplicialJoinStdSimplexIsoNat_naturality_rightCoface]
    _ = (simplicialJoinMap (SSet.boundary (m + 1)).ι (𝟙 (Δ[n] : SSet.{u})) ≫
          simplicialJoinMap (𝟙 (Δ[m + 1] : SSet.{u}))
            (SSet.stdSimplex.map (SimplexCategory.δ j))) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom ≫
        (leftJoinTargetIso m (n + 1)).inv := by simp only [Category.assoc]
    _ = _ := by
      rw [simplicialJoinMap_comp_general]
      simp

lemma boundaryJoinHornCocone_app
    (m : ℕ) {n : ℕ} (i : Fin (n + 1))
    (a : Limits.WalkingMultispan
      (Limits.MultispanShape.ofLinearOrder ({i}ᶜ : Set (Fin (n + 1))))) :
    (boundaryJoinHornCocone.{u} m i).ι.app a =
      simplicialJoinMap (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
        (((SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
          SSet.Subcomplex.toSSetFunctor).ι.app a) := by
  simp only [boundaryJoinHornCocone, Functor.mapCocone_ι_app]
  rw [simplicialJoinMap_id_eq_augmentedDayTensorLeft_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma boundaryJoinHornCocone_right_precomp
    (m n : ℕ) (i : Fin (n + 2))
    (j : ({i}ᶜ : Set (Fin (n + 2)))) :
    let e := ordinaryJoinBifunctor.{u}.map
      ((𝟙 (SSet.boundary (m + 1) : SSet.{u}),
        (SSet.stdSimplex.faceSingletonComplIso.{u} j.1).hom) :
        ((SSet.boundary (m + 1) : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
          ((SSet.boundary (m + 1) : SSet.{u}),
            (SSet.stdSimplex.face {j.1}ᶜ : SSet.{u})))
    e ≫ (boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
        normalizedJoinBoundaryHornOverlapMap m n i =
      normalizedJoinBoundaryStandardMap m n ≫
        normalizedJoinRightCoface m n j.1 := by
  dsimp only
  rw [normalizedJoinBoundaryStandardMap_rightCoface]
  unfold normalizedJoinBoundaryHornOverlapMap
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [boundaryJoinHornCocone_app]
  change simplicialJoinMap
      (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
      (SSet.stdSimplex.faceSingletonComplIso j.1).hom ≫
      simplicialJoinMap (𝟙 (SSet.boundary (m + 1) : SSet.{u})) _ ≫
      simplicialJoinMap (SSet.boundary (m + 1)).ι (SSet.horn (n + 1) i).ι = _
  rw [simplicialJoinMap_comp_general, simplicialJoinMap_comp_general]
  simp only [Category.id_comp]
  congr 1

lemma boundaryJoinHornCocone_right_comp_mono
    (m n : ℕ) (i : Fin (n + 2))
    (j : ({i}ᶜ : Set (Fin (n + 2)))) :
    Mono ((boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
      normalizedJoinBoundaryHornOverlapMap m n i) := by
  let e := ordinaryJoinBifunctor.{u}.map
    ((𝟙 (SSet.boundary (m + 1) : SSet.{u}),
      (SSet.stdSimplex.faceSingletonComplIso.{u} j.1).hom) :
      ((SSet.boundary (m + 1) : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.boundary (m + 1) : SSet.{u}),
          (SSet.stdSimplex.face {j.1}ᶜ : SSet.{u})))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  have hmono : Mono (normalizedJoinBoundaryStandardMap.{u} m n ≫
      normalizedJoinRightCoface m n j.1) := by
    haveI : Mono (normalizedJoinBoundaryStandardMap.{u} m n) := inferInstance
    haveI : Mono (normalizedJoinRightCoface.{u} m n j.1) := by
      unfold normalizedJoinRightCoface
      change Mono (SSet.stdSimplex.δ
        (⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3)))
      infer_instance
    exact mono_comp _ _
  let f := (boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
    normalizedJoinBoundaryHornOverlapMap m n i
  have heq : e ≫ f = normalizedJoinBoundaryStandardMap m n ≫
      normalizedJoinRightCoface m n j.1 := by
    exact boundaryJoinHornCocone_right_precomp m n i j
  haveI : Mono (e ≫ f) := heq.symm ▸ hmono
  change Mono f
  have hf : f = inv e ≫ (e ≫ f) := by simp
  haveI : Mono (inv e) := inferInstance
  have hcomp : Mono (inv e ≫ (e ≫ f)) := mono_comp _ _
  exact hf.symm ▸ hcomp

set_option backward.isDefEq.respectTransparency false in
lemma boundaryJoinHornCocone_left_precomp
    (m n : ℕ) (i : Fin (n + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (n + 3)))).L) :
    let j := a.1.1
    let k := a.1.2
    let kp := k.1.pred (Fin.ne_zero_of_lt a.2)
    let e := ordinaryJoinBifunctor.{u}.map
      ((𝟙 (SSet.boundary (m + 1) : SSet.{u}),
        (SSet.stdSimplex.facePairComplIso.{u} j.1 k.1 a.2).hom) :
        ((SSet.boundary (m + 1) : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
          ((SSet.boundary (m + 1) : SSet.{u}),
            (SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u})))
    e ≫ (boundaryJoinHornCocone.{u} m i).ι.app (.left a) ≫
        normalizedJoinBoundaryHornOverlapMap m (n + 1) i =
      (normalizedJoinBoundaryStandardMap m n ≫
        normalizedJoinRightCoface m n kp) ≫
          normalizedJoinRightCoface m (n + 1) j.1 := by
  dsimp only
  rw [normalizedJoinBoundaryStandardMap_rightCoface]
  rw [normalizedSimplicialJoinMap_rightCoface]
  unfold normalizedJoinBoundaryHornOverlapMap
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [boundaryJoinHornCocone_app]
  change simplicialJoinMap
      (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
      (SSet.stdSimplex.facePairComplIso a.1.1.1 a.1.2.1 a.2).hom ≫
      simplicialJoinMap (𝟙 (SSet.boundary (m + 1) : SSet.{u})) _ ≫
      simplicialJoinMap (SSet.boundary (m + 1)).ι (SSet.horn (n + 2) i).ι = _
  rw [simplicialJoinMap_comp_general, simplicialJoinMap_comp_general]
  simp only [Category.id_comp]
  congr 1
  let l := (((SSet.horn.multicoequalizerDiagram i).multicofork.toLinearOrder.map
    SSet.Subcomplex.toSSetFunctor).ι.app (.left a))
  have hface : l ≫ (SSet.horn (n + 2) i).ι =
      (SSet.stdSimplex.face {a.1.1.1, a.1.2.1}ᶜ).ι := by
    rfl
  rw [hface]
  exact SSet.stdSimplex.facePairComplIso_hom_ι'
    a.1.1.1 a.1.2.1 a.2

lemma boundaryJoinHornCocone_left_comp_mono
    (m n : ℕ) (i : Fin (n + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (n + 3)))).L) :
    Mono ((boundaryJoinHornCocone.{u} m i).ι.app (.left a) ≫
      normalizedJoinBoundaryHornOverlapMap m (n + 1) i) := by
  let j := a.1.1
  let k := a.1.2
  let kp := k.1.pred (Fin.ne_zero_of_lt a.2)
  let e := ordinaryJoinBifunctor.{u}.map
    ((𝟙 (SSet.boundary (m + 1) : SSet.{u}),
      (SSet.stdSimplex.facePairComplIso.{u} j.1 k.1 a.2).hom) :
      ((SSet.boundary (m + 1) : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.boundary (m + 1) : SSet.{u}),
          (SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u})))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let q := (normalizedJoinBoundaryStandardMap.{u} m n ≫
      normalizedJoinRightCoface m n kp) ≫
    normalizedJoinRightCoface m (n + 1) j.1
  haveI : Mono (normalizedJoinBoundaryStandardMap.{u} m n) := inferInstance
  haveI : Mono (normalizedJoinRightCoface.{u} m n kp) := by
    unfold normalizedJoinRightCoface
    change Mono (SSet.stdSimplex.δ
      (⟨m + 2 + kp.val, by omega⟩ : Fin (m + (n + 1) + 3)))
    infer_instance
  haveI : Mono (normalizedJoinRightCoface.{u} m (n + 1) j.1) := by
    unfold normalizedJoinRightCoface
    change Mono (SSet.stdSimplex.δ
      (⟨m + 2 + j.1.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3)))
    infer_instance
  have hq : Mono q := by
    dsimp [q]
    exact mono_comp _ _
  let f := (boundaryJoinHornCocone.{u} m i).ι.app (.left a) ≫
    normalizedJoinBoundaryHornOverlapMap m (n + 1) i
  have heq : e ≫ f = q := by
    exact boundaryJoinHornCocone_left_precomp m n i a
  haveI : Mono (e ≫ f) := heq.symm ▸ hq
  change Mono f
  have hf : f = inv e ≫ (e ≫ f) := by simp
  haveI : Mono (inv e) := inferInstance
  have hcomp : Mono (inv e ≫ (e ≫ f)) := mono_comp _ _
  exact hf.symm ▸ hcomp

lemma normalizedLeftFace_image_normalizedJoinRightCoface
    (m n : ℕ) (l : Fin (m + 2)) (j : Fin (n + 2)) :
    (SSet.stdSimplex.face
      ({(Fin.castLE (by omega) l : Fin (m + n + 3))}ᶜ)).image
        (normalizedJoinRightCoface.{u} m n j) =
      SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + (n + 1) + 3)),
          (⟨m + 2 + j.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ) := by
  let L₀ := (Fin.castLE (by omega) l : Fin (m + n + 3))
  let L := (Fin.castLE (by omega) l : Fin (m + (n + 1) + 3))
  let J := (⟨m + 2 + j.val, by omega⟩ : Fin (m + (n + 1) + 3))
  have hLJ : L < J := by
    simp only [L, J, Fin.lt_def, Fin.val_castLE]
    omega
  have hδ :
      SSet.stdSimplex.map (SimplexCategory.δ L₀) ≫
          normalizedJoinRightCoface.{u} m n j =
        SSet.stdSimplex.map
            (SimplexCategory.δ (J.pred (Fin.ne_zero_of_lt hLJ))) ≫
          SSet.stdSimplex.map (SimplexCategory.δ L) := by
    unfold normalizedJoinRightCoface
    rw [← Functor.map_comp, ← Functor.map_comp]
    apply congrArg SSet.stdSimplex.map
    exact SimplexCategory.δ_comp_δ' (by
      simpa only [L₀, L, J, Fin.lt_def, Fin.val_castSucc, Fin.val_castLE] using hLJ)
  calc
    (SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + n + 3))}ᶜ)).image
          (normalizedJoinRightCoface.{u} m n j) =
      SSet.Subcomplex.range
        (SSet.stdSimplex.map (SimplexCategory.δ L₀) ≫
          normalizedJoinRightCoface.{u} m n j) := by
            rw [SSet.Subcomplex.range_comp,
              stdSimplex_range_map_delta]
    _ = SSet.Subcomplex.range
        (SSet.stdSimplex.map
            (SimplexCategory.δ (J.pred (Fin.ne_zero_of_lt hLJ))) ≫
          SSet.stdSimplex.map (SimplexCategory.δ L)) :=
      congrArg SSet.Subcomplex.range hδ
    _ = SSet.Subcomplex.range
        ((SSet.stdSimplex.facePairComplIso.{u} L J hLJ).hom ≫
          (SSet.stdSimplex.face {L, J}ᶜ).ι) := by
            congr 1
            exact (SSet.stdSimplex.facePairComplIso_hom_ι' L J hLJ).symm
    _ = SSet.stdSimplex.face {L, J}ᶜ := by
      rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top,
        SSet.Subcomplex.image_top]
      ext U x
      simp [SSet.Subcomplex.range]
    _ = _ := rfl

lemma boundaryJoinHornCocone_right_comp_range
    (m n : ℕ) (i : Fin (n + 2))
    (j : ({i}ᶜ : Set (Fin (n + 2)))) :
    SSet.Subcomplex.range
        ((boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
          normalizedJoinBoundaryHornOverlapMap m n i) =
      ⨆ l : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + (n + 1) + 3)),
          (⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ) := by
  let e := ordinaryJoinBifunctor.{u}.map
    ((𝟙 (SSet.boundary (m + 1) : SSet.{u}),
      (SSet.stdSimplex.faceSingletonComplIso.{u} j.1).hom) :
      ((SSet.boundary (m + 1) : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.boundary (m + 1) : SSet.{u}),
          (SSet.stdSimplex.face {j.1}ᶜ : SSet.{u})))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let f := (boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
    normalizedJoinBoundaryHornOverlapMap m n i
  let q := normalizedJoinBoundaryStandardMap.{u} m n ≫
    normalizedJoinRightCoface m n j.1
  have heq : e ≫ f = q := boundaryJoinHornCocone_right_precomp m n i j
  calc
    SSet.Subcomplex.range
        ((boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
          normalizedJoinBoundaryHornOverlapMap m n i) =
      SSet.Subcomplex.range q :=
        subcomplex_range_eq_of_precomp_iso e f q heq
    _ = (SSet.Subcomplex.range
          (normalizedJoinBoundaryStandardMap.{u} m n)).image
        (normalizedJoinRightCoface m n j.1) :=
      SSet.Subcomplex.range_comp _ _
    _ = _ := by
      rw [normalizedJoinBoundaryStandardMap_range,
        SSet.Subcomplex.image_iSup]
      apply iSup_congr
      intro l
      exact normalizedLeftFace_image_normalizedJoinRightCoface m n l j.1

lemma subcomplex_image_inf_of_mono
    {X Y : SSet.{u}} (A B : X.Subcomplex) (f : X ⟶ Y) [Mono f] :
    (A ⊓ B).image f = A.image f ⊓ B.image f := by
  ext U y
  constructor
  · rintro ⟨x, ⟨hxA, hxB⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, ⟨x, hxB, rfl⟩⟩
  · rintro ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
    have hxz : x = z := (mono_iff_injective _).mp
      (inferInstance : Mono (f.app U)) (hxy.trans hzy.symm)
    subst z
    exact ⟨x, ⟨hxA, hzB⟩, hxy⟩

lemma normalizedRightFace_image_nextNormalizedJoinRightCoface
    (m n : ℕ) {j k : Fin (n + 3)} (hjk : j < k) :
    let kp := k.pred (Fin.ne_zero_of_lt hjk)
    (SSet.stdSimplex.face
      ({(⟨m + 2 + kp.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ)).image
        (normalizedJoinRightCoface.{u} m (n + 1) j) =
      SSet.stdSimplex.face
        ({(⟨m + 2 + j.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + k.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3))}ᶜ) := by
  dsimp only
  let J := (⟨m + 2 + j.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3))
  let K := (⟨m + 2 + k.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3))
  have hJK : J < K := by
    simp only [J, K, Fin.lt_def]
    omega
  let KP := (⟨m + 2 + (k.pred (Fin.ne_zero_of_lt hjk)).val, by omega⟩ :
    Fin (m + (n + 1) + 3))
  have hKP : KP = K.pred (Fin.ne_zero_of_lt hJK) := by
    apply Fin.ext
    simp [KP, K]
    omega
  calc
    (SSet.stdSimplex.face
        ({(⟨m + 2 + (k.pred (Fin.ne_zero_of_lt hjk)).val, by omega⟩ :
          Fin (m + (n + 1) + 3))}ᶜ)).image
          (normalizedJoinRightCoface.{u} m (n + 1) j) =
      SSet.Subcomplex.range
        (SSet.stdSimplex.map (SimplexCategory.δ KP) ≫
          normalizedJoinRightCoface.{u} m (n + 1) j) := by
            rw [SSet.Subcomplex.range_comp, stdSimplex_range_map_delta]
    _ = SSet.Subcomplex.range
        (SSet.stdSimplex.map (SimplexCategory.δ KP) ≫
          SSet.stdSimplex.map (SimplexCategory.δ J)) := by
            rfl
    _ = SSet.Subcomplex.range
        ((SSet.stdSimplex.facePairComplIso.{u} J K hJK).hom ≫
          (SSet.stdSimplex.face {J, K}ᶜ).ι) := by
            congr 1
            rw [hKP]
            exact (SSet.stdSimplex.facePairComplIso_hom_ι' J K hJK).symm
    _ = SSet.stdSimplex.face {J, K}ᶜ := by
      rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top,
        SSet.Subcomplex.image_top]
      ext U x
      simp [SSet.Subcomplex.range]
    _ = _ := rfl

lemma normalizedLeftPairFace_image_normalizedJoinRightCoface
    (m n : ℕ) (l : Fin (m + 2)) {j k : Fin (n + 3)} (hjk : j < k) :
    let kp := k.pred (Fin.ne_zero_of_lt hjk)
    (SSet.stdSimplex.face
      ({(Fin.castLE (by omega) l : Fin (m + (n + 1) + 3)),
        (⟨m + 2 + kp.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ)).image
        (normalizedJoinRightCoface.{u} m (n + 1) j) =
      SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + j.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + k.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3))}ᶜ) := by
  dsimp only
  let L₀ := (Fin.castLE (by omega) l : Fin (m + (n + 1) + 3))
  let KP := (⟨m + 2 + (k.pred (Fin.ne_zero_of_lt hjk)).val, by omega⟩ :
    Fin (m + (n + 1) + 3))
  have hface : SSet.stdSimplex.face {L₀, KP}ᶜ =
      SSet.stdSimplex.face {L₀}ᶜ ⊓ SSet.stdSimplex.face {KP}ᶜ := by
    rw [SSet.stdSimplex.face_inter_face]
    congr 1
    ext x
    simp
  rw [hface]
  haveI : Mono (normalizedJoinRightCoface.{u} m (n + 1) j) := by
    unfold normalizedJoinRightCoface
    change Mono (SSet.stdSimplex.δ
      (⟨m + 2 + j.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3)))
    infer_instance
  rw [subcomplex_image_inf_of_mono,
    normalizedLeftFace_image_normalizedJoinRightCoface,
    normalizedRightFace_image_nextNormalizedJoinRightCoface m n hjk,
    SSet.stdSimplex.face_inter_face]
  congr 1
  ext x
  simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_compl,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  tauto

lemma boundaryJoinHornCocone_left_comp_range
    (m n : ℕ) (i : Fin (n + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (n + 3)))).L) :
    SSet.Subcomplex.range
        ((boundaryJoinHornCocone.{u} m i).ι.app (.left a) ≫
          normalizedJoinBoundaryHornOverlapMap m (n + 1) i) =
      ⨆ l : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + a.1.1.1.val, by omega⟩ :
            Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + a.1.2.1.val, by omega⟩ :
            Fin (m + ((n + 1) + 1) + 3))}ᶜ) := by
  let j := a.1.1
  let k := a.1.2
  let kp := k.1.pred (Fin.ne_zero_of_lt a.2)
  let e := ordinaryJoinBifunctor.{u}.map
    ((𝟙 (SSet.boundary (m + 1) : SSet.{u}),
      (SSet.stdSimplex.facePairComplIso.{u} j.1 k.1 a.2).hom) :
      ((SSet.boundary (m + 1) : SSet.{u}), (Δ[n] : SSet.{u})) ⟶
        ((SSet.boundary (m + 1) : SSet.{u}),
          (SSet.stdSimplex.face {j.1, k.1}ᶜ : SSet.{u})))
  haveI : IsIso e := by
    dsimp [e]
    apply ordinaryJoinBifunctor_map_isIso
  let f := (boundaryJoinHornCocone.{u} m i).ι.app (.left a) ≫
    normalizedJoinBoundaryHornOverlapMap m (n + 1) i
  let q := (normalizedJoinBoundaryStandardMap.{u} m n ≫
      normalizedJoinRightCoface m n kp) ≫
    normalizedJoinRightCoface m (n + 1) j.1
  have heq : e ≫ f = q := boundaryJoinHornCocone_left_precomp m n i a
  calc
    SSet.Subcomplex.range
        ((boundaryJoinHornCocone.{u} m i).ι.app (.left a) ≫
          normalizedJoinBoundaryHornOverlapMap m (n + 1) i) =
      SSet.Subcomplex.range q :=
        subcomplex_range_eq_of_precomp_iso e f q heq
    _ = ((SSet.Subcomplex.range
          (normalizedJoinBoundaryStandardMap.{u} m n)).image
            (normalizedJoinRightCoface m n kp)).image
          (normalizedJoinRightCoface m (n + 1) j.1) := by
      dsimp [q]
      rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_comp]
    _ = _ := by
      rw [normalizedJoinBoundaryStandardMap_range,
        SSet.Subcomplex.image_iSup, SSet.Subcomplex.image_iSup]
      apply iSup_congr
      intro l
      rw [normalizedLeftFace_image_normalizedJoinRightCoface]
      exact normalizedLeftPairFace_image_normalizedJoinRightCoface m n l a.2

lemma normalizedRightFaceRange_iSup_inf
    (m n : ℕ) {j k : Fin (n + 3)} (hjk : j < k) :
    (⨆ l : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + j.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3))}ᶜ)) ⊓
      (⨆ l : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + k.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3))}ᶜ)) =
      ⨆ l : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + j.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3)),
          (⟨m + 2 + k.val, by omega⟩ : Fin (m + ((n + 1) + 1) + 3))}ᶜ) := by
  apply le_antisymm
  · rw [subcomplex_iSup_inf_eq]
    apply iSup_le
    intro l
    rw [inf_comm, subcomplex_iSup_inf_eq]
    apply iSup_le
    intro r
    refine le_iSup_of_le l ?_
    rw [SSet.stdSimplex.face_inter_face,
      SSet.stdSimplex.face_le_face_iff]
    intro x hx
    simp only [
      Finset.mem_compl] at hx ⊢
    aesop
  · apply iSup_le
    intro l
    apply le_inf
    · refine le_iSup_of_le l ?_
      rw [SSet.stdSimplex.face_le_face_iff]
      intro x hx
      simp only [Finset.mem_compl,
        ] at hx ⊢
      aesop
    · refine le_iSup_of_le l ?_
      rw [SSet.stdSimplex.face_le_face_iff]
      intro x hx
      simp only [Finset.mem_compl,
        ] at hx ⊢
      aesop

lemma boundaryJoinHornCocone_left_comp_range_eq_inf
    (m n : ℕ) (i : Fin (n + 3))
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin (n + 3)))).L) :
    SSet.Subcomplex.range
        ((boundaryJoinHornCocone.{u} m i).ι.app (.left a) ≫
          normalizedJoinBoundaryHornOverlapMap m (n + 1) i) =
      SSet.Subcomplex.range
          ((boundaryJoinHornCocone.{u} m i).ι.app (.right a.1.1) ≫
            normalizedJoinBoundaryHornOverlapMap m (n + 1) i) ⊓
        SSet.Subcomplex.range
          ((boundaryJoinHornCocone.{u} m i).ι.app (.right a.1.2) ≫
            normalizedJoinBoundaryHornOverlapMap m (n + 1) i) := by
  rw [boundaryJoinHornCocone_left_comp_range,
    boundaryJoinHornCocone_right_comp_range,
    boundaryJoinHornCocone_right_comp_range,
    normalizedRightFaceRange_iSup_inf m n a.2]

lemma no_left_boundaryJoinHornIndex_zero
    (i : Fin 2)
    (a : (Limits.MultispanShape.ofLinearOrder
      ({i}ᶜ : Set (Fin 2))).L) : False := by
  have hj := a.1.1.2
  have hk := a.1.2.2
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hj hk
  have hjv : a.1.1.1.val ≠ i.val := by
    intro h
    exact hj (Fin.ext h)
  have hkv : a.1.2.1.val ≠ i.val := by
    intro h
    exact hk (Fin.ext h)
  have hlt : a.1.1.1.val < a.1.2.1.val := a.2
  have hi := i.isLt
  have hjlt := a.1.1.1.isLt
  have hklt := a.1.2.1.isLt
  omega

noncomputable instance normalizedJoinBoundaryHornOverlapMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (normalizedJoinBoundaryHornOverlapMap.{u} m n i) := by
  let c := boundaryJoinHornCocone.{u} m i
  let hc := boundaryJoinHornIsColimit.{u} m i (by omega)
  apply mono_of_linearMultispan_ranges c
    (normalizedJoinBoundaryHornOverlapMap m n i) hc
  · rintro (a | j)
    · cases n with
      | zero => exact (no_left_boundaryJoinHornIndex_zero i a).elim
      | succ n => exact boundaryJoinHornCocone_left_comp_mono m n i a
    · exact boundaryJoinHornCocone_right_comp_mono m n i j
  · intro a
    cases n with
    | zero => exact (no_left_boundaryJoinHornIndex_zero i a).elim
    | succ n => exact boundaryJoinHornCocone_left_comp_range_eq_inf m n i a

lemma normalizedJoinBoundaryHornOverlapMap_range_eq_iSup_right
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (normalizedJoinBoundaryHornOverlapMap.{u} m n i) =
      ⨆ j : ({i}ᶜ : Set (Fin (n + 2))),
        SSet.Subcomplex.range
          ((boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
            normalizedJoinBoundaryHornOverlapMap m n i) := by
  let c := boundaryJoinHornCocone.{u} m i
  let f := normalizedJoinBoundaryHornOverlapMap.{u} m n i
  calc
    SSet.Subcomplex.range f =
        ⨆ q, SSet.Subcomplex.range (c.ι.app q ≫ f) :=
      SSet.range_eq_iSup_of_isColimit
        (boundaryJoinHornIsColimit.{u} m i (by omega)) f
    _ = _ := by
      apply le_antisymm
      · apply iSup_le
        rintro (a | j)
        · cases n with
          | zero => exact (no_left_boundaryJoinHornIndex_zero i a).elim
          | succ n =>
              rw [boundaryJoinHornCocone_left_comp_range_eq_inf]
              exact inf_le_left.trans (le_iSup
                (fun j : ({i}ᶜ : Set (Fin (n + 3))) ↦
                  SSet.Subcomplex.range
                    ((boundaryJoinHornCocone.{u} m i).ι.app (.right j) ≫
                      normalizedJoinBoundaryHornOverlapMap m (n + 1) i)) a.1.1)
        · exact le_iSup (fun q : ({i}ᶜ : Set (Fin (n + 2))) ↦
            SSet.Subcomplex.range
              ((boundaryJoinHornCocone.{u} m i).ι.app (.right q) ≫
                normalizedJoinBoundaryHornOverlapMap m n i)) j
      · apply iSup_le
        intro j
        exact le_iSup (fun q : Limits.WalkingMultispan
          (Limits.MultispanShape.ofLinearOrder ({i}ᶜ : Set (Fin (n + 2)))) ↦
            SSet.Subcomplex.range
              ((boundaryJoinHornCocone.{u} m i).ι.app q ≫
                normalizedJoinBoundaryHornOverlapMap m n i)) (.right j)

lemma normalizedJoinBoundaryHornOverlapMap_range
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (normalizedJoinBoundaryHornOverlapMap.{u} m n i) =
      ⨆ j : ({i}ᶜ : Set (Fin (n + 2))), ⨆ l : Fin (m + 2),
        SSet.stdSimplex.face
          ({(Fin.castLE (by omega) l : Fin (m + (n + 1) + 3)),
            (⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ) := by
  rw [normalizedJoinBoundaryHornOverlapMap_range_eq_iSup_right]
  apply iSup_congr
  intro j
  exact boundaryJoinHornCocone_right_comp_range m n i j

/-- The join boundary-horn corner in the same strict standard coordinates as
`normalizedJoinBoundaryStandardMap`. -/
noncomputable def normalizedJoinBoundaryHornCornerMap
    (m n : ℕ) (i : Fin (n + 2)) :
    (joinBoundaryHornCornerSq (m + 1) (n + 1) i).pt ⟶
      Δ[m + (n + 1) + 2] :=
  joinBoundaryHornStandardCornerMap (m + 1) (n + 1) i ≫
    (leftJoinTargetIso m (n + 1)).inv

lemma normalizedJoinBoundaryHornCornerMap_range
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (normalizedJoinBoundaryHornCornerMap.{u} m n i) =
      (representableJoinHornInitial (m + 1) (n + 1) i).image
          (leftJoinTargetIso m (n + 1)).inv ⊔
        SSet.Subcomplex.range
          (normalizedJoinBoundaryStandardMap m (n + 1)) := by
  unfold normalizedJoinBoundaryHornCornerMap
  rw [SSet.Subcomplex.range_comp,
    joinBoundaryHornStandardCornerMap_range]
  unfold normalizedJoinBoundaryStandardMap
  rw [SSet.Subcomplex.range_comp]
  simp only [sup_eq_iSup, SSet.Subcomplex.image_iSup]
  congr 1
  funext b
  cases b <;> rfl

lemma shiftedRightFace_image_leftJoinTargetIso_inv
    (m n : ℕ) (j : Fin (n + 2)) :
    (SSet.stdSimplex.face
      ({(⟨(m + 1) + 1 + j.val, by omega⟩ :
        Fin ((m + 1) + (n + 1) + 2))}ᶜ)).image
        (leftJoinTargetIso.{u} m (n + 1)).inv =
      SSet.stdSimplex.face
        ({(⟨m + 2 + j.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ) := by
  have hi : inv (leftJoinTargetIso.{u} m (n + 1)).hom =
      (leftJoinTargetIso m (n + 1)).inv := by simp
  rw [← hi]
  rw [SSet.Subcomplex.image_inv]
  ext U x
  rcases U with ⟨⟨d⟩⟩
  change ((leftJoinTargetIso m (n + 1)).hom.app _ x ∈
      (SSet.stdSimplex.face _).obj _) ↔
    x ∈ (SSet.stdSimplex.face _).obj _
  rw [SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff]
  simp only [Finset.mem_compl, Finset.mem_singleton]
  have hval (k : Fin (d + 1)) :
      (((leftJoinTargetIso m (n + 1)).hom.app _ x) k).val = (x k).val := by
    change (SimplexCategory.Hom.toOrderHom
      (eqToHom (by
        apply SimplexCategory.ext
        simp
        omega) : SimplexCategory.mk (m + (n + 1) + 2) ⟶
          SimplexCategory.mk ((m + 1) + (n + 1) + 1)) (x k)).val = _
    simp
  constructor
  · intro h k hk
    apply h k
    apply Fin.ext
    rw [hval]
    exact congrArg Fin.val hk
  · intro h k hk
    apply h k
    apply Fin.ext
    have hv := congrArg Fin.val hk
    rw [hval] at hv
    exact hv

lemma representableJoinHornInitial_image_leftJoinTargetIso_inv
    (m n : ℕ) (i : Fin (n + 2)) :
    (representableJoinHornInitial (m + 1) (n + 1) i).image
        (leftJoinTargetIso.{u} m (n + 1)).inv =
      ⨆ j : ({i}ᶜ : Set (Fin (n + 2))), SSet.stdSimplex.face
        ({(⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ) := by
  rw [representableJoinHornInitial_eq_iSup_shiftedRightFaces,
    SSet.Subcomplex.image_iSup]
  apply iSup_congr
  intro j
  exact shiftedRightFace_image_leftJoinTargetIso_inv m n j

set_option maxHeartbeats 800000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
lemma normalizedRightFaces_sup_leftFaces_eq_horn
    (m n : ℕ) (i : Fin (n + 2)) :
    (⨆ j : ({i}ᶜ : Set (Fin (n + 2))), SSet.stdSimplex.face
        ({(⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ)) ⊔
      (⨆ j : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) j : Fin (m + (n + 1) + 3))}ᶜ)) =
      SSet.horn (m + (n + 1) + 2)
        (⟨m + 2 + i.val, by omega⟩ : Fin (m + (n + 1) + 3)) := by
  rw [SSet.horn_eq_iSup]
  apply le_antisymm
  · apply sup_le
    · apply iSup_le
      rintro ⟨j, hj⟩
      exact le_iSup (fun q :
        ({(⟨m + 2 + i.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ :
          Set (Fin (m + (n + 1) + 3))) ↦
          SSet.stdSimplex.face ({q.1}ᶜ))
        ⟨⟨m + 2 + j.val, by omega⟩, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          apply hj
          apply Fin.ext
          have hv := congrArg Fin.val h
          have hv' : m + 2 + j.val = m + 2 + i.val := by
            exact hv
          omega⟩
    · apply iSup_le
      intro j
      exact le_iSup (fun q :
        ({(⟨m + 2 + i.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ :
          Set (Fin (m + (n + 1) + 3))) ↦
          SSet.stdSimplex.face ({q.1}ᶜ))
        ⟨Fin.castLE (by omega) j, by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castLE] at hv
          omega⟩
  · apply iSup_le
    rintro ⟨j, hj⟩
    by_cases hleft : j.val < m + 2
    · let k : Fin (m + 2) := ⟨j.val, hleft⟩
      have hk : (Fin.castLE (by omega) k : Fin (m + (n + 1) + 3)) = j := by
        apply Fin.ext
        rfl
      exact le_sup_of_le_right (by
        convert le_iSup (fun q : Fin (m + 2) ↦ SSet.stdSimplex.face
          ({(Fin.castLE (by omega) q : Fin (m + (n + 1) + 3))}ᶜ)) k using 1
        rw [hk])
    · let k : Fin (n + 2) := ⟨j.val - (m + 2), by omega⟩
      have hkface :
          (⟨m + 2 + k.val, by omega⟩ : Fin (m + (n + 1) + 3)) = j := by
        apply Fin.ext
        dsimp [k]
        omega
      have hki : k ≠ i := by
        intro h
        apply hj
        simp only [Set.mem_singleton_iff]
        exact hkface.symm.trans (by
          apply Fin.ext
          change m + 2 + k.val = m + 2 + i.val
          rw [h])
      exact le_sup_of_le_left (by
        convert le_iSup (fun q : ({i}ᶜ : Set (Fin (n + 2))) ↦
          SSet.stdSimplex.face
            ({(⟨m + 2 + q.1.val, by omega⟩ :
              Fin (m + (n + 1) + 3))}ᶜ)) ⟨k, by simpa using hki⟩ using 1
        rw [hkface])

lemma normalizedJoinBoundaryHornCornerMap_range_eq_horn
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (normalizedJoinBoundaryHornCornerMap.{u} m n i) =
      SSet.horn (m + (n + 1) + 2)
        (⟨m + 2 + i.val, by omega⟩ : Fin (m + (n + 1) + 3)) := by
  rw [normalizedJoinBoundaryHornCornerMap_range,
    representableJoinHornInitial_image_leftJoinTargetIso_inv,
    normalizedJoinBoundaryStandardMap_range,
    normalizedRightFaces_sup_leftFaces_eq_horn]

noncomputable def normalizedRepresentableJoinHornMap
    (m n : ℕ) (i : Fin (n + 2)) :
    simplicialJoin (Δ[m + 1] : SSet.{u}) Λ[n + 1, i] ⟶
      Δ[m + (n + 1) + 2] :=
  representableJoinHornMap (m + 1) (n + 1) i ≫
    (leftJoinTargetIso m (n + 1)).inv

lemma normalizedRepresentableJoinHornMap_range
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (normalizedRepresentableJoinHornMap.{u} m n i) =
      ⨆ j : ({i}ᶜ : Set (Fin (n + 2))), SSet.stdSimplex.face
        ({(⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ) := by
  unfold normalizedRepresentableJoinHornMap
  rw [SSet.Subcomplex.range_comp]
  change (representableJoinHornInitial (m + 1) (n + 1) i).image
      (leftJoinTargetIso.{u} m (n + 1)).inv = _
  exact representableJoinHornInitial_image_leftJoinTargetIso_inv m n i

lemma normalizedRightFaces_iSup_inf_normalizedLeftFaces_iSup
    (m n : ℕ) (i : Fin (n + 2)) :
    (⨆ j : ({i}ᶜ : Set (Fin (n + 2))), SSet.stdSimplex.face
        ({(⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ)) ⊓
      (⨆ l : Fin (m + 2), SSet.stdSimplex.face
        ({(Fin.castLE (by omega) l : Fin (m + (n + 1) + 3))}ᶜ)) =
      ⨆ j : ({i}ᶜ : Set (Fin (n + 2))), ⨆ l : Fin (m + 2),
        SSet.stdSimplex.face
          ({(Fin.castLE (by omega) l : Fin (m + (n + 1) + 3)),
            (⟨m + 2 + j.1.val, by omega⟩ : Fin (m + (n + 1) + 3))}ᶜ) := by
  rw [subcomplex_iSup_inf_eq]
  apply iSup_congr
  intro j
  rw [inf_comm, subcomplex_iSup_inf_eq]
  apply iSup_congr
  intro l
  rw [SSet.stdSimplex.face_inter_face]
  congr 1
  ext x
  simp

lemma normalizedJoinBoundaryHornOverlapMap_range_eq_inf
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (normalizedJoinBoundaryHornOverlapMap.{u} m n i) =
      SSet.Subcomplex.range
          (normalizedRepresentableJoinHornMap.{u} m n i) ⊓
        SSet.Subcomplex.range
          (normalizedJoinBoundaryStandardMap.{u} m (n + 1)) := by
  rw [normalizedJoinBoundaryHornOverlapMap_range,
    normalizedRepresentableJoinHornMap_range,
    normalizedJoinBoundaryStandardMap_range,
    normalizedRightFaces_iSup_inf_normalizedLeftFaces_iSup]

noncomputable instance normalizedRepresentableJoinHornMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (normalizedRepresentableJoinHornMap.{u} m n i) := by
  unfold normalizedRepresentableJoinHornMap
  haveI : Mono (leftJoinTargetIso.{u} m (n + 1)).inv := inferInstance
  cases n with
  | zero =>
      fin_cases i
      · change Mono (representableJoinHornMap.{u} (m + 1) 1 (0 : Fin 2) ≫
          (leftJoinTargetIso m 1).inv)
        haveI : Mono (representableJoinHornMap.{u} (m + 1) 1 (0 : Fin 2)) :=
          representableJoinHornMap_one_zero_mono (m + 1)
        exact mono_comp _ _
      · change Mono (representableJoinHornMap.{u} (m + 1) 1 (1 : Fin 2) ≫
          (leftJoinTargetIso m 1).inv)
        haveI : Mono (representableJoinHornMap.{u} (m + 1) 1 (1 : Fin 2)) :=
          representableJoinHornMap_one_one_mono (m + 1)
        exact mono_comp _ _
  | succ n =>
      haveI : Mono (representableJoinHornMap.{u} (m + 1) (n + 2) i) :=
        representableJoinHornMap_mono (m + 1) n i
      exact mono_comp _ _

lemma normalizedJoinBoundaryHornOverlapMap_top
    (m n : ℕ) (i : Fin (n + 2)) :
    simplicialJoinMap (SSet.boundary (m + 1)).ι
        (𝟙 (Λ[n + 1, i] : SSet.{u})) ≫
      normalizedRepresentableJoinHornMap m n i =
        normalizedJoinBoundaryHornOverlapMap m n i := by
  unfold normalizedRepresentableJoinHornMap
  unfold normalizedJoinBoundaryHornOverlapMap representableJoinHornMap
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  rw [simplicialJoinMap_comp_general]
  simp

lemma normalizedJoinBoundaryHornOverlapMap_bottom
    (m n : ℕ) (i : Fin (n + 2)) :
    simplicialJoinMap (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
        (SSet.horn (n + 1) i).ι ≫
      normalizedJoinBoundaryStandardMap m (n + 1) =
        normalizedJoinBoundaryHornOverlapMap m n i := by
  unfold normalizedJoinBoundaryStandardMap joinBoundaryStandardMap
  unfold normalizedJoinBoundaryHornOverlapMap
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  rw [simplicialJoinMap_comp_general]
  simp

lemma normalizedJoinBoundaryHornTopMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (simplicialJoinMap (SSet.boundary (m + 1)).ι
      (𝟙 (Λ[n + 1, i] : SSet.{u}))) := by
  haveI : Mono (normalizedJoinBoundaryHornOverlapMap.{u} m n i) := inferInstance
  apply mono_of_mono_fac
    (h := normalizedJoinBoundaryHornOverlapMap.{u} m n i)
  exact normalizedJoinBoundaryHornOverlapMap_top m n i

lemma normalizedJoinBoundaryHornBottomMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (simplicialJoinMap (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
      (SSet.horn (n + 1) i).ι) := by
  haveI : Mono (normalizedJoinBoundaryHornOverlapMap.{u} m n i) := inferInstance
  apply mono_of_mono_fac
    (h := normalizedJoinBoundaryHornOverlapMap.{u} m n i)
  exact normalizedJoinBoundaryHornOverlapMap_bottom m n i

set_option backward.isDefEq.respectTransparency false in
noncomputable instance normalizedJoinBoundaryHornCornerMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (normalizedJoinBoundaryHornCornerMap.{u} m n i) := by
  let a := (ordinaryJoinCurried.{u}.map (SSet.boundary (m + 1)).ι).app
    (Λ[n + 1, i] : SSet.{u})
  let b := (ordinaryJoinCurried.{u}.obj
    (SSet.boundary (m + 1) : SSet.{u})).map (SSet.horn (n + 1) i).ι
  let h := normalizedRepresentableJoinHornMap.{u} m n i
  let k := normalizedJoinBoundaryStandardMap.{u} m (n + 1)
  have ha : a ≫ h = normalizedJoinBoundaryHornOverlapMap m n i := by
    exact normalizedJoinBoundaryHornOverlapMap_top m n i
  have hb : b ≫ k = normalizedJoinBoundaryHornOverlapMap m n i := by
    exact normalizedJoinBoundaryHornOverlapMap_bottom m n i
  have w : a ≫ h = b ≫ k := ha.trans hb.symm
  haveI : Mono a := by
    dsimp [a]
    exact normalizedJoinBoundaryHornTopMap_mono m n i
  haveI : Mono b := by
    dsimp [b]
    exact normalizedJoinBoundaryHornBottomMap_mono m n i
  haveI : Mono h := by
    dsimp [h]
    infer_instance
  haveI : Mono k := by
    dsimp [k]
    infer_instance
  have hr : SSet.Subcomplex.range (a ≫ h) =
      SSet.Subcomplex.range h ⊓ SSet.Subcomplex.range k := by
    rw [ha]
    exact normalizedJoinBoundaryHornOverlapMap_range_eq_inf m n i
  have hp : Mono (pushout.desc h k w) :=
    mono_of_pushout_range_inter w hr
  let sq := joinBoundaryHornCornerSq (m + 1) (n + 1) i
  let g := sq.isPushout.desc h k w
  have hgp : g = pushout.desc h k w := by
    apply sq.hom_ext
    · dsimp [g]
      rw [sq.isPushout.inl_desc]
      dsimp [sq, joinBoundaryHornCornerSq,
        Functor.PushoutObjObj.ofHasPushout]
      rw [pushout.inl_desc]
    · dsimp [g]
      rw [sq.isPushout.inr_desc]
      dsimp [sq, joinBoundaryHornCornerSq,
        Functor.PushoutObjObj.ofHasPushout]
      rw [pushout.inr_desc]
  have hg : Mono g := by
    exact hgp.symm ▸ hp
  have heq : normalizedJoinBoundaryHornCornerMap.{u} m n i =
      g := by
    apply sq.hom_ext
    · rw [sq.isPushout.inl_desc]
      unfold normalizedJoinBoundaryHornCornerMap
      rw [joinBoundaryHornStandardCornerMap_inl_assoc]
      rfl
    · rw [sq.isPushout.inr_desc]
      unfold normalizedJoinBoundaryHornCornerMap
      rw [joinBoundaryHornStandardCornerMap_inr_assoc]
      rfl
  exact heq.symm ▸ hg

/--
A monic normalized boundary-horn corner is inner anodyne away from the last right vertex.
-/
lemma normalizedJoinBoundaryHornCornerMap_innerAnodyne_of_mono
    (m n : ℕ) (i : Fin (n + 2))
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m n i)]
    (hi : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (normalizedJoinBoundaryHornCornerMap.{u} m n i) := by
  let f := normalizedJoinBoundaryHornCornerMap.{u} m n i
  let e := simplicialSetIsoRangeOfMono f
  have he := SSet.innerAnodyneExtensions.of_isIso e.hom
  have hι : SSet.innerAnodyneExtensions (SSet.Subcomplex.range f).ι := by
    rw [normalizedJoinBoundaryHornCornerMap_range_eq_horn]
    exact SSet.innerAnodyneExtensions.horn_ι (by
      change 0 < m + 2 + i.val
      omega) (by
      apply Fin.mk_lt_mk.mpr
      have hi' := Fin.mk_lt_mk.mp hi
      omega)
  have hc := SSet.innerAnodyneExtensions.comp_mem _ _ he hι
  change SSet.innerAnodyneExtensions
    (e.hom ≫ (SSet.Subcomplex.range f).ι) at hc
  simpa [e, f, simplicialSetIsoRangeOfMono] using hc

/--
The normalized boundary-horn corner is inner anodyne away from the last right vertex.
-/
lemma normalizedJoinBoundaryHornCornerMap_innerAnodyne
    (m n : ℕ) (i : Fin (n + 2))
    (hi : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (normalizedJoinBoundaryHornCornerMap.{u} m n i) :=
  normalizedJoinBoundaryHornCornerMap_innerAnodyne_of_mono m n i hi

end LeanLCAExactChallenge.Infinity
