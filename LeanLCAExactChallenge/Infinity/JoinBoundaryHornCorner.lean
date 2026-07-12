import LeanLCAExactChallenge.Infinity.RightConeHorn
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

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

end LeanLCAExactChallenge.Infinity
