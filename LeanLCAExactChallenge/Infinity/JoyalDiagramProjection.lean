import LeanLCAExactChallenge.Infinity.JoyalDiagramSlices
import LeanLCAExactChallenge.Infinity.JoinBoundaryHornCorner

/-! # Projections from diagram-under-slices -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution
  MonoidalCategory.ExternalProduct MonoidalCategory Prod

/-- The universal fixed-base cone represented by a diagram-under-slice. -/
def diagramUnderUniversalCone
    (Q K : SSet.{u}) (a : K ⟶ Q) :=
  (relativeDaySliceOverMapFixedBaseEquiv
    (emptyAugmentation.{u}.obj K)
    (emptyAugmentation.{u}.obj Q)
    (diagramUnderSlice Q K a)
    (emptyAugmentation.{u}.map a)) (𝟙 _)

/-- Forget the fixed diagram and retain the varying cone point. -/
def diagramUnderProjection
    (Q K : SSet.{u}) (a : K ⟶ Q) :
    diagramUnderSlice Q K a ⟶ Q :=
  simplicialJoinRightInclusion K (diagramUnderSlice Q K a) ≫
    forgetAugmentation.{u}.map (diagramUnderUniversalCone Q K a).1

/-- The inclusion of the right join factor is natural in that factor. -/
private theorem simplicialJoinRightInclusion_naturality_right
    {X Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    g ≫ simplicialJoinRightInclusion X Y' =
      simplicialJoinRightInclusion X Y ≫
        simplicialJoinMap (𝟙 X) g := by
  apply NatTrans.ext
  funext U
  let F := emptyAugmentation.{u}.obj X
  let G := emptyAugmentation.{u}.obj Y
  let G' := emptyAugmentation.{u}.obj Y'
  letI := augmentedDayConvolution F G
  letI := augmentedDayConvolution F G'
  letI : Unique (F.obj (Opposite.op WithInitial.star)) :=
    (Limits.Types.isTerminalEquivUnique _)
      (emptyAugmentationStarIsTerminal X)
  let s : G.obj (AugmentedSimplexCategory.inclusion.op.obj U) ⟶
      (F ⊠ G).obj (Opposite.op WithInitial.star,
        AugmentedSimplexCategory.inclusion.op.obj U) :=
    ConcreteCategory.ofHom (TypeCat.Fun.mk (fun y ↦ (default, y)))
  let s' : G'.obj (AugmentedSimplexCategory.inclusion.op.obj U) ⟶
      (F ⊠ G').obj (Opposite.op WithInitial.star,
        AugmentedSimplexCategory.inclusion.op.obj U) :=
    ConcreteCategory.ofHom (TypeCat.Fun.mk (fun y ↦ (default, y)))
  change (emptyAugmentation.map g).app
      (AugmentedSimplexCategory.inclusion.op.obj U) ≫ s' ≫
      (CategoryTheory.MonoidalCategory.DayConvolution.unit F G').app
        (Opposite.op WithInitial.star,
          AugmentedSimplexCategory.inclusion.op.obj U) =
    s ≫ (CategoryTheory.MonoidalCategory.DayConvolution.unit F G).app
        (Opposite.op WithInitial.star,
          AugmentedSimplexCategory.inclusion.op.obj U) ≫
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map (𝟙 X))
        (emptyAugmentation.map g)).app _
  rw [emptyAugmentation.map_id]
  change _ = s ≫
    (CategoryTheory.MonoidalCategory.DayConvolution.unit F G).app
      (Opposite.op WithInitial.star,
        AugmentedSimplexCategory.inclusion.op.obj U) ≫
    (CategoryTheory.MonoidalCategory.DayConvolution.map
      (𝟙 F) (emptyAugmentation.map g)).app
        (Opposite.op WithInitial.star ⊗
          AugmentedSimplexCategory.inclusion.op.obj U)
  rw [CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app]
  have hpref : (emptyAugmentation.map g).app
        (AugmentedSimplexCategory.inclusion.op.obj U) ≫ s' =
      s ≫ (NatTrans.app (𝟙 F) (Opposite.op WithInitial.star) ⊗ₘ
        (emptyAugmentation.map g).app
          (AugmentedSimplexCategory.inclusion.op.obj U)) := by
    apply ConcreteCategory.hom_ext
    intro y
    rfl
  rw [← Category.assoc, hpref]
  exact Category.assoc _ _ _

/--
Right restriction of the fixed-base transpose composes with the diagram-under projection.
-/
theorem diagramUnderProjection_comp_eq_fixedBaseCone
    (Q K L : SSet.{u}) (a : K ⟶ Q)
    (f : L ⟶ diagramUnderSlice Q K a) :
    f ≫ diagramUnderProjection Q K a =
      simplicialJoinRightInclusion K L ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv
            (emptyAugmentation.{u}.obj K)
            (emptyAugmentation.{u}.obj Q) L
            (emptyAugmentation.{u}.map a)) f).1 := by
  let F := emptyAugmentation.{u}.obj K
  let G := emptyAugmentation.{u}.obj Q
  let aMap := emptyAugmentation.{u}.map a
  have ht := relativeDaySliceOverMapFixedBaseEquiv_precomp_fst
    F G aMap f (𝟙 (diagramUnderSlice Q K a))
  simp only [Category.comp_id] at ht
  dsimp only [F, G, aMap] at ht ⊢
  unfold diagramUnderProjection diagramUnderUniversalCone
  rw [ht]
  rw [← Category.assoc,
    simplicialJoinRightInclusion_naturality_right, Category.assoc]
  let T := (augmentedDayTensorLeft
    (emptyAugmentation.obj K)).map (emptyAugmentation.map f)
  let V := ((relativeDaySliceOverMapFixedBaseEquiv
      (emptyAugmentation.obj K) (emptyAugmentation.obj Q)
      (diagramUnderSlice Q K a) (emptyAugmentation.map a))
        (𝟙 (diagramUnderSlice Q K a))).1
  have hc := (forgetAugmentation.{u}).map_comp T V
  have hT : forgetAugmentation.map T =
      simplicialJoinMap (𝟙 K) f := by
    unfold T simplicialJoinMap augmentedDayTensorLeft
    rw [emptyAugmentation.map_id]
    rfl
  change _ = simplicialJoinRightInclusion K L ≫
    forgetAugmentation.map (T ≫ V)
  calc
    _ = simplicialJoinRightInclusion K L ≫
        (simplicialJoinMap (𝟙 K) f ≫
          forgetAugmentation.map V) := Category.assoc _ _ _
    _ = simplicialJoinRightInclusion K L ≫
        (forgetAugmentation.map T ≫ forgetAugmentation.map V) :=
      congrArg (fun k ↦ simplicialJoinRightInclusion K L ≫ k)
        (congrArg (fun k ↦ k ≫ forgetAugmentation.map V) hT.symm)
    _ = _ := congrArg
      (fun k ↦ simplicialJoinRightInclusion K L ≫ k) hc.symm

/--
A diagram-under-slice horn square glues its fixed-base cone to the prescribed cone point.
-/
noncomputable def diagramUnderProjectionLiftingCornerTop
    (Q K : SSet.{u}) (a : K ⟶ Q) {n : ℕ} {i : Fin (n + 1)}
    {f : (Λ[n, i] : SSet.{u}) ⟶ diagramUnderSlice Q K a}
    {b : Δ[n] ⟶ Q}
    (sq : CommSq f (SSet.horn n i).ι (diagramUnderProjection Q K a) b) :
    pushout (simplicialJoinRightInclusion K Λ[n, i])
        (SSet.horn n i).ι ⟶ Q :=
  pushout.desc
    (forgetAugmentation.{u}.map
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj K)
        (emptyAugmentation.{u}.obj Q) (Λ[n, i] : SSet.{u})
        (emptyAugmentation.{u}.map a)) f).1)
    b (by
      exact (diagramUnderProjection_comp_eq_fixedBaseCone
        Q K _ a f).symm.trans sq.w)

@[reassoc (attr := simp)]
theorem diagramUnderProjectionLiftingCornerTop_inl
    (Q K : SSet.{u}) (a : K ⟶ Q) {n : ℕ} {i : Fin (n + 1)}
    {f : (Λ[n, i] : SSet.{u}) ⟶ diagramUnderSlice Q K a}
    {b : Δ[n] ⟶ Q}
    (sq : CommSq f (SSet.horn n i).ι (diagramUnderProjection Q K a) b) :
    pushout.inl (simplicialJoinRightInclusion K Λ[n, i])
        (SSet.horn n i).ι ≫
      diagramUnderProjectionLiftingCornerTop Q K a sq =
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv
            (emptyAugmentation.{u}.obj K)
            (emptyAugmentation.{u}.obj Q) (Λ[n, i] : SSet.{u})
            (emptyAugmentation.{u}.map a)) f).1 := by
  apply pushout.inl_desc

@[reassoc (attr := simp)]
theorem diagramUnderProjectionLiftingCornerTop_inr
    (Q K : SSet.{u}) (a : K ⟶ Q) {n : ℕ} {i : Fin (n + 1)}
    {f : (Λ[n, i] : SSet.{u}) ⟶ diagramUnderSlice Q K a}
    {b : Δ[n] ⟶ Q}
    (sq : CommSq f (SSet.horn n i).ι (diagramUnderProjection Q K a) b) :
    pushout.inr (simplicialJoinRightInclusion K Λ[n, i])
        (SSet.horn n i).ι ≫
      diagramUnderProjectionLiftingCornerTop Q K a sq = b := by
  apply pushout.inr_desc

/-- The join corner controlling horn lifts for a diagram-under projection. -/
noncomputable def diagramUnderProjectionHornCornerMap
    (K : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) :
    pushout (simplicialJoinRightInclusion K Λ[n, i])
        (SSet.horn n i).ι ⟶ simplicialJoin K Δ[n] :=
  pushout.desc
    (simplicialJoinMap (𝟙 K) (SSet.horn n i).ι)
    (simplicialJoinRightInclusion K Δ[n]) (by
      simpa using
        (simplicialJoinRightInclusion_naturality_right
          (X := K) (SSet.horn n i).ι).symm)

@[reassoc (attr := simp)]
theorem diagramUnderProjectionHornCornerMap_inl
    (K : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) :
    pushout.inl (simplicialJoinRightInclusion K Λ[n, i])
        (SSet.horn n i).ι ≫ diagramUnderProjectionHornCornerMap K n i =
      simplicialJoinMap (𝟙 K) (SSet.horn n i).ι := by
  apply pushout.inl_desc

@[reassoc (attr := simp)]
theorem diagramUnderProjectionHornCornerMap_inr
    (K : SSet.{u}) (n : ℕ) (i : Fin (n + 1)) :
    pushout.inr (simplicialJoinRightInclusion K Λ[n, i])
        (SSet.horn n i).ι ≫ diagramUnderProjectionHornCornerMap K n i =
      simplicialJoinRightInclusion K Δ[n] := by
  apply pushout.inr_desc

/--
A join-corner extension for a diagram-under projection square determines a diagram-slice lift.
-/
theorem diagramUnderProjectionLiftOfCornerExtension
    (Q K : SSet.{u}) (a : K ⟶ Q) {n : ℕ} {i : Fin (n + 1)}
    {f : (Λ[n, i] : SSet.{u}) ⟶ diagramUnderSlice Q K a}
    {b : Δ[n] ⟶ Q}
    (sq : CommSq f (SSet.horn n i).ι (diagramUnderProjection Q K a) b)
    (g : simplicialJoin K Δ[n] ⟶ Q)
    (hg : diagramUnderProjectionLiftingCornerTop Q K a sq =
      diagramUnderProjectionHornCornerMap K n i ≫ g) : sq.HasLift := by
  let F := emptyAugmentation.{u}.obj K
  let G := emptyAugmentation.{u}.obj Q
  let aMap := emptyAugmentation.{u}.map a
  let φ := (relativeDaySliceOverMapFixedBaseEquiv F G
    (Λ[n, i] : SSet.{u}) aMap) f
  let τ := augmentedJoinMapOfUnderlying K Δ[n] Q g
  have hleft : simplicialJoinMap (𝟙 K)
      (SSet.horn n i).ι ≫ g = forgetAugmentation.map φ.1 := by
    calc
      _ = pushout.inl (simplicialJoinRightInclusion K Λ[n, i])
          (SSet.horn n i).ι ≫
            diagramUnderProjectionHornCornerMap K n i ≫ g :=
        (diagramUnderProjectionHornCornerMap_inl_assoc K n i g).symm
      _ = pushout.inl (simplicialJoinRightInclusion K Λ[n, i])
          (SSet.horn n i).ι ≫
            diagramUnderProjectionLiftingCornerTop Q K a sq := by rw [hg]
      _ = _ := diagramUnderProjectionLiftingCornerTop_inl Q K a sq
  letI := augmentedDayConvolution F (emptyAugmentation.obj Δ[n])
  letI := augmentedDayConvolution F
    (emptyAugmentation.obj (Λ[n, i] : SSet.{u}))
  have hτ : (augmentedDayTensorLeft F).map
        (emptyAugmentation.map (SSet.horn n i).ι) ≫ τ = φ.1 := by
    apply augmentedMapToEmptyAugmentation_ext
    rw [Functor.map_comp]
    change forgetAugmentation.map ((augmentedDayTensorLeft F).map
      (emptyAugmentation.map (SSet.horn n i).ι)) ≫
        forgetAugmentation.map (augmentedJoinMapOfUnderlying K Δ[n] Q g) = _
    have hforgetτ := forgetAugmentation_augmentedJoinMapOfUnderlying
      K Δ[n] Q g
    have hT : forgetAugmentation.map ((augmentedDayTensorLeft F).map
        (emptyAugmentation.map (SSet.horn n i).ι)) =
        simplicialJoinMap (𝟙 K) (SSet.horn n i).ι := by
      unfold F simplicialJoinMap augmentedDayTensorLeft
      rw [emptyAugmentation.map_id]
      rfl
    exact (congrArg (fun k ↦ forgetAugmentation.map
      ((augmentedDayTensorLeft F).map
        (emptyAugmentation.map (SSet.horn n i).ι)) ≫ k) hforgetτ).trans
      ((congrArg (fun k ↦ k ≫ g) hT).trans hleft)
  let Φ := fixedBaseDayConvolutionMapOfRestriction F G aMap
    (SSet.horn n i).ι φ τ hτ
  let l := (relativeDaySliceOverMapFixedBaseEquiv F G Δ[n] aMap).symm Φ
  apply CommSq.HasLift.mk'
  refine { l := l, fac_left := ?_, fac_right := ?_ }
  · apply (relativeDaySliceOverMapFixedBaseEquiv F G
      (Λ[n, i] : SSet.{u}) aMap).injective
    apply Subtype.ext
    have hpre := relativeDaySliceOverMapFixedBaseEquiv_precomp_fst
      F G aMap (SSet.horn n i).ι l
    have hl : (relativeDaySliceOverMapFixedBaseEquiv F G Δ[n] aMap) l = Φ :=
      Equiv.apply_symm_apply _ Φ
    have hm := congrArg (fun k ↦ (augmentedDayTensorLeft F).map
      (emptyAugmentation.map (SSet.horn n i).ι) ≫ k.1) hl
    have hΦ : (augmentedDayTensorLeft F).map
        (emptyAugmentation.map (SSet.horn n i).ι) ≫ Φ.1 = φ.1 := by
      dsimp only [Φ, fixedBaseDayConvolutionMapOfRestriction]
      exact hτ
    exact hpre.trans (hm.trans hΦ)
  · rw [diagramUnderProjection_comp_eq_fixedBaseCone]
    have hl : (relativeDaySliceOverMapFixedBaseEquiv F G Δ[n] aMap) l = Φ :=
      Equiv.apply_symm_apply _ Φ
    rw [hl]
    have hright : simplicialJoinRightInclusion K Δ[n] ≫ g = b := by
      calc
        _ = pushout.inr (simplicialJoinRightInclusion K Λ[n, i])
            (SSet.horn n i).ι ≫
              diagramUnderProjectionHornCornerMap K n i ≫ g :=
          (diagramUnderProjectionHornCornerMap_inr_assoc K n i g).symm
        _ = pushout.inr (simplicialJoinRightInclusion K Λ[n, i])
            (SSet.horn n i).ι ≫
              diagramUnderProjectionLiftingCornerTop Q K a sq := by rw [hg]
        _ = b := diagramUnderProjectionLiftingCornerTop_inr Q K a sq
    dsimp only [Φ, fixedBaseDayConvolutionMapOfRestriction]
    rw [forgetAugmentation_augmentedJoinMapOfUnderlying]
    exact hright

/-- Inner anodyneness of a diagram-projection horn corner supplies its horn lift. -/
theorem diagramUnderProjection_hasLiftingProperty_of_corner
    (Q K : SSet.{u}) (a : K ⟶ Q) [SSet.Quasicategory Q]
    (n : ℕ) (i : Fin (n + 1))
    (hcorner : SSet.innerAnodyneExtensions
      (diagramUnderProjectionHornCornerMap K n i)) :
    HasLiftingProperty (SSet.horn n i).ι
      (diagramUnderProjection Q K a) := by
  refine ⟨fun {f b} sq ↦ ?_⟩
  let t : IsTerminal (⊤_ SSet.{u}) := Limits.terminalIsTerminal
  have hq : SSet.InnerFibration (t.from Q) :=
    (SSet.quasicategory_iff_of_isTerminal (t.from Q) t).mp inferInstance
  letI : HasLiftingProperty (diagramUnderProjectionHornCornerMap K n i)
      (t.from Q) := hcorner _ hq.mem
  let csq : CommSq (diagramUnderProjectionLiftingCornerTop Q K a sq)
      (diagramUnderProjectionHornCornerMap K n i) (t.from Q)
      (t.from (simplicialJoin K Δ[n])) := ⟨t.hom_ext _ _⟩
  exact diagramUnderProjectionLiftOfCornerExtension
    Q K a sq csq.lift csq.fac_left.symm

/-- Inner-anodyne join corners imply that the diagram-under projection is a left fibration. -/
theorem diagramUnderProjection_leftFibration_of_innerAnodyne_corners
    (Q K : SSet.{u}) (a : K ⟶ Q) [SSet.Quasicategory Q]
    (hcorners : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) →
        SSet.innerAnodyneExtensions
          (diagramUnderProjectionHornCornerMap K (s + 1) i)) :
    LeftFibration (diagramUnderProjection Q K a) := by
  refine ⟨?_⟩
  intro A B j hj
  cases hj with
  | @intro s i hi =>
      exact diagramUnderProjection_hasLiftingProperty_of_corner
        Q K a (s + 1) i (hcorners s i hi)

private lemma projection_innerAnodyne_homOfLE_transport_target
    {X : SSet.{u}} {A B C : X.Subcomplex} (e : B = C) (h : A ≤ B)
    (hh : SSet.innerAnodyneExtensions (SSet.Subcomplex.homOfLE h)) :
    SSet.innerAnodyneExtensions (SSet.Subcomplex.homOfLE (e ▸ h)) := by
  subst C
  exact hh

/--
A paired join cell attaches along an inner horn whenever its actual distinguished index is positive.
-/
lemma joinSigmaOneHornRangeToFace_innerAnodyne_of_distinguished_pos
    (m n : ℕ) (T : Finset (Fin (m + 1))) (i : Fin (n + 1))
    (hpos : 0 < T.card + i.val) (hn : i < Fin.last n) :
    SSet.innerAnodyneExtensions (joinSigmaOneHornRangeToFace.{u} m n T i) := by
  apply (SSet.innerAnodyneExtensions.arrow_mk_iso_iff
    (joinSigmaOneHornArrowIso m n T i)).1
  exact SSet.innerAnodyneExtensions.horn_ι
    (Fin.mk_lt_mk.mpr hpos)
    (joinSigmaOneDistinguishedIndex_lt_last T i hn)

/--
The same positive-index attachment, with the target written as the generated simplex subcomplex.
-/
lemma joinSigmaOneHornRangeToOfSimplex_innerAnodyne_of_distinguished_pos
    (m n : ℕ) (T : Finset (Fin (m + 1))) (i : Fin (n + 1))
    (hpos : 0 < T.card + i.val) (hn : i < Fin.last n) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE
        (joinSigmaOneHornRange_le_face.{u} m n T i)) := by
  let F := SSet.stdSimplex.face.{u} (joinSigmaOneVertices m n T)
  let G := SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex.{u} m n T)
  have hFG : F = G := joinSigmaOneFace_eq_ofSimplex.{u} m n T
  have hF : joinSigmaOneHornRange m n T i ≤ F := by
    dsimp [F]
    rw [joinSigmaOneFace_eq_ofSimplex]
    exact joinSigmaOneHornRange_le_face.{u} m n T i
  have hh : SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE hF) :=
    joinSigmaOneHornRangeToFace_innerAnodyne_of_distinguished_pos
      m n T i hpos hn
  exact projection_innerAnodyne_homOfLE_transport_target hFG hF hh

/--
A positive-cardinality paired cell attaches inner anodynely even at right vertex zero.
-/
lemma projection_adjoinJoinCellList_cons_innerAnodyne
    (m n r : ℕ) (i : Fin (n + 2)) (T : Finset (Fin (m + 1)))
    (ts : List (Finset (Fin (m + 1))))
    (hT : T.card = r + 1) (hcards : ∀ U ∈ ts, U.card = r + 1)
    (hnot : T ∉ ts) (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE (le_sup_left :
        adjoinJoinCellList m n
            (representableJoinHornStage m (n + 1) i r) ts ≤
          adjoinJoinCellList m n
            (representableJoinHornStage m (n + 1) i r) (T :: ts))) := by
  let sq : SSet.Subcomplex.BicartSq
      (joinSigmaOneHornRange m (n + 1) T i)
      (adjoinJoinCellList m n
        (representableJoinHornStage m (n + 1) i r) ts)
      (SSet.Subcomplex.ofSimplex (joinSigmaOneSimplex m (n + 1) T))
      (adjoinJoinCellList m n
        (representableJoinHornStage m (n + 1) i r) (T :: ts)) := {
    sup_eq := rfl
    inf_eq := adjoinJoinCellList_inf_newCell_eq_hornRange
      m n r i T ts hT hcards hnot }
  have hf : SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE sq.le₁₃) := by
    apply joinSigmaOneHornRangeToOfSimplex_innerAnodyne_of_distinguished_pos
    · rw [hT]
      omega
    · exact hn
  rw [SSet.innerAnodyneExtensions_eq_llp_rlp] at hf ⊢
  intro E B p hp
  letI : HasLiftingProperty (SSet.Subcomplex.homOfLE sq.le₁₃) p :=
    hf p hp
  exact sq.isPushout.hasLiftingProperty p

/--
Finite positive-cardinality paired cells attach inner anodynely at every right-horn index.
-/
lemma projection_adjoinJoinCellList_innerAnodyne
    (m n r : ℕ) (i : Fin (n + 2))
    (ts : List (Finset (Fin (m + 1)))) (hnd : ts.Nodup)
    (hcards : ∀ T ∈ ts, T.card = r + 1)
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE (le_adjoinJoinCellList m n
        (representableJoinHornStage m (n + 1) i r) ts)) := by
  induction ts with
  | nil =>
      simpa only [adjoinJoinCellList, SSet.Subcomplex.homOfLE_refl] using
        SSet.innerAnodyneExtensions.id_mem
          (representableJoinHornStage m (n + 1) i r : SSet)
  | cons T ts ih =>
      have hndTail : ts.Nodup := hnd.tail
      have hcardsTail : ∀ U ∈ ts, U.card = r + 1 := by
        intro U hU
        exact hcards U (by simp [hU])
      have hTail := ih hndTail hcardsTail
      have hStep := projection_adjoinJoinCellList_cons_innerAnodyne
        m n r i T ts (hcards T (by simp)) hcardsTail
          (List.nodup_cons.mp hnd).1 hn
      have hComp := SSet.innerAnodyneExtensions.comp_mem _ _ hTail hStep
      rw [SSet.Subcomplex.homOfLE_comp] at hComp
      change SSet.innerAnodyneExtensions
        (SSet.Subcomplex.homOfLE
          ((le_adjoinJoinCellList m n
            (representableJoinHornStage m (n + 1) i r) ts).trans le_sup_left))
      exact hComp

/--
Each post-pure-right filtration successor is inner anodyne at a nonfinal right vertex.
-/
lemma representableJoinHornStage_succ_innerAnodyne_of_nonfinal
    (m n r : ℕ) (i : Fin (n + 2))
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE
        (representableJoinHornStage_monotone m (n + 1) i
          (by omega : r ≤ r + 1))) := by
  have hlist := projection_adjoinJoinCellList_innerAnodyne m n r i
    (joinCellsAtCard m r) (joinCellsAtCard_nodup m r)
    (fun T hT ↦ (mem_joinCellsAtCard_iff m r T).1 hT) hn
  exact projection_innerAnodyne_homOfLE_transport_target
    (adjoinJoinCellsAtCard_eq_nextStage m n r i)
    (le_adjoinJoinCellList m n
      (representableJoinHornStage m (n + 1) i r)
      (joinCellsAtCard m r)) hlist

/--
The pure-right stage grows to every later representable-join stage by inner-anodyne attachments.
-/
lemma representableJoinHornStage_zero_to_stage_innerAnodyne
    (m n r : ℕ) (i : Fin (n + 2))
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE
        (representableJoinHornStage_monotone m (n + 1) i
          (Nat.zero_le r))) := by
  induction r with
  | zero =>
      simpa only [SSet.Subcomplex.homOfLE_refl] using
        SSet.innerAnodyneExtensions.id_mem
          (representableJoinHornStage m (n + 1) i 0 : SSet)
  | succ r ih =>
      have hs := representableJoinHornStage_succ_innerAnodyne_of_nonfinal
        m n r i hn
      have hc := SSet.innerAnodyneExtensions.comp_mem _ _ ih hs
      rw [SSet.Subcomplex.homOfLE_comp] at hc
      exact hc

/--
The joined horn with its pure right factor is inner anodyne in the full join simplex.
-/
lemma representableJoinHornStage_zero_to_top_innerAnodyne
    (m n : ℕ) (i : Fin (n + 2))
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE
        (show representableJoinHornStage m (n + 1) i 0 ≤ ⊤ from le_top)) := by
  have hstage := representableJoinHornStage_zero_to_stage_innerAnodyne
    m n (m + 1) i hn
  exact projection_innerAnodyne_homOfLE_transport_target
    (representableJoinHornStage_eq_top m (n + 1) i)
    (representableJoinHornStage_monotone m (n + 1) i
      (Nat.zero_le (m + 1))) hstage

lemma representableJoinRightInclusion_range_eq_emptyCell
    (m n : ℕ) :
    SSet.Subcomplex.range
        (simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Δ[n + 1] ≫
          (simplicialJoinStdSimplexIsoNat m (n + 1)).hom) =
      SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex m (n + 1)
          (∅ : Finset (Fin (m + 1)))) := by
  rw [simplicialJoinRightInclusion_stdSimplex]
  rw [← joinSigmaOneFace_eq_ofSimplex]
  rw [SSet.stdSimplex.face_eq_ofSimplex
    (joinSigmaOneVertices m (n + 1) (∅ : Finset (Fin (m + 1))))
    (n + 1)
    ((joinSigmaOneVertices m (n + 1)
      (∅ : Finset (Fin (m + 1)))).orderIsoOfFin (by
        rw [card_joinSigmaOneVertices]
        simp))]
  rw [SSet.Subcomplex.range_eq_ofSimplex]
  congr 1
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  ext j
  simp only [SSet.stdSimplex.objEquiv_toOrderHom_apply,
    Equiv.apply_symm_apply, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.comp_coe, OrderHom.Subtype.val_coe,
    OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding,
    Function.comp_apply, Finset.coe_orderIsoOfFin_apply]
  let e : Fin (n + 2) ↪o Fin (m + (n + 1) + 2) :=
    { toFun := fun k => ⟨m + 1 + k.val, by omega⟩
      inj' := by
        intro a b h
        apply Fin.ext
        simpa using congrArg Fin.val h
      map_rel_iff' := by
        intro a b
        change (m + 1 + a.val ≤ m + 1 + b.val) ↔ a.val ≤ b.val
        omega }
  have he : e =
      (joinSigmaOneVertices m (n + 1)
        (∅ : Finset (Fin (m + 1)))).orderEmbOfFin (by
          rw [card_joinSigmaOneVertices]
          simp) := by
    apply Finset.orderEmbOfFin_unique'
    intro a
    simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices, e]
  exact congrArg Fin.val (congrArg (fun f ↦ f j) he)

lemma normalizedEmptyJoinAmbientIso_hom_comp_faceIso_ι_general
    (m r : ℕ) :
    (normalizedEmptyJoinAmbientIso.{u} r).hom ≫
        (joinSigmaOneFaceIso m (r + 1)
          (∅ : Finset (Fin (m + 1)))).hom ≫
        (SSet.stdSimplex.face
          (joinSigmaOneVertices m (r + 1)
            (∅ : Finset (Fin (m + 1))))).ι =
      SSet.stdSimplex.map (standardJoinRightOperator m (r + 1)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map]
  apply ULift.ext
  apply SimplexCategory.Hom.ext
  ext j
  simp only [joinSigmaOneVertices, joinFirstVertices, Finset.map_empty,
    joinSecondVertices, Finset.card_empty, joinSigmaOneFaceIso,
    SSet.stdSimplex.isoOfRepresentableBy,
    SSet.stdSimplex.faceRepresentableBy, op_unop, NatTrans.comp_app,
    NatIso.ofComponents_hom_app,
    SSet.stdSimplex.objEquiv_toOrderHom_apply, Subfunctor.ι_app,
    comp_apply, TypeCat.hom_ofHom, normalizedEmptyJoinAmbientIso,
    Functor.mapIso_hom, eqToIso.hom, SSet.yonedaEquiv_map,
    Equiv.toIso_hom_hom_apply, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.coe_fn_mk,
    SimplexCategory.eqToHom_toOrderHom, TypeCat.Fun.coe_mk,
    standardJoinRightOperator, SimplexCategory.mkHom]
  let e : Fin (r + 2) ↪o Fin (m + (r + 1) + 2) :=
    { toFun := fun k => ⟨m + 1 + k.val, by omega⟩
      inj' := by
        intro a b h
        apply Fin.ext
        simpa using congrArg Fin.val h
      map_rel_iff' := by
        intro a b
        change (m + 1 + a.val ≤ m + 1 + b.val) ↔ a.val ≤ b.val
        omega }
  have he : e =
      (joinSigmaOneVertices m (r + 1)
        (∅ : Finset (Fin (m + 1)))).orderEmbOfFin (by
          rw [card_joinSigmaOneVertices]
          simp) := by
    apply Finset.orderEmbOfFin_unique'
    intro a
    simp [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices, e]
  exact congrArg Fin.val (congrArg (fun f ↦ f j) he.symm)

noncomputable def generalEmptyJoinHornIsoRange
    (m r : ℕ) (i : Fin (r + 2)) :
    (Λ[r + 1, i] : SSet.{u}) ≅
      (joinSigmaOneHornRange m (r + 1)
        (∅ : Finset (Fin (m + 1))) i : SSet.{u}) := by
  let iRaw := Fin.cast
    (congrArg (fun n => n + 1) (Nat.zero_add (r + 1)).symm) i
  let iJoin := joinSigmaOneDistinguishedIndex (r + 1)
    (∅ : Finset (Fin (m + 1))) i
  have hidx : iRaw = iJoin := by
    apply Fin.ext
    simp [iRaw, iJoin, joinSigmaOneDistinguishedIndex]
  exact normalizedEmptyJoinHornIso r i ≪≫
    eqToIso (congrArg (fun j =>
      (SSet.horn (0 + (r + 1)) j : SSet.{u})) hidx) ≪≫
    joinSigmaOneHornIsoRange m (r + 1)
      (∅ : Finset (Fin (m + 1))) i

set_option maxHeartbeats 800000 in
-- This finite combinatorial normalization exceeds the default elaboration budget.
lemma generalEmptyJoinHornIsoRange_hom_ι
    (m r : ℕ) (i : Fin (r + 2)) :
    (generalEmptyJoinHornIsoRange.{u} m r i).hom ≫
        (joinSigmaOneHornRange m (r + 1)
          (∅ : Finset (Fin (m + 1))) i).ι =
      (SSet.horn (r + 1) i).ι ≫
        SSet.stdSimplex.map (standardJoinRightOperator m (r + 1)) := by
  unfold generalEmptyJoinHornIsoRange
  change (normalizedEmptyJoinHornIso r i).hom ≫ _ ≫
    (joinSigmaOneHornIsoRange m (r + 1)
      (∅ : Finset (Fin (m + 1))) i).hom ≫
    (joinSigmaOneHornRange m (r + 1)
      (∅ : Finset (Fin (m + 1))) i).ι = _
  have hj : (joinSigmaOneHornIsoRange m (r + 1)
        (∅ : Finset (Fin (m + 1))) i).hom ≫
      (joinSigmaOneHornRange m (r + 1)
        (∅ : Finset (Fin (m + 1))) i).ι =
      joinSigmaOneHornMap m (r + 1)
        (∅ : Finset (Fin (m + 1))) i := by
    change SSet.Subcomplex.toRange
        (joinSigmaOneHornMap m (r + 1)
          (∅ : Finset (Fin (m + 1))) i) ≫
      (SSet.Subcomplex.range
        (joinSigmaOneHornMap m (r + 1)
          (∅ : Finset (Fin (m + 1))) i)).ι = _
    exact SSet.Subcomplex.toRange_ι _
  let iRaw := Fin.cast
    (congrArg (fun n => n + 1) (Nat.zero_add (r + 1)).symm) i
  let iJoin := joinSigmaOneDistinguishedIndex (r + 1)
    (∅ : Finset (Fin (m + 1))) i
  have hidx : iRaw = iJoin := by
    apply Fin.ext
    simp [iRaw, iJoin, joinSigmaOneDistinguishedIndex]
  have hi := eqToIso_horn_index_hom_ι (0 + (r + 1)) hidx
  have hn := normalizedEmptyJoinHornIso_hom_ι r i
  have hpref : (normalizedEmptyJoinHornIso r i).hom ≫
      (eqToIso (congrArg (fun j =>
          (SSet.horn (0 + (r + 1)) j : SSet.{u})) hidx)).hom ≫
      (SSet.horn (0 + (r + 1)) iJoin).ι =
      (SSet.horn (r + 1) i).ι ≫
        (normalizedEmptyJoinAmbientIso r).hom := by
    exact (congrArg (fun k =>
      (normalizedEmptyJoinHornIso r i).hom ≫ k) hi).trans hn
  have hpref' : ((normalizedEmptyJoinHornIso r i).hom ≫
      (eqToIso (congrArg (fun j =>
        (SSet.horn (0 + (r + 1)) j : SSet.{u})) hidx)).hom) ≫
      (SSet.horn (0 + (r + 1)) iJoin).ι =
      (SSet.horn (r + 1) i).ι ≫
        (normalizedEmptyJoinAmbientIso r).hom := by
    rw [Category.assoc]
    exact hpref
  dsimp [iJoin] at hpref'
  calc
    _ = (normalizedEmptyJoinHornIso r i).hom ≫ _ ≫
        joinSigmaOneHornMap m (r + 1)
          (∅ : Finset (Fin (m + 1))) i :=
      congrArg (fun k => (normalizedEmptyJoinHornIso r i).hom ≫ _ ≫ k) hj
    _ = _ := by
      unfold joinSigmaOneHornMap
      simp only [Finset.card_empty]
      exact (congrArg (fun k => k ≫
        (joinSigmaOneFaceIso m (r + 1)
          (∅ : Finset (Fin (m + 1)))).hom ≫
        (SSet.stdSimplex.face
          (joinSigmaOneVertices m (r + 1)
            (∅ : Finset (Fin (m + 1))))).ι) hpref').trans (congrArg
          (fun k => (SSet.horn (r + 1) i).ι ≫ k)
          (normalizedEmptyJoinAmbientIso_hom_comp_faceIso_ι_general m r))

lemma representableJoinRightHornRange_eq_emptyHornRange
    (m r : ℕ) (i : Fin (r + 2)) :
    SSet.Subcomplex.range
        ((SSet.horn (r + 1) i).ι ≫
          simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Δ[r + 1] ≫
          (simplicialJoinStdSimplexIsoNat m (r + 1)).hom) =
      joinSigmaOneHornRange m (r + 1)
        (∅ : Finset (Fin (m + 1))) i := by
  rw [simplicialJoinRightInclusion_stdSimplex]
  simpa only [Subfunctor.range_ι] using
    (subcomplex_range_eq_of_precomp_iso
      (generalEmptyJoinHornIsoRange m r i).hom
      (joinSigmaOneHornRange m (r + 1)
        (∅ : Finset (Fin (m + 1))) i).ι
      ((SSet.horn (r + 1) i).ι ≫
        SSet.stdSimplex.map (standardJoinRightOperator m (r + 1)))
      (generalEmptyJoinHornIsoRange_hom_ι m r i)).symm

noncomputable def representableProjectionHornCornerStdMap
    (m r : ℕ) (i : Fin (r + 2)) :
    pushout
        (simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Λ[r + 1, i])
        (SSet.horn (r + 1) i).ι ⟶ Δ[m + (r + 1) + 1] :=
  diagramUnderProjectionHornCornerMap (Δ[m] : SSet.{u}) (r + 1) i ≫
    (simplicialJoinStdSimplexIsoNat m (r + 1)).hom

@[reassoc]
lemma representableProjectionHornCornerStdMap_inl
    (m r : ℕ) (i : Fin (r + 2)) :
    pushout.inl
        (simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Λ[r + 1, i])
        (SSet.horn (r + 1) i).ι ≫
      representableProjectionHornCornerStdMap m r i =
        representableJoinHornMap m (r + 1) i := by
  unfold representableProjectionHornCornerStdMap representableJoinHornMap
  exact diagramUnderProjectionHornCornerMap_inl_assoc
    (Δ[m] : SSet.{u}) (r + 1) i
      (simplicialJoinStdSimplexIsoNat m (r + 1)).hom

@[reassoc]
lemma representableProjectionHornCornerStdMap_inr
    (m r : ℕ) (i : Fin (r + 2)) :
    pushout.inr
        (simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Λ[r + 1, i])
        (SSet.horn (r + 1) i).ι ≫
      representableProjectionHornCornerStdMap m r i =
        simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Δ[r + 1] ≫
          (simplicialJoinStdSimplexIsoNat m (r + 1)).hom := by
  unfold representableProjectionHornCornerStdMap
  exact diagramUnderProjectionHornCornerMap_inr_assoc
    (Δ[m] : SSet.{u}) (r + 1) i
      (simplicialJoinStdSimplexIsoNat m (r + 1)).hom

lemma representableProjectionHornCornerStdMap_range
    (m r : ℕ) (i : Fin (r + 2)) :
    SSet.Subcomplex.range
        (representableProjectionHornCornerStdMap.{u} m r i) =
      representableJoinHornInitial m (r + 1) i ⊔
        SSet.Subcomplex.ofSimplex
          (joinSigmaOneSimplex m (r + 1)
            (∅ : Finset (Fin (m + 1)))) := by
  rw [range_isPushout_map_eq_sup
    (IsPushout.of_hasPushout
      (simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Λ[r + 1, i])
      (SSet.horn (r + 1) i).ι)
    (representableProjectionHornCornerStdMap m r i)]
  rw [representableProjectionHornCornerStdMap_inl,
    representableProjectionHornCornerStdMap_inr]
  exact congrArg₂ (· ⊔ ·) rfl
    (representableJoinRightInclusion_range_eq_emptyCell m r)

lemma representableJoinRightStdMap_mono (m r : ℕ) :
    Mono (simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Δ[r + 1] ≫
      (simplicialJoinStdSimplexIsoNat m (r + 1)).hom) := by
  rw [simplicialJoinRightInclusion_stdSimplex]
  let e := normalizedEmptyJoinAmbientIso.{u} r ≪≫
    joinSigmaOneFaceIso m (r + 1) (∅ : Finset (Fin (m + 1)))
  have heq : e.hom ≫
      (SSet.stdSimplex.face
        (joinSigmaOneVertices m (r + 1)
          (∅ : Finset (Fin (m + 1))))).ι =
      SSet.stdSimplex.map (standardJoinRightOperator m (r + 1)) := by
    exact normalizedEmptyJoinAmbientIso_hom_comp_faceIso_ι_general m r
  have hm : Mono (e.hom ≫
      (SSet.stdSimplex.face
        (joinSigmaOneVertices m (r + 1)
          (∅ : Finset (Fin (m + 1))))).ι) := by
    infer_instance
  exact heq ▸ hm

lemma representableJoinHornMap_succ_mono
    (m r : ℕ) (i : Fin (r + 2)) :
    Mono (representableJoinHornMap.{u} m (r + 1) i) := by
  cases r with
  | zero =>
      fin_cases i
      · exact representableJoinHornMap_one_zero_mono m
      · exact representableJoinHornMap_one_one_mono m
  | succ r =>
      exact representableJoinHornMap_mono m r i

set_option backward.isDefEq.respectTransparency false in
noncomputable instance representableProjectionHornCornerStdMap_mono
    (m r : ℕ) (i : Fin (r + 2)) :
    Mono (representableProjectionHornCornerStdMap.{u} m r i) := by
  let a := simplicialJoinRightInclusion
    (Δ[m] : SSet.{u}) Λ[r + 1, i]
  let b := (SSet.horn (r + 1) i).ι
  let h := representableJoinHornMap.{u} m (r + 1) i
  let k := simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Δ[r + 1] ≫
    (simplicialJoinStdSimplexIsoNat m (r + 1)).hom
  have w : a ≫ h = b ≫ k := by
    change a ≫ representableJoinHornMap m (r + 1) i =
      b ≫ (simplicialJoinRightInclusion (Δ[m] : SSet.{u}) Δ[r + 1] ≫
        (simplicialJoinStdSimplexIsoNat m (r + 1)).hom)
    rw [← representableProjectionHornCornerStdMap_inl,
      ← representableProjectionHornCornerStdMap_inr]
    rw [← Category.assoc, ← Category.assoc, pushout.condition]
  haveI : Mono b := by
    dsimp [b]
    infer_instance
  haveI : Mono h := by
    dsimp [h]
    exact representableJoinHornMap_succ_mono m r i
  haveI : Mono k := by
    dsimp [k]
    exact representableJoinRightStdMap_mono m r
  haveI : Mono (a ≫ h) := by
    have hbk : Mono (b ≫ k) := mono_comp _ _
    exact w.symm ▸ hbk
  haveI : Mono a := by
    apply mono_of_mono_fac (h := a ≫ h)
    rfl
  have hoverlap : SSet.Subcomplex.range (a ≫ h) =
      joinSigmaOneHornRange m (r + 1)
        (∅ : Finset (Fin (m + 1))) i := by
    rw [w]
    exact representableJoinRightHornRange_eq_emptyHornRange m r i
  have hr : SSet.Subcomplex.range (a ≫ h) =
      SSet.Subcomplex.range h ⊓ SSet.Subcomplex.range k := by
    rw [hoverlap]
    change joinSigmaOneHornRange m (r + 1)
        (∅ : Finset (Fin (m + 1))) i =
      representableJoinHornInitial m (r + 1) i ⊓
        SSet.Subcomplex.range k
    rw [representableJoinRightInclusion_range_eq_emptyCell]
    exact (initial_inf_emptyJoinCell_eq_hornRange m r i).symm
  have hp : Mono (pushout.desc h k w) :=
    mono_of_pushout_range_inter w hr
  have heq : representableProjectionHornCornerStdMap.{u} m r i =
      pushout.desc h k w := by
    apply pushout.hom_ext
    · rw [representableProjectionHornCornerStdMap_inl,
        pushout.inl_desc]
    · rw [representableProjectionHornCornerStdMap_inr,
        pushout.inr_desc]
  exact heq.symm ▸ hp

/-- The pure-right stage includes inner anodynely into the representable join simplex. -/
lemma representableJoinHornStage_zero_ι_innerAnodyne
    (m r : ℕ) (i : Fin (r + 2))
    (hi : i < Fin.last (r + 1)) :
    SSet.innerAnodyneExtensions
      (representableJoinHornStage.{u} m (r + 1) i 0).ι := by
  have htop := representableJoinHornStage_zero_to_top_innerAnodyne
    m r i hi
  have hcomp := SSet.innerAnodyneExtensions.comp_mem _ _ htop
    (SSet.innerAnodyneExtensions.of_isIso
      (SSet.Subcomplex.topIso (Δ[m + (r + 1) + 1] : SSet.{u})).hom)
  rw [SSet.Subcomplex.topIso_hom, SSet.Subcomplex.homOfLE_ι] at hcomp
  exact hcomp

/-- The standard-simplex projection corner is inner anodyne in standard coordinates. -/
lemma representableProjectionHornCornerStdMap_innerAnodyne
    (m r : ℕ) (i : Fin (r + 2))
    (hi : i < Fin.last (r + 1)) :
    SSet.innerAnodyneExtensions
      (representableProjectionHornCornerStdMap.{u} m r i) := by
  let f := representableProjectionHornCornerStdMap.{u} m r i
  have hRange : SSet.innerAnodyneExtensions
      (SSet.Subcomplex.range f).ι := by
    rw [representableProjectionHornCornerStdMap_range,
      ← representableJoinHornStage_zero_eq]
    exact representableJoinHornStage_zero_ι_innerAnodyne m r i hi
  have hToRange := SSet.innerAnodyneExtensions.of_isIso
    (SSet.Subcomplex.toRange f)
  have hcomp := SSet.innerAnodyneExtensions.comp_mem _ _ hToRange hRange
  change SSet.innerAnodyneExtensions
    (SSet.Subcomplex.toRange f ≫ (SSet.Subcomplex.range f).ι) at hcomp
  rw [SSet.Subcomplex.toRange_ι] at hcomp
  exact hcomp

/-- The standard-simplex projection corner is inner anodyne. -/
lemma representableProjectionHornCornerMap_innerAnodyne
    (m r : ℕ) (i : Fin (r + 2))
    (hi : i < Fin.last (r + 1)) :
    SSet.innerAnodyneExtensions
      (diagramUnderProjectionHornCornerMap
        (Δ[m] : SSet.{u}) (r + 1) i) := by
  have hstd := representableProjectionHornCornerStdMap_innerAnodyne
    m r i hi
  have hinv := SSet.innerAnodyneExtensions.of_isIso
    (simplicialJoinStdSimplexIsoNat m (r + 1)).inv
  have hcomp := SSet.innerAnodyneExtensions.comp_mem _ _ hstd hinv
  simpa [representableProjectionHornCornerStdMap, Category.assoc] using hcomp

lemma leftFace_image_leftJoinTargetIso_hom_eq_joinCell
    (m n : ℕ) (l : Fin (m + 2)) :
    (SSet.stdSimplex.face
      ({(Fin.castLE (by omega) l : Fin (m + (n + 1) + 3))}ᶜ)).image
        (leftJoinTargetIso.{u} m (n + 1)).hom =
      SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1)
          (Finset.univ.erase l)) := by
  rw [← joinSigmaOneFace_eq_ofSimplex]
  have hi : inv (leftJoinTargetIso.{u} m (n + 1)).inv =
      (leftJoinTargetIso m (n + 1)).hom := by simp
  rw [← hi, SSet.Subcomplex.image_inv]
  ext U x
  rcases U with ⟨⟨d⟩⟩
  change ((leftJoinTargetIso m (n + 1)).inv.app _ x ∈
      (SSet.stdSimplex.face _).obj _) ↔
    x ∈ (SSet.stdSimplex.face _).obj _
  rw [SSet.stdSimplex.mem_face_iff, SSet.stdSimplex.mem_face_iff]
  constructor
  · intro h k
    have hk := h k
    simp only [Finset.mem_compl, Finset.mem_singleton] at hk
    have hval : (((leftJoinTargetIso m (n + 1)).inv.app _ x) k).val =
        (x k).val := by
      change (SimplexCategory.Hom.toOrderHom
        (eqToHom (by
          apply SimplexCategory.ext
          simp
          omega) : SimplexCategory.mk ((m + 1) + (n + 1) + 1) ⟶
            SimplexCategory.mk (m + (n + 1) + 2)) (x k)).val = _
      simp
    have hne : (x k).val ≠ l.val := by
      intro heq
      apply hk
      apply Fin.ext
      rw [hval]
      exact heq
    simp only [joinSigmaOneVertices, joinFirstVertices, Finset.map_erase,
      Fin.castLEEmb_apply, joinSecondVertices, Finset.mem_union,
      Finset.mem_erase, ne_eq, Finset.mem_map, Finset.mem_univ,
      true_and, Function.Embedding.coeFn_mk]
    by_cases hleft : (x k).val < m + 2
    · left
      constructor
      · intro heq
        apply hne
        exact congrArg Fin.val heq
      · exact ⟨⟨(x k).val, hleft⟩, by apply Fin.ext; rfl⟩
    · right
      let j : Fin (n + 2) := ⟨(x k).val - (m + 2), by omega⟩
      exact ⟨j, by apply Fin.ext; dsimp [j]; omega⟩
  · intro h k
    simp only [Finset.mem_compl, Finset.mem_singleton]
    intro heq
    have hval : (((leftJoinTargetIso m (n + 1)).inv.app _ x) k).val =
        (x k).val := by
      change (SimplexCategory.Hom.toOrderHom
        (eqToHom (by
          apply SimplexCategory.ext
          simp
          omega) : SimplexCategory.mk ((m + 1) + (n + 1) + 1) ⟶
            SimplexCategory.mk (m + (n + 1) + 2)) (x k)).val = _
      simp
    have hxval : (x k).val = l.val := by
      have hv := congrArg Fin.val heq
      rw [hval] at hv
      simpa only [Fin.val_castLE] using hv
    have hxmem := h k
    simp only [joinSigmaOneVertices, joinFirstVertices, Finset.map_erase,
      Fin.castLEEmb_apply, joinSecondVertices, Finset.mem_union,
      Finset.mem_erase, ne_eq, Finset.mem_map, Finset.mem_univ,
      true_and, Function.Embedding.coeFn_mk] at hxmem
    rcases hxmem with hxmem | hxmem
    · exact hxmem.1 (by
        apply Fin.ext
        simpa only [Fin.val_castLE] using hxval)
    · obtain ⟨j, hj⟩ := hxmem
      have hjv := congrArg Fin.val hj
      change m + 2 + j.val = (x k).val at hjv
      have hl := l.isLt
      omega

lemma ordinaryJoinTransportedLeftLeg_range_eq_joinCell
    (m n : ℕ) (l : Fin (m + 2)) :
    SSet.Subcomplex.range
        (ordinaryJoinTransportedLeftLeg.{u} m (n + 1) l) =
      SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1)
          (Finset.univ.erase l)) := by
  rw [ordinaryJoinTransportedLeftLeg_range]
  exact leftFace_image_leftJoinTargetIso_hom_eq_joinCell m n l

def boundaryProjectionTargetRange (m n : ℕ) :
    (Δ[(m + 1) + (n + 1) + 1] : SSet.{u}).Subcomplex :=
  SSet.Subcomplex.range (joinBoundaryStandardMap (m + 1) (n + 1))

lemma joinSigmaOneCell_le_boundaryProjectionTargetRange
    (m n : ℕ) (T : Finset (Fin (m + 2)))
    (hT : T.card ≤ m + 1) :
    SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1) T) ≤
      boundaryProjectionTargetRange.{u} m n := by
  have hnsub : ¬ (Finset.univ : Finset (Fin (m + 2))) ⊆ T := by
    intro hsub
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  obtain ⟨l, _, hl⟩ := Finset.not_subset.mp hnsub
  rw [boundaryProjectionTargetRange,
    joinBoundaryStandardMap_range_eq_iSup_leftFaces]
  refine le_iSup_of_le l ?_
  rw [ordinaryJoinTransportedLeftLeg_range_eq_joinCell]
  rw [← joinSigmaOneFace_eq_ofSimplex,
    ← joinSigmaOneFace_eq_ofSimplex]
  apply (SSet.stdSimplex.face_le_face_iff _ _).mpr
  intro x hx
  simp only [joinSigmaOneVertices, joinFirstVertices, joinSecondVertices,
    Finset.mem_union, Finset.mem_map, Fin.castLEEmb_apply,
    Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
    Finset.map_erase, Finset.mem_erase, ne_eq] at hx ⊢
  rcases hx with hx | hx
  · left
    obtain ⟨t, ht, htx⟩ := hx
    constructor
    · intro hxl
      apply hl
      have htl : t = l := by
        apply Fin.ext
        have htxv := congrArg Fin.val htx
        have hxlv := congrArg Fin.val hxl
        simp only [Fin.val_castLE] at htxv hxlv
        omega
      simpa [htl] using ht
    · exact ⟨t, htx⟩
  · exact Or.inr hx

def boundaryProjectionHornStage
    (m n : ℕ) (i : Fin (n + 2)) (r : ℕ) :
    (Δ[(m + 1) + (n + 1) + 1] : SSet.{u}).Subcomplex :=
  representableJoinHornStage (m + 1) (n + 1) i r ⊓
    boundaryProjectionTargetRange m n

lemma boundaryProjectionHornStage_zero_eq
    (m n : ℕ) (i : Fin (n + 2)) :
    boundaryProjectionHornStage.{u} m n i 0 =
      (representableJoinHornInitial (m + 1) (n + 1) i ⊓
        boundaryProjectionTargetRange m n) ⊔
      SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1)
          (∅ : Finset (Fin (m + 2)))) := by
  rw [boundaryProjectionHornStage, representableJoinHornStage_zero_eq]
  let P := SSet.Subcomplex.ofSimplex
    (joinSigmaOneSimplex (m + 1) (n + 1)
      (∅ : Finset (Fin (m + 2))))
  have hP : P ≤ boundaryProjectionTargetRange.{u} m n := by
    apply joinSigmaOneCell_le_boundaryProjectionTargetRange
    simp
  ext U x
  change (_ ∨ _) ∧ _ ↔ (_ ∧ _) ∨ _
  constructor
  · rintro ⟨hH | hP', hB⟩
    · exact Or.inl ⟨hH, hB⟩
    · exact Or.inr hP'
  · rintro (hH | hP')
    · exact ⟨Or.inl hH.1, hH.2⟩
    · exact ⟨Or.inr hP', hP _ hP'⟩

lemma boundaryProjectionTargetRange_le_stage
    (m n : ℕ) (i : Fin (n + 2)) :
    boundaryProjectionTargetRange.{u} m n ≤
      representableJoinHornStage (m + 1) (n + 1) i (m + 1) := by
  rw [boundaryProjectionTargetRange,
    joinBoundaryStandardMap_range_eq_iSup_leftFaces]
  apply iSup_le
  intro l
  let T : Finset (Fin (m + 2)) := Finset.univ.erase l
  have hT : T.card ≤ m + 1 := by
    dsimp [T]
    simp
  rw [ordinaryJoinTransportedLeftLeg_range_eq_joinCell]
  exact joinSigmaOne_of_card_le_stage
    (m + 1) (n + 1) i (m + 1) T hT

lemma boundaryProjectionHornStage_eq_target
    (m n : ℕ) (i : Fin (n + 2)) :
    boundaryProjectionHornStage.{u} m n i (m + 1) =
      boundaryProjectionTargetRange m n := by
  rw [boundaryProjectionHornStage, inf_eq_right]
  exact boundaryProjectionTargetRange_le_stage m n i

lemma adjoinBoundaryProjectionCells_eq_inf
    (m n r : ℕ) (i : Fin (n + 2))
    (ts : List (Finset (Fin (m + 2))))
    (hcards : ∀ T ∈ ts, T.card = r + 1) (hr : r ≤ m) :
    adjoinJoinCellList.{u} (m + 1) n
        (boundaryProjectionHornStage.{u} m n i r) ts =
      adjoinJoinCellList.{u} (m + 1) n
          (representableJoinHornStage.{u} (m + 1) (n + 1) i r) ts ⊓
        boundaryProjectionTargetRange.{u} m n := by
  induction ts with
  | nil => rfl
  | cons T ts ih =>
      have hcardsTail : ∀ U ∈ ts, U.card = r + 1 := by
        intro U hU
        exact hcards U (by simp [hU])
      rw [adjoinJoinCellList, adjoinJoinCellList, ih hcardsTail]
      have hTcard := hcards T (by simp)
      have hTB : SSet.Subcomplex.ofSimplex
          (joinSigmaOneSimplex (m + 1) (n + 1) T) ≤
          boundaryProjectionTargetRange.{u} m n := by
        apply joinSigmaOneCell_le_boundaryProjectionTargetRange
        omega
      ext U x
      change ((_ ∧ _) ∨ _) ↔ ((_ ∨ _) ∧ _)
      constructor
      · rintro (hx | hx)
        · exact ⟨Or.inl hx.1, hx.2⟩
        · exact ⟨Or.inr hx, hTB _ hx⟩
      · rintro ⟨hx | hx, hB⟩
        · exact Or.inl ⟨hx, hB⟩
        · exact Or.inr hx

lemma adjoinBoundaryProjectionCells_inf_newCell_eq_hornRange
    (m n r : ℕ) (i : Fin (n + 2))
    (T : Finset (Fin (m + 2)))
    (ts : List (Finset (Fin (m + 2))))
    (hT : T.card = r + 1) (hcards : ∀ U ∈ ts, U.card = r + 1)
    (hnot : T ∉ ts) (hr : r ≤ m) :
    adjoinJoinCellList.{u} (m + 1) n
        (boundaryProjectionHornStage.{u} m n i r) ts ⊓
      SSet.Subcomplex.ofSimplex
          (joinSigmaOneSimplex (m + 1) (n + 1) T) =
        joinSigmaOneHornRange (m + 1) (n + 1) T i := by
  rw [adjoinBoundaryProjectionCells_eq_inf m n r i ts hcards hr]
  have hTB : SSet.Subcomplex.ofSimplex
      (joinSigmaOneSimplex (m + 1) (n + 1) T) ≤
      boundaryProjectionTargetRange.{u} m n := by
    apply joinSigmaOneCell_le_boundaryProjectionTargetRange
    omega
  have hBC : boundaryProjectionTargetRange.{u} m n ⊓
      SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1) T) =
      SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1) T) :=
    inf_eq_right.mpr hTB
  let A := adjoinJoinCellList.{u} (m + 1) n
    (representableJoinHornStage (m + 1) (n + 1) i r) ts
  calc
    (A ⊓ boundaryProjectionTargetRange m n) ⊓
        SSet.Subcomplex.ofSimplex
          (joinSigmaOneSimplex (m + 1) (n + 1) T) =
      A ⊓ (boundaryProjectionTargetRange m n ⊓
        SSet.Subcomplex.ofSimplex
          (joinSigmaOneSimplex (m + 1) (n + 1) T)) :=
        inf_assoc _ _ _
    _ = A ⊓ SSet.Subcomplex.ofSimplex
          (joinSigmaOneSimplex (m + 1) (n + 1) T) :=
      congrArg (fun D => A ⊓ D) hBC
    _ = _ := adjoinJoinCellList_inf_newCell_eq_hornRange
      (m + 1) n r i T ts hT hcards hnot

lemma boundaryProjection_innerAnodyne_homOfLE_transport_target
    {X : SSet.{u}} {A B C : X.Subcomplex} (e : B = C) (h : A ≤ B)
    (hh : SSet.innerAnodyneExtensions (SSet.Subcomplex.homOfLE h)) :
    SSet.innerAnodyneExtensions (SSet.Subcomplex.homOfLE (e ▸ h)) := by
  subst C
  exact hh

lemma adjoinBoundaryProjectionCells_cons_innerAnodyne
    (m n r : ℕ) (i : Fin (n + 2))
    (T : Finset (Fin (m + 2)))
    (ts : List (Finset (Fin (m + 2))))
    (hT : T.card = r + 1) (hcards : ∀ U ∈ ts, U.card = r + 1)
    (hnot : T ∉ ts) (hr : r ≤ m) (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE (le_sup_left :
        adjoinJoinCellList (m + 1) n
            (boundaryProjectionHornStage m n i r) ts ≤
          adjoinJoinCellList (m + 1) n
            (boundaryProjectionHornStage m n i r) (T :: ts))) := by
  let sq : SSet.Subcomplex.BicartSq
      (joinSigmaOneHornRange (m + 1) (n + 1) T i)
      (adjoinJoinCellList (m + 1) n
        (boundaryProjectionHornStage m n i r) ts)
      (SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1) T))
      (adjoinJoinCellList (m + 1) n
        (boundaryProjectionHornStage m n i r) (T :: ts)) := {
    sup_eq := rfl
    inf_eq := adjoinBoundaryProjectionCells_inf_newCell_eq_hornRange
      m n r i T ts hT hcards hnot hr }
  have hf : SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE sq.le₁₃) := by
    apply joinSigmaOneHornRangeToOfSimplex_innerAnodyne_of_distinguished_pos
    · rw [hT]
      omega
    · exact hn
  rw [SSet.innerAnodyneExtensions_eq_llp_rlp] at hf ⊢
  intro E B p hp
  letI : HasLiftingProperty (SSet.Subcomplex.homOfLE sq.le₁₃) p :=
    hf p hp
  exact sq.isPushout.hasLiftingProperty p

lemma adjoinBoundaryProjectionCells_innerAnodyne
    (m n r : ℕ) (i : Fin (n + 2))
    (ts : List (Finset (Fin (m + 2)))) (hnd : ts.Nodup)
    (hcards : ∀ T ∈ ts, T.card = r + 1)
    (hr : r ≤ m) (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE (le_adjoinJoinCellList (m + 1) n
        (boundaryProjectionHornStage m n i r) ts)) := by
  induction ts with
  | nil =>
      simpa only [adjoinJoinCellList,
        SSet.Subcomplex.homOfLE_refl] using
          SSet.innerAnodyneExtensions.id_mem
            (boundaryProjectionHornStage m n i r : SSet)
  | cons T ts ih =>
      have hndTail : ts.Nodup := hnd.tail
      have hcardsTail : ∀ U ∈ ts, U.card = r + 1 := by
        intro U hU
        exact hcards U (by simp [hU])
      have hTail := ih hndTail hcardsTail
      have hStep := adjoinBoundaryProjectionCells_cons_innerAnodyne
        m n r i T ts (hcards T (by simp)) hcardsTail
          (List.nodup_cons.mp hnd).1 hr hn
      have hComp := SSet.innerAnodyneExtensions.comp_mem _ _ hTail hStep
      rw [SSet.Subcomplex.homOfLE_comp] at hComp
      change SSet.innerAnodyneExtensions
        (SSet.Subcomplex.homOfLE
          ((le_adjoinJoinCellList (m + 1) n
            (boundaryProjectionHornStage m n i r) ts).trans le_sup_left))
      exact hComp

lemma adjoinBoundaryProjectionCellsAtCard_eq_nextStage
    (m n r : ℕ) (i : Fin (n + 2)) (hr : r ≤ m) :
    adjoinJoinCellList.{u} (m + 1) n
        (boundaryProjectionHornStage m n i r)
        (joinCellsAtCard (m + 1) r) =
      boundaryProjectionHornStage m n i (r + 1) := by
  rw [adjoinBoundaryProjectionCells_eq_inf m n r i
    (joinCellsAtCard (m + 1) r)
    (fun T hT => (mem_joinCellsAtCard_iff (m + 1) r T).1 hT) hr]
  rw [adjoinJoinCellsAtCard_eq_nextStage]
  rfl

lemma boundaryProjectionHornStage_succ_innerAnodyne
    (m n r : ℕ) (i : Fin (n + 2)) (hr : r ≤ m)
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE
        (show boundaryProjectionHornStage m n i r ≤
          boundaryProjectionHornStage m n i (r + 1) from by
            apply inf_le_inf_right
            exact representableJoinHornStage_monotone
              (m + 1) (n + 1) i (by omega))) := by
  have hlist := adjoinBoundaryProjectionCells_innerAnodyne
    m n r i (joinCellsAtCard (m + 1) r)
    (joinCellsAtCard_nodup (m + 1) r)
    (fun T hT => (mem_joinCellsAtCard_iff (m + 1) r T).1 hT)
    hr hn
  exact boundaryProjection_innerAnodyne_homOfLE_transport_target
    (adjoinBoundaryProjectionCellsAtCard_eq_nextStage m n r i hr)
    (le_adjoinJoinCellList (m + 1) n
      (boundaryProjectionHornStage m n i r)
      (joinCellsAtCard (m + 1) r)) hlist

lemma boundaryProjectionHornStage_zero_to_stage_innerAnodyne
    (m n r : ℕ) (i : Fin (n + 2)) (hr : r ≤ m + 1)
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE
        (show boundaryProjectionHornStage m n i 0 ≤
          boundaryProjectionHornStage m n i r from by
            apply inf_le_inf_right
            exact representableJoinHornStage_monotone
              (m + 1) (n + 1) i (Nat.zero_le r))) := by
  induction r with
  | zero =>
      simpa only [SSet.Subcomplex.homOfLE_refl] using
        SSet.innerAnodyneExtensions.id_mem
          (boundaryProjectionHornStage m n i 0 : SSet)
  | succ r ih =>
      have hir := ih (by omega)
      have hs := boundaryProjectionHornStage_succ_innerAnodyne
        m n r i (by omega) hn
      have hc := SSet.innerAnodyneExtensions.comp_mem _ _ hir hs
      rw [SSet.Subcomplex.homOfLE_comp] at hc
      exact hc

lemma boundaryProjectionHornStage_zero_to_target_innerAnodyne
    (m n : ℕ) (i : Fin (n + 2))
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE
        (show boundaryProjectionHornStage m n i 0 ≤
          boundaryProjectionTargetRange m n from inf_le_right)) := by
  have hs := boundaryProjectionHornStage_zero_to_stage_innerAnodyne
    m n (m + 1) i le_rfl hn
  exact boundaryProjection_innerAnodyne_homOfLE_transport_target
    (boundaryProjectionHornStage_eq_target m n i)
    (show boundaryProjectionHornStage m n i 0 ≤
      boundaryProjectionHornStage m n i (m + 1) from by
        apply inf_le_inf_right
        exact representableJoinHornStage_monotone
          (m + 1) (n + 1) i (by omega)) hs

lemma subcomplex_image_iso_injective
    {X Y : SSet.{u}} (e : X ≅ Y) {A B : X.Subcomplex}
    (h : A.image e.hom = B.image e.hom) : A = B := by
  have h' := congrArg (fun C : Y.Subcomplex => C.image e.inv) h
  simpa [← SSet.Subcomplex.image_comp] using h'

noncomputable def boundaryProjectionHornOverlapStdMap
    (m n : ℕ) (i : Fin (n + 2)) :
    simplicialJoin (SSet.boundary (m + 1) : SSet.{u}) Λ[n + 1, i] ⟶
      Δ[(m + 1) + (n + 1) + 1] :=
  simplicialJoinMap (SSet.boundary (m + 1)).ι
      (SSet.horn (n + 1) i).ι ≫
    (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom

lemma boundaryProjectionHornOverlapStdMap_range_eq_inf
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (boundaryProjectionHornOverlapStdMap.{u} m n i) =
      representableJoinHornInitial (m + 1) (n + 1) i ⊓
        boundaryProjectionTargetRange m n := by
  have hn := normalizedJoinBoundaryHornOverlapMap_range_eq_inf.{u} m n i
  unfold normalizedJoinBoundaryHornOverlapMap
    normalizedRepresentableJoinHornMap
    normalizedJoinBoundaryStandardMap at hn
  rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_comp,
    SSet.Subcomplex.range_comp] at hn
  rw [SSet.Subcomplex.image_comp] at hn
  rw [← SSet.Subcomplex.range_comp
    (simplicialJoinMap (SSet.boundary (m + 1)).ι
      (SSet.horn (n + 1) i).ι)
    (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom] at hn
  let e := (leftJoinTargetIso.{u} m (n + 1)).symm
  change (SSet.Subcomplex.range
      (boundaryProjectionHornOverlapStdMap.{u} m n i)).image e.hom =
    (representableJoinHornInitial (m + 1) (n + 1) i).image e.hom ⊓
      (boundaryProjectionTargetRange m n).image e.hom at hn
  haveI : Mono e.hom := inferInstance
  rw [← subcomplex_image_inf_of_mono] at hn
  exact subcomplex_image_iso_injective e hn

lemma boundaryProjectionHornOverlapStdMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (boundaryProjectionHornOverlapStdMap.{u} m n i) := by
  let e := (leftJoinTargetIso.{u} m (n + 1)).inv
  haveI : Mono (boundaryProjectionHornOverlapStdMap.{u} m n i ≫ e) := by
    change Mono (normalizedJoinBoundaryHornOverlapMap.{u} m n i)
    infer_instance
  apply mono_of_mono_fac
    (h := boundaryProjectionHornOverlapStdMap.{u} m n i ≫ e)
  rfl

lemma joinBoundaryStandardMap_succ_one_mono
    (m n : ℕ) : Mono (joinBoundaryStandardMap.{u} (m + 1) (n + 1)) := by
  let e := (leftJoinTargetIso.{u} m (n + 1)).inv
  haveI : Mono (joinBoundaryStandardMap.{u} (m + 1) (n + 1) ≫ e) := by
    change Mono (normalizedJoinBoundaryStandardMap.{u} m (n + 1))
    infer_instance
  apply mono_of_mono_fac
    (h := joinBoundaryStandardMap.{u} (m + 1) (n + 1) ≫ e)
  rfl

noncomputable def boundaryProjectionHornCornerStdMap
    (m n : ℕ) (i : Fin (n + 2)) :
    pushout
        (simplicialJoinRightInclusion
          (SSet.boundary (m + 1) : SSet.{u}) Λ[n + 1, i])
        (SSet.horn (n + 1) i).ι ⟶
      Δ[(m + 1) + (n + 1) + 1] :=
  diagramUnderProjectionHornCornerMap
      (SSet.boundary (m + 1) : SSet.{u}) (n + 1) i ≫
    simplicialJoinMap (SSet.boundary (m + 1)).ι
      (𝟙 (Δ[n + 1] : SSet.{u})) ≫
    (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom

@[reassoc]
lemma boundaryProjectionHornCornerStdMap_inl
    (m n : ℕ) (i : Fin (n + 2)) :
    pushout.inl
        (simplicialJoinRightInclusion
          (SSet.boundary (m + 1) : SSet.{u}) Λ[n + 1, i])
        (SSet.horn (n + 1) i).ι ≫
      boundaryProjectionHornCornerStdMap m n i =
        boundaryProjectionHornOverlapStdMap m n i := by
  unfold boundaryProjectionHornCornerStdMap
    boundaryProjectionHornOverlapStdMap
  rw [← Category.assoc,
    diagramUnderProjectionHornCornerMap_inl]
  rw [← Category.assoc, simplicialJoinMap_comp_general]
  simp

@[reassoc]
lemma boundaryProjectionHornCornerStdMap_inr
    (m n : ℕ) (i : Fin (n + 2)) :
    pushout.inr
        (simplicialJoinRightInclusion
          (SSet.boundary (m + 1) : SSet.{u}) Λ[n + 1, i])
        (SSet.horn (n + 1) i).ι ≫
      boundaryProjectionHornCornerStdMap m n i =
        simplicialJoinRightInclusion
            (Δ[m + 1] : SSet.{u}) Δ[n + 1] ≫
          (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom := by
  unfold boundaryProjectionHornCornerStdMap
  rw [← Category.assoc,
    diagramUnderProjectionHornCornerMap_inr]
  rw [← Category.assoc,
    simplicialJoinRightInclusion_naturality_left]

lemma boundaryProjectionHornCornerStdMap_range
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (boundaryProjectionHornCornerStdMap.{u} m n i) =
      (representableJoinHornInitial (m + 1) (n + 1) i ⊓
        boundaryProjectionTargetRange m n) ⊔
      SSet.Subcomplex.ofSimplex
        (joinSigmaOneSimplex (m + 1) (n + 1)
          (∅ : Finset (Fin (m + 2)))) := by
  rw [range_isPushout_map_eq_sup
    (IsPushout.of_hasPushout
      (simplicialJoinRightInclusion
        (SSet.boundary (m + 1) : SSet.{u}) Λ[n + 1, i])
      (SSet.horn (n + 1) i).ι)
    (boundaryProjectionHornCornerStdMap m n i)]
  rw [boundaryProjectionHornCornerStdMap_inl,
    boundaryProjectionHornCornerStdMap_inr,
    boundaryProjectionHornOverlapStdMap_range_eq_inf,
    representableJoinRightInclusion_range_eq_emptyCell]

noncomputable instance boundaryProjectionHornCornerStdMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (boundaryProjectionHornCornerStdMap.{u} m n i) := by
  let K := (SSet.boundary (m + 1) : SSet.{u})
  let a := simplicialJoinRightInclusion K Λ[n + 1, i]
  let b := (SSet.horn (n + 1) i).ι
  let h := boundaryProjectionHornOverlapStdMap.{u} m n i
  let k := simplicialJoinRightInclusion (Δ[m + 1] : SSet.{u}) Δ[n + 1] ≫
    (simplicialJoinStdSimplexIsoNat (m + 1) (n + 1)).hom
  have w : a ≫ h = b ≫ k := by
    dsimp [a, b, h, k, K]
    rw [← boundaryProjectionHornCornerStdMap_inl,
      ← boundaryProjectionHornCornerStdMap_inr]
    rw [← Category.assoc, ← Category.assoc, pushout.condition]
  haveI : Mono b := by
    dsimp [b]
    infer_instance
  haveI : Mono h := by
    dsimp [h]
    exact boundaryProjectionHornOverlapStdMap_mono m n i
  haveI : Mono k := by
    dsimp [k]
    exact representableJoinRightStdMap_mono (m + 1) n
  haveI : Mono (a ≫ h) := by
    have hbk : Mono (b ≫ k) := mono_comp _ _
    exact w.symm ▸ hbk
  haveI : Mono a := by
    apply mono_of_mono_fac (h := a ≫ h)
    rfl
  have hoverlap : SSet.Subcomplex.range (a ≫ h) =
      joinSigmaOneHornRange (m + 1) (n + 1)
        (∅ : Finset (Fin (m + 2))) i := by
    rw [w]
    exact representableJoinRightHornRange_eq_emptyHornRange (m + 1) n i
  have hrange : SSet.Subcomplex.range (a ≫ h) =
      SSet.Subcomplex.range h ⊓ SSet.Subcomplex.range k := by
    rw [hoverlap,
      boundaryProjectionHornOverlapStdMap_range_eq_inf,
      representableJoinRightInclusion_range_eq_emptyCell]
    symm
    let P := SSet.Subcomplex.ofSimplex
      (joinSigmaOneSimplex (m + 1) (n + 1)
        (∅ : Finset (Fin (m + 2))))
    have hPB : P ≤ boundaryProjectionTargetRange.{u} m n := by
      apply joinSigmaOneCell_le_boundaryProjectionTargetRange
      simp
    have hBP : boundaryProjectionTargetRange.{u} m n ⊓ P = P :=
      inf_eq_right.mpr hPB
    calc
      (representableJoinHornInitial (m + 1) (n + 1) i ⊓
          boundaryProjectionTargetRange m n) ⊓ P =
        representableJoinHornInitial (m + 1) (n + 1) i ⊓
          (boundaryProjectionTargetRange m n ⊓ P) := inf_assoc _ _ _
      _ = representableJoinHornInitial (m + 1) (n + 1) i ⊓ P :=
        congrArg (fun D =>
          representableJoinHornInitial (m + 1) (n + 1) i ⊓ D) hBP
      _ = _ := initial_inf_emptyJoinCell_eq_hornRange (m + 1) n i
  have hp : Mono (pushout.desc h k w) :=
    mono_of_pushout_range_inter w hrange
  have heq : boundaryProjectionHornCornerStdMap.{u} m n i =
      pushout.desc h k w := by
    apply pushout.hom_ext
    · rw [boundaryProjectionHornCornerStdMap_inl, pushout.inl_desc]
    · rw [boundaryProjectionHornCornerStdMap_inr, pushout.inr_desc]
  exact heq.symm ▸ hp

lemma boundaryProjectionHornCornerStdMap_range_eq_stage_zero
    (m n : ℕ) (i : Fin (n + 2)) :
    SSet.Subcomplex.range
        (boundaryProjectionHornCornerStdMap.{u} m n i) =
      boundaryProjectionHornStage m n i 0 := by
  rw [boundaryProjectionHornCornerStdMap_range,
    boundaryProjectionHornStage_zero_eq]

noncomputable instance boundaryDiagramUnderProjectionHornCornerMap_mono
    (m n : ℕ) (i : Fin (n + 2)) :
    Mono (diagramUnderProjectionHornCornerMap
      (SSet.boundary (m + 1) : SSet.{u}) (n + 1) i) := by
  let g := diagramUnderProjectionHornCornerMap
    (SSet.boundary (m + 1) : SSet.{u}) (n + 1) i
  let t := joinBoundaryStandardMap.{u} (m + 1) (n + 1)
  have hgt : g ≫ t = boundaryProjectionHornCornerStdMap.{u} m n i := by
    rfl
  haveI : Mono (g ≫ t) := hgt.symm ▸
    (inferInstance : Mono (boundaryProjectionHornCornerStdMap.{u} m n i))
  change Mono g
  apply mono_of_mono_fac (h := g ≫ t)
  rfl

lemma innerAnodyne_of_mono_fac_range
    {S T X : SSet.{u}} (g : S ⟶ T) (t : T ⟶ X)
    [Mono g] [Mono t] {A B : X.Subcomplex}
    (hA : SSet.Subcomplex.range (g ≫ t) = A)
    (hB : SSet.Subcomplex.range t = B) (hAB : A ≤ B)
    (hinner : SSet.innerAnodyneExtensions
      (SSet.Subcomplex.homOfLE hAB)) :
    SSet.innerAnodyneExtensions g := by
  subst A
  subst B
  let eA := simplicialSetIsoRangeOfMono (g ≫ t)
  let eB := simplicialSetIsoRangeOfMono t
  have heq : eA.hom ≫ SSet.Subcomplex.homOfLE hAB =
      g ≫ eB.hom := by
    apply (cancel_mono (SSet.Subcomplex.range t).ι).mp
    dsimp [eA, eB, simplicialSetIsoRangeOfMono]
    simp only [Category.assoc, SSet.Subcomplex.homOfLE_ι,
      SSet.Subcomplex.toRange_ι]
  let e : Arrow.mk g ≅ Arrow.mk (SSet.Subcomplex.homOfLE hAB) :=
    Arrow.isoMk eA eB heq
  exact (SSet.innerAnodyneExtensions.arrow_mk_iso_iff e).2 hinner

lemma boundaryDiagramUnderProjectionHornCornerMap_innerAnodyne
    (m n : ℕ) (i : Fin (n + 2))
    (hn : i < Fin.last (n + 1)) :
    SSet.innerAnodyneExtensions
      (diagramUnderProjectionHornCornerMap
        (SSet.boundary (m + 1) : SSet.{u}) (n + 1) i) := by
  let g := diagramUnderProjectionHornCornerMap
    (SSet.boundary (m + 1) : SSet.{u}) (n + 1) i
  let t := joinBoundaryStandardMap.{u} (m + 1) (n + 1)
  let f := boundaryProjectionHornCornerStdMap.{u} m n i
  have hgt : g ≫ t = f := by rfl
  haveI : Mono g := by
    dsimp [g]
    infer_instance
  haveI : Mono t := by
    dsimp [t]
    exact joinBoundaryStandardMap_succ_one_mono m n
  haveI : Mono f := by
    dsimp [f]
    infer_instance
  have hA : SSet.Subcomplex.range (g ≫ t) =
      boundaryProjectionHornStage m n i 0 := by
    rw [hgt]
    exact boundaryProjectionHornCornerStdMap_range_eq_stage_zero m n i
  have hB : SSet.Subcomplex.range t =
      boundaryProjectionTargetRange m n := by rfl
  exact innerAnodyne_of_mono_fac_range g t hA hB inf_le_right
    (boundaryProjectionHornStage_zero_to_target_innerAnodyne m n i hn)

end LeanLCAExactChallenge.Infinity
