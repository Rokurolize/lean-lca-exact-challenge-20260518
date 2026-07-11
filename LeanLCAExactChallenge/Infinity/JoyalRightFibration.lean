import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension

/-!
# Right fibrations for the Joyal extension argument

This file introduces the horn-lifting class used in Rezk's proof of the
Joyal extension theorem.  A right fibration lifts every horn whose missing
face is not the initial face.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Simplicial

/-- Two successive preinverses give a genuine inverse.  The second candidate
need not be strictly equal to the original arrow. -/
lemma isIso_of_preinverse_chain
    {C : Type u} [Category C] {x y : C}
    (e : x ⟶ y) (g : y ⟶ x) (e' : x ⟶ y)
    (hge : g ≫ e = 𝟙 y) (he'g : e' ≫ g = 𝟙 x) : IsIso e := by
  have hee' : e = e' := by
    calc
      e = 𝟙 x ≫ e := (Category.id_comp e).symm
      _ = (e' ≫ g) ≫ e := by rw [he'g]
      _ = e' ≫ (g ≫ e) := Category.assoc _ _ _
      _ = e' ≫ 𝟙 y := by rw [hge]
      _ = e' := Category.comp_id e'
  exact ⟨⟨g, hee' ▸ he'g, hge⟩⟩

/-- Positive-index horn inclusions, including the last horn. -/
inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (h0 : 0 < i) :
      rightHornInclusions Λ[n + 1, i].ι

lemma horn_ι_mem_rightHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (h0 : 0 < i) : rightHornInclusions (SSet.horn.{u} n i).ι := by
  obtain _ | n := n
  · omega
  · exact ⟨i, h0⟩

/-- Right fibrations are maps with the RLP against every positive-index horn. -/
def rightFibrations : MorphismProperty SSet.{u} := rightHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

class RightFibration {X Y : SSet.{u}} (p : X ⟶ Y) : Prop where
  mem : rightFibrations p

lemma RightFibration.hasLiftingProperty
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p]
    {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i) :
    HasLiftingProperty (SSet.horn n i).ι p :=
  RightFibration.mem _ (horn_ι_mem_rightHornInclusions h0)

/-- A right fibration lifts an edge once its target vertex has been lifted. -/
lemma RightFibration.hasLiftingProperty_edgeTarget
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    HasLiftingProperty
      (SSet.horn 1 (1 : Fin 2)).ι p :=
  RightFibration.hasLiftingProperty p (by simp)

/-- The outer `2`-horn used to lift a chosen preinverse triangle. -/
lemma RightFibration.hasLiftingProperty_preinverseTriangle
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    HasLiftingProperty
      (SSet.horn 2 (2 : Fin 3)).ι p :=
  RightFibration.hasLiftingProperty p (by simp)

lemma innerHornInclusions_le_rightHornInclusions :
    SSet.innerHornInclusions.{u} ≤ rightHornInclusions.{u} := by
  intro A B f hf
  obtain @⟨n, i, h0, _⟩ := hf
  exact horn_ι_mem_rightHornInclusions h0

lemma rightFibrations_le_innerFibrations :
    rightFibrations.{u} ≤ SSet.innerFibrations.{u} :=
  antitone_rlp innerHornInclusions_le_rightHornInclusions

instance {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] :
    SSet.InnerFibration p :=
  ⟨rightFibrations_le_innerFibrations _ RightFibration.mem⟩

instance rightFibration_comp
    {X Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    [RightFibration p] [RightFibration q] : RightFibration (p ≫ q) :=
  ⟨rightFibrations.comp_mem p q RightFibration.mem RightFibration.mem⟩

instance rightFibration_pullback_snd
    {X Y Z : SSet.{u}} (p : X ⟶ Z) (q : Y ⟶ Z) [RightFibration p] :
    RightFibration (pullback.snd p q) := by
  refine ⟨?_⟩
  exact rightFibrations.pullback_snd _ _ RightFibration.mem

/-- Map-level relative lifting of a right outer `2`-horn. -/
lemma RightFibration.liftHorn₂₂
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p]
    (f₀₂ f₁₂ : (Δ[1] : SSet.{u}) ⟶ X)
    (hcompat : SSet.stdSimplex.δ 0 ≫ f₀₂ = SSet.stdSimplex.δ 0 ≫ f₁₂)
    (b : (Δ[2] : SSet.{u}) ⟶ Y)
    (hb₀₂ : f₀₂ ≫ p = SSet.stdSimplex.δ 1 ≫ b)
    (hb₁₂ : f₁₂ ≫ p = SSet.stdSimplex.δ 0 ≫ b) :
    ∃ σ : (Δ[2] : SSet.{u}) ⟶ X,
      SSet.stdSimplex.δ 1 ≫ σ = f₀₂ ∧
      SSet.stdSimplex.δ 0 ≫ σ = f₁₂ ∧ σ ≫ p = b := by
  let h : (Λ[2, 2] : SSet.{u}) ⟶ X :=
    SSet.horn₂₂.isPushout.desc f₀₂ f₁₂ hcompat
  have hsquare : h ≫ p = (SSet.horn 2 (2 : Fin 3)).ι ≫ b := by
    apply SSet.horn₂₂.isPushout.hom_ext
    · rw [← Category.assoc, SSet.horn₂₂.isPushout.inl_desc, hb₀₂]
      rfl
    · rw [← Category.assoc, SSet.horn₂₂.isPushout.inr_desc, hb₁₂]
      rfl
  let sq : CommSq h (SSet.horn 2 (2 : Fin 3)).ι p b := ⟨hsquare⟩
  letI : HasLiftingProperty (SSet.horn 2 (2 : Fin 3)).ι p :=
    RightFibration.hasLiftingProperty_preinverseTriangle p
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · calc
      SSet.stdSimplex.δ 1 ≫ sq.lift =
          SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι ≫ sq.lift := rfl
      _ = SSet.horn₂₂.ι₀₂ ≫ h := by rw [sq.fac_left]
      _ = f₀₂ := SSet.horn₂₂.isPushout.inl_desc _ _ _
  · calc
      SSet.stdSimplex.δ 0 ≫ sq.lift =
          SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι ≫ sq.lift := rfl
      _ = SSet.horn₂₂.ι₁₂ ≫ h := by rw [sq.fac_left]
      _ = f₁₂ := SSet.horn₂₂.isPushout.inr_desc _ _ _

/-- Lift the two inverse triangles of the image of an edge.  The first lift keeps the
original edge, while the second may produce a new forward edge. -/
lemma RightFibration.liftPreinverseChain
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] [SSet.Quasicategory Y]
    {x y : X _⦋0⦌} (e : SSet.Edge x y)
    (he : EdgeIsEquivalence (e.map p)) :
    ∃ (g : SSet.Edge y x) (e' : SSet.Edge x y),
      edgeHomotopyClass g ≫ edgeHomotopyClass e = 𝟙 (homotopyObject y) ∧
      edgeHomotopyClass e' ≫ edgeHomotopyClass g = 𝟙 (homotopyObject x) := by
  let d := Truncated.inverseTriangleDataOfEdgeIsEquivalence (e.map p) he
  let gY : SSet.Edge (p.app _ y) (p.app _ x) := SSet.Edge.ofTruncated d.inverse
  let leftTriangle : SSet.Edge.CompStruct gY (e.map p) (SSet.Edge.id (p.app _ y)) :=
    SSet.Edge.CompStruct.ofTruncated d.leftTriangle
  let rightTriangle : SSet.Edge.CompStruct (e.map p) gY (SSet.Edge.id (p.app _ x)) :=
    SSet.Edge.CompStruct.ofTruncated d.rightTriangle
  let eMap : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm e.edge
  let idYMap : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm (SSet.Edge.id y).edge
  let leftMap : (Δ[2] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm leftTriangle.simplex
  have hpId : idYMap ≫ p = SSet.stdSimplex.δ 1 ≫ leftMap := by
    apply SSet.yonedaEquiv.injective
    dsimp only [idYMap, leftMap]
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change p.app _ (SSet.Edge.id y).edge = Y.δ 1 leftTriangle.simplex
    rw [← SSet.Edge.map_edge, SSet.Edge.map_id, leftTriangle.d₁]
  have hpE : eMap ≫ p = SSet.stdSimplex.δ 0 ≫ leftMap := by
    apply SSet.yonedaEquiv.injective
    dsimp only [eMap, leftMap]
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change p.app _ e.edge = Y.δ 0 leftTriangle.simplex
    rw [← SSet.Edge.map_edge, leftTriangle.d₀]
  obtain ⟨leftLift, hleftId, hleftE, hleftP⟩ :=
    RightFibration.liftHorn₂₂ p idYMap eMap (by
      apply SSet.yonedaEquiv.injective
      dsimp only [idYMap, eMap]
      simp only [SSet.yonedaEquiv_comp]
      change X.δ 0 (SSet.Edge.id y).edge = X.δ 0 e.edge
      exact (SSet.Edge.id y).tgt_eq.trans e.tgt_eq.symm) leftMap hpId hpE
  let sLeft : X _⦋2⦌ := SSet.yonedaEquiv leftLift
  have yonedaFace {Z : SSet.{u}} (i : Fin 3) (σ : (Δ[2] : SSet.{u}) ⟶ Z) :
      SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ σ) = Z.δ i (SSet.yonedaEquiv σ) := by
    change σ.app _ (Δ[2].δ i (SSet.yonedaEquiv (𝟙 Δ[2]))) =
      Z.δ i (σ.app _ (SSet.yonedaEquiv (𝟙 Δ[2])))
    exact SSet.δ_naturality_apply σ i (SSet.yonedaEquiv (𝟙 Δ[2]))
  have hsLeft₁ : X.δ 1 sLeft = (SSet.Edge.id y).edge := by
    have h := congrArg SSet.yonedaEquiv hleftId
    rw [yonedaFace] at h
    simpa [sLeft, idYMap] using h
  have hsLeft₀ : X.δ 0 sLeft = e.edge := by
    have h := congrArg SSet.yonedaEquiv hleftE
    rw [yonedaFace] at h
    simpa [sLeft, eMap] using h
  have hgSrc : X.δ 1 (X.δ 2 sLeft) = y := by
    calc
      X.δ 1 (X.δ 2 sLeft) = X.δ 1 (X.δ 1 sLeft) :=
        X.δ_comp_δ_apply (le_refl (1 : Fin 2)) sLeft
      _ = X.δ 1 (SSet.Edge.id y).edge := congrArg (X.δ 1) hsLeft₁
      _ = y := (SSet.Edge.id y).src_eq
  have hgTgt : X.δ 0 (X.δ 2 sLeft) = x := by
    calc
      X.δ 0 (X.δ 2 sLeft) = X.δ 1 (X.δ 0 sLeft) :=
        X.δ_comp_δ_apply (show (0 : Fin 2) ≤ 1 by simp) sLeft
      _ = X.δ 1 e.edge := congrArg (X.δ 1) hsLeft₀
      _ = x := e.src_eq
  let g : SSet.Edge y x := SSet.Edge.mk (X.δ 2 sLeft) hgSrc hgTgt
  let leftLiftTriangle : SSet.Edge.CompStruct g e (SSet.Edge.id y) :=
    SSet.Edge.CompStruct.mk sLeft (by rfl) hsLeft₀ hsLeft₁
  have hgp : g.map p = gY := by
    apply SSet.Edge.ext
    change p.app _ (X.δ 2 sLeft) = gY.edge
    have h := congrArg SSet.yonedaEquiv hleftP
    dsimp only [leftMap] at h
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
    change p.app _ sLeft = leftTriangle.simplex at h
    rw [SSet.δ_naturality_apply p 2 sLeft, h, leftTriangle.d₂]
  let gMap : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm g.edge
  let idXMap : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm (SSet.Edge.id x).edge
  let rightMap : (Δ[2] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm rightTriangle.simplex
  have hpIdX : idXMap ≫ p = SSet.stdSimplex.δ 1 ≫ rightMap := by
    apply SSet.yonedaEquiv.injective
    dsimp only [idXMap, rightMap]
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change p.app _ (SSet.Edge.id x).edge = Y.δ 1 rightTriangle.simplex
    rw [← SSet.Edge.map_edge, SSet.Edge.map_id, rightTriangle.d₁]
  have hpG : gMap ≫ p = SSet.stdSimplex.δ 0 ≫ rightMap := by
    apply SSet.yonedaEquiv.injective
    dsimp only [gMap, rightMap]
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change p.app _ g.edge = Y.δ 0 rightTriangle.simplex
    rw [← SSet.Edge.map_edge, hgp, rightTriangle.d₀]
  obtain ⟨rightLift, hrightId, hrightG, _⟩ :=
    RightFibration.liftHorn₂₂ p idXMap gMap (by
      apply SSet.yonedaEquiv.injective
      dsimp only [idXMap, gMap]
      simp only [SSet.yonedaEquiv_comp]
      change X.δ 0 (SSet.Edge.id x).edge = X.δ 0 g.edge
      exact (SSet.Edge.id x).tgt_eq.trans g.tgt_eq.symm) rightMap hpIdX hpG
  let sRight : X _⦋2⦌ := SSet.yonedaEquiv rightLift
  have hsRight₁ : X.δ 1 sRight = (SSet.Edge.id x).edge := by
    have h := congrArg SSet.yonedaEquiv hrightId
    rw [yonedaFace] at h
    simpa [sRight, idXMap] using h
  have hsRight₀ : X.δ 0 sRight = g.edge := by
    have h := congrArg SSet.yonedaEquiv hrightG
    rw [yonedaFace] at h
    simpa [sRight, gMap] using h
  have he'Src : X.δ 1 (X.δ 2 sRight) = x := by
    calc
      X.δ 1 (X.δ 2 sRight) = X.δ 1 (X.δ 1 sRight) :=
        X.δ_comp_δ_apply (le_refl (1 : Fin 2)) sRight
      _ = X.δ 1 (SSet.Edge.id x).edge := congrArg (X.δ 1) hsRight₁
      _ = x := (SSet.Edge.id x).src_eq
  have he'Tgt : X.δ 0 (X.δ 2 sRight) = y := by
    calc
      X.δ 0 (X.δ 2 sRight) = X.δ 1 (X.δ 0 sRight) :=
        X.δ_comp_δ_apply (show (0 : Fin 2) ≤ 1 by simp) sRight
      _ = X.δ 1 g.edge := congrArg (X.δ 1) hsRight₀
      _ = y := g.src_eq
  let e' : SSet.Edge x y := SSet.Edge.mk (X.δ 2 sRight) he'Src he'Tgt
  let rightLiftTriangle : SSet.Edge.CompStruct e' g (SSet.Edge.id x) :=
    SSet.Edge.CompStruct.mk sRight (by rfl) hsRight₀ hsRight₁
  refine ⟨g, e', ?_, ?_⟩
  · exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
      leftLiftTriangle.toTruncated).trans
        (SSet.Truncated.HomotopyCategory.homMk_id _)
  · exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
      rightLiftTriangle.toTruncated).trans
        (SSet.Truncated.HomotopyCategory.homMk_id _)

/-- A right fibration reflects equivalence edges. -/
theorem RightFibration.edgeIsEquivalence_of_map
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] [SSet.Quasicategory Y]
    {x y : X _⦋0⦌} (e : SSet.Edge x y)
    (he : EdgeIsEquivalence (e.map p)) : EdgeIsEquivalence e := by
  obtain ⟨g, e', hge, he'g⟩ := RightFibration.liftPreinverseChain p e he
  exact isIso_of_preinverse_chain (edgeHomotopyClass e) (edgeHomotopyClass g)
    (edgeHomotopyClass e') hge he'g

/-- Lift an edge along a right fibration after fixing its target vertex. -/
lemma RightFibration.exists_edge_lift_target
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p]
    (x : X _⦋0⦌) {y : Y _⦋0⦌} (e : SSet.Edge y (p.app _ x)) :
    ∃ s : X _⦋1⦌, X.δ 0 s = x ∧ p.app _ s = e.edge := by
  let a : (Λ[1, 1] : SSet.{u}) ⟶ X := SSet.const x
  let b : (Δ[1] : SSet.{u}) ⟶ Y := SSet.yonedaEquiv.symm e.edge
  have hsquare : a ≫ p = (SSet.horn 1 (1 : Fin 2)).ι ≫ b := by
    apply SSet.horn.hom_ext
    intro j hj
    fin_cases j
    · have hf : (SSet.horn 1 (1 : Fin 2)).ι.app _
          (SSet.horn.face (1 : Fin 2) (0 : Fin 2) hj) =
          SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2)) := rfl
      calc
        (a ≫ p).app _ (SSet.horn.face 1 0 hj) =
            p.app _ (a.app _ (SSet.horn.face 1 0 hj)) := rfl
        _ = p.app _ x := by simp [a]
        _ = Y.δ 0 e.edge := e.tgt_eq.symm
        _ = b.app _ (SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2))) := rfl
        _ = b.app _ ((SSet.horn 1 (1 : Fin 2)).ι.app _
            (SSet.horn.face 1 0 hj)) := by rw [hf]
        _ = ((SSet.horn 1 (1 : Fin 2)).ι ≫ b).app _
            (SSet.horn.face 1 0 hj) := rfl
    · simp at hj
  let sq : CommSq a (SSet.horn 1 (1 : Fin 2)).ι p b := ⟨hsquare⟩
  letI : HasLiftingProperty (SSet.horn 1 (1 : Fin 2)).ι p :=
    RightFibration.hasLiftingProperty_edgeTarget p
  let s : X _⦋1⦌ := SSet.yonedaEquiv sq.lift
  have htgt : X.δ 0 s = x := by
    let hne : (0 : Fin 2) ≠ 1 := by simp
    have h := congrArg
      (fun k ↦ k.app _ (SSet.horn.face (1 : Fin 2) (0 : Fin 2) hne)) sq.fac_left
    have hf : (SSet.horn 1 (1 : Fin 2)).ι.app _
        (SSet.horn.face (1 : Fin 2) (0 : Fin 2) hne) =
        SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2)) := rfl
    change sq.lift.app _ ((SSet.horn 1 (1 : Fin 2)).ι.app _
      (SSet.horn.face 1 0 hne)) = a.app _ (SSet.horn.face 1 0 hne) at h
    rw [hf] at h
    calc
      X.δ 0 s = sq.lift.app _
          (SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2))) := by
        exact (SSet.δ_naturality_apply sq.lift 0
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))).symm
      _ = a.app _ (SSet.horn.face 1 0 hne) := h
      _ = x := by simp [a]
  refine ⟨s, htgt, ?_⟩
  have h := congrArg SSet.yonedaEquiv sq.fac_right
  dsimp only [b] at h
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  exact h

/-- A target-preserving lift of a base equivalence edge, bundled with the proof that the
lifted edge is itself an equivalence. -/
structure RightFibration.EquivalenceTargetLift
    {X Y : SSet.{u}} (p : X ⟶ Y) (x : X _⦋0⦌)
    {y : Y _⦋0⦌} (e : SSet.Edge y (p.app _ x)) where
  simplex : X _⦋1⦌
  target : X.δ 0 simplex = x
  map : p.app _ simplex = e.edge
  isEquivalence : EdgeIsEquivalence (SSet.Edge.mk' simplex)

/-- A right fibration lifts a base equivalence edge with a prescribed target, and the
lifted edge is an equivalence.  This is the isofibration form used for over-slices. -/
lemma RightFibration.nonempty_equivalenceTargetLift
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] [SSet.Quasicategory Y]
    (x : X _⦋0⦌) {y : Y _⦋0⦌} (e : SSet.Edge y (p.app _ x))
    (he : EdgeIsEquivalence e) :
    Nonempty (RightFibration.EquivalenceTargetLift p x e) := by
  obtain ⟨s, hsTarget, hsMap⟩ := RightFibration.exists_edge_lift_target p x e
  have hsSource : p.app _ (X.δ 1 s) = y := by
    calc
      p.app _ (X.δ 1 s) = Y.δ 1 (p.app _ s) :=
        SSet.δ_naturality_apply p 1 s
      _ = Y.δ 1 e.edge := congrArg (Y.δ 1) hsMap
      _ = y := e.src_eq
  subst y
  subst x
  have hEdgeMap : (SSet.Edge.mk' s).map p = e := by
    apply SSet.Edge.ext
    exact hsMap
  have hLiftEquivalence : EdgeIsEquivalence (SSet.Edge.mk' s) :=
    RightFibration.edgeIsEquivalence_of_map p (SSet.Edge.mk' s) (hEdgeMap ▸ he)
  exact ⟨⟨s, rfl, hsMap, hLiftEquivalence⟩⟩

end LeanLCAExactChallenge.Infinity
