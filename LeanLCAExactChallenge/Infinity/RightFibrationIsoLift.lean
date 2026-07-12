import LeanLCAExactChallenge.Infinity.JoyalRightFibration

/-! # Source-preserving equivalence lifts for right fibrations -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

/-- A source-preserving lift of a base equivalence along a right fibration. -/
structure RightFibration.EquivalenceSourceLift
    {X Y : SSet.{u}} (p : X ⟶ Y) (x : X _⦋0⦌)
    {y : Y _⦋0⦌} (e : SSet.Edge (p.app _ x) y) where
  simplex : X _⦋1⦌
  source : X.δ 1 simplex = x
  map : p.app _ simplex = e.edge
  isEquivalence : EdgeIsEquivalence (SSet.Edge.mk' simplex)

/-- Right fibrations lift equivalence edges with a prescribed source.

First lift a chosen inverse with prescribed target.  The right inverse
triangle is then a right outer horn, whose missing edge is the required
strict lift of the original edge. -/
lemma RightFibration.nonempty_equivalenceSourceLift
    {X Y : SSet.{u}} (p : X ⟶ Y) [RightFibration p] [SSet.Quasicategory Y]
    (x : X _⦋0⦌) {y : Y _⦋0⦌} (e : SSet.Edge (p.app _ x) y)
    (he : EdgeIsEquivalence e) :
    Nonempty (RightFibration.EquivalenceSourceLift p x e) := by
  let d := Truncated.inverseTriangleDataOfEdgeIsEquivalence e he
  let eInv : SSet.Edge y (p.app _ x) := SSet.Edge.ofTruncated d.inverse
  let rightTriangle : SSet.Edge.CompStruct e eInv
      (SSet.Edge.id (p.app _ x)) :=
    SSet.Edge.CompStruct.ofTruncated d.rightTriangle
  have heInv : EdgeIsEquivalence eInv := by
    let leftTriangle : SSet.Edge.CompStruct eInv e
        (SSet.Edge.id y) :=
      SSet.Edge.CompStruct.ofTruncated d.leftTriangle
    refine ⟨⟨edgeHomotopyClass e, ?_, ?_⟩⟩
    · exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        leftTriangle.toTruncated).trans
          (SSet.Truncated.HomotopyCategory.homMk_id _)
    · exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        rightTriangle.toTruncated).trans
          (SSet.Truncated.HomotopyCategory.homMk_id _)
  obtain ⟨inverseLift⟩ :=
    RightFibration.nonempty_equivalenceTargetLift p x eInv heInv
  let idXMap : (Δ[1] : SSet.{u}) ⟶ X :=
    SSet.yonedaEquiv.symm (SSet.Edge.id x).edge
  let inverseMap : (Δ[1] : SSet.{u}) ⟶ X :=
    SSet.yonedaEquiv.symm inverseLift.simplex
  let triangleMap : (Δ[2] : SSet.{u}) ⟶ Y :=
    SSet.yonedaEquiv.symm rightTriangle.simplex
  have hcompat : SSet.stdSimplex.δ 0 ≫ idXMap =
      SSet.stdSimplex.δ 0 ≫ inverseMap := by
    apply SSet.yonedaEquiv.injective
    simp only [idXMap, inverseMap, SSet.yonedaEquiv_comp]
    exact (SSet.Edge.id x).tgt_eq.trans inverseLift.target.symm
  have hpId : idXMap ≫ p = SSet.stdSimplex.δ 1 ≫ triangleMap := by
    apply SSet.yonedaEquiv.injective
    simp only [idXMap, triangleMap, SSet.yonedaEquiv_comp,
      Equiv.apply_symm_apply]
    change p.app _ (SSet.Edge.id x).edge = Y.δ 1 rightTriangle.simplex
    rw [← SSet.Edge.map_edge, SSet.Edge.map_id, rightTriangle.d₁]
  have hpInv : inverseMap ≫ p = SSet.stdSimplex.δ 0 ≫ triangleMap := by
    apply SSet.yonedaEquiv.injective
    simp only [inverseMap, triangleMap, SSet.yonedaEquiv_comp,
      Equiv.apply_symm_apply]
    change p.app _ inverseLift.simplex = Y.δ 0 rightTriangle.simplex
    rw [inverseLift.map, rightTriangle.d₀]
  obtain ⟨lift, hfaceId, _hfaceInv, hlift⟩ :=
    RightFibration.liftHorn₂₂ p idXMap inverseMap hcompat triangleMap hpId hpInv
  let simplex := SSet.yonedaEquiv lift
  have yonedaFace {Z : SSet.{u}} (i : Fin 3)
      (σ : (Δ[2] : SSet.{u}) ⟶ Z) :
      SSet.yonedaEquiv (SSet.stdSimplex.δ i ≫ σ) =
        Z.δ i (SSet.yonedaEquiv σ) := by
    change σ.app _ (Δ[2].δ i (SSet.yonedaEquiv (𝟙 Δ[2]))) =
      Z.δ i (σ.app _ (SSet.yonedaEquiv (𝟙 Δ[2])))
    exact SSet.δ_naturality_apply σ i (SSet.yonedaEquiv (𝟙 Δ[2]))
  have hsource : X.δ 1 (X.δ 2 simplex) = x := by
    calc
      X.δ 1 (X.δ 2 simplex) = X.δ 1 (X.δ 1 simplex) :=
        X.δ_comp_δ_apply (le_refl (1 : Fin 2)) simplex
      _ = x := by
        have h := congrArg SSet.yonedaEquiv hfaceId
        rw [yonedaFace] at h
        have h' : X.δ 1 simplex = (SSet.Edge.id x).edge := by
          simpa only [simplex, idXMap, Equiv.apply_symm_apply] using h
        rw [h', (SSet.Edge.id x).src_eq]
  have hmap : p.app _ (X.δ 2 simplex) = e.edge := by
    rw [SSet.δ_naturality_apply p 2 simplex]
    have h := congrArg SSet.yonedaEquiv hlift
    simp only [triangleMap, SSet.yonedaEquiv_comp,
      Equiv.apply_symm_apply] at h
    change p.app _ simplex = rightTriangle.simplex at h
    rw [h, rightTriangle.d₂]
  let liftedEdge := SSet.Edge.mk' (X.δ 2 simplex)
  have hsrcMap : p.app _ (X.δ 1 (X.δ 2 simplex)) = p.app _ x :=
    congrArg (p.app (op ⦋0⦌)) hsource
  have htgtMap : p.app _ (X.δ 0 (X.δ 2 simplex)) = y := by
    calc
      _ = Y.δ 0 (p.app _ (X.δ 2 simplex)) :=
        SSet.δ_naturality_apply p 0 (X.δ 2 simplex)
      _ = Y.δ 0 e.edge := congrArg (Y.δ 0) hmap
      _ = y := e.tgt_eq
  have hmapped : EdgeIsEquivalence (liftedEdge.map p) := by
    have hc := he.castEndpoints hsrcMap htgtMap
    have hedge : SSet.Edge.castEndpoints hsrcMap htgtMap e =
        liftedEdge.map p := by
      apply SSet.Edge.ext
      simp only [SSet.Edge.castEndpoints_edge, SSet.Edge.map_edge,
        liftedEdge, SSet.Edge.mk'_edge]
      exact hmap.symm
    simpa only [hedge] using hc
  exact ⟨⟨X.δ 2 simplex, hsource, hmap,
    RightFibration.edgeIsEquivalence_of_map p liftedEdge hmapped⟩⟩

end LeanLCAExactChallenge.Infinity
