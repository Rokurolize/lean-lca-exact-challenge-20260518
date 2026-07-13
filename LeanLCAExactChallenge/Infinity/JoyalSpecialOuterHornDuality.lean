import LeanLCAExactChallenge.Infinity.JoyalSpecialOuterHornDirect
import LeanLCAExactChallenge.Infinity.SimplicialOppositeEquivalences
import LeanLCAExactChallenge.Infinity.ThickSimplexFiltration

/-! # Joyal special left outer horns by simplicial reversal -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

/-- Reverse a special left horn to a special right horn. -/
def specialLeftHornOp {Q : SSet.{u}} (n : ℕ)
    (a : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ Q) :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ Q.op :=
  (hornOpIso (n + 2) (0 : Fin (n + 3))).inv ≫ SSet.opFunctor.map a

lemma stdSimplexEdgeLastTwo_apply (n : ℕ) (i : Fin 2) :
    SSet.yonedaEquiv (stdSimplexEdgeLastTwo.{u} n) i =
      (⟨n + 1 + i.val, by omega⟩ : Fin (n + 3)) := by
  unfold stdSimplexEdgeLastTwo
  rw [Equiv.apply_symm_apply]
  exact SSet.stdSimplex.objEquiv_symm_apply _ i

lemma stdSimplexEdgeZeroOne_apply (n : ℕ) (i : Fin 2) :
    SSet.yonedaEquiv (stdSimplexEdgeZeroOne.{u} n) i =
      (⟨i.val, by omega⟩ : Fin (n + 3)) := by
  unfold stdSimplexEdgeZeroOne
  rw [Equiv.apply_symm_apply]
  exact SSet.stdSimplex.objEquiv_symm_apply _ i

/-- Reversal identifies the trailing edge of the reversed horn with the original leading
edge. -/
lemma specialRightHornEdge_specialLeftHornOp {Q : SSet.{u}} (n : ℕ)
    (a : (Λ[n + 2, (0 : Fin (n + 3))] : SSet.{u}) ⟶ Q) :
    specialRightHornEdge (specialLeftHornOp n a) = specialLeftHornEdge a := by
  have htrail : (SSet.yonedaEquiv (specialRightHornTrailingEdge.{u} n)).val =
      SSet.yonedaEquiv (stdSimplexEdgeLastTwo.{u} n) := rfl
  have hlead : (SSet.yonedaEquiv (specialLeftHornLeadingEdge.{u} n)).val =
      SSet.yonedaEquiv (stdSimplexEdgeZeroOne.{u} n) := rfl
  unfold specialRightHornEdge specialLeftHornEdge specialLeftHornOp
  simp only [SSet.yonedaEquiv_comp]
  change a.app _ ((hornOpIso (n + 2) (0 : Fin (n + 3))).inv.app _
      (SSet.yonedaEquiv (specialRightHornTrailingEdge.{u} n))) =
    a.app _ (SSet.yonedaEquiv (specialLeftHornLeadingEdge.{u} n))
  congr 1
  apply Subtype.ext
  change SSet.stdSimplex.opObjEquiv.{u, u}.symm
      (SSet.yonedaEquiv (specialRightHornTrailingEdge.{u} n)).val =
    (SSet.yonedaEquiv (specialLeftHornLeadingEdge.{u} n)).val
  calc
    _ = SSet.stdSimplex.opObjEquiv.{u, u}.symm
        (SSet.yonedaEquiv (stdSimplexEdgeLastTwo.{u} n)) :=
      congrArg SSet.stdSimplex.opObjEquiv.{u, u}.symm htrail
    _ = SSet.yonedaEquiv (stdSimplexEdgeZeroOne.{u} n) := by
      apply SSet.stdSimplex.ext
      intro i
      change SSet.opObjEquiv (SSet.stdSimplex.opObjEquiv.{u, u}.symm
        (SSet.yonedaEquiv (stdSimplexEdgeLastTwo.{u} n))) i =
          (SSet.yonedaEquiv (stdSimplexEdgeZeroOne.{u} n)) i
      rw [SSet.stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
      rw [stdSimplexEdgeLastTwo_apply, stdSimplexEdgeZeroOne_apply]
      apply Fin.ext
      simp only [Fin.val_rev]
      omega
    _ = _ := hlead.symm

/-- The direct right-horn theorem, transported by simplicial reversal, fills every special
left outer horn of dimension at least three. -/
theorem specialLeftOuterHorn_filling_succ_direct
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (m : ℕ) (a : (Λ[m + 3, (0 : Fin (m + 4))] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence
      (SSet.Edge.mk' (specialLeftHornEdge (n := m + 1) a))) :
    ∃ σ : (Δ[m + 3] : SSet.{u}) ⟶ Q,
      (SSet.horn (m + 3) (0 : Fin (m + 4))).ι ≫ σ = a := by
  let aop : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q.op :=
    (hornOpIso (m + 3) (0 : Fin (m + 4))).inv ≫
      SSet.opFunctor.map a
  have heop : EdgeIsEquivalence
      (SSet.Edge.mk' (specialRightHornEdge (n := m + 1) aop)) := by
    have hop := he.op
    have hraw : specialRightHornEdge (n := m + 1) aop =
        specialLeftHornEdge (n := m + 1) a := by
      simpa only [aop, specialLeftHornOp, Nat.add_assoc, Nat.reduceAdd] using
        specialRightHornEdge_specialLeftHornOp (m + 1) a
    rw [← hraw] at hop
    let s : Q.op _⦋1⦌ := specialRightHornEdge (n := m + 1) aop
    let eop := edgeOp (SSet.Edge.mk' (X := Q) (SSet.opObjEquiv s))
    change EdgeIsEquivalence eop at hop
    have hsrc : Q.op.δ 1 s = Q.δ 0 (SSet.opObjEquiv s) := by
      rw [SSet.op_δ]
      change SSet.opObjEquiv
        (SSet.opObjEquiv.symm (Q.δ 0 (SSet.opObjEquiv s))) = _
      exact Equiv.apply_symm_apply _ _
    have htgt : Q.op.δ 0 s = Q.δ 1 (SSet.opObjEquiv s) := by
      rw [SSet.op_δ]
      change SSet.opObjEquiv
        (SSet.opObjEquiv.symm (Q.δ 1 (SSet.opObjEquiv s))) = _
      exact Equiv.apply_symm_apply _ _
    have hcast := hop.castEndpoints hsrc htgt
    have hedge : SSet.Edge.castEndpoints hsrc htgt eop =
        SSet.Edge.mk' (X := Q.op) s := by
      apply SSet.Edge.ext
      rw [SSet.Edge.castEndpoints_edge]
      dsimp [eop, edgeOp, SSet.Edge.mk']
      change SSet.opObjEquiv.symm (SSet.opObjEquiv s) = s
      exact Equiv.symm_apply_apply _ _
    simpa only [s] using hedge ▸ hcast
  obtain ⟨σop, hσop⟩ := specialRightOuterHorn_filling_succ_direct m aop heop
  let σ : (Δ[m + 3] : SSet.{u}) ⟶ Q :=
    (SSet.stdSimplex.opIso (SimplexCategory.mk (m + 3))).inv ≫
      SSet.opFunctor.map σop ≫
        (SSet.opFunctorCompOpFunctorIso.app Q).hom
  refine ⟨σ, ?_⟩
  letI : SSet.opFunctor.{u}.Faithful :=
    (SSet.opEquivalence.{u}).faithful_functor
  apply SSet.opFunctor.map_injective
  apply (cancel_epi
    (hornOpIso (m + 3) (0 : Fin (m + 4))).inv).mp
  simp only [σ, Functor.map_comp]
  change (hornOpIso (m + 3) (0 : Fin (m + 4))).inv ≫
      (SSet.horn (m + 3) (0 : Fin (m + 4))).op.ι ≫
        SSet.opFunctor.map
          (SSet.stdSimplex.opIso (SimplexCategory.mk (m + 3))).inv ≫
        SSet.opFunctor.map (SSet.opFunctor.map σop) ≫
        SSet.opFunctor.map (SSet.opFunctorCompOpFunctorIso.app Q).hom =
      (hornOpIso (m + 3) (0 : Fin (m + 4))).inv ≫
        SSet.opFunctor.map a
  rw [hornOpIso_inv_comp_inclusion_assoc]
  have hΔ :
      (SSet.stdSimplex.opIso (SimplexCategory.mk (m + 3))).inv ≫
        SSet.opFunctor.map
          (SSet.stdSimplex.opIso (SimplexCategory.mk (m + 3))).inv =
      (SSet.opFunctorCompOpFunctorIso.app
        (Δ[m + 3] : SSet.{u})).inv := by
    apply NatTrans.ext
    funext d
    rcases d with ⟨⟨k⟩⟩
    apply ConcreteCategory.hom_ext
    intro x
    apply SSet.stdSimplex.ext
    intro i
    change SSet.opObjEquiv
        (SSet.stdSimplex.opObjEquiv.{u, u}.symm
          (SSet.opObjEquiv
            (SSet.stdSimplex.opObjEquiv.{u, u}.symm x))) i =
      SSet.opObjEquiv (SSet.opObjEquiv.symm x) i
    rw [SSet.stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
    rw [SSet.stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
    simp
  have hcoh :
      (SSet.stdSimplex.opIso (SimplexCategory.mk (m + 3))).inv ≫
        SSet.opFunctor.map
          (SSet.stdSimplex.opIso (SimplexCategory.mk (m + 3))).inv ≫
        SSet.opFunctor.map (SSet.opFunctor.map σop) ≫
      SSet.opFunctor.map (SSet.opFunctorCompOpFunctorIso.app Q).hom =
      σop := by
    rw [← Category.assoc, ← Category.assoc, hΔ]
    change (SSet.opFunctorCompOpFunctorIso.app
          (Δ[m + 3] : SSet.{u})).inv ≫
        SSet.opFunctor.map (SSet.opFunctor.map σop) ≫
        (SSet.opFunctorCompOpFunctorIso.app Q.op).hom = σop
    have hnat := SSet.opFunctorCompOpFunctorIso.hom.naturality σop
    calc
      _ = (SSet.opFunctorCompOpFunctorIso.app
            (Δ[m + 3] : SSet.{u})).inv ≫
          ((SSet.opFunctorCompOpFunctorIso.app
            (Δ[m + 3] : SSet.{u})).hom ≫ (𝟭 SSet).map σop) :=
        congrArg (fun k ↦ (SSet.opFunctorCompOpFunctorIso.app
          (Δ[m + 3] : SSet.{u})).inv ≫ k) hnat
      _ = σop := Iso.inv_hom_id_assoc _ σop
  rw [hcoh]
  change (SSet.horn (m + 3) (0 : Fin (m + 4)).rev).ι ≫ σop = aop
  have hidx : (0 : Fin (m + 4)).rev = Fin.last (m + 3) := by
    apply Fin.ext
    simp
  cases hidx
  exact hσop

lemma specialLeftHornLeadingEdge_zero :
    specialLeftHornLeadingEdge.{u} 0 = SSet.horn₂₀.ι₀₁ := by
  apply (cancel_mono (SSet.horn 2 (0 : Fin 3)).ι).1
  rw [specialLeftHornLeadingEdge, SSet.Subcomplex.lift_ι]
  apply SSet.yonedaEquiv.injective
  simp only [SSet.horn.ι_ι, stdSimplexEdgeZeroOne, Equiv.apply_symm_apply]
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma specialLeftHornEdge_zero_eq_leftOuterHorn₂FirstEdge
    {Q : SSet.{u}} (a : (Λ[2, (0 : Fin 3)] : SSet.{u}) ⟶ Q) :
    specialLeftHornEdge (n := 0) a = leftOuterHorn₂FirstEdge a := by
  unfold specialLeftHornEdge leftOuterHorn₂FirstEdge
  rw [specialLeftHornLeadingEdge_zero]

lemma specialRightHornTrailingEdge_zero :
    specialRightHornTrailingEdge.{u} 0 = SSet.horn₂₂.ι₁₂ := by
  apply (cancel_mono (SSet.horn 2 (Fin.last 2)).ι).1
  rw [specialRightHornTrailingEdge, SSet.Subcomplex.lift_ι]
  apply SSet.yonedaEquiv.injective
  simp only [stdSimplexEdgeLastTwo, Equiv.apply_symm_apply]
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

lemma specialRightHornEdge_zero_eq_rightOuterHorn₂LastEdge
    {Q : SSet.{u}} (a : (Λ[2, Fin.last 2] : SSet.{u}) ⟶ Q) :
    specialRightHornEdge (n := 0) a = rightOuterHorn₂LastEdge a := by
  unfold specialRightHornEdge rightOuterHorn₂LastEdge
  rw [specialRightHornTrailingEdge_zero]
  rfl

/-- All-dimensional Joyal special-right-horn filling property. -/
def HasAllSpecialRightHornFillers (Q : SSet.{u}) : Prop :=
  ∀ (n : ℕ) (a : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ Q),
    EdgeIsEquivalence (SSet.Edge.mk' (specialRightHornEdge a)) →
      ∃ b : (Δ[n + 2] : SSet.{u}) ⟶ Q,
        (SSet.horn (n + 2) (Fin.last (n + 2))).ι ≫ b = a

/-- Every quasicategory has fillers for all special right outer horns. -/
theorem hasAllSpecialRightHornFillers_direct
    (Q : SSet.{u}) [SSet.Quasicategory Q] :
    HasAllSpecialRightHornFillers Q := by
  intro n a he
  cases n with
  | zero =>
      apply Truncated.specialRightOuterHorn₂_filling a
      rw [← specialRightHornEdge_zero_eq_rightOuterHorn₂LastEdge a]
      exact he
  | succ m =>
      exact specialRightOuterHorn_filling_succ_direct m a he

/-- Every quasicategory has fillers for all special left outer horns. -/
theorem hasAllSpecialLeftHornFillers_direct
    (Q : SSet.{u}) [SSet.Quasicategory Q] :
    HasAllSpecialLeftHornFillers Q := by
  intro n a he
  cases n with
  | zero =>
      apply Truncated.specialLeftOuterHorn₂_filling a
      rw [← specialLeftHornEdge_zero_eq_leftOuterHorn₂FirstEdge a]
      exact he
  | succ m =>
      exact specialLeftOuterHorn_filling_succ_direct m a he

end LeanLCAExactChallenge.Infinity
