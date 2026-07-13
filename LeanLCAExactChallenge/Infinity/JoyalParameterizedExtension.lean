import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension
import LeanLCAExactChallenge.Infinity.FixedPairingExtension
import LeanLCAExactChallenge.Infinity.MarkedRelativeLifting
import LeanLCAExactChallenge.Infinity.ThickSimplexFiltration
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.RankNat
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.UnionProd

/-! # Parameterized extension of equivalence edges -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.MonoidalCategory Opposite Simplicial

/-- The pairing core for the product of a special left outer horn with a standard boundary. -/
noncomputable abbrev specialOuterCore (m n : ℕ) :=
  SSet.prodStdSimplex.pairingCore (0 : Fin (m + 2)) n

/-- The regular pairing induced by the special outer product pairing core. -/
noncomputable abbrev specialOuterPairing (m n : ℕ) :=
  (specialOuterCore m n).pairing

/-- The canonical natural-number rank function on the special outer product pairing. -/
noncomputable def specialOuterRank (m n : ℕ) :
    (specialOuterPairing.{u} m n).RankFunction ℕ :=
  (specialOuterPairing.{u} m n).rankFunction

/-- Recover the pairing-core index represented by a ranked special outer product cell. -/
noncomputable def specialOuterRankCellCore {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) : (specialOuterCore.{u} m n).ι :=
  (specialOuterCore.{u} m n).equivII.symm c.s

/-- A ranked cell and its pairing-core representative have the same horn index. -/
theorem specialOuterRank_cell_index_val {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) :
    c.index.val = ((specialOuterCore.{u} m n).index (specialOuterRankCellCore c)).val := by
  let core := specialOuterCore.{u} m n
  rcases c with ⟨cs, hcs⟩
  obtain ⟨s, rfl⟩ := core.equivII.surjective cs
  let c' : (specialOuterRank.{u} m n).Cell r := ⟨core.equivII s, hcs⟩
  change c'.index.val = (core.index (core.equivII.symm (core.equivII s))).val
  rw [core.equivII.symm_apply_apply]
  dsimp only [c', SSet.Subcomplex.Pairing.RankFunction.Cell.index]
  convert core.isUniquelyCodimOneFace_index_coe s rfl using 1
  congr 2
  exact congrArg (fun x ↦ x.toS) (core.type₁_pairing s).symm

/-- A zero-index ranked cell is represented by a zero-index pairing-core cell. -/
theorem specialOuterRank_cell_core_index_zero {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (h : c.index = 0) :
    (specialOuterCore.{u} m n).index (specialOuterRankCellCore c) = 0 := by
  apply Fin.ext
  have hv := specialOuterRank_cell_index_val c
  have hzero := congrArg Fin.val h
  simp only [Fin.val_zero] at hzero ⊢
  omega

/-- A zero-index cell has positive dimension because its walk reaches the second later column. -/
theorem specialOuterCore_dim_pos {m n : ℕ} (s : (specialOuterCore.{u} m n).ι)
    (h : (specialOuterCore.{u} m n).index s = 0) : 0 < (specialOuterCore.{u} m n).dim s := by
  have hsindex : s.index = 0 := by
    apply Fin.ext
    have hv := congrArg Fin.val h
    change s.index.castSucc.val = 0 at hv
    simpa using hv
  by_contra hd
  have hdzero : s.d = 0 := Nat.eq_zero_of_not_pos hd
  let i₂ : Fin (m + 3) := ⟨2, by omega⟩
  have hi₂ : i₂ ≠ (0 : Fin (m + 3)) := by
    intro hi
    have := congrArg Fin.val hi
    simp [i₂] at this
  obtain ⟨j, hj⟩ := SSet.prodStdSimplex.pairingCore.mem_range_left s.x s.hd i₂ hi₂
  have hfirst := s.isIndex.simplex_fst_castSucc
  have hsecond := s.isIndex.simplex_fst_succ
  have hjlt : j.val < 2 := by
    have hjlt' := j.isLt
    change j.val < s.d + 2 at hjlt'
    omega
  have hjcases : j.val = 0 ∨ j.val = 1 := by omega
  rcases hjcases with hjzero | hjone
  · have hjeq : j = s.index.castSucc := by
      apply Fin.ext
      rw [hsindex]
      exact hjzero
    rw [hjeq, hfirst] at hj
    have := congrArg Fin.val hj
    simp [i₂] at this
  · have hjeq : j = s.index.succ := by
      apply Fin.ext
      rw [hsindex]
      exact hjone
    rw [hjeq, hsecond] at hj
    have := congrArg Fin.val hj
    simp [i₂] at this

/-- No cell in the special outer product pairing has final horn index. -/
theorem specialOuterRank_cell_index_ne_last (m n r : ℕ)
    (c : (specialOuterRank.{u} m n).Cell r) :
    c.index ≠ Fin.last (c.dim + 1) := by
  let core := specialOuterCore.{u} m n
  let s := specialOuterRankCellCore c
  intro h
  have hindex := specialOuterRank_cell_index_val c
  have hlt : (core.index s).val < c.dim + 1 := by
    have hs : core.equivII s = c.s := core.equivII.apply_symm_apply c.s
    change s.index.castSucc.val < c.s.val.dim + 1
    rw [← hs]
    exact s.index.isLt
  have hlast := congrArg Fin.val h
  simp only [Fin.val_last] at hlast
  have hx : (core.index s).val = c.dim + 1 := hindex.symm.trans hlast
  omega

/-- The edge on the first two vertices of a positive-dimensional standard simplex. -/
def stdSimplexLeadingEdge (d : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[d + 1] :=
  SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.mkHom
      { toFun := fun i ↦ ⟨i.val, by omega⟩
        monotone' := fun _ _ h ↦ h }))

/-- The constant one-simplex at a vertex of a standard simplex. -/
def stdSimplexConstantOneSimplex (n : ℕ) (t : Fin (n + 1)) :
    (Δ[n] : SSet.{u}) _⦋1⦌ :=
  SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.mkHom
      { toFun := fun _ ↦ t
        monotone' := fun _ _ _ ↦ le_refl t })

/-- The leading edge in a special outer horn product at a parameter vertex. -/
def specialOuterProductLeadingEdge (m n : ℕ) (t : Fin (n + 1)) :
    (Δ[1] : SSet.{u}) ⟶ (Δ[m + 2] : SSet.{u}) ⊗ (Δ[n] : SSet.{u}) :=
  SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (stdSimplexEdgeZeroOne m), stdSimplexConstantOneSimplex n t)

/-- The leading product edge factors through the union of the horn and boundary products. -/
def specialOuterUnionProdLeadingEdge (m n : ℕ) (t : Fin (n + 1)) :
    (Δ[1] : SSet.{u}) ⟶
      (SSet.Subcomplex.unionProd.{u} Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n] : SSet.{u}) :=
  SSet.Subcomplex.lift (specialOuterProductLeadingEdge m n t) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    change (SSet.yonedaEquiv (stdSimplexEdgeZeroOne m),
      stdSimplexConstantOneSimplex n t) ∈
        (SSet.Subcomplex.unionProd.{u} Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n]).obj
          (op ⦋1⦌)
    apply (SSet.Subcomplex.mem_unionProd_iff
      (S := SSet.horn (m + 2) (0 : Fin (m + 3))) (T := SSet.boundary n) _).2
    apply Or.inr
    change SSet.yonedaEquiv (stdSimplexEdgeZeroOne m) ∈
      (SSet.horn (m + 2) (0 : Fin (m + 3))).obj (op ⦋1⦌)
    apply (SSet.mem_horn_iff_notMem_range _ 0).2
    refine ⟨Fin.last (m + 2), by simp, ?_⟩
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val = m + 2 at hv
    omega)

/-- The parameter vertex at the start of a special outer product pairing cell. -/
def specialOuterCoreParameterVertex {m n : ℕ} (s : (specialOuterCore.{u} m n).ι) :
    Fin (n + 1) :=
  (s.x.cast s.hd).simplex.2 0

/-- The simplex map represented by a special outer product pairing-core cell. -/
def specialOuterCoreSimplexMap {m n : ℕ} (s : (specialOuterCore.{u} m n).ι) :
    (Δ[s.d + 1] : SSet.{u}) ⟶ (Δ[m + 2] : SSet.{u}) ⊗ (Δ[n] : SSet.{u}) :=
  SSet.yonedaEquiv.symm (s.x.cast s.hd).simplex

/-- A zero-index cell begins with the first-factor edge and stays constant in the parameter. -/
theorem specialOuterCore_leadingEdge {m n : ℕ} (s : (specialOuterCore.{u} m n).ι)
    (h : (specialOuterCore.{u} m n).index s = 0) :
    stdSimplexLeadingEdge s.d ≫ specialOuterCoreSimplexMap s =
      specialOuterProductLeadingEdge m n (specialOuterCoreParameterVertex s) := by
  have hsindex : s.index = 0 := by
    apply Fin.ext
    have hv := congrArg Fin.val h
    change s.index.castSucc.val = 0 at hv
    simpa using hv
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, specialOuterCoreSimplexMap,
    specialOuterProductLeadingEdge, Equiv.apply_symm_apply]
  rw [stdSimplexLeadingEdge, Equiv.apply_symm_apply,
    SSet.yonedaEquiv_symm_app_objEquiv_symm]
  apply SSet.prodStdSimplex.objEquiv.injective
  rw [← SSet.prodStdSimplex.objEquiv_naturality]
  apply OrderHom.ext
  funext i
  fin_cases i
  · apply Prod.ext
    · change (s.x.cast s.hd).simplex.1 0 = 0
      have hfirst := s.isIndex.simplex_fst_castSucc
      rw [hsindex] at hfirst
      exact hfirst
    · rfl
  · apply Prod.ext
    · change (s.x.cast s.hd).simplex.1 1 = 1
      have hsecond := s.isIndex.simplex_fst_succ
      rw [hsindex] at hsecond
      exact hsecond
    · change (s.x.cast s.hd).simplex.2 1 = (s.x.cast s.hd).simplex.2 0
      have hsecond := s.isIndex.simplex_snd_succ
      rw [hsindex] at hsecond
      exact hsecond

@[reassoc]
theorem specialOuterUnionProdLeadingEdge_ι (m n : ℕ) (t : Fin (n + 1)) :
    specialOuterUnionProdLeadingEdge m n t ≫
        (SSet.Subcomplex.unionProd.{u} Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n]).ι =
      specialOuterProductLeadingEdge m n t := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem specialOuterUnionProdLeadingEdge_filtrationZeroIso_inv_ι
    (m n : ℕ) (t : Fin (n + 1)) :
    specialOuterUnionProdLeadingEdge m n t ≫
        (specialOuterRank.{u} m n).filtrationZeroIso.inv ≫
        ((specialOuterRank.{u} m n).filtration 0).ι =
      specialOuterProductLeadingEdge m n t := by
  rw [(specialOuterRank.{u} m n).filtrationZeroIso_inv_ι]
  exact specialOuterUnionProdLeadingEdge_ι m n t

set_option backward.isDefEq.respectTransparency false in
theorem specialOuterRank_cell_leadingEdge {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (h : c.index = 0) :
    stdSimplexLeadingEdge c.dim ≫ c.map =
      specialOuterProductLeadingEdge m n
        (specialOuterCoreParameterVertex (specialOuterRankCellCore c)) := by
  let core := specialOuterCore.{u} m n
  rcases c with ⟨cs, hcs⟩
  obtain ⟨s, rfl⟩ := core.equivII.surjective cs
  dsimp only [core] at *
  simp only [specialOuterRankCellCore, Equiv.symm_apply_apply]
  have hindex' := specialOuterRank_cell_core_index_zero
    ({ s := (specialOuterCore.{u} m n).equivII s, rank_s := hcs }) h
  change ((specialOuterCore.{u} m n).equivII.symm
    ((specialOuterCore.{u} m n).equivII s)).index.castSucc = 0 at hindex'
  rw [Equiv.symm_apply_apply] at hindex'
  have hindex : (specialOuterCore.{u} m n).index s = 0 := hindex'
  rw [← specialOuterCore_leadingEdge s hindex]
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, stdSimplexLeadingEdge,
    specialOuterCoreSimplexMap, Equiv.apply_symm_apply]
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm,
    SSet.yonedaEquiv_symm_app_objEquiv_symm]
  congr 1
  have hp :
      ((specialOuterPairing.{u} m n).p
        ((specialOuterCore.{u} m n).equivII s)).val = s.x := by
    rw [← (specialOuterCore.{u} m n).type₁_pairing s]
    exact SSet.prodStdSimplex.type₁_pairingCore (0 : Fin (m + 2)) s
  have hcast :
      ((specialOuterPairing.{u} m n).p
          ((specialOuterCore.{u} m n).equivII s)).val.cast
            ((specialOuterPairing.{u} m n).dim_p
              ((specialOuterCore.{u} m n).equivII s)) =
        s.x.cast s.hd := by
    rw [SSet.Subcomplex.N.cast_eq_self, SSet.Subcomplex.N.cast_eq_self, hp]
  rw [← SSet.S.ext_iff]
  exact congrArg (fun z ↦ z.toS) hcast

theorem specialOuterRank_cell_dim {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) :
    c.dim = (specialOuterRankCellCore c).d := by
  let core := specialOuterCore.{u} m n
  let s := specialOuterRankCellCore c
  have hs : core.equivII s = c.s := core.equivII.apply_symm_apply c.s
  calc
    c.dim = c.s.val.dim := rfl
    _ = (core.equivII s).val.dim := by rw [hs]
    _ = (core.type₂ s).dim := by rw [core.equivII_apply_coe]
    _ = s.d := rfl

/-- The leading edge corestricted to a positive-dimensional zero-index ranked cell horn. -/
def specialOuterRankCellLeadingEdge {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) : (Δ[1] : SSet.{u}) ⟶ c.horn :=
  SSet.Subcomplex.lift (stdSimplexLeadingEdge c.dim) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    change SSet.yonedaEquiv (stdSimplexLeadingEdge c.dim) ∈
      (SSet.horn (c.dim + 1) c.index).obj (op ⦋1⦌)
    apply (SSet.mem_horn_iff_notMem_range _ c.index).2
    refine ⟨Fin.last (c.dim + 1), ?_, ?_⟩
    · rw [hindex]
      simp
    · rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      change i.val = c.dim + 1 at hv
      omega)

@[reassoc]
theorem specialOuterRankCellLeadingEdge_ι {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) :
    specialOuterRankCellLeadingEdge c hindex hdim ≫ c.horn.ι =
      stdSimplexLeadingEdge c.dim := rfl

@[reassoc]
theorem specialOuterRankCellLeadingEdge_map {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) :
    specialOuterRankCellLeadingEdge c hindex hdim ≫ c.horn.ι ≫ c.map =
      specialOuterProductLeadingEdge m n
        (specialOuterCoreParameterVertex (specialOuterRankCellCore c)) := by
  rw [← Category.assoc, specialOuterRankCellLeadingEdge_ι]
  exact specialOuterRank_cell_leadingEdge c hindex

@[reassoc]
theorem specialOuterRankCellLeadingEdge_mapHorn_ι {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) :
    specialOuterRankCellLeadingEdge c hindex hdim ≫ c.mapHorn ≫
        ((specialOuterRank.{u} m n).filtration r).ι =
      specialOuterProductLeadingEdge m n
        (specialOuterCoreParameterVertex (specialOuterRankCellCore c)) := by
  rw [c.mapHorn_ι]
  simpa only [Category.assoc] using
    specialOuterRankCellLeadingEdge_map c hindex hdim

set_option backward.isDefEq.respectTransparency false in
theorem specialOuterRankCellLeadingEdge_mapHorn {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) :
    specialOuterRankCellLeadingEdge c hindex hdim ≫ c.mapHorn =
      specialOuterUnionProdLeadingEdge m n
          (specialOuterCoreParameterVertex (specialOuterRankCellCore c)) ≫
        (specialOuterRank.{u} m n).filtrationZeroIso.inv ≫
        (specialOuterRank.{u} m n).filtrationMap (Nat.zero_le r) := by
  apply (cancel_mono ((specialOuterRank.{u} m n).filtration r).ι).1
  simpa only [Category.assoc,
    (specialOuterRank.{u} m n).filtrationMap_ι,
    specialOuterUnionProdLeadingEdge_filtrationZeroIso_inv_ι] using
    specialOuterRankCellLeadingEdge_mapHorn_ι c hindex hdim

set_option backward.isDefEq.respectTransparency false in
def zeroIndexHornLeadingEdge (d : ℕ) (hdim : 0 < d) :
    (Δ[1] : SSet.{u}) ⟶ Λ[d + 1, (0 : Fin (d + 2))] :=
  SSet.Subcomplex.lift (stdSimplexLeadingEdge d) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    apply (SSet.mem_horn_iff_notMem_range _ 0).2
    refine ⟨Fin.last (d + 1), by simp, ?_⟩
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change i.val = d + 1 at hv
    omega)

@[reassoc]
theorem zeroIndexHornLeadingEdge_ι (d : ℕ) (hdim : 0 < d) :
    zeroIndexHornLeadingEdge d hdim ≫
        (SSet.horn (d + 1) (0 : Fin (d + 2))).ι =
      stdSimplexLeadingEdge d := rfl

theorem zeroIndexHornLeadingEdge_succ (k : ℕ) :
    zeroIndexHornLeadingEdge (k + 1) (by omega) =
      specialLeftHornLeadingEdge k := by
  apply (cancel_mono (SSet.horn (k + 2) (0 : Fin (k + 3))).ι).1
  rw [zeroIndexHornLeadingEdge_ι]
  rfl

theorem fillPositiveZeroIndexHorn
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (hQ : HasAllSpecialLeftHornFillers Q) (d : ℕ) (hdim : 0 < d)
    (a : (Λ[d + 1, (0 : Fin (d + 2))] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence (SSet.Edge.mk'
      (SSet.yonedaEquiv (zeroIndexHornLeadingEdge d hdim ≫ a)))) :
    ∃ b : (Δ[d + 1] : SSet.{u}) ⟶ Q,
      (SSet.horn (d + 1) (0 : Fin (d + 2))).ι ≫ b = a := by
  cases d with
  | zero => omega
  | succ k =>
      have hedge : zeroIndexHornLeadingEdge (k + 1) hdim =
          specialLeftHornLeadingEdge k := by
        exact zeroIndexHornLeadingEdge_succ k
      apply hQ k a
      rw [specialLeftHornEdge, ← hedge]
      exact he

noncomputable def specialOuterRankCellHornZeroIso {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0) :
    (c.horn : SSet.{u}) ≅ Λ[c.dim + 1, (0 : Fin (c.dim + 2))] :=
  SSet.Subcomplex.eqToIso (by
    dsimp only [SSet.Subcomplex.Pairing.RankFunction.Cell.horn]
    rw [hindex])

@[reassoc]
theorem specialOuterRankCellHornZeroIso_hom_ι {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0) :
    (specialOuterRankCellHornZeroIso c hindex).hom ≫
        (SSet.horn (c.dim + 1) (0 : Fin (c.dim + 2))).ι =
      c.horn.ι := rfl

@[reassoc]
theorem specialOuterRankCellHornZeroIso_inv_ι {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0) :
    (specialOuterRankCellHornZeroIso c hindex).inv ≫ c.horn.ι =
      (SSet.horn (c.dim + 1) (0 : Fin (c.dim + 2))).ι := rfl

theorem zeroIndexHornLeadingEdge_comp_cellHornZeroIso_inv {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) :
    zeroIndexHornLeadingEdge c.dim hdim ≫
        (specialOuterRankCellHornZeroIso c hindex).inv =
      specialOuterRankCellLeadingEdge c hindex hdim := by
  apply (cancel_mono c.horn.ι).1
  simp only [Category.assoc,
    specialOuterRankCellHornZeroIso_inv_ι,
    zeroIndexHornLeadingEdge_ι,
    specialOuterRankCellLeadingEdge_ι]

theorem fillZeroIndexRankedCell
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (hQ : HasAllSpecialLeftHornFillers Q) {m n r : ℕ}
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) (a : (c.horn : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence (SSet.Edge.mk'
      (SSet.yonedaEquiv
        (specialOuterRankCellLeadingEdge c hindex hdim ≫ a)))) :
    ∃ b : (Δ[c.dim + 1] : SSet.{u}) ⟶ Q, c.horn.ι ≫ b = a := by
  let e := specialOuterRankCellHornZeroIso c hindex
  let a₀ : (Λ[c.dim + 1, (0 : Fin (c.dim + 2))] : SSet.{u}) ⟶ Q := e.inv ≫ a
  have hedge : zeroIndexHornLeadingEdge c.dim hdim ≫ a₀ =
      specialOuterRankCellLeadingEdge c hindex hdim ≫ a := by
    dsimp only [a₀, e]
    rw [← Category.assoc,
      zeroIndexHornLeadingEdge_comp_cellHornZeroIso_inv]
  have he₀ : EdgeIsEquivalence (SSet.Edge.mk'
      (SSet.yonedaEquiv (zeroIndexHornLeadingEdge c.dim hdim ≫ a₀))) := by
    rw [hedge]
    exact he
  obtain ⟨b, hb⟩ := fillPositiveZeroIndexHorn hQ c.dim hdim a₀ he₀
  refine ⟨b, ?_⟩
  calc
    c.horn.ι ≫ b = e.hom ≫
        (SSet.horn (c.dim + 1) (0 : Fin (c.dim + 2))).ι ≫ b := by
      rw [← Category.assoc, specialOuterRankCellHornZeroIso_hom_ι]
    _ = e.hom ≫ a₀ := by rw [hb]
    _ = a := by simp [a₀, e]

/-- Every parameter-vertex leading edge of an initial product-boundary map is an equivalence. -/
def SpecialOuterLeadingEdgesAreEquivalences
    {Q : SSet.{u}} (m n : ℕ)
    (a : (SSet.Subcomplex.unionProd.{u}
      Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n] : SSet.{u}) ⟶ Q) : Prop :=
  ∀ t : Fin (n + 1), EdgeIsEquivalence (SSet.Edge.mk'
    (SSet.yonedaEquiv (specialOuterUnionProdLeadingEdge m n t ≫ a)))

theorem specialOuterRankCellLeadingEdge_mapHorn_isEquivalence
    {Q : SSet.{u}} {m n r : ℕ}
    (a : (SSet.Subcomplex.unionProd.{u}
      Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n] : SSet.{u}) ⟶ Q)
    (ha : SpecialOuterLeadingEdgesAreEquivalences m n a)
    (g : ((specialOuterRank.{u} m n).filtration r : SSet.{u}) ⟶ Q)
    (hg : (specialOuterRank.{u} m n).filtrationMap (Nat.zero_le r) ≫ g =
      (specialOuterRank.{u} m n).initialMap a)
    (c : (specialOuterRank.{u} m n).Cell r) (hindex : c.index = 0)
    (hdim : 0 < c.dim) :
    EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
      (specialOuterRankCellLeadingEdge c hindex hdim ≫ c.mapHorn ≫ g))) := by
  let t := specialOuterCoreParameterVertex (specialOuterRankCellCore c)
  have hedge : specialOuterRankCellLeadingEdge c hindex hdim ≫ c.mapHorn ≫ g =
      specialOuterUnionProdLeadingEdge m n t ≫ a := by
    rw [← Category.assoc,
      specialOuterRankCellLeadingEdge_mapHorn]
    simp only [Category.assoc, hg]
    exact congrArg (fun z ↦ specialOuterUnionProdLeadingEdge m n t ≫ z)
      ((specialOuterRank.{u} m n).filtrationZeroIso_inv_initialMap a)
  rw [hedge]
  exact ha t

theorem specialOuterRank_hasFixedCellFillers
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (hQ : HasAllSpecialLeftHornFillers Q) (m n : ℕ)
    (a : (SSet.Subcomplex.unionProd.{u}
      Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n] : SSet.{u}) ⟶ Q)
    (ha : SpecialOuterLeadingEdgesAreEquivalences m n a) :
    (specialOuterRank.{u} m n).HasFixedCellFillers
      ((specialOuterRank.{u} m n).initialMap a) := by
  apply (specialOuterRank.{u} m n).hasFixedCellFillers_of_zero_and_inner
    ((specialOuterRank.{u} m n).initialMap a)
    (specialOuterRank_cell_index_ne_last m n)
  intro r g hg c hindex
  have hdim : 0 < c.dim := by
    rw [specialOuterRank_cell_dim]
    exact specialOuterCore_dim_pos (specialOuterRankCellCore c)
      (specialOuterRank_cell_core_index_zero c hindex)
  apply fillZeroIndexRankedCell hQ c hindex hdim (c.mapHorn ≫ g)
  exact specialOuterRankCellLeadingEdge_mapHorn_isEquivalence
    a ha g hg c hindex hdim

/-- Extend a special-left-outer-horn product boundary along equivalence parameter edges. -/
noncomputable def specialOuterParameterizedExtension
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (hQ : HasAllSpecialLeftHornFillers Q) (m n : ℕ)
    (a : (SSet.Subcomplex.unionProd.{u}
      Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n] : SSet.{u}) ⟶ Q)
    (ha : SpecialOuterLeadingEdgesAreEquivalences m n a) :
    (Δ[m + 2] : SSet.{u}) ⊗ (Δ[n] : SSet.{u}) ⟶ Q :=
  (specialOuterRank.{u} m n).extensionFromInitial a
    (specialOuterRank_hasFixedCellFillers hQ m n a ha)

@[reassoc]
theorem specialOuterParameterizedExtension_restrict
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (hQ : HasAllSpecialLeftHornFillers Q) (m n : ℕ)
    (a : (SSet.Subcomplex.unionProd.{u}
      Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n] : SSet.{u}) ⟶ Q)
    (ha : SpecialOuterLeadingEdgesAreEquivalences m n a) :
    (SSet.Subcomplex.unionProd.{u}
        Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n]).ι ≫
      specialOuterParameterizedExtension hQ m n a ha = a :=
  (specialOuterRank.{u} m n).extensionFromInitial_restrict a
    (specialOuterRank_hasFixedCellFillers hQ m n a ha)

/-- Parameterized special-left-outer-horn filling against every standard boundary. -/
def HasParameterizedSpecialLeftHornFillers (Q : SSet.{u}) : Prop :=
  ∀ (m n : ℕ)
    (a : (SSet.Subcomplex.unionProd.{u}
      Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n] : SSet.{u}) ⟶ Q),
    SpecialOuterLeadingEdgesAreEquivalences m n a →
      ∃ b : (Δ[m + 2] : SSet.{u}) ⊗ (Δ[n] : SSet.{u}) ⟶ Q,
        (SSet.Subcomplex.unionProd.{u}
          Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n]).ι ≫ b = a

/-- All-dimensional special-left-horn fillers imply their boundary-parameterized form. -/
theorem hasParameterizedSpecialLeftHornFillers_of_specialLeftHornFillers
    (Q : SSet.{u}) [SSet.Quasicategory Q]
    (hQ : HasAllSpecialLeftHornFillers Q) :
    HasParameterizedSpecialLeftHornFillers Q := by
  intro m n a ha
  exact ⟨specialOuterParameterizedExtension hQ m n a ha,
    specialOuterParameterizedExtension_restrict hQ m n a ha⟩

@[reassoc]
theorem specialLeftHornLeadingEdge_ι (m : ℕ) :
    specialLeftHornLeadingEdge m ≫
        (SSet.horn (m + 2) (0 : Fin (m + 3))).ι =
      stdSimplexLeadingEdge (m + 1) := rfl

def edgeAtParameterVertex {K : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ K) (n : ℕ) (t : Fin (n + 1)) :
    (Δ[1] : SSet.{u}) ⟶ K ⊗ (Δ[n] : SSet.{u}) :=
  SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv e, stdSimplexConstantOneSimplex n t)

@[reassoc]
theorem edgeAtParameterVertex_naturality {K L : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ K) (f : K ⟶ L)
    (n : ℕ) (t : Fin (n + 1)) :
    edgeAtParameterVertex e n t ≫ (f ▷ (Δ[n] : SSet.{u})) =
      edgeAtParameterVertex (e ≫ f) n t := by
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, edgeAtParameterVertex,
    Equiv.apply_symm_apply]
  rfl

theorem specialOuterProductLeadingEdge_eq_edgeAtParameterVertex
    (m n : ℕ) (t : Fin (n + 1)) :
    specialOuterProductLeadingEdge m n t =
      edgeAtParameterVertex (stdSimplexEdgeZeroOne m) n t := rfl

def specialOuterHornProductLeadingEdge
    (m n : ℕ) (t : Fin (n + 1)) :
    (Δ[1] : SSet.{u}) ⟶
      (Λ[m + 2, (0 : Fin (m + 3))] : SSet.{u}) ⊗ (Δ[n] : SSet.{u}) :=
  edgeAtParameterVertex (specialLeftHornLeadingEdge m) n t

@[reassoc]
theorem specialOuterHornProductLeadingEdge_unionProd_ι₂
    (m n : ℕ) (t : Fin (n + 1)) :
    specialOuterHornProductLeadingEdge m n t ≫
        SSet.Subcomplex.unionProd.ι₂
          (SSet.horn (m + 2) (0 : Fin (m + 3))) (SSet.boundary n) =
      specialOuterUnionProdLeadingEdge.{u} m n t := by
  apply (cancel_mono
    (SSet.Subcomplex.unionProd.{u} Λ[m + 2, (0 : Fin (m + 3))] ∂Δ[n]).ι).1
  rw [Category.assoc, SSet.Subcomplex.unionProd.ι₂_ι]
  rw [specialOuterUnionProdLeadingEdge_ι]
  change edgeAtParameterVertex (specialLeftHornLeadingEdge m) n t ≫
      ((SSet.horn (m + 2) (0 : Fin (m + 3))).ι ▷ (Δ[n] : SSet.{u})) = _
  rw [edgeAtParameterVertex_naturality]
  rw [specialLeftHornLeadingEdge_ι]
  rfl

def parameterVertexMap (n : ℕ) (t : Fin (n + 1)) :
    𝟙_ SSet.{u} ⟶ Δ[n] :=
  (SSet.unitHomEquiv (Δ[n] : SSet.{u})).symm
    (SSet.stdSimplex.obj₀Equiv.symm t)

theorem parameterizedUnitHomEquiv_symm_natural {A B : SSet.{u}}
    (F : A ⟶ B) (a : A _⦋0⦌) :
    (SSet.unitHomEquiv B).symm (F.app _ a) =
      (SSet.unitHomEquiv A).symm a ≫ F := by
  ext U x
  obtain ⟨⟩ := x
  dsimp [SSet.unitHomEquiv]
  rw [← NatTrans.naturality_apply]

theorem edgeAtParameterVertex_id_factor
    (n : ℕ) (t : Fin (n + 1)) :
    edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) n t =
      (ρ_ (Δ[1] : SSet.{u})).inv ≫
        ((Δ[1] : SSet.{u}) ◁ parameterVertexMap n t) := by
  apply SSet.yonedaEquiv.injective
  simp only [edgeAtParameterVertex, Equiv.apply_symm_apply,
    SSet.yonedaEquiv_comp]
  rfl

set_option maxHeartbeats 800000 in
-- Normalizing the tensor/closed adjunction expression requires a larger reduction budget.
theorem internalHomVertexMap_parameter
    {Q : SSet.{u}} (n : ℕ)
    (g : (Δ[n] : SSet.{u}) ⟶ (ihom (Δ[1] : SSet.{u})).obj Q)
    (t : Fin (n + 1)) :
    internalHomVertexMap (Δ[1] : SSet.{u}) Q
        (g.app _ (SSet.stdSimplex.obj₀Equiv.symm t)) =
      edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) n t ≫
        MonoidalClosed.uncurry g := by
  unfold internalHomVertexMap MonoidalClosed.uncurry'
  rw [parameterizedUnitHomEquiv_symm_natural]
  change (ρ_ (Δ[1] : SSet.{u})).inv ≫
      MonoidalClosed.uncurry (parameterVertexMap n t ≫ g) = _
  rw [MonoidalClosed.uncurry_natural_left]
  calc
    _ = ((ρ_ (Δ[1] : SSet.{u})).inv ≫
          ((Δ[1] : SSet.{u}) ◁ parameterVertexMap n t)) ≫
        MonoidalClosed.uncurry g := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z ↦ z ≫ MonoidalClosed.uncurry g)
      (edgeAtParameterVertex_id_factor n t).symm

theorem equivalenceEdgeFamily_parameter_isEquivalence
    {Q : SSet.{u}} (n : ℕ)
    (g : (Δ[n] : SSet.{u}) ⟶ (equivalenceEdgeInternalHom Q : SSet.{u}))
    (t : Fin (n + 1)) :
    EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
      (edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) n t ≫
        MonoidalClosed.uncurry (g ≫ (equivalenceEdgeInternalHom Q).ι)))) := by
  let x := SSet.stdSimplex.obj₀Equiv.symm t
  let v := g.app (op ⦋0⦌) x
  have hv := v.property (0 : Fin 1)
  change EdgeIsEquivalence (SSet.Edge.mk'
    (SSet.yonedaEquiv (internalHomVertexMap (Δ[1] : SSet.{u}) Q
      (((g ≫ (equivalenceEdgeInternalHom Q).ι).app (op ⦋0⦌)) x)))) at hv
  rw [internalHomVertexMap_parameter] at hv
  exact hv

structure ParameterizedAlternatingProblem
    (Q : SSet.{u}) (d : ℕ) where
  boundaryMap :
    CategoryTheory.nerve EquivalenceInterval.{u} ⊗
      (SSet.boundary d : SSet.{u}) ⟶ Q
  initialMap : (Δ[1] : SSet.{u}) ⊗ (Δ[d] : SSet.{u}) ⟶ Q
  compatibility :
    ((Δ[1] : SSet.{u}) ◁ (SSet.boundary d).ι) ≫ initialMap =
      (equivalenceIntervalInclusion.{u} ▷ (SSet.boundary d : SSet.{u})) ≫ boundaryMap
  leadingEquivalence : ∀ t : Fin (d + 1),
    EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
      (edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) d t ≫ initialMap)))

namespace ParameterizedAlternatingProblem

variable {Q : SSet.{u}} {d : ℕ} (P : ParameterizedAlternatingProblem Q d)

def firstStageMap :
    (alternatingEquivalenceSubcomplex 1 : SSet.{u}) ⊗ (Δ[d] : SSet.{u}) ⟶ Q :=
  (alternatingEquivalenceFirstStageIso.{u}.inv ▷ (Δ[d] : SSet.{u})) ≫ P.initialMap

@[reassoc]
theorem firstStageMap_boundary :
    ((alternatingEquivalenceSubcomplex 1 : SSet.{u}) ◁ (SSet.boundary d).ι) ≫
        P.firstStageMap =
      ((alternatingEquivalenceSubcomplex 1).ι ▷ (SSet.boundary d : SSet.{u})) ≫
        P.boundaryMap := by
  change ((alternatingEquivalenceSubcomplex 1 : SSet.{u}) ◁
      (SSet.boundary d).ι) ≫
        (alternatingEquivalenceFirstStageIso.{u}.inv ▷ (Δ[d] : SSet.{u})) ≫
          P.initialMap = _
  calc
    _ = (alternatingEquivalenceFirstStageIso.{u}.inv ▷
          (SSet.boundary d : SSet.{u})) ≫
        ((Δ[1] : SSet.{u}) ◁ (SSet.boundary d).ι) ≫ P.initialMap :=
      whisker_exchange_assoc _ _ _
    _ = (alternatingEquivalenceFirstStageIso.{u}.inv ▷
          (SSet.boundary d : SSet.{u})) ≫
        (equivalenceIntervalInclusion.{u} ▷ (SSet.boundary d : SSet.{u})) ≫
          P.boundaryMap := by rw [P.compatibility]
    _ = ((alternatingEquivalenceSubcomplex 1).ι ▷
          (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap := by
      have hinv : alternatingEquivalenceFirstStageIso.{u}.inv ≫
          equivalenceIntervalInclusion.{u} =
        (alternatingEquivalenceSubcomplex 1).ι := by
        calc
          _ = alternatingEquivalenceFirstStageIso.inv ≫
              alternatingEquivalenceFirstStageIso.hom ≫
                alternatingEquivalenceFiltrationInclusion :=
            congrArg (fun z ↦ alternatingEquivalenceFirstStageIso.inv ≫ z)
              alternatingEquivalenceFirstStageIso_hom_comp_inclusion.symm
          _ = alternatingEquivalenceFiltrationInclusion :=
            Iso.inv_hom_id_assoc _ _
      let F := MonoidalCategory.tensorRight (SSet.boundary d : SSet.{u})
      have htensor :
          (alternatingEquivalenceFirstStageIso.{u}.inv ▷
              (SSet.boundary d : SSet.{u})) ≫
            (equivalenceIntervalInclusion.{u} ▷ (SSet.boundary d : SSet.{u})) =
          ((alternatingEquivalenceSubcomplex 1).ι ▷
            (SSet.boundary d : SSet.{u})) := by
        calc
          _ = F.map (alternatingEquivalenceFirstStageIso.inv ≫
              equivalenceIntervalInclusion) :=
            (F.map_comp _ _).symm
          _ = F.map (alternatingEquivalenceSubcomplex 1).ι := congrArg F.map hinv
          _ = _ := rfl
      exact congrArg (fun z ↦ z ≫ P.boundaryMap) htensor

structure State (s : ℕ) where
  map : (alternatingEquivalenceSubcomplex (s + 1) : SSet.{u}) ⊗
    (Δ[d] : SSet.{u}) ⟶ Q
  boundary :
    ((alternatingEquivalenceSubcomplex (s + 1) : SSet.{u}) ◁
        (SSet.boundary d).ι) ≫ map =
      ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
        (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap
  initial :
    (alternatingFiltrationMap (Nat.zero_le s) ▷ (Δ[d] : SSet.{u})) ≫ map =
      P.firstStageMap

def initialState : P.State 0 where
  map := P.firstStageMap
  boundary := P.firstStageMap_boundary
  initial := by simp [alternatingFiltrationMap]

def cellBoundaryMap (s : ℕ) :
    (Δ[s + 2] : SSet.{u}) ⊗ (SSet.boundary d : SSet.{u}) ⟶ Q :=
  (alternatingEquivalenceSimplexMap (s + 2) ▷
      (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap

def cellHornMap {s : ℕ} (state : P.State s) :
    (Λ[s + 2, (0 : Fin (s + 3))] : SSet.{u}) ⊗ (Δ[d] : SSet.{u}) ⟶ Q :=
  (alternatingHornToSubcomplex (s + 1) ▷ (Δ[d] : SSet.{u})) ≫ state.map

theorem cellCompatibility {s : ℕ} (state : P.State s) :
    ((SSet.horn (s + 2) (0 : Fin (s + 3))).ι ▷
        (SSet.boundary d : SSet.{u})) ≫ P.cellBoundaryMap s =
      ((SSet.horn (s + 2) (0 : Fin (s + 3)) : SSet.{u}) ◁
        (SSet.boundary d).ι) ≫ P.cellHornMap state := by
  let F := MonoidalCategory.tensorRight (SSet.boundary d : SSet.{u})
  have hstage := alternatingHornToSubcomplex_ι (s + 1)
  have hmap :
      ((SSet.horn (s + 2) (0 : Fin (s + 3))).ι ▷
          (SSet.boundary d : SSet.{u})) ≫
        (alternatingEquivalenceSimplexMap (s + 2) ▷
          (SSet.boundary d : SSet.{u})) =
      (alternatingHornToSubcomplex (s + 1) ▷
          (SSet.boundary d : SSet.{u})) ≫
        ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
          (SSet.boundary d : SSet.{u})) := by
    calc
      _ = F.map ((SSet.horn (s + 2) (0 : Fin (s + 3))).ι ≫
          alternatingEquivalenceSimplexMap (s + 2)) := (F.map_comp _ _).symm
      _ = F.map (alternatingHornToSubcomplex (s + 1) ≫
          (alternatingEquivalenceSubcomplex (s + 1)).ι) := congrArg F.map hstage.symm
      _ = _ := F.map_comp _ _
  unfold cellBoundaryMap cellHornMap
  calc
    _ = ((alternatingHornToSubcomplex (s + 1) ▷
            (SSet.boundary d : SSet.{u})) ≫
          ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
            (SSet.boundary d : SSet.{u}))) ≫ P.boundaryMap :=
      congrArg (fun z ↦ z ≫ P.boundaryMap) hmap
    _ = (alternatingHornToSubcomplex (s + 1) ▷
          (SSet.boundary d : SSet.{u})) ≫
        (((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
          (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap) :=
      Category.assoc _ _ _
    _ = (alternatingHornToSubcomplex (s + 1) ▷
          (SSet.boundary d : SSet.{u})) ≫
        (((alternatingEquivalenceSubcomplex (s + 1) : SSet.{u}) ◁
          (SSet.boundary d).ι) ≫ state.map) :=
      congrArg (fun z ↦ (alternatingHornToSubcomplex (s + 1) ▷
        (SSet.boundary d : SSet.{u})) ≫ z) state.boundary.symm
    _ = ((SSet.horn (s + 2) (0 : Fin (s + 3)) : SSet.{u}) ◁
          (SSet.boundary d).ι) ≫
        (alternatingHornToSubcomplex (s + 1) ▷ (Δ[d] : SSet.{u})) ≫
          state.map :=
      (whisker_exchange_assoc _ _ _).symm

noncomputable def cellUnionMap {s : ℕ} (state : P.State s) :
    (SSet.Subcomplex.unionProd.{u}
      Λ[s + 2, (0 : Fin (s + 3))] ∂Δ[d] : SSet.{u}) ⟶ Q :=
  (SSet.Subcomplex.unionProd.isPushout
    (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d)).desc
      (P.cellBoundaryMap s) (P.cellHornMap state) (P.cellCompatibility state)

@[reassoc]
theorem unionProd_ι₁_cellUnionMap {s : ℕ} (state : P.State s) :
    SSet.Subcomplex.unionProd.ι₁
        (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d) ≫
      P.cellUnionMap state = P.cellBoundaryMap s :=
  (SSet.Subcomplex.unionProd.isPushout
    (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d)).inl_desc _ _ _

@[reassoc]
theorem unionProd_ι₂_cellUnionMap {s : ℕ} (state : P.State s) :
    SSet.Subcomplex.unionProd.ι₂
        (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d) ≫
      P.cellUnionMap state = P.cellHornMap state :=
  (SSet.Subcomplex.unionProd.isPushout
    (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d)).inr_desc _ _ _

theorem hornProductLeadingEdge_cellHornMap {s : ℕ} (state : P.State s)
    (t : Fin (d + 1)) :
    specialOuterHornProductLeadingEdge s d t ≫ P.cellHornMap state =
      edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) d t ≫ P.initialMap := by
  have hcancel : alternatingSimplexToSubcomplex 1 ≫
      alternatingEquivalenceFirstStageIso.{u}.inv = 𝟙 (Δ[1] : SSet.{u}) := by
    change alternatingEquivalenceFirstStageIso.hom ≫
      alternatingEquivalenceFirstStageIso.inv = _
    simp
  calc
    _ = edgeAtParameterVertex
          (specialLeftHornLeadingEdge s ≫ alternatingHornToSubcomplex (s + 1))
          d t ≫ state.map :=
      edgeAtParameterVertex_naturality_assoc _ _ _ _ _
    _ = edgeAtParameterVertex
          (alternatingSimplexToSubcomplex 1 ≫
            alternatingFiltrationMap (Nat.zero_le s)) d t ≫ state.map :=
      congrArg (fun z ↦ edgeAtParameterVertex z d t ≫ state.map)
        (specialLeftHornLeadingEdge_comp_alternatingHornToSubcomplex s)
    _ = edgeAtParameterVertex (alternatingSimplexToSubcomplex 1) d t ≫
        ((alternatingFiltrationMap (Nat.zero_le s) ▷ (Δ[d] : SSet.{u})) ≫
          state.map) :=
      (edgeAtParameterVertex_naturality_assoc _ _ _ _ _).symm
    _ = edgeAtParameterVertex (alternatingSimplexToSubcomplex 1) d t ≫
        P.firstStageMap :=
      congrArg (fun z ↦
        edgeAtParameterVertex (alternatingSimplexToSubcomplex 1) d t ≫ z)
        state.initial
    _ = edgeAtParameterVertex
          (alternatingSimplexToSubcomplex 1 ≫
            alternatingEquivalenceFirstStageIso.inv) d t ≫ P.initialMap :=
      edgeAtParameterVertex_naturality_assoc _ _ _ _ _
    _ = _ := by rw [hcancel]

theorem cellUnionMap_leadingEdgesAreEquivalences {s : ℕ} (state : P.State s) :
    SpecialOuterLeadingEdgesAreEquivalences s d (P.cellUnionMap state) := by
  intro t
  have hedge : specialOuterUnionProdLeadingEdge s d t ≫ P.cellUnionMap state =
      edgeAtParameterVertex (𝟙 (Δ[1] : SSet.{u})) d t ≫ P.initialMap := by
    rw [← specialOuterHornProductLeadingEdge_unionProd_ι₂,
      Category.assoc, P.unionProd_ι₂_cellUnionMap]
    exact P.hornProductLeadingEdge_cellHornMap state t
  rw [hedge]
  exact P.leadingEquivalence t

noncomputable def cellFiller
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    (Δ[s + 2] : SSet.{u}) ⊗ (Δ[d] : SSet.{u}) ⟶ Q :=
  Classical.choose (hQ s d (P.cellUnionMap state)
    (P.cellUnionMap_leadingEdgesAreEquivalences state))

@[reassoc]
theorem cellFiller_restrict
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    (SSet.Subcomplex.unionProd.{u}
        Λ[s + 2, (0 : Fin (s + 3))] ∂Δ[d]).ι ≫
      P.cellFiller hQ state = P.cellUnionMap state :=
  Classical.choose_spec (hQ s d (P.cellUnionMap state)
    (P.cellUnionMap_leadingEdgesAreEquivalences state))

theorem cellCompatibilityForStagePushout
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    (alternatingHornToSubcomplex (s + 1) ▷ (Δ[d] : SSet.{u})) ≫ state.map =
      ((SSet.horn (s + 2) (0 : Fin (s + 3))).ι ▷ (Δ[d] : SSet.{u})) ≫
        P.cellFiller hQ state := by
  calc
    _ = P.cellHornMap state := rfl
    _ = SSet.Subcomplex.unionProd.ι₂
          (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d) ≫
        P.cellUnionMap state := (P.unionProd_ι₂_cellUnionMap state).symm
    _ = SSet.Subcomplex.unionProd.ι₂
          (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d) ≫
        (SSet.Subcomplex.unionProd.{u}
          Λ[s + 2, (0 : Fin (s + 3))] ∂Δ[d]).ι ≫
            P.cellFiller hQ state := by rw [P.cellFiller_restrict hQ state]
    _ = ((SSet.horn (s + 2) (0 : Fin (s + 3))).ι ▷
          (Δ[d] : SSet.{u})) ≫ P.cellFiller hQ state := by
      rw [← Category.assoc, SSet.Subcomplex.unionProd.ι₂_ι]

noncomputable def nextMap
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    (alternatingEquivalenceSubcomplex (s + 2) : SSet.{u}) ⊗
      (Δ[d] : SSet.{u}) ⟶ Q :=
  ((MonoidalCategory.tensorRight (Δ[d] : SSet.{u})).map_isPushout
    (alternatingEquivalenceSubcomplex_isPushout (s + 1))).desc
      state.map (P.cellFiller hQ state) (P.cellCompatibilityForStagePushout hQ state)

@[reassoc]
theorem filtrationMap_nextMap
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    (alternatingFiltrationMap (Nat.le_succ s) ▷ (Δ[d] : SSet.{u})) ≫
      P.nextMap hQ state = state.map :=
  ((MonoidalCategory.tensorRight (Δ[d] : SSet.{u})).map_isPushout
    (alternatingEquivalenceSubcomplex_isPushout (s + 1))).inl_desc _ _ _

@[reassoc]
theorem alternatingSimplex_nextMap
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    (alternatingSimplexToSubcomplex (s + 2) ▷ (Δ[d] : SSet.{u})) ≫
      P.nextMap hQ state = P.cellFiller hQ state :=
  ((MonoidalCategory.tensorRight (Δ[d] : SSet.{u})).map_isPushout
    (alternatingEquivalenceSubcomplex_isPushout (s + 1))).inr_desc _ _ _

theorem boundary_cellFiller
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    ((Δ[s + 2] : SSet.{u}) ◁ (SSet.boundary d).ι) ≫
      P.cellFiller hQ state = P.cellBoundaryMap s := by
  calc
    _ = SSet.Subcomplex.unionProd.ι₁
          (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d) ≫
        (SSet.Subcomplex.unionProd.{u}
          Λ[s + 2, (0 : Fin (s + 3))] ∂Δ[d]).ι ≫
            P.cellFiller hQ state := by
      rw [← Category.assoc, SSet.Subcomplex.unionProd.ι₁_ι]
    _ = SSet.Subcomplex.unionProd.ι₁
          (SSet.horn (s + 2) (0 : Fin (s + 3))) (SSet.boundary d) ≫
        P.cellUnionMap state := by rw [P.cellFiller_restrict hQ state]
    _ = P.cellBoundaryMap s := P.unionProd_ι₁_cellUnionMap state

theorem nextMap_boundary
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    ((alternatingEquivalenceSubcomplex (s + 2) : SSet.{u}) ◁
        (SSet.boundary d).ι) ≫ P.nextMap hQ state =
      ((alternatingEquivalenceSubcomplex (s + 2)).ι ▷
        (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap := by
  let sq := (MonoidalCategory.tensorRight (SSet.boundary d : SSet.{u})).map_isPushout
    (alternatingEquivalenceSubcomplex_isPushout (s + 1))
  apply sq.hom_ext
  · calc
      _ = ((alternatingEquivalenceSubcomplex (s + 1) : SSet.{u}) ◁
            (SSet.boundary d).ι) ≫
          (alternatingFiltrationMap (Nat.le_succ s) ▷ (Δ[d] : SSet.{u})) ≫
            P.nextMap hQ state :=
        (whisker_exchange_assoc _ _ _).symm
      _ = ((alternatingEquivalenceSubcomplex (s + 1) : SSet.{u}) ◁
            (SSet.boundary d).ι) ≫ state.map := by
        rw [P.filtrationMap_nextMap hQ state]
      _ = ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
            (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap := state.boundary
      _ = (alternatingFiltrationMap (Nat.le_succ s) ▷
            (SSet.boundary d : SSet.{u})) ≫
          ((alternatingEquivalenceSubcomplex (s + 2)).ι ▷
            (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap := by
        let F := MonoidalCategory.tensorRight (SSet.boundary d : SSet.{u})
        have hinc : alternatingFiltrationMap (Nat.le_succ s) ≫
            (alternatingEquivalenceSubcomplex (s + 2)).ι =
          (alternatingEquivalenceSubcomplex (s + 1)).ι := rfl
        have htensor :
            (alternatingFiltrationMap (Nat.le_succ s) ▷
                (SSet.boundary d : SSet.{u})) ≫
              ((alternatingEquivalenceSubcomplex (s + 2)).ι ▷
                (SSet.boundary d : SSet.{u})) =
            ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
              (SSet.boundary d : SSet.{u})) := by
          calc
            _ = F.map (alternatingFiltrationMap (Nat.le_succ s) ≫
                (alternatingEquivalenceSubcomplex (s + 2)).ι) := (F.map_comp _ _).symm
            _ = F.map (alternatingEquivalenceSubcomplex (s + 1)).ι := congrArg F.map hinc
            _ = _ := rfl
        exact (congrArg (fun z ↦ z ≫ P.boundaryMap) htensor).symm
  · calc
      _ = ((Δ[s + 2] : SSet.{u}) ◁ (SSet.boundary d).ι) ≫
          (alternatingSimplexToSubcomplex (s + 2) ▷ (Δ[d] : SSet.{u})) ≫
            P.nextMap hQ state :=
        (whisker_exchange_assoc _ _ _).symm
      _ = ((Δ[s + 2] : SSet.{u}) ◁ (SSet.boundary d).ι) ≫
          P.cellFiller hQ state := by
        rw [P.alternatingSimplex_nextMap hQ state]
      _ = P.cellBoundaryMap s := P.boundary_cellFiller hQ state
      _ = (alternatingEquivalenceSimplexMap (s + 2) ▷
            (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap := rfl
      _ = (alternatingSimplexToSubcomplex (s + 2) ▷
            (SSet.boundary d : SSet.{u})) ≫
          ((alternatingEquivalenceSubcomplex (s + 2)).ι ▷
            (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap := by
        let F := MonoidalCategory.tensorRight (SSet.boundary d : SSet.{u})
        have htensor :
            (alternatingSimplexToSubcomplex (s + 2) ▷
                (SSet.boundary d : SSet.{u})) ≫
              ((alternatingEquivalenceSubcomplex (s + 2)).ι ▷
                (SSet.boundary d : SSet.{u})) =
            (alternatingEquivalenceSimplexMap (s + 2) ▷
              (SSet.boundary d : SSet.{u})) := by
          calc
            _ = F.map (alternatingSimplexToSubcomplex (s + 2) ≫
                (alternatingEquivalenceSubcomplex (s + 2)).ι) := (F.map_comp _ _).symm
            _ = F.map (alternatingEquivalenceSimplexMap (s + 2)) :=
              congrArg F.map (alternatingSimplexToSubcomplex_ι (s + 2))
            _ = _ := rfl
        exact (congrArg (fun z ↦ z ≫ P.boundaryMap) htensor).symm

theorem nextMap_initial
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) :
    (alternatingFiltrationMap (Nat.zero_le (s + 1)) ▷ (Δ[d] : SSet.{u})) ≫
      P.nextMap hQ state = P.firstStageMap := by
  have hcomp : alternatingFiltrationMap (Nat.zero_le s) ≫
      alternatingFiltrationMap (Nat.le_succ s) =
    alternatingFiltrationMap (Nat.zero_le (s + 1)) :=
    alternatingFiltrationMap_comp (Nat.zero_le s) (Nat.le_succ s)
  have htensorComp :
      ((alternatingFiltrationMap (Nat.zero_le s) ≫
          alternatingFiltrationMap (Nat.le_succ s)) ▷ (Δ[d] : SSet.{u})) =
        (alternatingFiltrationMap (Nat.zero_le s) ▷ (Δ[d] : SSet.{u})) ≫
          (alternatingFiltrationMap (Nat.le_succ s) ▷ (Δ[d] : SSet.{u})) :=
    (MonoidalCategory.tensorRight (Δ[d] : SSet.{u})).map_comp _ _
  calc
    _ = ((alternatingFiltrationMap (Nat.zero_le s) ≫
          alternatingFiltrationMap (Nat.le_succ s)) ▷ (Δ[d] : SSet.{u})) ≫
        P.nextMap hQ state :=
      congrArg (fun z ↦ (z ▷ (Δ[d] : SSet.{u})) ≫ P.nextMap hQ state) hcomp.symm
    _ = ((alternatingFiltrationMap (Nat.zero_le s) ▷ (Δ[d] : SSet.{u})) ≫
          (alternatingFiltrationMap (Nat.le_succ s) ▷ (Δ[d] : SSet.{u}))) ≫
        P.nextMap hQ state :=
      congrArg (fun z ↦ z ≫ P.nextMap hQ state) htensorComp
    _ = (alternatingFiltrationMap (Nat.zero_le s) ▷ (Δ[d] : SSet.{u})) ≫
        ((alternatingFiltrationMap (Nat.le_succ s) ▷ (Δ[d] : SSet.{u})) ≫
          P.nextMap hQ state) := Category.assoc _ _ _
    _ = (alternatingFiltrationMap (Nat.zero_le s) ▷ (Δ[d] : SSet.{u})) ≫
        state.map := congrArg (fun z ↦
          (alternatingFiltrationMap (Nat.zero_le s) ▷ (Δ[d] : SSet.{u})) ≫ z)
            (P.filtrationMap_nextMap hQ state)
    _ = P.firstStageMap := state.initial

noncomputable def nextState
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s : ℕ} (state : P.State s) : P.State (s + 1) where
  map := P.nextMap hQ state
  boundary := P.nextMap_boundary hQ state
  initial := P.nextMap_initial hQ state

noncomputable def state
    (hQ : HasParameterizedSpecialLeftHornFillers Q) :
    (s : ℕ) → P.State s
  | 0 => P.initialState
  | s + 1 => P.nextState hQ (state hQ s)

@[reassoc]
theorem state_step
    (hQ : HasParameterizedSpecialLeftHornFillers Q) (s : ℕ) :
    (alternatingFiltrationMap (Nat.le_succ s) ▷ (Δ[d] : SSet.{u})) ≫
      (P.state hQ (s + 1)).map = (P.state hQ s).map := by
  rw [state]
  exact P.filtrationMap_nextMap hQ (P.state hQ s)

theorem state_compat
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {s t : ℕ} (hst : s ≤ t) :
    (alternatingFiltrationMap hst ▷ (Δ[d] : SSet.{u})) ≫
      (P.state hQ t).map = (P.state hQ s).map := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
      have hcomp : alternatingFiltrationMap hst ≫
          alternatingFiltrationMap (Nat.le_succ t) =
        alternatingFiltrationMap (hst.trans (Nat.le_succ t)) :=
        alternatingFiltrationMap_comp hst (Nat.le_succ t)
      have htensorComp :
          ((alternatingFiltrationMap hst ≫
              alternatingFiltrationMap (Nat.le_succ t)) ▷ (Δ[d] : SSet.{u})) =
            (alternatingFiltrationMap hst ▷ (Δ[d] : SSet.{u})) ≫
              (alternatingFiltrationMap (Nat.le_succ t) ▷ (Δ[d] : SSet.{u})) :=
        (MonoidalCategory.tensorRight (Δ[d] : SSet.{u})).map_comp _ _
      calc
        _ = ((alternatingFiltrationMap hst ≫
              alternatingFiltrationMap (Nat.le_succ t)) ▷ (Δ[d] : SSet.{u})) ≫
            (P.state hQ (t + 1)).map :=
          congrArg (fun z ↦ (z ▷ (Δ[d] : SSet.{u})) ≫
            (P.state hQ (t + 1)).map) hcomp.symm
        _ = ((alternatingFiltrationMap hst ▷ (Δ[d] : SSet.{u})) ≫
              (alternatingFiltrationMap (Nat.le_succ t) ▷ (Δ[d] : SSet.{u}))) ≫
            (P.state hQ (t + 1)).map :=
          congrArg (fun z ↦ z ≫ (P.state hQ (t + 1)).map) htensorComp
        _ = (alternatingFiltrationMap hst ▷ (Δ[d] : SSet.{u})) ≫
            ((alternatingFiltrationMap (Nat.le_succ t) ▷ (Δ[d] : SSet.{u})) ≫
              (P.state hQ (t + 1)).map) := Category.assoc _ _ _
        _ = (alternatingFiltrationMap hst ▷ (Δ[d] : SSet.{u})) ≫
            (P.state hQ t).map := congrArg (fun z ↦
              (alternatingFiltrationMap hst ▷ (Δ[d] : SSet.{u})) ≫ z)
                (P.state_step hQ t)
        _ = _ := ih

noncomputable def cocone
    (hQ : HasParameterizedSpecialLeftHornFillers Q) :
    Cocone (alternatingEquivalenceTransfiniteComposition.{u}.F ⋙
      MonoidalCategory.tensorRight (Δ[d] : SSet.{u})) :=
  Cocone.mk Q
    { app s := (P.state hQ s).map
      naturality := by
        intro s t f
        exact P.state_compat hQ (CategoryTheory.leOfHom f) }

noncomputable def extension
    (hQ : HasParameterizedSpecialLeftHornFillers Q) :
    CategoryTheory.nerve EquivalenceInterval.{u} ⊗ (Δ[d] : SSet.{u}) ⟶ Q :=
  (isColimitOfPreserves (MonoidalCategory.tensorRight (Δ[d] : SSet.{u}))
    alternatingEquivalenceTransfiniteComposition.isColimit).desc (P.cocone hQ)

@[reassoc]
theorem stage_extension
    (hQ : HasParameterizedSpecialLeftHornFillers Q) (s : ℕ) :
    ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷ (Δ[d] : SSet.{u})) ≫
      P.extension hQ = (P.state hQ s).map := by
  exact (isColimitOfPreserves (MonoidalCategory.tensorRight (Δ[d] : SSet.{u}))
    alternatingEquivalenceTransfiniteComposition.isColimit).fac (P.cocone hQ) s

@[reassoc]
theorem initial_extension
    (hQ : HasParameterizedSpecialLeftHornFillers Q) :
    (equivalenceIntervalInclusion.{u} ▷ (Δ[d] : SSet.{u})) ≫
      P.extension hQ = P.initialMap := by
  let F := MonoidalCategory.tensorRight (Δ[d] : SSet.{u})
  have hinc := alternatingEquivalenceFirstStageIso_hom_comp_inclusion.{u}
  have htensor :
      (equivalenceIntervalInclusion.{u} ▷ (Δ[d] : SSet.{u})) =
        (alternatingEquivalenceFirstStageIso.{u}.hom ▷ (Δ[d] : SSet.{u})) ≫
          ((alternatingEquivalenceSubcomplex 1).ι ▷ (Δ[d] : SSet.{u})) := by
    calc
      _ = F.map (alternatingEquivalenceFirstStageIso.hom ≫
          alternatingEquivalenceFiltrationInclusion) := congrArg F.map hinc.symm
      _ = _ := F.map_comp _ _
  calc
    _ = ((alternatingEquivalenceFirstStageIso.{u}.hom ▷ (Δ[d] : SSet.{u})) ≫
          ((alternatingEquivalenceSubcomplex 1).ι ▷ (Δ[d] : SSet.{u}))) ≫
        P.extension hQ := congrArg (fun z ↦ z ≫ P.extension hQ) htensor
    _ = (alternatingEquivalenceFirstStageIso.{u}.hom ▷ (Δ[d] : SSet.{u})) ≫
        (((alternatingEquivalenceSubcomplex 1).ι ▷ (Δ[d] : SSet.{u})) ≫
          P.extension hQ) := Category.assoc _ _ _
    _ = (alternatingEquivalenceFirstStageIso.{u}.hom ▷ (Δ[d] : SSet.{u})) ≫
        (P.state hQ 0).map := congrArg (fun z ↦
          (alternatingEquivalenceFirstStageIso.{u}.hom ▷ (Δ[d] : SSet.{u})) ≫ z)
            (P.stage_extension hQ 0)
    _ = (alternatingEquivalenceFirstStageIso.{u}.hom ▷ (Δ[d] : SSet.{u})) ≫
        P.firstStageMap := rfl
    _ = P.initialMap := by
      unfold firstStageMap
      have hcancelTensor :
          (alternatingEquivalenceFirstStageIso.{u}.hom ▷ (Δ[d] : SSet.{u})) ≫
            (alternatingEquivalenceFirstStageIso.{u}.inv ▷ (Δ[d] : SSet.{u})) =
          𝟙 ((Δ[1] : SSet.{u}) ⊗ (Δ[d] : SSet.{u})) := by
        calc
          _ = F.map (alternatingEquivalenceFirstStageIso.hom ≫
              alternatingEquivalenceFirstStageIso.inv) := (F.map_comp _ _).symm
          _ = F.map (𝟙 (Δ[1] : SSet.{u})) :=
            congrArg F.map alternatingEquivalenceFirstStageIso.hom_inv_id
          _ = _ := F.map_id _
      rw [← Category.assoc, hcancelTensor, Category.id_comp]

@[reassoc]
theorem extension_boundary
    (hQ : HasParameterizedSpecialLeftHornFillers Q) :
    (CategoryTheory.nerve EquivalenceInterval.{u} ◁ (SSet.boundary d).ι) ≫
      P.extension hQ = P.boundaryMap := by
  let hc := isColimitOfPreserves
    (MonoidalCategory.tensorRight (SSet.boundary d : SSet.{u}))
    alternatingEquivalenceTransfiniteComposition.isColimit
  apply hc.hom_ext
  intro s
  change ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
      (SSet.boundary d : SSet.{u})) ≫
        (CategoryTheory.nerve EquivalenceInterval.{u} ◁ (SSet.boundary d).ι) ≫
          P.extension hQ =
    ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
      (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap
  calc
    _ = ((alternatingEquivalenceSubcomplex (s + 1) : SSet.{u}) ◁
          (SSet.boundary d).ι) ≫
        ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷ (Δ[d] : SSet.{u})) ≫
          P.extension hQ :=
      (whisker_exchange_assoc _ _ _).symm
    _ = ((alternatingEquivalenceSubcomplex (s + 1) : SSet.{u}) ◁
          (SSet.boundary d).ι) ≫ (P.state hQ s).map := by
      rw [P.stage_extension hQ s]
    _ = ((alternatingEquivalenceSubcomplex (s + 1)).ι ▷
          (SSet.boundary d : SSet.{u})) ≫ P.boundaryMap :=
      (P.state hQ s).boundary

end ParameterizedAlternatingProblem

noncomputable def parameterizedAlternatingProblemOfSquare
    {Q : SSet.{u}} {n : ℕ}
    {f : (SSet.boundary n : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q}
    {g : (Δ[n] : SSet.{u}) ⟶ (equivalenceEdgeInternalHom Q : SSet.{u})}
    (sq : CommSq f (SSet.boundary n).ι
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) g) :
    ParameterizedAlternatingProblem Q n where
  boundaryMap := MonoidalClosed.uncurry f
  initialMap := MonoidalClosed.uncurry (g ≫ (equivalenceEdgeInternalHom Q).ι)
  compatibility := by
    have hinter : (SSet.boundary n).ι ≫ g ≫ (equivalenceEdgeInternalHom Q).ι =
        f ≫ internalHomPrecomp equivalenceIntervalInclusion Q := by
      calc
        _ = ((SSet.boundary n).ι ≫ g) ≫
            (equivalenceEdgeInternalHom Q).ι := (Category.assoc _ _ _).symm
        _ = (f ≫ equivalenceIntervalRestrictionToEquivalenceEdges Q) ≫
            (equivalenceEdgeInternalHom Q).ι :=
          congrArg (fun z ↦ z ≫ (equivalenceEdgeInternalHom Q).ι) sq.w.symm
        _ = f ≫ (equivalenceIntervalRestrictionToEquivalenceEdges Q ≫
            (equivalenceEdgeInternalHom Q).ι) := Category.assoc _ _ _
        _ = f ≫ internalHomPrecomp equivalenceIntervalInclusion Q :=
          congrArg (fun z ↦ f ≫ z)
            (equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion Q)
    calc
      _ = MonoidalClosed.uncurry
          ((SSet.boundary n).ι ≫ g ≫ (equivalenceEdgeInternalHom Q).ι) :=
        (MonoidalClosed.uncurry_natural_left _ _).symm
      _ = MonoidalClosed.uncurry
          (f ≫ internalHomPrecomp equivalenceIntervalInclusion Q) :=
        congrArg MonoidalClosed.uncurry hinter
      _ = _ := MonoidalClosed.uncurry_pre_app Q f equivalenceIntervalInclusion
  leadingEquivalence := equivalenceEdgeFamily_parameter_isEquivalence n g

noncomputable def parameterizedAlternatingLift
    {Q : SSet.{u}} {n : ℕ}
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {f : (SSet.boundary n : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q}
    {g : (Δ[n] : SSet.{u}) ⟶ (equivalenceEdgeInternalHom Q : SSet.{u})}
    (sq : CommSq f (SSet.boundary n).ι
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) g) :
    (Δ[n] : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q :=
  MonoidalClosed.curry ((parameterizedAlternatingProblemOfSquare sq).extension hQ)

theorem parameterizedAlternatingLift_fac_left
    {Q : SSet.{u}} {n : ℕ}
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {f : (SSet.boundary n : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q}
    {g : (Δ[n] : SSet.{u}) ⟶ (equivalenceEdgeInternalHom Q : SSet.{u})}
    (sq : CommSq f (SSet.boundary n).ι
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) g) :
    (SSet.boundary n).ι ≫ parameterizedAlternatingLift hQ sq = f := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left]
  rw [parameterizedAlternatingLift, MonoidalClosed.uncurry_curry]
  rw [(parameterizedAlternatingProblemOfSquare sq).extension_boundary]
  rfl

theorem parameterizedAlternatingLift_fac_right
    {Q : SSet.{u}} {n : ℕ}
    (hQ : HasParameterizedSpecialLeftHornFillers Q)
    {f : (SSet.boundary n : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q}
    {g : (Δ[n] : SSet.{u}) ⟶ (equivalenceEdgeInternalHom Q : SSet.{u})}
    (sq : CommSq f (SSet.boundary n).ι
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) g) :
    parameterizedAlternatingLift hQ sq ≫
      equivalenceIntervalRestrictionToEquivalenceEdges Q = g := by
  apply (cancel_mono (equivalenceEdgeInternalHom Q).ι).1
  rw [Category.assoc,
    equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion]
  rw [parameterizedAlternatingLift]
  change MonoidalClosed.curry _ ≫
      (MonoidalClosed.pre equivalenceIntervalInclusion).app Q = _
  rw [MonoidalClosed.curry_pre_app]
  rw [(parameterizedAlternatingProblemOfSquare sq).initial_extension]
  exact MonoidalClosed.curry_uncurry _

theorem boundary_hasLiftingProperty_intervalRestriction
    {Q : SSet.{u}}
    (hQ : HasParameterizedSpecialLeftHornFillers Q) (n : ℕ) :
    HasLiftingProperty (SSet.boundary.{u} n).ι
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) := by
  constructor
  intro f g sq
  exact ⟨⟨
    { l := parameterizedAlternatingLift hQ sq
      fac_left := parameterizedAlternatingLift_fac_left hQ sq
      fac_right := parameterizedAlternatingLift_fac_right hQ sq }⟩⟩

theorem hasMarkedRestrictedBoundaryLifts_intervalRestriction
    {Q : SSet.{u}} (hQ : HasParameterizedSpecialLeftHornFillers Q) :
    HasMarkedRestrictedBoundaryLifts
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) :=
  fun n ↦ boundary_hasLiftingProperty_intervalRestriction hQ n

theorem intervalRestriction_mem_monomorphisms_rlp
    {Q : SSet.{u}} (hQ : HasParameterizedSpecialLeftHornFillers Q) :
    (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}).rlp
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) :=
  markedRestricted_mem_monomorphisms_rlp
    (hasMarkedRestrictedBoundaryLifts_intervalRestriction hQ)

theorem hasMarkedRestrictedBoundaryLifts_intervalRestriction_of_specialLeftHornFillers
    (Q : SSet.{u}) [SSet.Quasicategory Q] (hQ : HasAllSpecialLeftHornFillers Q) :
    HasMarkedRestrictedBoundaryLifts
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) :=
  hasMarkedRestrictedBoundaryLifts_intervalRestriction
    (hasParameterizedSpecialLeftHornFillers_of_specialLeftHornFillers Q hQ)

theorem intervalRestriction_mem_monomorphisms_rlp_of_specialLeftHornFillers
    (Q : SSet.{u}) [SSet.Quasicategory Q] (hQ : HasAllSpecialLeftHornFillers Q) :
    (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}).rlp
      (equivalenceIntervalRestrictionToEquivalenceEdges Q) :=
  intervalRestriction_mem_monomorphisms_rlp
    (hasParameterizedSpecialLeftHornFillers_of_specialLeftHornFillers Q hQ)

end LeanLCAExactChallenge.Infinity
