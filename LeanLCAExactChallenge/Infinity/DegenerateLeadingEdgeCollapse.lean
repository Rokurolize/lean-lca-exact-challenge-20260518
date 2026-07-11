import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Collapsing the leading edge of a standard simplex

This file records the explicit simplex operators used by the edge-collapse approach to
special left outer horns.  The quotient operator identifies vertices `0` and `1`; its two
sections choose either endpoint of the collapsed edge.  Keeping these operators explicit is
useful because the quotient is not, by itself, a replacement for the coherence supplied by
inner-horn fillers.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open Opposite
open Simplicial

/-- The monotone map `[n+2] → [n+1]` identifying the first two vertices. -/
def leadingEdgeCollapseOperator (n : ℕ) :=
  SimplexCategory.mkHom
    ({ toFun := (0 : Fin (n + 2)).predAbove
       monotone' := Fin.predAbove_right_monotone 0 } : Fin (n + 3) →o Fin (n + 2))

/-- The section of `leadingEdgeCollapseOperator` which chooses vertex `1`. -/
def leadingEdgeUpperSectionOperator (n : ℕ) :=
  SimplexCategory.mkHom
    (Fin.succAboveOrderEmb (0 : Fin (n + 3))).toOrderHom

/-- The section of `leadingEdgeCollapseOperator` which chooses vertex `0`. -/
def leadingEdgeLowerSectionOperator (n : ℕ) :=
  SimplexCategory.mkHom
    (Fin.succAboveOrderEmb (1 : Fin (n + 3))).toOrderHom

@[simp]
theorem leadingEdgeUpperSectionOperator_comp_collapse (n : ℕ) :
    leadingEdgeUpperSectionOperator n ≫ leadingEdgeCollapseOperator n = 𝟙 _ := by
  ext i
  simp [leadingEdgeUpperSectionOperator, leadingEdgeCollapseOperator]

@[simp]
theorem leadingEdgeLowerSectionOperator_comp_collapse (n : ℕ) :
    leadingEdgeLowerSectionOperator n ≫ leadingEdgeCollapseOperator n = 𝟙 _ := by
  ext i
  simp only [leadingEdgeLowerSectionOperator, leadingEdgeCollapseOperator,
    SimplexCategory.mkHom, SimplexCategory.comp_toOrderHom,
    SimplexCategory.Hom.toOrderHom_mk, SimplexCategory.id_toOrderHom,
    OrderHom.comp_coe, OrderHom.id_coe, id_eq, OrderEmbedding.toOrderHom_coe,
    Function.comp_apply, Fin.succAboveOrderEmb_apply]
  by_cases hi : i = 0
  · subst i
    simp
  · rw [Fin.succAbove_of_le_castSucc]
    · change ((0 : Fin (n + 2)).predAbove i.succ).val = i.val
      rw [Fin.predAbove_of_castSucc_lt]
      · simp
      · simp
    · simp only [Fin.le_iff_val_le_val, Fin.val_one, Fin.val_castSucc]
      have hiVal : i.val ≠ 0 := fun h ↦ hi (Fin.ext h)
      omega

/-- The operator selecting the ordered edge on vertices `0,1`. -/
def leadingEdgeOperator (n : ℕ) :=
  SimplexCategory.mkOfSucc (0 : Fin (n + 2))

/-- Collapsing the leading edge sends both of its vertices to vertex `0`. -/
theorem leadingEdgeOperator_comp_collapse (n : ℕ) :
    leadingEdgeOperator n ≫ leadingEdgeCollapseOperator n =
      SimplexCategory.const (SimplexCategory.mk 1) (SimplexCategory.mk (n + 1))
        (0 : Fin (n + 2)) := by
  ext i
  fin_cases i <;>
    simp [leadingEdgeOperator, leadingEdgeCollapseOperator, SimplexCategory.mkOfSucc,
      SimplexCategory.const]

/-- The quotient map of representables induced by collapsing vertices `0` and `1`. -/
def leadingEdgeCollapse (n : ℕ) : (Δ[n + 2] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.stdSimplex.map (leadingEdgeCollapseOperator n)

/-- The upper section of `leadingEdgeCollapse`. -/
def leadingEdgeUpperSection (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2] :=
  SSet.stdSimplex.map (leadingEdgeUpperSectionOperator n)

/-- The lower section of `leadingEdgeCollapse`. -/
def leadingEdgeLowerSection (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 2] :=
  SSet.stdSimplex.map (leadingEdgeLowerSectionOperator n)

/-- The leading-edge inclusion into `Δ[n+2]`. -/
def leadingEdgeInSimplex (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[n + 2] :=
  SSet.stdSimplex.map (leadingEdgeOperator n)

/-- The constant edge at vertex `0` of `Δ[n+1]`. -/
def leadingEdgeCollapsedConstant (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.stdSimplex.map
    (SimplexCategory.const (SimplexCategory.mk 1) (SimplexCategory.mk (n + 1))
      (0 : Fin (n + 2)))

@[reassoc]
theorem leadingEdgeInSimplex_comp_collapse (n : ℕ) :
    leadingEdgeInSimplex n ≫ leadingEdgeCollapse n = leadingEdgeCollapsedConstant n := by
  rw [leadingEdgeInSimplex, leadingEdgeCollapse, leadingEdgeCollapsedConstant,
    ← Functor.map_comp, leadingEdgeOperator_comp_collapse]

@[simp, reassoc]
theorem leadingEdgeUpperSection_comp_collapse (n : ℕ) :
    leadingEdgeUpperSection n ≫ leadingEdgeCollapse n = 𝟙 _ := by
  rw [leadingEdgeUpperSection, leadingEdgeCollapse, ← Functor.map_comp,
    leadingEdgeUpperSectionOperator_comp_collapse]
  exact SSet.stdSimplex.map_id _

@[simp, reassoc]
theorem leadingEdgeLowerSection_comp_collapse (n : ℕ) :
    leadingEdgeLowerSection n ≫ leadingEdgeCollapse n = 𝟙 _ := by
  rw [leadingEdgeLowerSection, leadingEdgeCollapse, ← Functor.map_comp,
    leadingEdgeLowerSectionOperator_comp_collapse]
  exact SSet.stdSimplex.map_id _

end Infinity
end LeanLCAExactChallenge
