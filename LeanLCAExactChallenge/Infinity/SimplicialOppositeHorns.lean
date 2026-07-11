import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Reversal of simplicial horns
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

/-- Reversing a horn reverses its missing vertex. -/
def hornOpIso (n : ℕ) (i : Fin (n + 1)) :
    ((SSet.horn.{u} n i).op : SSet.{u}) ≅ SSet.horn n i.rev where
  hom := SSet.Subcomplex.lift
    ((SSet.horn n i).op.ι ≫
      (SSet.stdSimplex.opIso (SimplexCategory.mk n)).hom) (by
      intro d _ hy
      rcases hy with ⟨x, hx, rfl⟩
      change ((SSet.stdSimplex.opIso (SimplexCategory.mk n)).hom.app d x) ∈
        (SSet.horn n i.rev).obj d
      rw [← SSet.op_horn.{u} i]
      change ((SSet.stdSimplex.opIso (SimplexCategory.mk n)).inv.app d
        ((SSet.stdSimplex.opIso (SimplexCategory.mk n)).hom.app d x)) ∈
          (SSet.horn n i).op.obj d
      simpa using hx)
  inv := SSet.Subcomplex.lift
    ((SSet.horn n i.rev).ι ≫
      (SSet.stdSimplex.opIso (SimplexCategory.mk n)).inv) (by
      intro d _ hy
      rcases hy with ⟨x, hx, rfl⟩
      have hx' : x.val ∈ ((SSet.horn n i).op.preimage
          (SSet.stdSimplex.opIso (SimplexCategory.mk n)).inv).obj d := by
        rw [SSet.op_horn.{u} i]
        exact x.property
      exact hx')
  hom_inv_id := by
    apply (cancel_mono (SSet.horn n i).op.ι).1
    simp only [Category.assoc, SSet.Subcomplex.lift_ι]
    simp
  inv_hom_id := by
    apply (cancel_mono (SSet.horn n i.rev).ι).1
    simp only [Category.assoc, SSet.Subcomplex.lift_ι]
    simp

@[reassoc (attr := simp)]
theorem hornOpIso_hom_comp_inclusion (n : ℕ) (i : Fin (n + 1)) :
    (hornOpIso.{u} n i).hom ≫ (SSet.horn n i.rev).ι =
      (SSet.horn n i).op.ι ≫
        (SSet.stdSimplex.opIso (SimplexCategory.mk n)).hom :=
  rfl

@[reassoc (attr := simp)]
theorem hornOpIso_inv_comp_inclusion (n : ℕ) (i : Fin (n + 1)) :
    (hornOpIso.{u} n i).inv ≫ (SSet.horn n i).op.ι =
      (SSet.horn n i.rev).ι ≫
        (SSet.stdSimplex.opIso (SimplexCategory.mk n)).inv :=
  rfl

end LeanLCAExactChallenge.Infinity
