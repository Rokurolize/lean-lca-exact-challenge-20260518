import LeanLCAExactChallenge.Infinity.DoldKanMonoidal

/-!
# Explicit one-simplices in the Dold--Kan inverse

This file constructs the one-simplex in the explicit `Γ₀` model determined by a degree-zero
element and a degree-one element. Its two faces record the chain differential exactly.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory
open Opposite
open Simplicial

/-- The explicit Dold--Kan one-simplex `σ₀(x) + ι₁(h)` associated to a degree-zero element
`x` and a degree-one element `h`. -/
def doldKanGammaOneSimplex (T : ChainComplex (ModuleCat.{0} ℤ) ℕ) (x : T.X 0) (h : T.X 1) :
    (AlgebraicTopology.DoldKan.Γ₀.obj T).obj (op ⦋1⦌) := by
  let x' : (AlgebraicTopology.DoldKan.Γ₀.obj T).obj (op ⦋0⦌) :=
    ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x
  let h' : (AlgebraicTopology.DoldKan.Γ₀.obj T).obj (op ⦋1⦌) :=
    ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 1).hom h
  exact ((AlgebraicTopology.DoldKan.Γ₀.obj T).σ 0).hom x' + h'

/-- The final face of `doldKanGammaOneSimplex T x h` is `x + d(h)`. -/
theorem doldKanGammaOneSimplex_delta_zero (T : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (x : T.X 0) (h : T.X 1) :
    ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 0).hom
        (doldKanGammaOneSimplex T x h) =
      ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom
        (x + (T.d 1 0).hom h) := by
  dsimp [doldKanGammaOneSimplex]
  erw [map_add]
  erw [map_add]
  apply congrArg₂ (· + ·)
  · have hcat := SimplicialObject.δ_comp_σ_self'
        (X := AlgebraicTopology.DoldKan.Γ₀.obj T)
        (j := (0 : Fin 2)) (i := (0 : Fin 1)) (by decide)
    have happ := congrArg (fun q ↦ q.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x)) hcat
    exact happ
  · erw [← CategoryTheory.ConcreteCategory.comp_apply]
    rw [← (AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan_inj_id 1]
    change CategoryTheory.ConcreteCategory.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan (op ⦋1⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋1⦌)) ≫
        (AlgebraicTopology.DoldKan.Γ₀.obj T).map (SimplexCategory.δ 0).op) h = _
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.mapMono_on_summand_id]
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_δ₀]
    rw [(AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan_inj_id 0]
    erw [CategoryTheory.ConcreteCategory.comp_apply]

/-- The initial face of `doldKanGammaOneSimplex T x h` is `x`. -/
theorem doldKanGammaOneSimplex_delta_one (T : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (x : T.X 0) (h : T.X 1) :
    ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
        (doldKanGammaOneSimplex T x h) =
      ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x := by
  dsimp [doldKanGammaOneSimplex]
  erw [map_add]
  have hx :
      ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
          (((AlgebraicTopology.DoldKan.Γ₀.obj T).σ 0).hom
            (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x)) =
        ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x := by
    have hcat := SimplicialObject.δ_comp_σ_succ'
      (X := AlgebraicTopology.DoldKan.Γ₀.obj T)
      (j := (1 : Fin 2)) (i := (0 : Fin 1)) (by decide)
    have happ := congrArg (fun q ↦ q.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x)) hcat
    exact happ
  have hh :
      ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
          (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 1).hom h) = 0 := by
    erw [← CategoryTheory.ConcreteCategory.comp_apply]
    rw [← (AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan_inj_id 1]
    change CategoryTheory.ConcreteCategory.hom
      (((AlgebraicTopology.DoldKan.Γ₀.splitting T).cofan (op ⦋1⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋1⦌)) ≫
        (AlgebraicTopology.DoldKan.Γ₀.obj T).map (SimplexCategory.δ 1).op) h = 0
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.mapMono_on_summand_id]
    rw [AlgebraicTopology.DoldKan.Γ₀.Obj.Termwise.mapMono_eq_zero]
    · simp
    · intro hEq
      have hlen : 1 = 0 := by simpa using congrArg SimplexCategory.len hEq
      omega
    · simpa only [AlgebraicTopology.DoldKan.Isδ₀.iff] using (by omega : (1 : Fin 2) ≠ 0)
  calc
    _ = ((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 0).hom x +
        ((AlgebraicTopology.DoldKan.Γ₀.obj T).δ 1).hom
          (((AlgebraicTopology.DoldKan.Γ₀.splitting T).ι 1).hom h) :=
      congrArg (fun z ↦ z + _) hx
    _ = _ := by simp only [hh, add_zero]; rfl

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
