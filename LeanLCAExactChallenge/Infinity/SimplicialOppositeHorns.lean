import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

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

/-- The opposite of a horn inclusion is the inclusion of the reversed horn. -/
def hornInclusionOpArrowIso (n : ℕ) (i : Fin (n + 1)) :
    Arrow.mk (SSet.opFunctor.map (SSet.horn.{u} n i).ι) ≅
      Arrow.mk (SSet.horn n i.rev).ι := by
  refine Arrow.isoMk (hornOpIso n i)
    (SSet.stdSimplex.opIso (SimplexCategory.mk n)) ?_
  exact hornOpIso_hom_comp_inclusion n i

/-- Applying simplicial reversal twice to an arrow recovers that arrow. -/
def opOpArrowIso {X Y : SSet.{u}} (p : X ⟶ Y) :
    Arrow.mk (SSet.opFunctor.map (SSet.opFunctor.map p)) ≅ Arrow.mk p := by
  let e := SSet.opFunctorCompOpFunctorIso.{u}
  refine Arrow.isoMk (e.app X) (e.app Y) ?_
  exact e.hom.naturality p

/-- Simplicial reversal preserves a lifting problem when applied to both arrows. -/
theorem hasLiftingProperty_op_iff {A B X Y : SSet.{u}}
    (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty (SSet.opFunctor.map i) (SSet.opFunctor.map p) ↔
      HasLiftingProperty i p := by
  have h := SSet.opEquivalence.{u}.toAdjunction.hasLiftingProperty_iff
    i (SSet.opFunctor.map p)
  change HasLiftingProperty (SSet.opFunctor.map i) (SSet.opFunctor.map p) ↔ _ at h
  exact h.trans (HasLiftingProperty.iff_of_arrow_iso_right i (opOpArrowIso p))

/-- Reversal exchanges a horn lifting problem with the reversed horn lifting problem. -/
theorem hasLiftingProperty_horn_op_iff {X Y : SSet.{u}}
    (p : X ⟶ Y) (n : ℕ) (i : Fin (n + 1)) :
    HasLiftingProperty (SSet.horn n i).ι (SSet.opFunctor.map p) ↔
      HasLiftingProperty (SSet.horn n i.rev).ι p := by
  have hleft := HasLiftingProperty.iff_of_arrow_iso_left
    (hornInclusionOpArrowIso n i.rev) (SSet.opFunctor.map p)
  rw [Fin.rev_rev] at hleft
  exact hleft.symm.trans
    (hasLiftingProperty_op_iff (SSet.horn n i.rev).ι p)

/-- Simplicial reversal preserves quasicategories. -/
noncomputable instance quasicategory_op (Q : SSet.{u}) [SSet.Quasicategory Q] :
    SSet.Quasicategory Q.op := by
  let T : SSet.{u} :=
    (SimplicialObject.const (Type u)).obj (Limits.terminal (Type u))
  have hT : Limits.IsTerminal T := by
    let t : ∀ K : SSet.{u}, K ⟶ T := fun K ↦
      { app := fun _ ↦ Limits.terminal.from _
        naturality := by intros; apply Limits.terminal.hom_ext }
    apply Limits.IsTerminal.ofUniqueHom t
    intro K f
    apply NatTrans.ext
    funext d
    apply Limits.terminal.hom_ext
  have hTop : Limits.IsTerminal T.op := by
    let t : ∀ K : SSet.{u}, K ⟶ T.op := fun K ↦
      { app := fun _ ↦ Limits.terminal.from _
        naturality := by intros; apply Limits.terminal.hom_ext }
    apply Limits.IsTerminal.ofUniqueHom t
    intro K f
    apply NatTrans.ext
    funext d
    apply Limits.terminal.hom_ext
  rw [SSet.quasicategory_iff_hasLiftingProperty Q.op hTop]
  intro n i h0 hn
  have hrev0 : 0 < i.rev := by
    simp only [Fin.lt_def, Fin.val_zero, Fin.val_last, Fin.val_rev] at hn ⊢
    omega
  have hrevn : i.rev < Fin.last n := by
    simp only [Fin.lt_def, Fin.val_zero, Fin.val_last, Fin.val_rev] at h0 ⊢
    omega
  have hQ := SSet.Quasicategory.hasLiftingProperty Q hT hrev0 hrevn
  have hop : HasLiftingProperty
      (SSet.opFunctor.map (SSet.horn n i.rev).ι)
      (SSet.opFunctor.map (hT.from Q)) :=
    (hasLiftingProperty_op_iff (SSet.horn n i.rev).ι (hT.from Q)).2 hQ
  have hleft : HasLiftingProperty (SSet.horn n i).ι
      (SSet.opFunctor.map (hT.from Q)) :=
    by
      have htmp := (HasLiftingProperty.iff_of_arrow_iso_left
        (hornInclusionOpArrowIso n i.rev) (SSet.opFunctor.map (hT.from Q))).1 hop
      rw [Fin.rev_rev] at htmp
      exact htmp
  have hp : SSet.opFunctor.map (hT.from Q) = hTop.from Q.op := hTop.hom_ext _ _
  simpa only [hp] using hleft

end LeanLCAExactChallenge.Infinity
