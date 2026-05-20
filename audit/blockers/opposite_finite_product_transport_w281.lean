import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
W281: generic finite-coproduct to opposite finite-product transport.

The W277/W259 opposite finite-product route needed a formal theorem turning finite-coproduct
stability of a morphism property `W` into finite-product stability of `W.op`.  This file proves
that generic categorical bridge.  It does not prove finite-coproduct stability of
`boundedExactWeakEquivalence MetrizableLCA`; that direct closure theorem remains separate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace OppositeFiniteProductTransportW281

variable {C : Type u} [Category.{v} C]

/-- A product of opposite objects gives a coproduct of the original objects. -/
lemma hasCoproduct_unop_of_hasProduct_op {J : Type w}
    (X : J → Cᵒᵖ) [HasProduct X] :
    HasCoproduct (fun j => (X j).unop) := by
  let F : Discrete J ⥤ C := Discrete.functor (fun j => (X j).unop)
  have e : (Discrete.opposite J).symm.functor ⋙ F.op ≅ Discrete.functor X := by
    refine Discrete.natIso ?_
    intro j
    cases j
    rfl
  haveI : HasLimit ((Discrete.opposite J).symm.functor ⋙ F.op) :=
    hasLimit_of_iso e.symm
  haveI : HasLimit F.op :=
    hasLimit_of_equivalence_comp (Discrete.opposite J).symm
  exact hasColimit_of_hasLimit_op F

/-- Stability under coproducts of shape `J` transports to stability under products in `Cᵒᵖ`. -/
theorem op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape
    (W : MorphismProperty C) [W.RespectsIso] {J : Type w}
    [W.IsStableUnderCoproductsOfShape J] :
    W.op.IsStableUnderProductsOfShape J := by
  refine MorphismProperty.IsStableUnderProductsOfShape.mk W.op J ?_
  intro X₁ X₂ _ _ f hf
  let Z₁ : J → C := fun j => (X₁ j).unop
  let Z₂ : J → C := fun j => (X₂ j).unop
  let g : ∀ j, Z₂ j ⟶ Z₁ j := fun j => (f j).unop
  haveI : HasCoproduct Z₁ := hasCoproduct_unop_of_hasProduct_op X₁
  haveI : HasCoproduct Z₂ := hasCoproduct_unop_of_hasProduct_op X₂
  have hg : ∀ j, W (g j) := by
    intro j
    exact hf j
  let F₂ : Discrete J ⥤ C := Discrete.functor Z₂
  let F₁ : Discrete J ⥤ C := Discrete.functor Z₁
  let η : F₂ ⟶ F₁ := Discrete.natTrans (fun i => g i.as)
  have hη : W.functorCategory (Discrete J) η := by
    intro j
    exact hg j.as
  have hSigma : W (Limits.Sigma.map g) := by
    simpa [Limits.Sigma.map, η, F₁, F₂] using
      (MorphismProperty.colimMap (W := W) (J := Discrete J) η hη)
  let eo₁ : op (∐ Z₁) ≅ ∏ᶜ X₁ := by
    simpa [Z₁] using (opCoproductIsoProduct Z₁)
  let eo₂ : op (∐ Z₂) ≅ ∏ᶜ X₂ := by
    simpa [Z₂] using (opCoproductIsoProduct Z₂)
  let e₁ : (∏ᶜ X₁).unop ≅ ∐ Z₁ := eo₁.unop
  let e₂ : (∏ᶜ X₂).unop ≅ ∐ Z₂ := eo₂.unop
  refine (W.arrow_mk_iso_iff ?_).2 hSigma
  refine Arrow.isoMk e₂ e₁ ?_
  apply Quiver.Hom.op_inj
  apply Limits.Pi.hom_ext
  intro j
  dsimp [e₁, e₂, eo₁, eo₂]
  rw [Category.assoc, opCoproductIsoProduct_hom_comp_π]
  rw [Category.assoc, Limits.Pi.map_π]
  have hπ₁ : (opCoproductIsoProduct Z₁).hom ≫ Pi.π X₁ j = (Sigma.ι Z₁ j).op := by
    simpa [Z₁] using (opCoproductIsoProduct_hom_comp_π (Z := Z₁) j)
  conv_rhs => rw [← Category.assoc, hπ₁]
  rw [← op_comp, Limits.Sigma.ι_map]
  simp [g, Z₁, Z₂]

/-- Finite-coproduct stability transports to finite-product stability of the opposite property. -/
theorem op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
    (W : MorphismProperty C) [W.RespectsIso] [W.IsStableUnderFiniteCoproducts] :
    W.op.IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ :=
    op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape W (J := J)

def transportDeclarationNames : List String :=
  ["hasCoproduct_unop_of_hasProduct_op",
    "op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape",
    "op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts"]

theorem transportDeclarationNames_count :
    transportDeclarationNames.length = 3 := rfl

section Checks

#check hasCoproduct_unop_of_hasProduct_op
#check op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape
#check op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
#check transportDeclarationNames_count

end Checks

end OppositeFiniteProductTransportW281

end LeanLCAExactChallenge
