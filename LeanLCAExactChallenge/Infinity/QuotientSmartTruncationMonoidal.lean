import LeanLCAExactChallenge.Infinity.QuotientSmartTruncation

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientSmartTruncation

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

/-- The tensorator for nonpositive smart truncation. -/
def tensor (A B : QuotientDGCochain) :
    functor.obj A ⊗ functor.obj B ⟶ functor.obj (A ⊗ B) :=
  quotientTruncatedMap (𝟙 (A ⊗ B))

@[simp]
theorem tensor_f (A B : QuotientDGCochain) (n : ℕ) :
    (tensor A B).f n = tensorDegree A B n := by
  rfl

lemma tensor_natural {A A' B B' : QuotientDGCochain}
    (f : A ⟶ A') (g : B ⟶ B') :
    (functor.map f ⊗ₘ functor.map g) ≫ tensor A' B' =
      tensor A B ≫ functor.map (f ⊗ₘ g) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply (cancel_mono
    (((A' ⊗ B').truncLE'ToRestriction ComplexShape.embeddingDownNat).f n)).1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, tensor_f, Category.assoc]
  change _ ≫
      (HomologicalComplex.mapBifunctorMap (functor.map f) (functor.map g)
        (curriedTensor QuotientDoldKanMonoidal.QuotientModule)
        (ComplexShape.down ℕ)).f n ≫ _ = _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [ι_tensorDegree_assoc]
  slice_lhs 3 4 =>
    rw [tensorComponent_toRestriction]
  have hnat := congrArg (fun t => t.f n)
    (HomologicalComplex.truncLE'ToRestriction_naturality
      (f ⊗ₘ g) ComplexShape.embeddingDownNat)
  change (functor.map (f ⊗ₘ g)).f n ≫
      ((A' ⊗ B').truncLE'ToRestriction ComplexShape.embeddingDownNat).f n =
    ((A ⊗ B).truncLE'ToRestriction ComplexShape.embeddingDownNat).f n ≫
      (HomologicalComplex.restrictionMap (f ⊗ₘ g)
        ComplexShape.embeddingDownNat).f n at hnat
  slice_rhs 2 3 =>
    rw [hnat]
  slice_rhs 1 2 =>
    rw [tensorComponent_toRestriction]
  have hf := congrArg (fun t => t.f p)
    (HomologicalComplex.truncLE'ToRestriction_naturality
      f ComplexShape.embeddingDownNat)
  change (functor.map f).f p ≫
      (A'.truncLE'ToRestriction ComplexShape.embeddingDownNat).f p =
    (A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f p ≫
      f.f (ComplexShape.embeddingDownNat.f p) at hf
  have hg := congrArg (fun t => t.f q)
    (HomologicalComplex.truncLE'ToRestriction_naturality
      g ComplexShape.embeddingDownNat)
  change (functor.map g).f q ≫
      (B'.truncLE'ToRestriction ComplexShape.embeddingDownNat).f q =
    (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f q ≫
      g.f (ComplexShape.embeddingDownNat.f q) at hg
  dsimp [functor] at hf hg
  dsimp [tensorToCochain]
  rw [← MonoidalCategory.tensorHom_def_assoc]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [hf, hg]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]
  have hco : ComplexShape.embeddingDownNat.f p +
      ComplexShape.embeddingDownNat.f q = ComplexShape.embeddingDownNat.f n := by
    change p + q = n at h
    dsimp [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE]
    omega
  have hi :
      HomologicalComplex.ιTensorObj A B
          (ComplexShape.embeddingDownNat.f p)
          (ComplexShape.embeddingDownNat.f q)
          (ComplexShape.embeddingDownNat.f n) hco ≫
        (f ⊗ₘ g).f (ComplexShape.embeddingDownNat.f n) =
      (f.f (ComplexShape.embeddingDownNat.f p) ⊗ₘ
          g.f (ComplexShape.embeddingDownNat.f q)) ≫
        HomologicalComplex.ιTensorObj A' B'
          (ComplexShape.embeddingDownNat.f p)
          (ComplexShape.embeddingDownNat.f q)
          (ComplexShape.embeddingDownNat.f n) hco := by
    exact GradedObject.Monoidal.ι_tensorHom f.f g.f _ _ _ hco
  conv_rhs => rw [Category.assoc]
  erw [hi]
  exact Category.assoc _ _ _

end QuotientSmartTruncation
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
