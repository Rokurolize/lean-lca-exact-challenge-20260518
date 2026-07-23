/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientTruncation
import LeanLCAExactChallenge.Infinity.QuotientDoldKanLaxMonoidal

/-!
# Smart truncation for corrected quotient cochain complexes

This file specializes the general smart-truncation pairing construction to the tensor product.
-/

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

/-- Nonpositive smart truncation, regarded as a functor to nonnegative chain complexes. -/
abbrev functor : QuotientDGCochain ⥤ QuotientDoldKanMonoidal.QuotientChain :=
  ComplexShape.embeddingDownNat.truncLE'Functor QuotientDoldKanMonoidal.QuotientModule

/-- The tensor pairing on one homogeneous summand after smart truncation. -/
def tensorComponent (A B : QuotientDGCochain)
    {p q n : ℕ} (h : p + q = n) :
    (functor.obj A).X p ⊗ (functor.obj B).X q ⟶
      (functor.obj (A ⊗ B)).X n :=
  quotientTruncatedMapComponent (𝟙 (A ⊗ B)) h

/-- The homogeneous tensor pairing followed by the comparison to the untruncated tensor. -/
def tensorToCochain (A B : QuotientDGCochain)
    {p q n : ℕ} (h : p + q = n) :
    (functor.obj A).X p ⊗ (functor.obj B).X q ⟶
      (A ⊗ B).X (ComplexShape.embeddingDownNat.f n) :=
  ((A.truncLE'ToRestriction ComplexShape.embeddingDownNat).f p ⊗ₘ
      (B.truncLE'ToRestriction ComplexShape.embeddingDownNat).f q) ≫
    HomologicalComplex.ιTensorObj A B
      (ComplexShape.embeddingDownNat.f p)
      (ComplexShape.embeddingDownNat.f q)
      (ComplexShape.embeddingDownNat.f n) (by
        dsimp [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE]
        omega)

@[reassoc]
theorem tensorComponent_toRestriction (A B : QuotientDGCochain)
    {p q n : ℕ} (h : p + q = n) :
    tensorComponent A B h ≫
        ((A ⊗ B).truncLE'ToRestriction ComplexShape.embeddingDownNat).f n =
      tensorToCochain A B h := by
  refine (quotientTruncatedMapComponent_toRestriction (𝟙 (A ⊗ B)) h).trans ?_
  dsimp [tensorToCochain, quotientTruncatedMapToCochain]
  exact Category.comp_id _

/-- The tensor pairing in a fixed total degree. -/
def tensorDegree (A B : QuotientDGCochain) (n : ℕ) :
    (HomologicalComplex.tensorObj (functor.obj A) (functor.obj B)).X n ⟶
      (functor.obj (A ⊗ B)).X n :=
  HomologicalComplex.mapBifunctorDesc fun _ _ h => tensorComponent A B h

/-- The fixed-degree tensor pairing viewed in the untruncated target. -/
def tensorToRestrictionDegree (A B : QuotientDGCochain) (n : ℕ) :
    (HomologicalComplex.tensorObj (functor.obj A) (functor.obj B)).X n ⟶
      ((A ⊗ B).restriction ComplexShape.embeddingDownNat).X n :=
  HomologicalComplex.mapBifunctorDesc fun _ _ h => tensorToCochain A B h

@[reassoc (attr := simp)]
theorem ι_tensorDegree (A B : QuotientDGCochain)
    {p q n : ℕ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj (functor.obj A) (functor.obj B) p q n h ≫
        tensorDegree A B n = tensorComponent A B h := by
  apply HomologicalComplex.ι_mapBifunctorDesc

@[reassoc]
theorem tensorDegree_toRestriction (A B : QuotientDGCochain) (n : ℕ) :
    tensorDegree A B n ≫
        ((A ⊗ B).truncLE'ToRestriction ComplexShape.embeddingDownNat).f n =
      tensorToRestrictionDegree A B n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [← Category.assoc]
  simp only [tensorDegree, tensorToRestrictionDegree,
    HomologicalComplex.ι_mapBifunctorDesc]
  exact tensorComponent_toRestriction A B h

end QuotientSmartTruncation
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
