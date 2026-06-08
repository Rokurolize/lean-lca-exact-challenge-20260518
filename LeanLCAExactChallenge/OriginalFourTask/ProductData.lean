import LeanLCAExactChallenge.BoundedDerived.Basic
import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundary
import LeanLCAExactChallenge.Ext.Yoneda
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
Nonterminal product-data bridge for the original four-task challenge.

This file intentionally does not define `OriginalFourTaskProductSuccess`.
It records the exact data shape that the final positive witness must inhabit
once the metrizable bounded-derived stable package is available without an
external input.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

/-- Product-facing data for the original four tasks, parameterized by the
remaining bounded-derived stable package. -/
structure OriginalFourTaskProductData : Type 2 where
  quillenExactCategory : QuillenExactCategory MetrizableLCA.{0}
  metrizableLCAExactCategory : QuillenExactCategory MetrizableLCA.{0}
  metrizableLCAExactCategory_eq :
    metrizableLCAExactCategory = MetrizableLCA.quillenExactCategory
  metrizableLCAConflationIff :
    ∀ {S : ShortComplex MetrizableLCA.{0}},
      QuillenExactCategory.Conflation S ↔
        IsClosedEmbedding (S.f : S.X₁ → S.X₂) ∧
          IsOpenMap (S.g : S.X₂ → S.X₃) ∧
            Function.Surjective (S.g : S.X₂ → S.X₃) ∧
              ∀ x₂ : S.X₂, S.g x₂ = 0 → ∃ x₁ : S.X₁, S.f x₁ = x₂
  yonedaExt : MetrizableLCA.{0} → MetrizableLCA.{0} → ℕ → Type 1
  yonedaExt_eq :
    yonedaExt = fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n
  yonedaExtZeroEquivHom :
    ∀ X Y : MetrizableLCA.{0}, yonedaExt X Y 0 ≃ (X ⟶ Y)
  boundedDerivedInfinityCategory : BoundedDerived.Metrizable.StablePackage

/-- Assemble the original-four-task product data from the remaining stable package. -/
noncomputable def originalFourTaskProductDataOfStablePackage
    (P : BoundedDerived.Metrizable.StablePackage) :
    OriginalFourTaskProductData where
  quillenExactCategory := MetrizableLCA.quillenExactCategory
  metrizableLCAExactCategory := MetrizableLCA.quillenExactCategory
  metrizableLCAExactCategory_eq := rfl
  metrizableLCAConflationIff := fun {S} =>
    MetrizableLCA.quillenConflation_iff_closed_inclusion_open_surjection_algebraic_exact
      (S := S)
  yonedaExt := fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n
  yonedaExt_eq := rfl
  yonedaExtZeroEquivHom := fun X Y =>
    YonedaExt.zero_equiv_hom (C := MetrizableLCA.{0}) (X := X) (Y := Y)
  boundedDerivedInfinityCategory := P

theorem originalFourTaskProductDataOfStablePackage_boundedDerivedInfinityCategory
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).boundedDerivedInfinityCategory = P :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAExactCategory
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_yonedaExt
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/-- Assemble product data from the current canonical stable-instance boundary. -/
noncomputable def originalFourTaskProductDataOfStableInstanceBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory inputs)

theorem originalFourTaskProductDataOfStableInstanceBoundary_boundedDerivedInfinityCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryInputs) :
    (originalFourTaskProductDataOfStableInstanceBoundary inputs).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory inputs :=
  rfl

theorem originalFourTaskProductDataOfStableInstanceBoundary_metrizableLCAExactCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryInputs) :
    (originalFourTaskProductDataOfStableInstanceBoundary inputs).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfStableInstanceBoundary_yonedaExt
    (inputs : Dbounded.MetrizableStableInstanceBoundaryInputs) :
    (originalFourTaskProductDataOfStableInstanceBoundary inputs).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

end LeanLCAExactChallenge
