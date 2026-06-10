import LeanLCAExactChallenge.BoundedDerived.Basic
import LeanLCAExactChallenge.BoundedDerived.MetrizableStableBridge
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.MetrizableStableInstanceBoundaryDirectLocalization
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
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open BoundedDerived.Metrizable

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
  metrizableLCAForgetKernelCokernelIff :
    ∀ {S : ShortComplex MetrizableLCA.{0}},
      QuillenExactCategory.Conflation S ↔
        IsClosedEmbedding (S.f : S.X₁ → S.X₂) ∧
          IsOpenMap (S.g : S.X₂ → S.X₃) ∧
            Function.Surjective (S.g : S.X₂ → S.X₃) ∧
              Nonempty (IsLimit (KernelFork.ofι (S.map MetrizableLCA.forgetToAddCommGrpCat).f
                (S.map MetrizableLCA.forgetToAddCommGrpCat).zero)) ∧
                Nonempty (IsColimit (CokernelCofork.ofπ
                  (S.map MetrizableLCA.forgetToAddCommGrpCat).g
                  (S.map MetrizableLCA.forgetToAddCommGrpCat).zero))
  metrizableLCAForgetExact :
    ∀ {S : ShortComplex MetrizableLCA.{0}},
      QuillenExactCategory.Conflation S → (S.map MetrizableLCA.forgetToAddCommGrpCat).Exact
  metrizableLCAForgetKernel :
    ∀ {S : ShortComplex MetrizableLCA.{0}},
      QuillenExactCategory.Conflation S →
        IsLimit (KernelFork.ofι (S.map MetrizableLCA.forgetToAddCommGrpCat).f
          (S.map MetrizableLCA.forgetToAddCommGrpCat).zero)
  metrizableLCAForgetCokernel :
    ∀ {S : ShortComplex MetrizableLCA.{0}},
      QuillenExactCategory.Conflation S →
        IsColimit (CokernelCofork.ofπ (S.map MetrizableLCA.forgetToAddCommGrpCat).g
          (S.map MetrizableLCA.forgetToAddCommGrpCat).zero)
  yonedaExt : MetrizableLCA.{0} → MetrizableLCA.{0} → ℕ → Type 1
  yonedaExt_eq :
    yonedaExt = fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n
  yonedaExtAddCommGroup :
    ∀ X Y : MetrizableLCA.{0}, ∀ n : ℕ, AddCommGroup (yonedaExt X Y n)
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
  metrizableLCAForgetKernelCokernelIff := fun {S} =>
    MetrizableLCA.quillenConflation_iff_closed_inclusion_open_surjection_forget_kernel_cokernel
      (S := S)
  metrizableLCAForgetExact := fun hS =>
    MetrizableLCA.forgetToAddCommGrpCat_exact_of_quillenConflation hS
  metrizableLCAForgetKernel := fun hS =>
    MetrizableLCA.forgetToAddCommGrpCat_kernelForkOfQuillenConflation hS
  metrizableLCAForgetCokernel := fun hS =>
    MetrizableLCA.forgetToAddCommGrpCat_cokernelCoforkOfQuillenConflation hS
  yonedaExt := fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n
  yonedaExt_eq := rfl
  yonedaExtAddCommGroup := fun _ _ _ => inferInstance
  yonedaExtZeroEquivHom := fun X Y =>
    YonedaExt.zero_equiv_hom (C := MetrizableLCA.{0}) (X := X) (Y := Y)
  boundedDerivedInfinityCategory := P

theorem originalFourTaskProductDataOfStablePackage_boundedDerivedInfinityCategory
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).boundedDerivedInfinityCategory = P :=
  rfl

/--
Assemble original-four-task product data from the typeclass-resolved stable-instance route.

This is not a final positive witness until Lean can synthesize the listed `Dbounded
MetrizableLCA` stable instances with no local hypotheses. It keeps the remaining task-4
obligation on the mathematical instance surface instead of routing through semantic inputs.
-/
noncomputable def originalFourTaskProductDataOfMetrizableStableInstances
    [Preadditive (Dbounded MetrizableLCA.{0})]
    [HasFiniteLimits (Dbounded MetrizableLCA.{0})]
    [HasFiniteColimits (Dbounded MetrizableLCA.{0})]
    [HasZeroObject (Dbounded MetrizableLCA.{0})]
    [∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive]
    [Pretriangulated (Dbounded MetrizableLCA.{0})]
    [IsTriangulated (Dbounded MetrizableLCA.{0})] :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances

/-- The product-data stable-instance route has exactly the seven task-4 obligations. -/
def originalFourTaskMetrizableStableInstanceObligationNames : List String :=
  Dbounded.metrizableStableInstanceFieldNames

theorem originalFourTaskMetrizableStableInstanceObligationNames_count :
    originalFourTaskMetrizableStableInstanceObligationNames.length = 7 :=
  Dbounded.metrizableStableInstanceFieldNames_count

theorem originalFourTaskProductDataOfMetrizableStableInstances_boundedDerivedInfinityCategory
    [Preadditive (Dbounded MetrizableLCA.{0})]
    [HasFiniteLimits (Dbounded MetrizableLCA.{0})]
    [HasFiniteColimits (Dbounded MetrizableLCA.{0})]
    [HasZeroObject (Dbounded MetrizableLCA.{0})]
    [∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive]
    [Pretriangulated (Dbounded MetrizableLCA.{0})]
    [IsTriangulated (Dbounded MetrizableLCA.{0})] :
    originalFourTaskProductDataOfMetrizableStableInstances.boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_quillenExactCategory
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).quillenExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAExactCategory
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAConflationIff
    (P : BoundedDerived.Metrizable.StablePackage) {S : ShortComplex MetrizableLCA.{0}} :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAConflationIff
      (S := S) =
      MetrizableLCA.quillenConflation_iff_closed_inclusion_open_surjection_algebraic_exact
        (S := S) :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAForgetKernelCokernelIff
    (P : BoundedDerived.Metrizable.StablePackage) {S : ShortComplex MetrizableLCA.{0}} :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAForgetKernelCokernelIff
      (S := S) =
      MetrizableLCA.quillenConflation_iff_closed_inclusion_open_surjection_forget_kernel_cokernel
        (S := S) :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAForgetExact
    (P : BoundedDerived.Metrizable.StablePackage) {S : ShortComplex MetrizableLCA.{0}}
    (hS : QuillenExactCategory.Conflation S) :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAForgetExact hS =
      MetrizableLCA.forgetToAddCommGrpCat_exact_of_quillenConflation hS :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAForgetKernel
    (P : BoundedDerived.Metrizable.StablePackage) {S : ShortComplex MetrizableLCA.{0}}
    (hS : QuillenExactCategory.Conflation S) :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAForgetKernel hS =
      MetrizableLCA.forgetToAddCommGrpCat_kernelForkOfQuillenConflation hS :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAForgetCokernel
    (P : BoundedDerived.Metrizable.StablePackage) {S : ShortComplex MetrizableLCA.{0}}
    (hS : QuillenExactCategory.Conflation S) :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAForgetCokernel hS =
      MetrizableLCA.forgetToAddCommGrpCat_cokernelCoforkOfQuillenConflation hS :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_yonedaExt
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

theorem originalFourTaskProductDataOfStablePackage_yonedaExtZeroEquivHom
    (P : BoundedDerived.Metrizable.StablePackage) (X Y : MetrizableLCA.{0}) :
    (originalFourTaskProductDataOfStablePackage P).yonedaExtZeroEquivHom X Y =
      YonedaExt.zero_equiv_hom (C := MetrizableLCA.{0}) (X := X) (Y := Y) :=
  rfl

@[reducible]
noncomputable def originalFourTaskProductDataOfStablePackage_yonedaExtAddCommGroup
    (P : BoundedDerived.Metrizable.StablePackage) (X Y : MetrizableLCA.{0}) (n : ℕ) :
    AddCommGroup ((originalFourTaskProductDataOfStablePackage P).yonedaExt X Y n) :=
  (originalFourTaskProductDataOfStablePackage P).yonedaExtAddCommGroup X Y n

/--
Assemble product data from the W1537 direct-source stable-instance facts exposed
by the product-facing bounded-derived bridge.
-/
noncomputable def originalFourTaskProductDataOfStableInstanceFactsW1537
    (facts : BoundedDerived.Metrizable.StableInstanceFacts) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfInstanceFacts facts)

theorem originalFourTaskProductDataOfStableInstanceFactsW1537_boundedDerivedInfinityCategory
    (facts : BoundedDerived.Metrizable.StableInstanceFacts) :
    (originalFourTaskProductDataOfStableInstanceFactsW1537
      facts).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfInstanceFacts facts :=
  rfl

theorem originalFourTaskProductDataOfStableInstanceFactsW1537_metrizableLCAExactCategory
    (facts : BoundedDerived.Metrizable.StableInstanceFacts) :
    (originalFourTaskProductDataOfStableInstanceFactsW1537
      facts).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfStableInstanceFactsW1537_yonedaExt
    (facts : BoundedDerived.Metrizable.StableInstanceFacts) :
    (originalFourTaskProductDataOfStableInstanceFactsW1537 facts).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the closedness branch where endpoint topology is
provided by endpoint strict-exact data, rather than by a W735 exact-input
record.
-/
noncomputable def originalFourTaskProductDataOfClosednessEndpointStrictExactInput
    (input : BoundedDerived.Metrizable.ClosednessEndpointStrictExactInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosednessEndpointStrictExactInput
      input)

theorem
    originalFourTaskProductDataOfClosednessEndpointStrictExactInput_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.ClosednessEndpointStrictExactInput) :
    (originalFourTaskProductDataOfClosednessEndpointStrictExactInput
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfClosednessEndpointStrictExactInput
        input :=
  rfl

theorem
    originalFourTaskProductDataOfClosednessEndpointStrictExactInput_metrizableLCAExactCategory
    (input : BoundedDerived.Metrizable.ClosednessEndpointStrictExactInput) :
    (originalFourTaskProductDataOfClosednessEndpointStrictExactInput
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfClosednessEndpointStrictExactInput_yonedaExt
    (input : BoundedDerived.Metrizable.ClosednessEndpointStrictExactInput) :
    (originalFourTaskProductDataOfClosednessEndpointStrictExactInput
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W946 closedness branch: W730 supplies the
boundary/relation data and W945 supplies localized-unit data, then the bridge
projects this reduced surface to the W944 endpoint strict-exact route.
-/
noncomputable def
    originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationInput
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput
      input)

theorem
    originalFourTaskProductDataOfW946_eq_closednessEndpointStrictExactInput
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationInput
        input =
      originalFourTaskProductDataOfClosednessEndpointStrictExactInput
        (closednessEndpointStrictExactInputOfLocalizedUnitBoundaryRelationInput
          input) :=
  rfl

theorem
    originalFourTaskProductDataOfW946_boundedDerivedInfinityCategory
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    (originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationInput
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationInput
        input :=
  rfl

theorem
    originalFourTaskProductDataOfW946_metrizableLCAExactCategory
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    (originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationInput
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfW946_yonedaExt
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationInput) :
    (originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationInput
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W947 closedness branch: target no-univ data and
matched closedness data are supplied as one provider before projecting to W946.
-/
noncomputable def
    originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
      input)

theorem
    originalFourTaskProductDataOfW947_eq_localizedUnitBoundaryRelationInput
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
        input =
      originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationInput
        (closednessEndpointLocalizedUnitBoundaryRelationInputOfTargetNoUnivClosednessInput
          input) :=
  rfl

theorem
    originalFourTaskProductDataOfW947_boundedDerivedInfinityCategory
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    (originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
        input :=
  rfl

theorem
    originalFourTaskProductDataOfW947_metrizableLCAExactCategory
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    (originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfW947_yonedaExt
    (input :
      BoundedDerived.Metrizable.ClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput) :
    (originalFourTaskProductDataOfClosednessEndpointLocalizedUnitBoundaryRelationTargetNoUnivClosednessInput
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W961 closed-embedding closedness field surface,
which exposes the W725 closed-embedding branch as raw W718/W519 fields before
feeding the checked stable ExactAt route.
-/
noncomputable def originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961
    (input : BoundedDerived.Metrizable.ClosedEmbeddingClosednessFieldsInputW961) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosedEmbeddingClosednessFieldsW961
      input)

theorem
    originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.ClosedEmbeddingClosednessFieldsInputW961) :
    (originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfClosedEmbeddingClosednessFieldsW961
        input :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961_metrizableLCAExactCategory
    (input : BoundedDerived.Metrizable.ClosedEmbeddingClosednessFieldsInputW961) :
    (originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961_yonedaExt
    (input : BoundedDerived.Metrizable.ClosedEmbeddingClosednessFieldsInputW961) :
    (originalFourTaskProductDataOfClosedEmbeddingClosednessFieldsW961 input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1539 closed-map direct-source stable bridge.
-/
noncomputable def originalFourTaskProductDataOfClosedMapDirectSourceW1539
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedMapComponents :
      BoundedDerived.Metrizable.ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider :
      BoundedDerived.Metrizable.ClosedMapCokernelProvider) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.closedMapStablePackageOfDirectSource input
      globalClosedMapComponents mappedCokernelClosedMapProvider)

/--
Assemble product data from the W1539 closed-embedding direct-source stable
bridge.
-/
noncomputable def originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedEmbeddingComponents :
      BoundedDerived.Metrizable.ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider :
      BoundedDerived.Metrizable.ClosedEmbeddingCokernelProvider) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.closedEmbeddingStablePackageOfDirectSource input
      globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

theorem
    originalFourTaskProductDataOfClosedMapDirectSourceW1539_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedMapComponents :
      BoundedDerived.Metrizable.ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider :
      BoundedDerived.Metrizable.ClosedMapCokernelProvider) :
    (originalFourTaskProductDataOfClosedMapDirectSourceW1539 input
      globalClosedMapComponents
      mappedCokernelClosedMapProvider).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.closedMapStablePackageOfDirectSource input
        globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedEmbeddingComponents :
      BoundedDerived.Metrizable.ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider :
      BoundedDerived.Metrizable.ClosedEmbeddingCokernelProvider) :
    (originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539 input
      globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.closedEmbeddingStablePackageOfDirectSource input
        globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

theorem originalFourTaskProductDataOfClosedMapDirectSourceW1539_yonedaExt
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedMapComponents :
      BoundedDerived.Metrizable.ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider :
      BoundedDerived.Metrizable.ClosedMapCokernelProvider) :
    (originalFourTaskProductDataOfClosedMapDirectSourceW1539 input
      globalClosedMapComponents mappedCokernelClosedMapProvider).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

theorem originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539_yonedaExt
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedEmbeddingComponents :
      BoundedDerived.Metrizable.ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider :
      BoundedDerived.Metrizable.ClosedEmbeddingCokernelProvider) :
    (originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539 input
      globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1496 raw 74-field surface. W1494 projects the
closed-embedding W718/W519 providers, and the W1539 direct-source bridge supplies
the bounded-derived stable package.
-/
noncomputable def originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.closedEmbeddingStablePackageOfW1496RawFieldInput
      input)

theorem
    originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput_eq_directSourceW1539
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput input =
      originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539 input
        (BoundedDerived.Metrizable.closedEmbeddingComponentProviderOfW1496RawFieldInput
          input)
        (BoundedDerived.Metrizable.closedEmbeddingCokernelProviderOfW1496RawFieldInput
          input) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    (originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.closedEmbeddingStablePackageOfW1496RawFieldInput
        input :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput_metrizableLCAExactCategory
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    (originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput_yonedaExt
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    (originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1533 closed-map direct-localization boundary
bridge.
-/
noncomputable def originalFourTaskProductDataOfClosedMapDirectLocalizationBoundaryW1533
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedMapComponents :
      BoundedDerived.Metrizable.ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider :
      BoundedDerived.Metrizable.ClosedMapCokernelProvider) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.closedMapStablePackageOfDirectLocalizationBoundary input
      globalClosedMapComponents mappedCokernelClosedMapProvider)

/--
Assemble product data from the W1533 closed-embedding direct-localization
boundary bridge.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingDirectLocalizationBoundaryW1533
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedEmbeddingComponents :
      BoundedDerived.Metrizable.ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider :
      BoundedDerived.Metrizable.ClosedEmbeddingCokernelProvider) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.closedEmbeddingStablePackageOfDirectLocalizationBoundary input
      globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

theorem
    originalFourTaskProductDataOfClosedMapDirectLocalizationBoundaryW1533_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedMapComponents :
      BoundedDerived.Metrizable.ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider :
      BoundedDerived.Metrizable.ClosedMapCokernelProvider) :
    (originalFourTaskProductDataOfClosedMapDirectLocalizationBoundaryW1533 input
      globalClosedMapComponents
      mappedCokernelClosedMapProvider).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.closedMapStablePackageOfDirectLocalizationBoundary input
        globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingDirectLocalizationBoundaryW1533_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedEmbeddingComponents :
      BoundedDerived.Metrizable.ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider :
      BoundedDerived.Metrizable.ClosedEmbeddingCokernelProvider) :
    (originalFourTaskProductDataOfClosedEmbeddingDirectLocalizationBoundaryW1533
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.closedEmbeddingStablePackageOfDirectLocalizationBoundary
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapDirectSourceW1539_eq_directLocalizationBoundaryW1533
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedMapComponents :
      BoundedDerived.Metrizable.ClosedMapComponentProvider)
    (mappedCokernelClosedMapProvider :
      BoundedDerived.Metrizable.ClosedMapCokernelProvider) :
    originalFourTaskProductDataOfClosedMapDirectSourceW1539 input
        globalClosedMapComponents mappedCokernelClosedMapProvider =
      originalFourTaskProductDataOfClosedMapDirectLocalizationBoundaryW1533 input
        globalClosedMapComponents mappedCokernelClosedMapProvider := by
  simp [originalFourTaskProductDataOfClosedMapDirectSourceW1539,
    originalFourTaskProductDataOfClosedMapDirectLocalizationBoundaryW1533,
    BoundedDerived.Metrizable.closedMapStablePackageOfDirectSource_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539_eq_directLocalizationBoundaryW1533
    (input : BoundedDerived.Metrizable.DirectSourceInput)
    (globalClosedEmbeddingComponents :
      BoundedDerived.Metrizable.ClosedEmbeddingComponentProvider)
    (mappedCokernelClosedEmbeddingProvider :
      BoundedDerived.Metrizable.ClosedEmbeddingCokernelProvider) :
    originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539 input
        globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider =
      originalFourTaskProductDataOfClosedEmbeddingDirectLocalizationBoundaryW1533 input
        globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider := by
  simp [originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539,
    originalFourTaskProductDataOfClosedEmbeddingDirectLocalizationBoundaryW1533,
    BoundedDerived.Metrizable.closedEmbeddingStablePackageOfDirectSource_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput_eq_directLocalizationBoundaryW1533
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput input =
      originalFourTaskProductDataOfClosedEmbeddingDirectLocalizationBoundaryW1533
        input
        (BoundedDerived.Metrizable.closedEmbeddingComponentProviderOfW1496RawFieldInput
          input)
        (BoundedDerived.Metrizable.closedEmbeddingCokernelProviderOfW1496RawFieldInput
          input) := by
  rw [
    originalFourTaskProductDataOfClosedEmbeddingW1496RawFieldInput_eq_directSourceW1539,
    originalFourTaskProductDataOfClosedEmbeddingDirectSourceW1539_eq_directLocalizationBoundaryW1533]

/-- Assemble product data from the current canonical stable-instance boundary. -/
noncomputable def originalFourTaskProductDataOfStableInstanceBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfStableInstanceBoundary inputs)

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

/--
Assemble product data from the direct-localization refinement of the stable
instance boundary.
-/
noncomputable def originalFourTaskProductDataOfDirectLocalizationBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfDirectLocalizationBoundary inputs)

theorem originalFourTaskProductDataOfDirectLocalizationBoundary_eq_stableInstanceBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    originalFourTaskProductDataOfDirectLocalizationBoundary inputs =
      originalFourTaskProductDataOfStableInstanceBoundary
        (Dbounded.metrizableStableInstanceBoundaryInputs_of_directLocalization
          inputs) := by
  rw [originalFourTaskProductDataOfDirectLocalizationBoundary,
    originalFourTaskProductDataOfStableInstanceBoundary,
    BoundedDerived.Metrizable.stablePackageOfDirectLocalizationBoundary_eq_stableInstanceBoundary]

theorem
    originalFourTaskProductDataOfDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    (originalFourTaskProductDataOfDirectLocalizationBoundary
      inputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
        inputs :=
  rfl

theorem
    originalFourTaskProductDataOfDirectLocalizationBoundary_metrizableLCAExactCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    (originalFourTaskProductDataOfDirectLocalizationBoundary
      inputs).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfDirectLocalizationBoundary_yonedaExt
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    (originalFourTaskProductDataOfDirectLocalizationBoundary inputs).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the target-ExactAt direct-localization refinement of the stable
instance boundary.
-/
noncomputable def originalFourTaskProductDataOfTargetExactAtDirectLocalizationBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetExactAt
      inputs)

theorem
    originalFourTaskProductDataOfTargetExactAtDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    (originalFourTaskProductDataOfTargetExactAtDirectLocalizationBoundary
      inputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetExactAtDirectLocalization
        inputs :=
  rfl

theorem
    originalFourTaskProductDataOfTargetExactAtDirectLocalizationBoundary_metrizableLCAExactCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    (originalFourTaskProductDataOfTargetExactAtDirectLocalizationBoundary
      inputs).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfTargetExactAtDirectLocalizationBoundary_yonedaExt
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetExactAtDirectLocalizationInputs) :
    (originalFourTaskProductDataOfTargetExactAtDirectLocalizationBoundary inputs).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the target-isomorphism direct-localization refinement of the stable
instance boundary.
-/
noncomputable def originalFourTaskProductDataOfTargetIsoDirectLocalizationBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_targetIso
      inputs)

theorem
    originalFourTaskProductDataOfTargetIsoDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    (originalFourTaskProductDataOfTargetIsoDirectLocalizationBoundary
      inputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryTargetIsoDirectLocalization
        inputs :=
  rfl

theorem
    originalFourTaskProductDataOfTargetIsoDirectLocalizationBoundary_metrizableLCAExactCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    (originalFourTaskProductDataOfTargetIsoDirectLocalizationBoundary
      inputs).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfTargetIsoDirectLocalizationBoundary_yonedaExt
    (inputs : Dbounded.MetrizableStableInstanceBoundaryTargetIsoDirectLocalizationInputs) :
    (originalFourTaskProductDataOfTargetIsoDirectLocalizationBoundary inputs).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the iso-closure direct-localization refinement of the stable
instance boundary.
-/
noncomputable def originalFourTaskProductDataOfIsoClosureDirectLocalizationBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_isoClosure
      inputs)

theorem
    originalFourTaskProductDataOfIsoClosureDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    (originalFourTaskProductDataOfIsoClosureDirectLocalizationBoundary
      inputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryIsoClosureDirectLocalization
        inputs :=
  rfl

theorem
    originalFourTaskProductDataOfIsoClosureDirectLocalizationBoundary_metrizableLCAExactCategory
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    (originalFourTaskProductDataOfIsoClosureDirectLocalizationBoundary
      inputs).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfIsoClosureDirectLocalizationBoundary_yonedaExt
    (inputs : Dbounded.MetrizableStableInstanceBoundaryIsoClosureDirectLocalizationInputs) :
    (originalFourTaskProductDataOfIsoClosureDirectLocalizationBoundary inputs).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the closed-map branch-localized direct-localization refinement of the
stable instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBranchLocalizedDirectLocalizationBoundary
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedMapBranchLocalizedDirectLocalizationInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_closedMapBranchLocalized
      inputs)

/--
Assemble product data from the closed-embedding branch-localized direct-localization refinement
of the stable instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingBranchLocalizedDirectLocalizationBoundary
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedEmbeddingBranchLocalizedDirectLocalizationInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.metrizableStableInstanceBoundaryDirectLocalizationInputs_of_closedEmbeddingBranchLocalized
      inputs)

theorem
    originalFourTaskProductDataOfClosedMapBranchLocalizedDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedMapBranchLocalizedDirectLocalizationInputs) :
    (originalFourTaskProductDataOfClosedMapBranchLocalizedDirectLocalizationBoundary
      inputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryClosedMapBranchLocalizedDirectLocalization
        inputs :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingBranchLocalizedDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedEmbeddingBranchLocalizedDirectLocalizationInputs) :
    (originalFourTaskProductDataOfClosedEmbeddingBranchLocalizedDirectLocalizationBoundary
      inputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryClosedEmbeddingBranchLocalizedDirectLocalization
        inputs :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBranchLocalizedDirectLocalizationBoundary_metrizableLCAExactCategory
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedMapBranchLocalizedDirectLocalizationInputs) :
    (originalFourTaskProductDataOfClosedMapBranchLocalizedDirectLocalizationBoundary
      inputs).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingBranchLocalizedDirectLocalizationBoundary_metrizableLCAExactCategory
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedEmbeddingBranchLocalizedDirectLocalizationInputs) :
    (originalFourTaskProductDataOfClosedEmbeddingBranchLocalizedDirectLocalizationBoundary
      inputs).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBranchLocalizedDirectLocalizationBoundary_yonedaExt
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedMapBranchLocalizedDirectLocalizationInputs) :
    (originalFourTaskProductDataOfClosedMapBranchLocalizedDirectLocalizationBoundary
      inputs).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingBranchLocalizedDirectLocalizationBoundary_yonedaExt
    (inputs :
      Dbounded.MetrizableStableInstanceBoundaryClosedEmbeddingBranchLocalizedDirectLocalizationInputs) :
    (originalFourTaskProductDataOfClosedEmbeddingBranchLocalizedDirectLocalizationBoundary
      inputs).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1608 closed-map input route. The remaining inputs
are the target ExactAt payload and one W735 branch, routed through the
canonical direct-localization stable-instance boundary.
-/
noncomputable def originalFourTaskProductDataOfClosedMapComparisonTargetExactAtW1608
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedMapComparisonTargetExactAtW1608
      data)

/--
Assemble product data from the W1608 closed-embedding input route. The remaining
inputs are the target ExactAt payload and one W735 branch, routed through the
canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingComparisonTargetExactAtW1608
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingComparisonTargetExactAtW1608
      data)

theorem
    originalFourTaskProductDataOfClosedMapComparisonTargetExactAtW1608_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    (originalFourTaskProductDataOfClosedMapComparisonTargetExactAtW1608 data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapComparisonTargetExactAtDirectLocalizationBoundaryW1608
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingComparisonTargetExactAtW1608_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    (originalFourTaskProductDataOfClosedEmbeddingComparisonTargetExactAtW1608 data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedEmbeddingComparisonTargetExactAtDirectLocalizationBoundaryW1608
        data :=
  rfl

/--
Assemble product data from the W1609 closed-map input route. W1609 replaces the
raw target ExactAt payload by the W790 target-homology-zero payload through
the canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapTargetHomologyZeroComparisonW1609
    (data :
      Dbounded.MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedMapTargetHomologyZeroComparisonW1609
      data)

/--
Assemble product data from the W1609 closed-embedding input route. W1609 replaces
the raw target ExactAt payload by the W790 target-homology-zero payload through
the canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609
    (data :
      Dbounded.MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonW1609
      data)

theorem
    originalFourTaskProductDataOfClosedMapTargetHomologyZeroComparisonW1609_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (originalFourTaskProductDataOfClosedMapTargetHomologyZeroComparisonW1609 data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapTargetHomologyZeroDirectLocalizationBoundaryW1609
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (originalFourTaskProductDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609 data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedEmbeddingTargetHomologyZeroDirectLocalizationBoundaryW1609
        data :=
  rfl

/--
Assemble product data from the W852 route-data input. W852 projects one
W732 route-data provider to the selected-cochain branch and then through the
canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfRouteDataSelectedCochainComparisonW852
    (routeData :
      Dbounded.MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfRouteDataSelectedCochainComparisonW852
      routeData)

theorem
    originalFourTaskProductDataOfRouteDataW852_eq_directBoundary
    (routeData :
      Dbounded.MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    originalFourTaskProductDataOfRouteDataSelectedCochainComparisonW852 routeData =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfRouteDataComparisonSelectedCochainW852
          routeData) := by
  rw [originalFourTaskProductDataOfRouteDataSelectedCochainComparisonW852,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfRouteDataW852_eq_directBoundary]

theorem
    originalFourTaskProductDataOfRouteDataW852_boundedDerivedInfinityCategory
    (routeData :
      Dbounded.MetrizableWppBoundaryRelationTargetClosednessNormalizedDataProviderW732) :
    (originalFourTaskProductDataOfRouteDataSelectedCochainComparisonW852
      routeData).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfRouteDataDirectBoundaryW852
        routeData :=
  rfl

/--
Assemble product data from the W1614 closed-map input route. W1614 derives the
selected-cochain/strict-realization side from one W735 exact-input branch through
the canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      Dbounded.MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosedMapExactInputsSelectedCochainComparisonW1614
      exactInputs)

/--
Assemble product data from the W1614 closed-embedding input route. W1614 derives
the selected-cochain/strict-realization side from one W735 exact-input branch
through the canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      Dbounded.MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
      exactInputs)

theorem
    originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614_eq_directLocalizationBoundary
    (exactInputs :
      Dbounded.MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614
        exactInputs =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
          exactInputs) := by
  rw [originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapExactInputsSelectedCochainComparisonW1614_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614_eq_directLocalizationBoundary
    (exactInputs :
      Dbounded.MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
        exactInputs =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
          exactInputs) := by
  rw [originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614_boundedDerivedInfinityCategory
    (exactInputs :
      Dbounded.MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614
      exactInputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW1614
        exactInputs :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614_boundedDerivedInfinityCategory
    (exactInputs :
      Dbounded.MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
      exactInputs).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW1614
        exactInputs :=
  rfl

/--
Assemble product data from the W1615 closed-map concrete-field surface. W1615
unpacks the W735 exact-input branch into the concrete fields it carries before
feeding W1614 through the canonical direct-localization stable-instance
boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
      data)

/--
Assemble product data from the W1615 closed-embedding concrete-field surface.
W1615 unpacks the W735 exact-input branch into the concrete fields it carries
before feeding W1614 through the canonical direct-localization stable-instance
boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (BoundedDerived.Metrizable.stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
      data)

theorem
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_eq_exactInputsSelectedCochainComparisonW1614
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
        data =
      originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614
        (Dbounded.closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_eq_exactInputsSelectedCochainComparisonW1614
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        data =
      originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
        (Dbounded.closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
          data) := by
  rw [originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
          data) := by
  rw [originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainDirectLocalizationBoundaryW1615
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_metrizableLCAExactCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_metrizableLCAExactCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_yonedaExt
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_yonedaExt
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1616 closed-map split-field surface. W1616
separates four W1615 bundled providers into their checked fields before feeding
W1615 through the canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapSplitFieldsSelectedCochainComparisonW1616
      data)

/--
Assemble product data from the W1616 closed-embedding split-field surface.
W1616 separates four W1615 bundled providers into their checked fields before
feeding W1615 through the canonical direct-localization stable-instance
boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
      data)

theorem
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
        data =
      originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
        data =
      originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_directLocalizationBoundary
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapSplitFieldsSelectedCochainComparisonW1616
          data) := by
  rw [
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615,
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary]
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_directLocalizationBoundary
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
          data) := by
  rw [
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615,
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_eq_directLocalizationBoundary]
  rfl

theorem
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    (originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    (originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_metrizableLCAExactCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    (originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_metrizableLCAExactCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    (originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_yonedaExt
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    (originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_yonedaExt
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    (originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1617 closed-map structural-field surface.
W1617 splits the W719, W722, and W720 providers into checked structural fields
before feeding the canonical W1616 direct-localization stable package.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
      data)

/--
Assemble product data from the W1617 closed-embedding structural-field surface.
W1617 splits the W719, W722, and W720 providers into checked structural fields
before feeding the canonical W1616 direct-localization stable package.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
      data)

theorem
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
        data =
      originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616
        (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
        data =
      originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
        (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_concreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
        data =
      originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
            data)) := by
  rw [
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616,
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615]

theorem
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_concreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
        data =
      originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
        (Dbounded.closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
          (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
            data)) := by
  rw [
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616,
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_concreteFieldsSelectedCochainComparisonW1615]

theorem
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_directLocalizationBoundary
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapSplitFieldsSelectedCochainComparisonW1616
          (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
            data)) := by
  rw [
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616,
    originalFourTaskProductDataOfClosedMapSplitFieldsSelectedCochainComparisonW1616_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_directLocalizationBoundary
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
          (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
            data)) := by
  rw [
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_eq_splitFieldsSelectedCochainComparisonW1616,
    originalFourTaskProductDataOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    (originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        (Dbounded.closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    (originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainDirectLocalizationBoundaryW1616
        (Dbounded.closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_metrizableLCAExactCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    (originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_metrizableLCAExactCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    (originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617_yonedaExt
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    (originalFourTaskProductDataOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617_yonedaExt
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    (originalFourTaskProductDataOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W879 closed-map direct-localization boundary.
W879 derives the WPP limit and colimit stability fields from W735/W716 boundary
data plus selected-row WPP-op providers before feeding the canonical direct-
localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879
      data)

/--
Assemble product data from the W879 closed-embedding direct-localization
boundary. W879 derives the WPP limit and colimit stability fields from W735/W716
boundary data plus selected-row WPP-op providers before feeding the canonical
direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
    (data :
      BoundedDerived.Metrizable.ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879
      data)

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedRowsW879
          data) := by
  rw [originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
          data) := by
  rw [
    originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryW879_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedRowsW879
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    (originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    (originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedEmbeddingBoundarySourcePiZeroSelectedRowsDirectLocalizationBoundaryInputW879) :
    (originalFourTaskProductDataOfClosedEmbeddingBoundarySourcePiZeroSelectedRowsW879
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1620 closed-map direct-localization boundary.
The closed-map row provider is derived from closed-embedding rows by W580 before
the data is projected to W879.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620
      data)

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_eq_selectedRowsW879
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
        data =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedRowsW879
        (Dbounded.closedMapBoundarySourcePiZeroSelectedRowsDataOfClosedEmbeddingRowsW1620
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
          data) := by
  rw [
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryW1620_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDirectLocalizationBoundaryInputW1620) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1621 closed-map direct-localization boundary.
The selected-W461 provider is derived from W735 relation/target data, and the
closed-map row provider is still derived from closed-embedding rows by W580.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621
      data)

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_eq_selectedClosedEmbeddingRowsW1620
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
        data =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsW1620
        (Dbounded.closedMapBoundarySourcePiZeroSelectedClosedEmbeddingRowsDataOfTargetDataW1621
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
          data) := by
  rw [
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryW1621_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDirectLocalizationBoundaryInputW1621) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1622 closed-map direct-localization boundary.
The row-aware closed-embedding provider is derived from W718 diagram
closed-embedding components through W714/W711/W581.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622
      data)

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_eq_targetDataClosedEmbeddingRowsW1621
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
        data =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsW1621
        (Dbounded.closedMapBoundarySourcePiZeroTargetDataClosedEmbeddingRowsDataOfGlobalClosedEmbeddingComponentsW1622
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
          data) := by
  rw [
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryW1622_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDirectLocalizationBoundaryInputW1622) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1623 closed-map direct-localization boundary.
W1519 supplies the closed-embedding closedness source from which W1623 derives
the W735 exact inputs and W718 global closed-embedding component provider.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryW1623
      data)

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623_eq_targetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
        data =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
        (Dbounded.closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfW1519ClosedEmbeddingClosednessW1623
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
          data) := by
  rw [
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryW1623_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1623) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroW1519ClosedEmbeddingClosednessW1623
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1624 closed-map direct-localization boundary.
W1007 branch-full data supplies the W735 exact inputs and W718 closed-embedding
component provider used by the W1622 surface.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1624) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryW1624
      data)

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_eq_targetDataGlobalClosedEmbeddingComponentsW1622
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1624) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
        data =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsW1622
        (Dbounded.closedMapBoundarySourcePiZeroTargetDataGlobalClosedEmbeddingComponentsDataOfBranchFullDataClosedEmbeddingClosednessW1624
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1624) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
          data) := by
  rw [
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryW1624_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1624) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1624) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1624) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1625 closed-map direct-localization boundary.
W1625 eliminates the W1007 wrapper so the remaining input is the underlying
W987 full-data provider itself.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1625) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStablePackage
    (stablePackageOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryW1625
      data)

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_eq_branchFullDataClosedEmbeddingClosednessW1624
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1625) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        data =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroBranchFullDataClosedEmbeddingClosednessW1624
        (Dbounded.branchFullDataClosedEmbeddingClosednessDataOfFullDataClosedEmbeddingClosednessW1625
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_eq_directLocalizationBoundary
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1625) :
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        data =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          data) := by
  rw [
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625,
    originalFourTaskProductDataOfDirectLocalizationBoundary,
    BoundedDerived.Metrizable.stablePackageOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryW1625_eq_directLocalizationBoundary]

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_boundedDerivedInfinityCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1625) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
      data).boundedDerivedInfinityCategory =
      Dbounded.boundedDerivedOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        data :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_metrizableLCAExactCategory
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1625) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
      data).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_yonedaExt
    (data :
      BoundedDerived.Metrizable.ClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessDirectLocalizationBoundaryInputW1625) :
    (originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
      data).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1450 4-field construction input through the
W1625 full-data direct-localization boundary. W1450 supplies the W987 full-data
provider from W716, W717, W984, and W950 provider packages.
-/
noncomputable def
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1450FieldDataInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1450FieldDataInput
      input)

theorem
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary_eq_w1625
    (input : BoundedDerived.Metrizable.W1450FieldDataInput) :
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1450FieldDataInput
          input) :=
  rfl

theorem
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary_eq_directLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1450FieldDataInput) :
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1450FieldDataInput
            input)) :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_eq_directLocalizationBoundary
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1450FieldDataInput
      input)

theorem
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.W1450FieldDataInput) :
    (originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary
        input :=
  rfl

theorem
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary_metrizableLCAExactCategory
    (input : BoundedDerived.Metrizable.W1450FieldDataInput) :
    (originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary_yonedaExt
    (input : BoundedDerived.Metrizable.W1450FieldDataInput) :
    (originalFourTaskProductDataOfW1450FieldDataInputViaFullDataDirectLocalizationBoundary
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1479 62-field input through the W1625
full-data direct-localization boundary. This uses W1479's existing W987
full-data provider without adding the later W1490/W1496 surfaces.
-/
noncomputable def
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1479RawFieldInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1479RawFieldInput
      input)

theorem
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary_eq_w1625
    (input : BoundedDerived.Metrizable.W1479RawFieldInput) :
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1479RawFieldInput
          input) :=
  rfl

theorem
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary_eq_directLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1479RawFieldInput) :
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1479RawFieldInput
            input)) :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_eq_directLocalizationBoundary
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1479RawFieldInput
      input)

theorem
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.W1479RawFieldInput) :
    (originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary
        input :=
  rfl

theorem
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary_metrizableLCAExactCategory
    (input : BoundedDerived.Metrizable.W1479RawFieldInput) :
    (originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary_yonedaExt
    (input : BoundedDerived.Metrizable.W1479RawFieldInput) :
    (originalFourTaskProductDataOfW1479RawFieldInputViaFullDataDirectLocalizationBoundary
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1490 73-field input through the W1625
full-data direct-localization boundary. This bypasses the later W1494/W1496
74-field surface by using W1490's existing W987 full-data provider.
-/
noncomputable def
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1490RawFieldInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1490RawFieldInput
      input)

theorem
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary_eq_w1625
    (input : BoundedDerived.Metrizable.W1490RawFieldInput) :
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1490RawFieldInput
          input) :=
  rfl

theorem
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary_eq_directLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1490RawFieldInput) :
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1490RawFieldInput
            input)) :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_eq_directLocalizationBoundary
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1490RawFieldInput
      input)

theorem
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.W1490RawFieldInput) :
    (originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary
        input :=
  rfl

theorem
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary_metrizableLCAExactCategory
    (input : BoundedDerived.Metrizable.W1490RawFieldInput) :
    (originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary_yonedaExt
    (input : BoundedDerived.Metrizable.W1490RawFieldInput) :
    (originalFourTaskProductDataOfW1490RawFieldInputViaFullDataDirectLocalizationBoundary
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

/--
Assemble product data from the W1496 raw-field input through the W1625
full-data direct-localization boundary. W1496 constructs the W987 full-data
provider, and W1625 removes the W1007 wrapper from that downstream surface.
-/
noncomputable def
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1496RawFieldInput
      input)

theorem
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary_eq_w1625
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
        (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1496RawFieldInput
          input) :=
  rfl

theorem
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary_eq_directLocalizationBoundary
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
        input =
      originalFourTaskProductDataOfDirectLocalizationBoundary
        (Dbounded.directLocalizationBoundaryInputsOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625
          (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1496RawFieldInput
            input)) :=
  originalFourTaskProductDataOfClosedMapBoundarySourcePiZeroFullDataClosedEmbeddingClosednessW1625_eq_directLocalizationBoundary
    (BoundedDerived.Metrizable.fullDataDirectLocalizationBoundaryInputOfW1496RawFieldInput
      input)

theorem
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary_boundedDerivedInfinityCategory
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    (originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
      input).boundedDerivedInfinityCategory =
      BoundedDerived.Metrizable.stablePackageOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
        input :=
  rfl

theorem
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary_metrizableLCAExactCategory
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    (originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
      input).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
  rfl

theorem
    originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary_yonedaExt
    (input : BoundedDerived.Metrizable.W1496RawFieldInput) :
    (originalFourTaskProductDataOfW1496RawFieldInputViaFullDataDirectLocalizationBoundary
      input).yonedaExt =
      fun X Y n => YonedaExt (C := MetrizableLCA.{0}) X Y n :=
  rfl

end LeanLCAExactChallenge
