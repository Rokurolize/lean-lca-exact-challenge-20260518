import LeanLCAExactChallenge.BoundedDerived.Basic
import LeanLCAExactChallenge.BoundedDerived.MetrizableStableBridge
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonProductRoute
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

theorem originalFourTaskProductDataOfStablePackage_metrizableLCAExactCategory
    (P : BoundedDerived.Metrizable.StablePackage) :
    (originalFourTaskProductDataOfStablePackage P).metrizableLCAExactCategory =
      MetrizableLCA.quillenExactCategory :=
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

/--
Assemble product data from the direct-localization refinement of the stable
instance boundary.
-/
noncomputable def originalFourTaskProductDataOfDirectLocalizationBoundary
    (inputs : Dbounded.MetrizableStableInstanceBoundaryDirectLocalizationInputs) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.metrizableStableInstanceBoundaryInputs_of_directLocalization inputs)

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
Assemble product data from the W1608 closed-map frontier. The remaining inputs
are the target ExactAt payload and one W735 branch.
-/
noncomputable def originalFourTaskProductDataOfClosedMapComparisonTargetExactAtW1608
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedMapComparisonW1608 data)

/--
Assemble product data from the W1608 closed-embedding frontier. The remaining
inputs are the target ExactAt payload and one W735 branch.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingComparisonTargetExactAtW1608
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedEmbeddingComparisonW1608 data)

theorem
    originalFourTaskProductDataOfClosedMapComparisonTargetExactAtW1608_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    (originalFourTaskProductDataOfClosedMapComparisonTargetExactAtW1608 data).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedMapComparisonW1608 data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingComparisonTargetExactAtW1608_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroComparisonTargetExactAtDataW1608) :
    (originalFourTaskProductDataOfClosedEmbeddingComparisonTargetExactAtW1608 data).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedEmbeddingComparisonW1608 data) :=
  rfl

/--
Assemble product data from the W1609 closed-map frontier. W1609 replaces the
raw target ExactAt payload by the W790 target-homology-zero payload.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapTargetHomologyZeroComparisonW1609
    (data :
      Dbounded.MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedMapTargetHomologyZeroComparisonW1609 data)

/--
Assemble product data from the W1609 closed-embedding frontier. W1609 replaces
the raw target ExactAt payload by the W790 target-homology-zero payload.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609
    (data :
      Dbounded.MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonW1609 data)

theorem
    originalFourTaskProductDataOfClosedMapTargetHomologyZeroComparisonW1609_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (originalFourTaskProductDataOfClosedMapTargetHomologyZeroComparisonW1609 data).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedMapTargetHomologyZeroComparisonW1609 data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    (originalFourTaskProductDataOfClosedEmbeddingTargetHomologyZeroComparisonW1609 data).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedEmbeddingTargetHomologyZeroComparisonW1609 data) :=
  rfl

/--
Assemble product data from the W1614 closed-map frontier. W1614 derives the
selected-cochain/strict-realization side from one W735 exact-input branch through
the canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      Dbounded.MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
      exactInputs)

/--
Assemble product data from the W1614 closed-embedding frontier. W1614 derives
the selected-cochain/strict-realization side from one W735 exact-input branch
through the canonical direct-localization stable-instance boundary.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      Dbounded.MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
      exactInputs)

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
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
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
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
      data)

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
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedMapSplitFieldsSelectedCochainComparisonW1616
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
  originalFourTaskProductDataOfDirectLocalizationBoundary
    (Dbounded.directLocalizationBoundaryInputsOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
      data)

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

end LeanLCAExactChallenge
