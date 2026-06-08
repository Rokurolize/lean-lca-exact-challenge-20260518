import LeanLCAExactChallenge.BoundedDerived.Basic
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute
import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute
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
selected-cochain/strict-realization side from one W735 exact-input branch.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      Dbounded.MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
      exactInputs)

/--
Assemble product data from the W1614 closed-embedding frontier. W1614 derives
the selected-cochain/strict-realization side from one W735 exact-input branch.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    (exactInputs :
      Dbounded.MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
      exactInputs)

theorem
    originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614_boundedDerivedInfinityCategory
    (exactInputs :
      Dbounded.MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (originalFourTaskProductDataOfClosedMapExactInputsSelectedCochainComparisonW1614
      exactInputs).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedMapExactInputsSelectedCochainComparisonW1614
          exactInputs) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614_boundedDerivedInfinityCategory
    (exactInputs :
      Dbounded.MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (originalFourTaskProductDataOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
      exactInputs).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
          exactInputs) :=
  rfl

/--
Assemble product data from the W1615 closed-map concrete-field surface. W1615
unpacks the W735 exact-input branch into the concrete fields it carries before
feeding W1614.
-/
noncomputable def
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
      data)

/--
Assemble product data from the W1615 closed-embedding concrete-field surface.
W1615 unpacks the W735 exact-input branch into the concrete fields it carries
before feeding W1614.
-/
noncomputable def
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    OriginalFourTaskProductData :=
  originalFourTaskProductDataOfStableInstanceBoundary
    (Dbounded.stableBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
      data)

theorem
    originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
      data).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
          data) :=
  rfl

theorem
    originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615_boundedDerivedInfinityCategory
    (data :
      Dbounded.MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    (originalFourTaskProductDataOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
      data).boundedDerivedInfinityCategory =
      Dbounded.MetrizableStableInstanceBoundaryInputs.boundedDerivedInfinityCategory
        (Dbounded.stableBoundaryInputsOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
          data) :=
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

end LeanLCAExactChallenge
