import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW870BranchDispatchGuardW1521
import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataExactInputsComparisonSelectedCochainStableConvergenceFieldSplitGuardW1372

/-!
W1522 specializes the W1521 W870 branch-dispatch surface to the existing W1372
W870-to-W869 and W869-to-W868 selected-cochain convergence guard. W1521 exposes
the W870 exact-input branch; W1522 records the W831 comparison-isomorphism
specialization at W869 and the W850 selected-cochain direct-source assembly at
W868.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1522 reuses the W1521 W870 branch-dispatch surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputW1521

/-- W1522 closed-map W847 selected-cochain data built from the W1521 W870 branch. -/
def closedMapSelectedCochainDataOfW869W868ConvergenceW1522
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedMapSelectedCochainDirectSourceDataOfExactInputsW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1522 closed-embedding W847 selected-cochain data built from the W1521 W870 branch. -/
def closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1522 closed-map W847 data carries the W1521 W870 exact inputs. -/
theorem w1522ClosedMapSelectedCochainDataExactInputsFieldW850
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
        input globalClosedMapComponents mappedCokernelClosedMapProvider).exactInputs =
      closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1522 closed-embedding W847 data carries the W1521 W870 exact inputs. -/
theorem w1522ClosedEmbeddingSelectedCochainDataExactInputsFieldW850
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider).exactInputs =
      closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1522 closed-map W847 data uses W849 strictification from W831 comparison. -/
theorem w1522ClosedMapSelectedCochainDataStrictificationFieldW850
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).selectedCochainStrictification
        (T := T) hT h₁ h₃ =
      selectedCochainStrictificationOfClosedMapExactInputsW849
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider)
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1522 closed-embedding W847 data uses W849 strictification from W831 comparison. -/
theorem w1522ClosedEmbeddingSelectedCochainDataStrictificationFieldW850
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).selectedCochainStrictification
        (T := T) hT h₁ h₃ =
      selectedCochainStrictificationOfClosedEmbeddingExactInputsW849
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1522 closed-map W870 direct calculus delegates to W869. -/
theorem w1522ClosedMapDirectCalculusRunsThroughW869W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w870ClosedMapDirectCalculusRunsThroughW869W1372
    (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1522 closed-embedding W870 direct calculus delegates to W869. -/
theorem w1522ClosedEmbeddingDirectCalculusRunsThroughW869W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w870ClosedEmbeddingDirectCalculusRunsThroughW869W1372
    (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1522 closed-map W870 stable package delegates to W869. -/
theorem w1522ClosedMapStablePackageRunsThroughW869W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w870ClosedMapStablePackageRunsThroughW869W1372
    (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1522 closed-embedding W870 stable package delegates to W869. -/
theorem w1522ClosedEmbeddingStablePackageRunsThroughW869W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
  w870ClosedEmbeddingStablePackageRunsThroughW869W1372
    (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1522 closed-map W869 direct calculus delegates to W868. -/
theorem w1522ClosedMapDirectCalculusRunsThroughW868W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w869ClosedMapDirectCalculusRunsThroughW850W868W1372
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1522 closed-embedding W869 direct calculus delegates to W868. -/
theorem w1522ClosedEmbeddingDirectCalculusRunsThroughW868W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  w869ClosedEmbeddingDirectCalculusRunsThroughW850W868W1372
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1522 closed-map W869 stable package delegates to W868. -/
theorem w1522ClosedMapStablePackageRunsThroughW868W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  w869ClosedMapStablePackageRunsThroughW850W868W1372
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1522 closed-embedding W869 stable package delegates to W868. -/
theorem w1522ClosedEmbeddingStablePackageRunsThroughW868W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  w869ClosedEmbeddingStablePackageRunsThroughW850W868W1372
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1522 composes the closed-map W1519/W1521 direct path through W869. -/
theorem w1522ClosedMapDirectCalculusRunsThroughW869W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1521ClosedMapDirectCalculusRunsThroughW870W1519W1520W1373
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapDirectCalculusRunsThroughW869W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1522 composes the closed-embedding W1519/W1521 direct path through W869. -/
theorem w1522ClosedEmbeddingDirectCalculusRunsThroughW869W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1521ClosedEmbeddingDirectCalculusRunsThroughW870W1519W1520W1373
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingDirectCalculusRunsThroughW869W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1522 composes the closed-map W1519/W1521 stable path through W869. -/
theorem w1522ClosedMapStablePackageRunsThroughW869W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainStableExactAtW870
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1521ClosedMapStablePackageRunsThroughW870W1519W1520W1373
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapStablePackageRunsThroughW869W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1522 composes the closed-embedding W1519/W1521 stable path through W869. -/
theorem w1522ClosedEmbeddingStablePackageRunsThroughW869W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainStableExactAtW870
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1521ClosedEmbeddingStablePackageRunsThroughW870W1519W1520W1373
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingStablePackageRunsThroughW869W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1522 composes the closed-map W1519/W1521 direct path through W868. -/
theorem w1522ClosedMapDirectCalculusRunsThroughW868W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapDirectCalculusRunsThroughW869W1519W1521W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapDirectCalculusRunsThroughW868W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1522 composes the closed-embedding W1519/W1521 direct path through W868. -/
theorem w1522ClosedEmbeddingDirectCalculusRunsThroughW868W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingDirectCalculusRunsThroughW869W1519W1521W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingDirectCalculusRunsThroughW868W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1522 composes the closed-map W1519/W1521 stable path through W868. -/
theorem w1522ClosedMapStablePackageRunsThroughW868W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapStablePackageRunsThroughW869W1519W1521W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapSelectedCochainDirectSourceStableExactAtW868
        (closedMapSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1522ClosedMapStablePackageRunsThroughW868W1372
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1522 composes the closed-embedding W1519/W1521 stable path through W868. -/
theorem w1522ClosedEmbeddingStablePackageRunsThroughW868W1519W1521W1372
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainStableExactAtW869
        universalLeftRightComparisonIso_of_comparisonBijectivityW831
        (closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingStablePackageRunsThroughW869W1519W1521W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainDirectSourceStableExactAtW868
        (closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1522ClosedEmbeddingStablePackageRunsThroughW868W1372
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1522 keeps the W1521 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W870BranchDispatchInputNamesW1521_count

/-- Current W1522 nonterminal W869/W868 convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceStateW1522 :
    Type where
  seed : String
  declarations : List String
  selectedCochainDataResult : String
  w869Result : String
  w868Result : String
  remainingInputs : List String
  w869RemainingInputs : List String
  w868RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1522 records the W1521-to-W1372 W869/W868 convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceStateW1522 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceStateW1522 where
  seed :=
    "w1522-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w869-w868-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputW1522",
      "closedMapSelectedCochainDataOfW869W868ConvergenceW1522",
      "closedEmbeddingSelectedCochainDataOfW869W868ConvergenceW1522",
      "w1522ClosedMapSelectedCochainDataExactInputsFieldW850",
      "w1522ClosedEmbeddingSelectedCochainDataExactInputsFieldW850",
      "w1522ClosedMapSelectedCochainDataStrictificationFieldW850",
      "w1522ClosedEmbeddingSelectedCochainDataStrictificationFieldW850",
      "w1522ClosedMapDirectCalculusRunsThroughW869W1372",
      "w1522ClosedEmbeddingDirectCalculusRunsThroughW869W1372",
      "w1522ClosedMapStablePackageRunsThroughW869W1372",
      "w1522ClosedEmbeddingStablePackageRunsThroughW869W1372",
      "w1522ClosedMapDirectCalculusRunsThroughW868W1372",
      "w1522ClosedEmbeddingDirectCalculusRunsThroughW868W1372",
      "w1522ClosedMapStablePackageRunsThroughW868W1372",
      "w1522ClosedEmbeddingStablePackageRunsThroughW868W1372",
      "w1522ClosedMapDirectCalculusRunsThroughW869W1519W1521W1372",
      "w1522ClosedEmbeddingDirectCalculusRunsThroughW869W1519W1521W1372",
      "w1522ClosedMapStablePackageRunsThroughW869W1519W1521W1372",
      "w1522ClosedEmbeddingStablePackageRunsThroughW869W1519W1521W1372",
      "w1522ClosedMapDirectCalculusRunsThroughW868W1519W1521W1372",
      "w1522ClosedEmbeddingDirectCalculusRunsThroughW868W1519W1521W1372",
      "w1522ClosedMapStablePackageRunsThroughW868W1519W1521W1372",
      "w1522ClosedEmbeddingStablePackageRunsThroughW868W1519W1521W1372",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522_count"]
  selectedCochainDataResult :=
    "proved: W1521 closed-map and closed-embedding W870 exact-input branches \
      assemble W847 selected-cochain direct-source data through W850/W849"
  w869Result :=
    "proved: W1521 W870 direct-calculus and stable-package branches delegate \
      through W1372 to W869 with the W831 universal comparison isomorphism"
  w868Result :=
    "proved: W1519/W1521 direct-calculus and stable-package paths compose \
      through W869 to W868 on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceInputNamesW1522
  w869RemainingInputs :=
    exactInputsSelectedCochainStableExactAtInputNamesW869
  w868RemainingInputs :=
    selectedCochainDirectSourceStableExactAtExpandedInputNamesW868
  productSuccessClaimed := false

theorem currentW1522W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868Convergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W869W868ConvergenceStateW1522.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
