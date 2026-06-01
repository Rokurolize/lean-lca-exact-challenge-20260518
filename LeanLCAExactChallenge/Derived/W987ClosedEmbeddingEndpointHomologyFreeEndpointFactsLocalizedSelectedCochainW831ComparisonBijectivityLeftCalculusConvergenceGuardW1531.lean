import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW859ClosednessBranchTargetExactAtConvergenceGuardW1530

/-!
W1531 makes the W831 comparison-bijectivity left-calculus leg explicit for the
W1530 W987 surface. W1530 names the W832 target-ExactAt left-calculus data;
W1531 records the induced W831 data, the W830 direct-bounded-left-calculus data
underneath it, and the direct-calculus route through both surfaces.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1531 reuses the W1530 W859/W832 target-ExactAt convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputW1530

/-- W1531 closed-map W831 data from the W1530 W832 branch. -/
def closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831 :=
  targetExactAtLeftCalculusDataW832
    (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1531 closed-embedding W831 data from the W1530 W832 branch. -/
def closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831 :=
  targetExactAtLeftCalculusDataW832
    (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1531 closed-map W830 data from the W831 comparison-bijectivity branch. -/
def closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableDirectBoundedLeftCalculusDataW830 :=
  directBoundedLeftCalculusDataOfComparisonBijectivityW831
    (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1531 closed-embedding W830 data from the W831 comparison-bijectivity branch. -/
def closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableDirectBoundedLeftCalculusDataW830 :=
  directBoundedLeftCalculusDataOfComparisonBijectivityW831
    (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
      input globalClosedEmbeddingComponents
      mappedCokernelClosedEmbeddingProvider)

/-- W1531 closed-map W831 exact-closed field is the W832 target-ExactAt field. -/
theorem w1531ClosedMapExactClosed2FieldW832W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).exactClosed2 =
      exactClosed2OfTargetExactAtClosedRangeW796
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).closedRangeEndpointTopology
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).targetExactAtPayload :=
  rfl

/-- W1531 closed-embedding W831 exact-closed field is the W832 target-ExactAt field. -/
theorem w1531ClosedEmbeddingExactClosed2FieldW832W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactClosed2 =
      exactClosed2OfTargetExactAtClosedRangeW796
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).closedRangeEndpointTopology
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).targetExactAtPayload :=
  rfl

/-- W1531 closed-map W831 kernel/cokernel topology field is induced from W832. -/
theorem w1531ClosedMapKernelCokernelTopologyFieldW832W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).kernelCokernelTopologyData =
      metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).closedRangeEndpointTopology :=
  rfl

/-- W1531 closed-embedding W831 kernel/cokernel topology field is induced from W832. -/
theorem w1531ClosedEmbeddingKernelCokernelTopologyFieldW832W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).kernelCokernelTopologyData =
      metrizableExactAtKernelCokernelConditionedTopologyInputs_of_closedRangeEndpointTopologyW696
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).closedRangeEndpointTopology :=
  rfl

/-- W1531 closed-map W831 localized-right-adjoint field is induced from W832. -/
theorem w1531ClosedMapLocalizedRightAdjointFieldW832W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).localizedRightAdjoint =
      boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider).localizedRightAdjointData :=
  rfl

/-- W1531 closed-embedding W831 localized-right-adjoint field is induced from W832. -/
theorem w1531ClosedEmbeddingLocalizedRightAdjointFieldW832W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).localizedRightAdjoint =
      boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider).localizedRightAdjointData :=
  rfl

/-- W1531 closed-map W830 comparison input is supplied by W831. -/
theorem w1531ClosedMapComparisonIsoFieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).comparisonIso =
      universalLeftRightComparisonIso_of_comparisonBijectivityW831 :=
  rfl

/-- W1531 closed-embedding W830 comparison input is supplied by W831. -/
theorem w1531ClosedEmbeddingComparisonIsoFieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).comparisonIso =
      universalLeftRightComparisonIso_of_comparisonBijectivityW831 :=
  rfl

/-- W1531 closed-map W830 exact-closed field is the W831 field. -/
theorem w1531ClosedMapExactClosed2FieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).exactClosed2 =
      (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).exactClosed2 :=
  rfl

/-- W1531 closed-embedding W830 exact-closed field is the W831 field. -/
theorem w1531ClosedEmbeddingExactClosed2FieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactClosed2 =
      (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactClosed2 :=
  rfl

/-- W1531 closed-map W830 kernel/cokernel topology field is the W831 field. -/
theorem w1531ClosedMapKernelCokernelTopologyFieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).kernelCokernelTopologyData =
      (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).kernelCokernelTopologyData :=
  rfl

/-- W1531 closed-embedding W830 kernel/cokernel topology field is the W831 field. -/
theorem w1531ClosedEmbeddingKernelCokernelTopologyFieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).kernelCokernelTopologyData =
      (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).kernelCokernelTopologyData :=
  rfl

/-- W1531 closed-map W830 localized-right-adjoint field is the W831 field. -/
theorem w1531ClosedMapLocalizedRightAdjointFieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).localizedRightAdjoint =
      (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).localizedRightAdjoint :=
  rfl

/-- W1531 closed-embedding W830 localized-right-adjoint field is the W831 field. -/
theorem w1531ClosedEmbeddingLocalizedRightAdjointFieldW831W830
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).localizedRightAdjoint =
      (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).localizedRightAdjoint :=
  rfl

/-- W1531 closed-map W832 direct route is the W831 direct route. -/
theorem w1531ClosedMapDirectCalculusRunsThroughW831W832
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfTargetExactAtW832
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) :=
  rfl

/-- W1531 closed-embedding W832 direct route is the W831 direct route. -/
theorem w1531ClosedEmbeddingDirectCalculusRunsThroughW831W832
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfTargetExactAtW832
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1531 closed-map W831 direct route is the W830 direct route. -/
theorem w1531ClosedMapDirectCalculusRunsThroughW830W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) :=
  rfl

/-- W1531 closed-embedding W831 direct route is the W830 direct route. -/
theorem w1531ClosedEmbeddingDirectCalculusRunsThroughW830W831
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1531 composes the closed-map W1519/W1530 direct path through W831. -/
theorem w1531ClosedMapDirectCalculusRunsThroughW831W1519W1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedMapTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1530ClosedMapDirectCalculusRunsThroughW832W1519W1529
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1531ClosedMapDirectCalculusRunsThroughW831W832
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1531 composes the closed-embedding W1519/W1530 direct path through W831. -/
theorem w1531ClosedEmbeddingDirectCalculusRunsThroughW831W1519W1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfTargetExactAtW832
        (closedEmbeddingTargetExactAtLeftCalculusDataW832OfW859ConvergenceW1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1530ClosedEmbeddingDirectCalculusRunsThroughW832W1519W1529
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1531ClosedEmbeddingDirectCalculusRunsThroughW831W832
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider

/-- W1531 composes the closed-map W1519/W1530 direct path through W830. -/
theorem w1531ClosedMapDirectCalculusRunsThroughW830W1519W1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1531ClosedMapDirectCalculusRunsThroughW831W1519W1530
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1531ClosedMapDirectCalculusRunsThroughW830W831
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1531 composes the closed-embedding W1519/W1530 direct path through W830. -/
theorem w1531ClosedEmbeddingDirectCalculusRunsThroughW830W1519W1530
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfComparisonBijectivityW831
        (closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1531ClosedEmbeddingDirectCalculusRunsThroughW831W1519W1530
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfKernelCokernelComparisonW830
        (closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1531ClosedEmbeddingDirectCalculusRunsThroughW830W831
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider

/-- W1531 keeps the W1530 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W859ClosednessBranchTargetExactAtConvergenceInputNamesW1530_count

/-- Current W1531 nonterminal W831/W830 comparison-bijectivity left-calculus state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceStateW1531 :
    Type where
  seed : String
  declarations : List String
  comparisonBijectivityResult : String
  directBoundedResult : String
  directCalculusResult : String
  remainingInputs : List String
  w831RemainingInputs : List String
  w830RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1531 records the W832-to-W831 and W831-to-W830 bridges. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceStateW1531 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceStateW1531 where
  seed :=
    "w1531-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w831-comparison-bijectivity-left-calculus-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputW1531",
      "closedMapComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531",
      "closedEmbeddingComparisonBijectivityLeftCalculusDataW831OfW832ConvergenceW1531",
      "closedMapDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531",
      "closedEmbeddingDirectBoundedLeftCalculusDataW830OfW831ConvergenceW1531",
      "w1531ClosedMapExactClosed2FieldW832W831",
      "w1531ClosedEmbeddingExactClosed2FieldW832W831",
      "w1531ClosedMapKernelCokernelTopologyFieldW832W831",
      "w1531ClosedEmbeddingKernelCokernelTopologyFieldW832W831",
      "w1531ClosedMapLocalizedRightAdjointFieldW832W831",
      "w1531ClosedEmbeddingLocalizedRightAdjointFieldW832W831",
      "w1531ClosedMapComparisonIsoFieldW831W830",
      "w1531ClosedEmbeddingComparisonIsoFieldW831W830",
      "w1531ClosedMapExactClosed2FieldW831W830",
      "w1531ClosedEmbeddingExactClosed2FieldW831W830",
      "w1531ClosedMapKernelCokernelTopologyFieldW831W830",
      "w1531ClosedEmbeddingKernelCokernelTopologyFieldW831W830",
      "w1531ClosedMapLocalizedRightAdjointFieldW831W830",
      "w1531ClosedEmbeddingLocalizedRightAdjointFieldW831W830",
      "w1531ClosedMapDirectCalculusRunsThroughW831W832",
      "w1531ClosedEmbeddingDirectCalculusRunsThroughW831W832",
      "w1531ClosedMapDirectCalculusRunsThroughW830W831",
      "w1531ClosedEmbeddingDirectCalculusRunsThroughW830W831",
      "w1531ClosedMapDirectCalculusRunsThroughW831W1519W1530",
      "w1531ClosedEmbeddingDirectCalculusRunsThroughW831W1519W1530",
      "w1531ClosedMapDirectCalculusRunsThroughW830W1519W1530",
      "w1531ClosedEmbeddingDirectCalculusRunsThroughW830W1519W1530",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531_count"]
  comparisonBijectivityResult :=
    "proved: W1530 W832 target-ExactAt data assemble W831 \
      comparison-bijectivity left-calculus data on both branches"
  directBoundedResult :=
    "proved: W831 data expose W830 direct-bounded-left-calculus data with \
      the universal comparison isomorphism supplied by W821/W765"
  directCalculusResult :=
    "proved: W1519/W1530 direct-calculus paths compose through W831 and W830 \
      on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceInputNamesW1531
  w831RemainingInputs :=
    metrizableComparisonBijectivityLeftCalculusStableRouteExpandedRequiredFieldNamesW831
  w830RemainingInputs :=
    metrizableDirectLeftCalculusStableRouteExpandedRequiredFieldNamesW830
  productSuccessClaimed := false

theorem currentW1531W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W831ComparisonBijectivityLeftCalculusConvergenceStateW1531.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
