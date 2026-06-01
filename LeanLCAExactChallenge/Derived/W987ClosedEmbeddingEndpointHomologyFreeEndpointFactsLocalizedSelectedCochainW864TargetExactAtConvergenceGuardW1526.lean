import LeanLCAExactChallenge.Derived.W987ClosedEmbeddingEndpointHomologyFreeEndpointFactsLocalizedSelectedCochainW865TargetIsoConvergenceGuardW1525

/-!
W1526 specializes the W1525 W865 target-isomorphism surface to the W864
target-ExactAt stable-ExactAt route. W1525 reaches W844 target-isomorphism
data; W1526 names the induced W843 target-ExactAt direct-source data and
records that the W1519/W1524/W1525 direct-calculus and stable-package paths run
through W864 on both branches.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

noncomputable section

/-- W1526 reuses the W1525 W865 target-isomorphism convergence surface. -/
abbrev W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526 :
    Type 2 :=
  W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputW1525

/-- W1526 closed-map W843 target-ExactAt data from the W1525 W844 branch. -/
def closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    MetrizableClosedMapTargetExactAtDirectSourceStableRouteDataW843 :=
  closedMapTargetExactAtDirectSourceDataOfTargetIsoW844
    (closedMapTargetIsoDataOfW865ConvergenceW1525
      input globalClosedMapComponents mappedCokernelClosedMapProvider)

/-- W1526 closed-embedding W843 target-ExactAt data from the W1525 W844 branch. -/
def closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    MetrizableClosedEmbeddingTargetExactAtDirectSourceStableRouteDataW843 :=
  closedEmbeddingTargetExactAtDirectSourceDataOfTargetIsoW844
    (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
      input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider)

/-- W1526 closed-map W843 data preserves the W1521 W870 exact-input branch. -/
theorem w1526ClosedMapTargetExactAtDataExactInputsFieldW843
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedMapComponents mappedCokernelClosedMapProvider).exactInputs =
      closedMapExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedMapComponents mappedCokernelClosedMapProvider :=
  rfl

/-- W1526 closed-embedding W843 data preserves the W1521 W870 exact-input branch. -/
theorem w1526ClosedEmbeddingTargetExactAtDataExactInputsFieldW843
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).exactInputs =
      closedEmbeddingExactInputsOfEndpointFactsLocalizedSelectedCochainW870BranchDispatchW1521
        input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W1526 closed-map W843 target-ExactAt payload is the W844/W808 payload. -/
theorem w1526ClosedMapTargetExactAtDataPayloadFieldW844W808
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedMapComponents
        mappedCokernelClosedMapProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      (closedMapW803DataOfTargetIsoW844
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents
          mappedCokernelClosedMapProvider)).targetExactAtPayload
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1526 closed-embedding W843 target-ExactAt payload is the W844/W808 payload. -/
theorem w1526ClosedEmbeddingTargetExactAtDataPayloadFieldW844W808
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519)
    {T : Pretriangulated.Triangle (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ))}
    (hT : T ∈ distTriang (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)))
    (h₁ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₁)
    (h₃ : exactAcyclicHomotopyObject MetrizableLCA.{0} T.obj₃) :
    (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
        input globalClosedEmbeddingComponents
        mappedCokernelClosedEmbeddingProvider).targetExactAtPayload
        (T := T) hT h₁ h₃ =
      (closedEmbeddingW803DataOfTargetIsoW844
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider)).targetExactAtPayload
        (T := T) hT h₁ h₃ :=
  rfl

/-- W1526 closed-map W865 direct calculus delegates to W864. -/
theorem w1526ClosedMapDirectCalculusRunsThroughW864W865
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1526 closed-embedding W865 direct calculus delegates to W864. -/
theorem w1526ClosedEmbeddingDirectCalculusRunsThroughW864W865
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1526 closed-map W865 stable package delegates to W864. -/
theorem w1526ClosedMapStablePackageRunsThroughW864W865
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
  rfl

/-- W1526 closed-embedding W865 stable package delegates to W864. -/
theorem w1526ClosedEmbeddingStablePackageRunsThroughW864W865
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
  rfl

/-- W1526 composes the closed-map W1519/W1525 direct path through W864. -/
theorem w1526ClosedMapDirectCalculusRunsThroughW864W1519W1525
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      directBoundedLeftCalculusOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1525ClosedMapDirectCalculusRunsThroughW865W1519W1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      directBoundedLeftCalculusOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1526ClosedMapDirectCalculusRunsThroughW864W865
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1526 composes the closed-embedding W1519/W1525 direct path through W864. -/
theorem w1526ClosedEmbeddingDirectCalculusRunsThroughW864W1519W1525
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    directBoundedLeftCalculusOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      directBoundedLeftCalculusOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1525ClosedEmbeddingDirectCalculusRunsThroughW865W1519W1524
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      directBoundedLeftCalculusOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1526ClosedEmbeddingDirectCalculusRunsThroughW864W865
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1526 composes the closed-map W1519/W1525 stable path through W864. -/
theorem w1526ClosedMapStablePackageRunsThroughW864W1519W1525
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedMapComponents : SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider : MappedExplicitCokernelClosedMapProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedMapW735W732SelectedCochainConvergenceW1519
          input globalClosedMapComponents mappedCokernelClosedMapProvider) =
      boundedDerivedInfinityCategoryOfClosedMapTargetIsoDirectSourceStableExactAtW865
        (closedMapTargetIsoDataOfW865ConvergenceW1525
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1525ClosedMapStablePackageRunsThroughW865W1519W1524
          input globalClosedMapComponents mappedCokernelClosedMapProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedMapTargetExactAtDirectSourceStableExactAtW864
        (closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedMapComponents mappedCokernelClosedMapProvider) :=
        w1526ClosedMapStablePackageRunsThroughW864W865
          input globalClosedMapComponents mappedCokernelClosedMapProvider

/-- W1526 composes the closed-embedding W1519/W1525 stable path through W864. -/
theorem w1526ClosedEmbeddingStablePackageRunsThroughW864W1519W1525
    (input :
      W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526)
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) := by
  calc
    boundedDerivedInfinityCategoryOfW732SelectedCochainStableExactAtW875
        (routeDataProviderOfClosedEmbeddingW735W732SelectedCochainConvergenceW1519
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider) =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetIsoDirectSourceStableExactAtW865
        (closedEmbeddingTargetIsoDataOfW865ConvergenceW1525
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1525ClosedEmbeddingStablePackageRunsThroughW865W1519W1524
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider
    _ =
      boundedDerivedInfinityCategoryOfClosedEmbeddingTargetExactAtDirectSourceStableExactAtW864
        (closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526
          input globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) :=
        w1526ClosedEmbeddingStablePackageRunsThroughW864W865
          input globalClosedEmbeddingComponents mappedCokernelClosedEmbeddingProvider

/-- W1526 keeps the W1525 constructor-ledger input names. -/
def w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526 :
    List String :=
  w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525

theorem w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526_count :
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526.length =
      74 := by
  simpa [
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526]
    using
      w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W865TargetIsoConvergenceInputNamesW1525_count

/-- Current W1526 nonterminal W864 target-ExactAt convergence state. -/
structure W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceStateW1526 :
    Type where
  seed : String
  declarations : List String
  targetExactAtDataResult : String
  w864Result : String
  remainingInputs : List String
  w864RemainingInputs : List String
  w843RemainingInputs : List String
  productSuccessClaimed : Bool

/-- W1526 records the W1525-to-W864 target-ExactAt convergence bridge. -/
def currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceStateW1526 :
    W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceStateW1526 where
  seed :=
    "w1526-w987-boundary-relation-target-strict-preimage-object-image-right-adjoint-target-compactness-mapped-cokernel-pi1-pi2-pi3-w864-target-exact-at-convergence"
  declarations :=
    ["W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputW1526",
      "closedMapTargetExactAtDirectSourceDataOfW864ConvergenceW1526",
      "closedEmbeddingTargetExactAtDirectSourceDataOfW864ConvergenceW1526",
      "w1526ClosedMapTargetExactAtDataExactInputsFieldW843",
      "w1526ClosedEmbeddingTargetExactAtDataExactInputsFieldW843",
      "w1526ClosedMapTargetExactAtDataPayloadFieldW844W808",
      "w1526ClosedEmbeddingTargetExactAtDataPayloadFieldW844W808",
      "w1526ClosedMapDirectCalculusRunsThroughW864W865",
      "w1526ClosedEmbeddingDirectCalculusRunsThroughW864W865",
      "w1526ClosedMapStablePackageRunsThroughW864W865",
      "w1526ClosedEmbeddingStablePackageRunsThroughW864W865",
      "w1526ClosedMapDirectCalculusRunsThroughW864W1519W1525",
      "w1526ClosedEmbeddingDirectCalculusRunsThroughW864W1519W1525",
      "w1526ClosedMapStablePackageRunsThroughW864W1519W1525",
      "w1526ClosedEmbeddingStablePackageRunsThroughW864W1519W1525",
      "w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526_count"]
  targetExactAtDataResult :=
    "proved: W1525 closed-map and closed-embedding W844 target-isomorphism data \
      assemble W843 target-ExactAt direct-source data through W808"
  w864Result :=
    "proved: W1519/W1524/W1525 direct-calculus and stable-package paths \
      compose through W865 to W864 on both closed-map and closed-embedding branches"
  remainingInputs :=
    w987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceInputNamesW1526
  w864RemainingInputs :=
    targetExactAtDirectSourceStableExactAtExpandedInputNamesW864
  w843RemainingInputs :=
    targetExactAtDirectSourceStableRouteExpandedRequiredFieldNamesW843
  productSuccessClaimed := false

theorem currentW1526W987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergence_productSuccess :
    currentW987BoundaryRelationTargetStrictPreimageObjectImageRightAdjointFunctorTargetSurjectivityCompactnessMappedCokernelPi1Pi2Pi3W864TargetExactAtConvergenceStateW1526.productSuccessClaimed =
      false :=
  rfl

end

end Dbounded

end LeanLCAExactChallenge
