import LeanLCAExactChallenge.Derived.TargetExactAtFromClosednessBranch

/-!
W1368 records the definitional convergence between the W856 endpoint route and
the W859 target-ExactAt route at the shared W725/W519 closedness branch.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/-- W856 closed-map branches use the W519 closed-range provider through W694. -/
theorem w856EndpointForgetClosedMapUsesW519ClosureKernelW1368
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    endpointForgetPreservesHomologyOfClosedMapW856
        mappedCokernelClosedMapProvider =
      metrizableForgetfulPreservesHomology_of_closureKernelW694
        (closureKernelProvider_of_closedRangeProvider_w519
          (closedRangeProvider_of_closedMapProvider_w519
            mappedCokernelClosedMapProvider)) :=
  rfl

/-- W856 closed-embedding branches use the W519 closed-range provider through W694. -/
theorem w856EndpointForgetClosedEmbeddingUsesW519ClosureKernelW1368
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    endpointForgetPreservesHomologyOfClosedEmbeddingW856
        mappedCokernelClosedEmbeddingProvider =
      metrizableForgetfulPreservesHomology_of_closureKernelW694
        (closureKernelProvider_of_closedRangeProvider_w519
          (closedRangeProvider_of_closedEmbeddingProvider_w519
            mappedCokernelClosedEmbeddingProvider)) :=
  rfl

/-- W856 closed-map W725 branches select the closed-map W519 homology route. -/
theorem w856ClosedMapBranchSelectsW519EndpointHomologyW1368
    (globalClosedMapComponents :
      SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    endpointForgetPreservesHomologyOfClosednessBranchW856
        (.closedMap globalClosedMapComponents mappedCokernelClosedMapProvider) =
      endpointForgetPreservesHomologyOfClosedMapW856
        mappedCokernelClosedMapProvider :=
  rfl

/-- W856 closed-embedding W725 branches select the closed-embedding W519 homology route. -/
theorem w856ClosedEmbeddingBranchSelectsW519EndpointHomologyW1368
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    endpointForgetPreservesHomologyOfClosednessBranchW856
        (.closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      endpointForgetPreservesHomologyOfClosedEmbeddingW856
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W856 reconstructs W720 with the derived homology-preservation field. -/
theorem w856EndpointStrictTopologyDataUsesClosednessHomologyW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    (endpointStrictTopologyDataOfClosednessBranchW856
        closednessData endpointFacts).endpointForgetPreservesHomology =
      endpointForgetPreservesHomologyOfClosednessBranchW856
        closednessData :=
  rfl

/-- W856 preserves the endpoint closed-embedding field from the supplied facts. -/
theorem w856EndpointStrictTopologyDataClosedEmbeddingFieldW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    (endpointStrictTopologyDataOfClosednessBranchW856
        closednessData endpointFacts).endpointClosedEmbedding =
      endpointFacts.endpointClosedEmbedding :=
  rfl

/-- W856 preserves the endpoint open-map field from the supplied facts. -/
theorem w856EndpointStrictTopologyDataOpenMapFieldW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    (endpointStrictTopologyDataOfClosednessBranchW856
        closednessData endpointFacts).endpointOpenMap =
      endpointFacts.endpointOpenMap :=
  rfl

/-- W856 preserves the endpoint ExactAt-to-epi field from the supplied facts. -/
theorem w856EndpointStrictTopologyDataEpiFieldW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts : MetrizableWppEndpointTopologyFactsProviderW856) :
    (endpointStrictTopologyDataOfClosednessBranchW856
        closednessData endpointFacts).endpointEpiOfExactAt =
      endpointFacts.endpointEpiOfExactAt :=
  rfl

/-- W859 closed-map W725 branches select the closed-map W519 closed-range provider. -/
theorem w859ClosedRangeClosedMapBranchUsesW519W1368
    (globalClosedMapComponents :
      SelectedDifferenceClosedMapDiagramComponentProviderW718)
    (mappedCokernelClosedMapProvider :
      MappedExplicitCokernelClosedMapProviderW519) :
    closedRangeProviderOfClosednessBranchW859
        (.closedMap globalClosedMapComponents mappedCokernelClosedMapProvider) =
      closedRangeProvider_of_closedMapProvider_w519
        mappedCokernelClosedMapProvider :=
  rfl

/-- W859 closed-embedding W725 branches select the closed-embedding W519 closed-range provider. -/
theorem w859ClosedRangeClosedEmbeddingBranchUsesW519W1368
    (globalClosedEmbeddingComponents :
      SelectedDifferenceClosedEmbeddingDiagramComponentProviderW718)
    (mappedCokernelClosedEmbeddingProvider :
      MappedExplicitCokernelClosedEmbeddingProviderW519) :
    closedRangeProviderOfClosednessBranchW859
        (.closedEmbedding globalClosedEmbeddingComponents
          mappedCokernelClosedEmbeddingProvider) =
      closedRangeProvider_of_closedEmbeddingProvider_w519
        mappedCokernelClosedEmbeddingProvider :=
  rfl

/-- W859 reconstructs W696 with the W725-derived closed-range provider. -/
theorem w859ClosedRangeEndpointTopologyUsesClosednessProviderW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts :
      MetrizableWppEndpointExactAtTopologyFactsProviderW859) :
    (closedRangeEndpointTopologyOfClosednessBranchW859
        closednessData endpointFacts).closedRangeProvider =
      closedRangeProviderOfClosednessBranchW859 closednessData :=
  rfl

/-- W859 preserves the closed-embedding-of-ExactAt field from the supplied facts. -/
theorem w859ClosedRangeEndpointTopologyClosedEmbeddingFieldW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts :
      MetrizableWppEndpointExactAtTopologyFactsProviderW859) :
    (closedRangeEndpointTopologyOfClosednessBranchW859
        closednessData endpointFacts).closedEmbedding_of_exactAt =
      endpointFacts.closedEmbedding_of_exactAt :=
  rfl

/-- W859 preserves the open-map-of-ExactAt field from the supplied facts. -/
theorem w859ClosedRangeEndpointTopologyOpenMapFieldW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts :
      MetrizableWppEndpointExactAtTopologyFactsProviderW859) :
    (closedRangeEndpointTopologyOfClosednessBranchW859
        closednessData endpointFacts).openMap_of_exactAt =
      endpointFacts.openMap_of_exactAt :=
  rfl

/-- W859 preserves the epi-of-ExactAt field from the supplied facts. -/
theorem w859ClosedRangeEndpointTopologyEpiFieldW1368
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (endpointFacts :
      MetrizableWppEndpointExactAtTopologyFactsProviderW859) :
    (closedRangeEndpointTopologyOfClosednessBranchW859
        closednessData endpointFacts).epi_of_exactAt =
      endpointFacts.epi_of_exactAt :=
  rfl

/-- W1368 checks the remaining endpoint-fact count inherited from W856. -/
theorem w1368EndpointFactInputCountMatchesW856 :
    endpointTopologyFactInputNamesW856.length = 3 :=
  endpointTopologyFactInputNamesW856_count

/-- W1368 checks the remaining target-ExactAt fact count inherited from W859. -/
theorem w1368EndpointExactAtFactInputCountMatchesW859 :
    endpointExactAtTopologyFactInputNamesW859.length = 3 :=
  endpointExactAtTopologyFactInputNamesW859_count

/-- W1368 checks the closedness-branch target-ExactAt route input count. -/
theorem w1368ClosednessBranchTargetExactAtInputCountMatchesW859 :
    closednessBranchTargetExactAtLeftCalculusInputNamesW859.length = 4 :=
  closednessBranchTargetExactAtLeftCalculusInputNamesW859_count

/-- Current W1368 nonterminal state. -/
structure ClosednessBranchEndpointExactAtConvergenceStateW1368 : Type where
  seed : String
  declarations : List String
  endpointRouteResult : String
  targetExactAtRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1368 records convergence of the W856 and W859 routes at W725/W519. -/
def currentClosednessBranchEndpointExactAtConvergenceStateW1368 :
    ClosednessBranchEndpointExactAtConvergenceStateW1368 where
  seed := "w1368-closedness-branch-endpoint-exact-at-convergence"
  declarations :=
    ["w856EndpointForgetClosedMapUsesW519ClosureKernelW1368",
      "w856EndpointForgetClosedEmbeddingUsesW519ClosureKernelW1368",
      "w856ClosedMapBranchSelectsW519EndpointHomologyW1368",
      "w856ClosedEmbeddingBranchSelectsW519EndpointHomologyW1368",
      "w856EndpointStrictTopologyDataUsesClosednessHomologyW1368",
      "w859ClosedRangeClosedMapBranchUsesW519W1368",
      "w859ClosedRangeClosedEmbeddingBranchUsesW519W1368",
      "w859ClosedRangeEndpointTopologyUsesClosednessProviderW1368",
      "w1368EndpointFactInputCountMatchesW856",
      "w1368EndpointExactAtFactInputCountMatchesW859",
      "w1368ClosednessBranchTargetExactAtInputCountMatchesW859"]
  endpointRouteResult :=
    "proved: W856's closed-map and closed-embedding endpoint homology fields \
      are exactly the W519 closed-range-to-W694 closure-kernel route"
  targetExactAtRouteResult :=
    "proved: W859's closed-map and closed-embedding closed-range fields are \
      exactly the same W519 branch selected by W725"
  remainingInputs :=
    endpointTopologyFactInputNamesW856 ++
      closednessBranchTargetExactAtLeftCalculusInputNamesW859
  productSuccessClaimed := false

theorem currentW1368ClosednessBranchEndpointExactAtConvergence_productSuccess :
    currentClosednessBranchEndpointExactAtConvergenceStateW1368.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
