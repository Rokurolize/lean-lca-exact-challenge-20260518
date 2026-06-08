import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroStrictRealizationComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapIsoClosureComparisonDataOfStrictRealizationW1612
#check closedEmbeddingIsoClosureComparisonDataOfStrictRealizationW1612
#check productEvidenceOfClosedMapStrictRealizationComparisonW1612
#check productEvidenceOfClosedEmbeddingStrictRealizationComparisonW1612
#check boundedDerivedOfClosedMapStrictRealizationComparisonW1612
#check boundedDerivedOfClosedEmbeddingStrictRealizationComparisonW1612
#check currentW1612BoundarySourcePiZeroStrictRealizationComparisonRoute_productSuccess

noncomputable def probeClosedMapW1612Product
    (data : MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapStrictRealizationComparisonW1612 data

noncomputable def probeClosedEmbeddingW1612Product
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingStrictRealizationComparisonW1612 data

noncomputable def probeClosedMapW1612BoundedDerived
    (data : MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapStrictRealizationComparisonW1612 data

noncomputable def probeClosedEmbeddingW1612BoundedDerived
    (data :
      MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingStrictRealizationComparisonW1612 data

theorem probeBoundarySourcePiZeroStrictRealizationComparisonInputCountW1612 :
    boundarySourcePiZeroStrictRealizationComparisonInputNamesW1612.length = 2 :=
  boundarySourcePiZeroStrictRealizationComparisonInputNamesW1612_count

theorem probeW1612ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroStrictRealizationComparisonRouteStateW1612;
      state.productSuccessClaimed) =
      false :=
  currentW1612BoundarySourcePiZeroStrictRealizationComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
