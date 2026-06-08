import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroIsoClosureComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapTargetIsoComparisonDataOfIsoClosureW1611
#check closedEmbeddingTargetIsoComparisonDataOfIsoClosureW1611
#check productEvidenceOfClosedMapIsoClosureComparisonW1611
#check productEvidenceOfClosedEmbeddingIsoClosureComparisonW1611
#check boundedDerivedOfClosedMapIsoClosureComparisonW1611
#check boundedDerivedOfClosedEmbeddingIsoClosureComparisonW1611
#check currentW1611BoundarySourcePiZeroIsoClosureComparisonRoute_productSuccess

noncomputable def probeClosedMapW1611Product
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapIsoClosureComparisonW1611 data

noncomputable def probeClosedEmbeddingW1611Product
    (data : MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingIsoClosureComparisonW1611 data

noncomputable def probeClosedMapW1611BoundedDerived
    (data : MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapIsoClosureComparisonW1611 data

noncomputable def probeClosedEmbeddingW1611BoundedDerived
    (data : MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingIsoClosureComparisonW1611 data

theorem probeBoundarySourcePiZeroIsoClosureComparisonInputCountW1611 :
    boundarySourcePiZeroIsoClosureComparisonInputNamesW1611.length = 2 :=
  boundarySourcePiZeroIsoClosureComparisonInputNamesW1611_count

theorem probeW1611ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroIsoClosureComparisonRouteStateW1611;
      state.productSuccessClaimed) =
      false :=
  currentW1611BoundarySourcePiZeroIsoClosureComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
