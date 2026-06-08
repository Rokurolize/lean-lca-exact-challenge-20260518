import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroTargetIsoComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapTargetHomologyZeroComparisonDataOfTargetIsoW1610
#check closedEmbeddingTargetHomologyZeroComparisonDataOfTargetIsoW1610
#check productEvidenceOfClosedMapTargetIsoComparisonW1610
#check productEvidenceOfClosedEmbeddingTargetIsoComparisonW1610
#check boundedDerivedOfClosedMapTargetIsoComparisonW1610
#check boundedDerivedOfClosedEmbeddingTargetIsoComparisonW1610
#check currentW1610BoundarySourcePiZeroTargetIsoComparisonRoute_productSuccess

noncomputable def probeClosedMapW1610Product
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapTargetIsoComparisonW1610 data

noncomputable def probeClosedEmbeddingW1610Product
    (data : MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingTargetIsoComparisonW1610 data

noncomputable def probeClosedMapW1610BoundedDerived
    (data : MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapTargetIsoComparisonW1610 data

noncomputable def probeClosedEmbeddingW1610BoundedDerived
    (data : MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingTargetIsoComparisonW1610 data

theorem probeBoundarySourcePiZeroTargetIsoComparisonInputCountW1610 :
    boundarySourcePiZeroTargetIsoComparisonInputNamesW1610.length = 2 :=
  boundarySourcePiZeroTargetIsoComparisonInputNamesW1610_count

theorem probeW1610ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroTargetIsoComparisonRouteStateW1610;
      state.productSuccessClaimed) =
      false :=
  currentW1610BoundarySourcePiZeroTargetIsoComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
