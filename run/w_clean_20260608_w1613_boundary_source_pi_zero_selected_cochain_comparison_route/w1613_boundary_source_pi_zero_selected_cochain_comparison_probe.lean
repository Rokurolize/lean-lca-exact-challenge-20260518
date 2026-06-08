import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSelectedCochainComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapStrictRealizationComparisonDataOfSelectedCochainW1613
#check closedEmbeddingStrictRealizationComparisonDataOfSelectedCochainW1613
#check productEvidenceOfClosedMapSelectedCochainComparisonW1613
#check productEvidenceOfClosedEmbeddingSelectedCochainComparisonW1613
#check boundedDerivedOfClosedMapSelectedCochainComparisonW1613
#check boundedDerivedOfClosedEmbeddingSelectedCochainComparisonW1613
#check currentW1613BoundarySourcePiZeroSelectedCochainComparisonRoute_productSuccess

noncomputable def probeClosedMapW1613Product
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapSelectedCochainComparisonW1613 data

noncomputable def probeClosedEmbeddingW1613Product
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingSelectedCochainComparisonW1613 data

noncomputable def probeClosedMapW1613BoundedDerived
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapSelectedCochainComparisonW1613 data

noncomputable def probeClosedEmbeddingW1613BoundedDerived
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingSelectedCochainComparisonW1613 data

theorem probeBoundarySourcePiZeroSelectedCochainComparisonInputCountW1613 :
    boundarySourcePiZeroSelectedCochainComparisonInputNamesW1613.length = 2 :=
  boundarySourcePiZeroSelectedCochainComparisonInputNamesW1613_count

theorem probeW1613ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroSelectedCochainComparisonRouteStateW1613;
      state.productSuccessClaimed) =
      false :=
  currentW1613BoundarySourcePiZeroSelectedCochainComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
