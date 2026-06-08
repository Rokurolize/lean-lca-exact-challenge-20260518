import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
#check closedEmbeddingConcreteFieldsOfSplitFieldsSelectedCochainComparisonW1616
#check productEvidenceOfClosedMapSplitFieldsSelectedCochainComparisonW1616
#check productEvidenceOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
#check boundedDerivedOfClosedMapSplitFieldsSelectedCochainComparisonW1616
#check boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
#check currentW1616BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRoute_productSuccess

noncomputable def probeClosedMapW1616Product
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapSplitFieldsSelectedCochainComparisonW1616 data

noncomputable def probeClosedEmbeddingW1616Product
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    data

noncomputable def probeClosedMapW1616BoundedDerived
    (data :
      MetrizableClosedMapBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapSplitFieldsSelectedCochainComparisonW1616 data

noncomputable def probeClosedEmbeddingW1616BoundedDerived
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonBranchDataW1616) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingSplitFieldsSelectedCochainComparisonW1616
    data

theorem probeBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputCountW1616 :
    boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616.length =
      14 :=
  boundarySourcePiZeroSplitFieldsSelectedCochainComparisonInputNamesW1616_count

theorem probeW1616ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRouteStateW1616;
      state.productSuccessClaimed) =
      false :=
  currentW1616BoundarySourcePiZeroSplitFieldsSelectedCochainComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
