import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
#check closedEmbeddingSplitFieldsOfStructuralFieldsSelectedCochainComparisonW1617
#check productEvidenceOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
#check productEvidenceOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
#check boundedDerivedOfClosedMapStructuralFieldsSelectedCochainComparisonW1617
#check boundedDerivedOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
#check currentW1617BoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRoute_productSuccess

noncomputable def probeClosedMapW1617Product
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapStructuralFieldsSelectedCochainComparisonW1617 data

noncomputable def probeClosedEmbeddingW1617Product
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    data

noncomputable def probeClosedMapW1617BoundedDerived
    (data :
      MetrizableClosedMapBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapStructuralFieldsSelectedCochainComparisonW1617 data

noncomputable def probeClosedEmbeddingW1617BoundedDerived
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonBranchDataW1617) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingStructuralFieldsSelectedCochainComparisonW1617
    data

theorem
    probeBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputCountW1617 :
    boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617.length =
      21 :=
  boundarySourcePiZeroStructuralFieldsSelectedCochainComparisonInputNamesW1617_count

theorem probeW1617ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRouteStateW1617;
      state.productSuccessClaimed) =
      false :=
  currentW1617BoundarySourcePiZeroStructuralFieldsSelectedCochainComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
