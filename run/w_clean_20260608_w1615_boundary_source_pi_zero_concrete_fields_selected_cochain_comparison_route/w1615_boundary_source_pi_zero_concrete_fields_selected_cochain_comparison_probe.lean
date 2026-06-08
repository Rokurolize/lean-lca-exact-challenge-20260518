import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
#check closedEmbeddingExactInputsOfConcreteFieldsSelectedCochainComparisonW1615
#check productEvidenceOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
#check productEvidenceOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
#check boundedDerivedOfClosedMapConcreteFieldsSelectedCochainComparisonW1615
#check boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
#check currentW1615BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRoute_productSuccess

noncomputable def probeClosedMapW1615Product
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapConcreteFieldsSelectedCochainComparisonW1615 data

noncomputable def probeClosedEmbeddingW1615Product
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    data

noncomputable def probeClosedMapW1615BoundedDerived
    (data :
      MetrizableClosedMapBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapConcreteFieldsSelectedCochainComparisonW1615 data

noncomputable def probeClosedEmbeddingW1615BoundedDerived
    (data :
      MetrizableClosedEmbeddingBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonBranchDataW1615) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingConcreteFieldsSelectedCochainComparisonW1615
    data

theorem probeBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputCountW1615 :
    boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615.length =
      9 :=
  boundarySourcePiZeroConcreteFieldsSelectedCochainComparisonInputNamesW1615_count

theorem probeW1615ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRouteStateW1615;
      state.productSuccessClaimed) =
      false :=
  currentW1615BoundarySourcePiZeroConcreteFieldsSelectedCochainComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
