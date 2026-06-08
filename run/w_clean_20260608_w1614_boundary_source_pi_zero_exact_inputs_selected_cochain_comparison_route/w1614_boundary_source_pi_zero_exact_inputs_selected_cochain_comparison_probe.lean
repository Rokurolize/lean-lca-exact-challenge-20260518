import LeanLCAExactChallenge.Derived.BoundarySourcePiZeroExactInputsSelectedCochainComparisonProductRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

#check closedMapSelectedCochainComparisonDataOfExactInputsW1614
#check closedEmbeddingSelectedCochainComparisonDataOfExactInputsW1614
#check productEvidenceOfClosedMapExactInputsSelectedCochainComparisonW1614
#check productEvidenceOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
#check boundedDerivedOfClosedMapExactInputsSelectedCochainComparisonW1614
#check boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
#check currentW1614BoundarySourcePiZeroExactInputsSelectedCochainComparisonRoute_productSuccess

noncomputable def probeClosedMapW1614Product
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedMapExactInputsSelectedCochainComparisonW1614 exactInputs

noncomputable def probeClosedEmbeddingW1614Product
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableWppKernelCokernelProductEvidenceW767 :=
  productEvidenceOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    exactInputs

noncomputable def probeClosedMapW1614BoundedDerived
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedMapExactInputsSelectedCochainComparisonW1614 exactInputs

noncomputable def probeClosedEmbeddingW1614BoundedDerived
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedOfClosedEmbeddingExactInputsSelectedCochainComparisonW1614
    exactInputs

theorem probeBoundarySourcePiZeroExactInputsSelectedCochainComparisonInputCountW1614 :
    boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614.length =
      1 :=
  boundarySourcePiZeroExactInputsSelectedCochainComparisonInputNamesW1614_count

theorem probeW1614ProductSuccessFalse :
    (have state :=
      currentMetrizableBoundarySourcePiZeroExactInputsSelectedCochainComparisonRouteStateW1614;
      state.productSuccessClaimed) =
      false :=
  currentW1614BoundarySourcePiZeroExactInputsSelectedCochainComparisonRoute_productSuccess

end Dbounded

end LeanLCAExactChallenge
