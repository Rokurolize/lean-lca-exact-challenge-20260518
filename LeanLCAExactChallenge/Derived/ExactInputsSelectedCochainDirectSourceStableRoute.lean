import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainExactInputsRoute

/-!
W850 threads the W849 exact-input selected-cochain strictification into the
existing W847 direct-source stable route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/-- W850 closed-map W847 data assembled from W735 exact inputs and W736 comparison data. -/
noncomputable def closedMapSelectedCochainDirectSourceDataOfExactInputsW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847
    where
  exactInputs := exactInputs
  selectedCochainStrictification :=
    selectedCochainStrictificationOfClosedMapExactInputsW849
      comparisonIso exactInputs

/--
W850 closed-embedding W847 data assembled from W735 exact inputs and W736
comparison data.
-/
noncomputable def closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847
    where
  exactInputs := exactInputs
  selectedCochainStrictification :=
    selectedCochainStrictificationOfClosedEmbeddingExactInputsW849
      comparisonIso exactInputs

/-- W850 closed-map direct bounded left calculus from exact inputs plus comparison data. -/
theorem directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapSelectedCochainW847
    (closedMapSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/-- W850 closed-embedding direct bounded left calculus from exact inputs plus comparison data. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainW847
    (closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/--
W850 closed-map exact inputs as canonical direct-localization stable-instance
boundary inputs.
-/
noncomputable def
    closedMapStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedMapStableInstanceBoundaryDirectLocalizationInputsOfSelectedCochainW847
    (closedMapSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/--
W850 closed-embedding exact inputs as canonical direct-localization
stable-instance boundary inputs.
-/
noncomputable def
    closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfSelectedCochainW847
    (closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/-- W850 closed-map package through the canonical direct-localization boundary. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (closedMapStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850
      comparisonIso exactInputs)

/-- W850 closed-embedding package through the canonical direct-localization boundary. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850
      comparisonIso exactInputs)

/--
W850 closed-map bounded derived infinity-category package from exact inputs
plus comparison data.
-/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapSelectedCochainW847
    (closedMapSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

/--
W850 closed-embedding bounded derived infinity-category package from exact
inputs plus comparison data.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainW850
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainW847
    (closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
      comparisonIso exactInputs)

def exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850 :
    List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "one W735 closed-map or closed-embedding exact-input branch"]

theorem exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850_count :
    exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850.length =
      2 :=
  rfl

structure MetrizableExactInputsSelectedCochainDirectSourceStableRouteStateW850 :
    Type where
  seed : String
  declarations : List String
  dataAssemblyResult : String
  leftCalculusResult : String
  stablePackageResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableExactInputsSelectedCochainDirectSourceStableRouteStateW850 :
    MetrizableExactInputsSelectedCochainDirectSourceStableRouteStateW850
    where
  seed := "w850-exact-inputs-selected-cochain-direct-source-stable-route"
  declarations :=
    ["Dbounded.closedMapSelectedCochainDirectSourceDataOfExactInputsW850",
      "Dbounded.closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850",
      "Dbounded.directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainW850",
      "Dbounded.directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainW850",
      "Dbounded.closedMapStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850",
      "Dbounded.closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainDirectLocalizationBoundaryW850",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainDirectLocalizationBoundaryW850",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainW850",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainW850",
      "Dbounded.exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850",
      "Dbounded.exactInputsSelectedCochainDirectSourceStableRouteInputNamesW850_count"]
  dataAssemblyResult :=
    "proved: W735 exact inputs plus W736 comparison-isomorphism data assemble\
      the W847 selected-cochain direct-source route data through W849"
  leftCalculusResult :=
    "proved: the assembled W847 data supply direct bounded left calculus for\
      both exact-input branches"
  stablePackageResult :=
    "proved: the assembled W847 data supply the existing bounded derived\
      infinity-category package and canonical direct-localization boundary\
      package for both exact-input branches"
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 exact-input branch",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem currentW850ExactInputsSelectedCochainDirectSourceStableRoute_productSuccess :
    (let state :=
        currentMetrizableExactInputsSelectedCochainDirectSourceStableRouteStateW850;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
