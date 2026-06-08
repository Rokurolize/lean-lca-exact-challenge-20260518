import LeanLCAExactChallenge.Derived.ExactInputsSelectedCochainDirectSourceStableRoute
import LeanLCAExactChallenge.Derived.ComparisonBijectivityLeftCalculusRoute

/-!
W851 discharges W850's comparison-isomorphism input using the W831
comparison-bijectivity route.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W851 closed-map W847 data assembled from one W735 branch, with W831 supplying
the universal comparison isomorphism.
-/
noncomputable def closedMapSelectedCochainDirectSourceDataOfComparisonW851
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedMapSelectedCochainDirectSourceDataOfExactInputsW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/--
W851 closed-embedding W847 data assembled from one W735 branch, with W831
supplying the universal comparison isomorphism.
-/
noncomputable def closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :=
  closedEmbeddingSelectedCochainDirectSourceDataOfExactInputsW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/-- W851 closed-map direct bounded left calculus from one W735 branch. -/
theorem directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainW851
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapExactInputsSelectedCochainW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/-- W851 closed-embedding direct bounded left calculus from one W735 branch. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainW851
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingExactInputsSelectedCochainW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/--
W851 closed-map exact inputs as canonical direct-localization stable-instance
boundary inputs.
-/
noncomputable def
    closedMapStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedMapStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/--
W851 closed-embedding exact inputs as canonical direct-localization
stable-instance boundary inputs.
-/
noncomputable def
    closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableStableInstanceBoundaryDirectLocalizationInputs :=
  closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfExactInputsSelectedCochainW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/-- W851 closed-map package through the canonical direct-localization boundary. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainDirectLocalizationBoundaryW851
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (closedMapStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851
      exactInputs)

/-- W851 closed-embedding package through the canonical direct-localization boundary. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainDirectLocalizationBoundaryW851
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfMetrizableStableInstanceBoundaryDirectLocalization
    (closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851
      exactInputs)

/-- W851 closed-map bounded derived infinity-category package from one W735 branch. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainW851
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapExactInputsSelectedCochainW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

/--
W851 closed-embedding bounded derived infinity-category package from one W735
branch.
-/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainW851
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingExactInputsSelectedCochainW850
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs

def comparisonSelectedCochainStableRouteInputNamesW851 : List String :=
  ["one W735 closed-map or closed-embedding exact-input branch"]

theorem comparisonSelectedCochainStableRouteInputNamesW851_count :
    comparisonSelectedCochainStableRouteInputNamesW851.length =
      1 :=
  rfl

structure MetrizableComparisonSelectedCochainStableRouteStateW851 :
    Type where
  seed : String
  declarations : List String
  comparisonResult : String
  dataAssemblyResult : String
  leftCalculusResult : String
  stablePackageResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableComparisonSelectedCochainStableRouteStateW851 :
    MetrizableComparisonSelectedCochainStableRouteStateW851
    where
  seed := "w851-comparison-selected-cochain-stable-route"
  declarations :=
    ["Dbounded.closedMapSelectedCochainDirectSourceDataOfComparisonW851",
      "Dbounded.closedEmbeddingSelectedCochainDirectSourceDataOfComparisonW851",
      "Dbounded.directBoundedLeftCalculusOfClosedMapComparisonSelectedCochainW851",
      "Dbounded.directBoundedLeftCalculusOfClosedEmbeddingComparisonSelectedCochainW851",
      "Dbounded.closedMapStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851",
      "Dbounded.closedEmbeddingStableInstanceBoundaryDirectLocalizationInputsOfComparisonSelectedCochainW851",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainDirectLocalizationBoundaryW851",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainDirectLocalizationBoundaryW851",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedMapComparisonSelectedCochainW851",
      "Dbounded.boundedDerivedInfinityCategoryOfClosedEmbeddingComparisonSelectedCochainW851",
      "Dbounded.comparisonSelectedCochainStableRouteInputNamesW851",
      "Dbounded.comparisonSelectedCochainStableRouteInputNamesW851_count"]
  comparisonResult :=
    "proved: W831 supplies the universal left-right comparison-isomorphism input"
  dataAssemblyResult :=
    "proved: one W735 exact-input branch assembles the W847 selected-cochain\
      direct-source route data through W850"
  leftCalculusResult :=
    "proved: one W735 exact-input branch supplies direct bounded left calculus\
      for both branch shapes"
  stablePackageResult :=
    "proved: one W735 exact-input branch supplies the existing bounded derived\
      infinity-category package and canonical direct-localization boundary\
      package for both branch shapes"
  remainingInputs :=
    ["construct concrete values for one W735 exact-input branch",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem currentW851ComparisonSelectedCochainStableRoute_productSuccess :
    (let state :=
        currentMetrizableComparisonSelectedCochainStableRouteStateW851;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
