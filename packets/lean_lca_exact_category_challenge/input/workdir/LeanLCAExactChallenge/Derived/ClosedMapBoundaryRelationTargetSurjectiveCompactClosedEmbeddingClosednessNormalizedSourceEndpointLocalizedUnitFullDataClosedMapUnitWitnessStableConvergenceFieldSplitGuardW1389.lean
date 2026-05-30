import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataClosedMapTargetCompactNoUnivStableConvergenceFieldSplitGuardW1388
import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipUnitConflationWitnessPrimitiveFieldRoute

/-!
W1389 records definitional convergence for the closed-map W931-W934 localized
unit witness chain, from objectwise unit membership through cone iso-closure,
iso-closure witnesses, and conflation witnesses.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W931 concrete leaves delegate to W930 after objectwise unit primitive bundling. -/
theorem w931ConcreteLeavesRunThroughW930W1389
    (leaves :
      MetrizableWppClosedMapTargetCompactObjectwiseUnitPrimitiveFieldLeavesW931) :
    concreteLeavesOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        leaves =
      concreteLeavesOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        (w930LeavesOfTargetCompactObjectwiseUnitPrimitiveFieldsW931 leaves) :=
  rfl

/-- W931 route data delegates to W930 after objectwise unit primitive bundling. -/
theorem w931RouteDataProviderRunsThroughW930W1389
    (leaves :
      MetrizableWppClosedMapTargetCompactObjectwiseUnitPrimitiveFieldLeavesW931) :
    routeDataProviderOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        leaves =
      routeDataProviderOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        (w930LeavesOfTargetCompactObjectwiseUnitPrimitiveFieldsW931 leaves) :=
  rfl

/-- W931 direct calculus delegates to W930 after objectwise unit primitive bundling. -/
theorem w931DirectCalculusRunsThroughW930W1389
    (leaves :
      MetrizableWppClosedMapTargetCompactObjectwiseUnitPrimitiveFieldLeavesW931) :
    directBoundedLeftCalculusOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        (w930LeavesOfTargetCompactObjectwiseUnitPrimitiveFieldsW931 leaves) :=
  rfl

/-- W931 stable package delegates to W930 after objectwise unit primitive bundling. -/
theorem w931StablePackageRunsThroughW930W1389
    (leaves :
      MetrizableWppClosedMapTargetCompactObjectwiseUnitPrimitiveFieldLeavesW931) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactNoUnivMembershipPrimitiveFieldsW930
        (w930LeavesOfTargetCompactObjectwiseUnitPrimitiveFieldsW931 leaves) :=
  rfl

/-- W932 concrete leaves delegate to W931 after unit cone iso-closure bundling. -/
theorem w932ConcreteLeavesRunThroughW931W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConeIsoClosureFieldLeavesW932) :
    concreteLeavesOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932 leaves =
      concreteLeavesOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        (w931LeavesOfUnitConeIsoClosureFieldsW932 leaves) :=
  rfl

/-- W932 route data delegates to W931 after unit cone iso-closure bundling. -/
theorem w932RouteDataProviderRunsThroughW931W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConeIsoClosureFieldLeavesW932) :
    routeDataProviderOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932 leaves =
      routeDataProviderOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        (w931LeavesOfUnitConeIsoClosureFieldsW932 leaves) :=
  rfl

/-- W932 direct calculus delegates to W931 after unit cone iso-closure bundling. -/
theorem w932DirectCalculusRunsThroughW931W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConeIsoClosureFieldLeavesW932) :
    directBoundedLeftCalculusOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        (w931LeavesOfUnitConeIsoClosureFieldsW932 leaves) :=
  rfl

/-- W932 stable package delegates to W931 after unit cone iso-closure bundling. -/
theorem w932StablePackageRunsThroughW931W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConeIsoClosureFieldLeavesW932) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactObjectwiseUnitPrimitiveFieldsW931
        (w931LeavesOfUnitConeIsoClosureFieldsW932 leaves) :=
  rfl

/-- W933 concrete leaves delegate to W932 after unit iso-closure witness bundling. -/
theorem w933ConcreteLeavesRunThroughW932W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitIsoClosureWitnessFieldLeavesW933) :
    concreteLeavesOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        leaves =
      concreteLeavesOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932
        (w932LeavesOfUnitIsoClosureWitnessFieldsW933 leaves) :=
  rfl

/-- W933 route data delegates to W932 after unit iso-closure witness bundling. -/
theorem w933RouteDataProviderRunsThroughW932W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitIsoClosureWitnessFieldLeavesW933) :
    routeDataProviderOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        leaves =
      routeDataProviderOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932
        (w932LeavesOfUnitIsoClosureWitnessFieldsW933 leaves) :=
  rfl

/-- W933 direct calculus delegates to W932 after unit iso-closure witness bundling. -/
theorem w933DirectCalculusRunsThroughW932W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitIsoClosureWitnessFieldLeavesW933) :
    directBoundedLeftCalculusOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932
        (w932LeavesOfUnitIsoClosureWitnessFieldsW933 leaves) :=
  rfl

/-- W933 stable package delegates to W932 after unit iso-closure witness bundling. -/
theorem w933StablePackageRunsThroughW932W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitIsoClosureWitnessFieldLeavesW933) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactUnitConeIsoClosureFieldsW932
        (w932LeavesOfUnitIsoClosureWitnessFieldsW933 leaves) :=
  rfl

/-- W934 concrete leaves delegate to W933 after unit conflation witness bundling. -/
theorem w934ConcreteLeavesRunThroughW933W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConflationWitnessFieldLeavesW934) :
    concreteLeavesOfClosedMapTargetCompactUnitConflationWitnessFieldsW934
        leaves =
      concreteLeavesOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        (w933LeavesOfUnitConflationWitnessFieldsW934 leaves) :=
  rfl

/-- W934 route data delegates to W933 after unit conflation witness bundling. -/
theorem w934RouteDataProviderRunsThroughW933W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConflationWitnessFieldLeavesW934) :
    routeDataProviderOfClosedMapTargetCompactUnitConflationWitnessFieldsW934
        leaves =
      routeDataProviderOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        (w933LeavesOfUnitConflationWitnessFieldsW934 leaves) :=
  rfl

/-- W934 direct calculus delegates to W933 after unit conflation witness bundling. -/
theorem w934DirectCalculusRunsThroughW933W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConflationWitnessFieldLeavesW934) :
    directBoundedLeftCalculusOfClosedMapTargetCompactUnitConflationWitnessFieldsW934
        leaves =
      directBoundedLeftCalculusOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        (w933LeavesOfUnitConflationWitnessFieldsW934 leaves) :=
  rfl

/-- W934 stable package delegates to W933 after unit conflation witness bundling. -/
theorem w934StablePackageRunsThroughW933W1389
    (leaves : MetrizableWppClosedMapTargetCompactUnitConflationWitnessFieldLeavesW934) :
    boundedDerivedInfinityCategoryOfClosedMapTargetCompactUnitConflationWitnessFieldsW934
        leaves =
      boundedDerivedInfinityCategoryOfClosedMapTargetCompactUnitIsoClosureWitnessFieldsW933
        (w933LeavesOfUnitConflationWitnessFieldsW934 leaves) :=
  rfl

/-- W1389 keeps W931-W934 input counts visible. -/
theorem w1389ClosedMapW931ToW934InputCounts :
    closedMapTargetCompactObjectwiseUnitPrimitiveFieldsInputNamesW931.length = 39 ∧
      closedMapTargetCompactUnitConeIsoClosureFieldsInputNamesW932.length = 39 ∧
      closedMapTargetCompactUnitIsoClosureWitnessFieldsInputNamesW933.length = 39 ∧
      closedMapTargetCompactUnitConflationWitnessFieldsInputNamesW934.length = 39 :=
  ⟨closedMapTargetCompactObjectwiseUnitPrimitiveFieldsInputNamesW931_count,
    closedMapTargetCompactUnitConeIsoClosureFieldsInputNamesW932_count,
    closedMapTargetCompactUnitIsoClosureWitnessFieldsInputNamesW933_count,
    closedMapTargetCompactUnitConflationWitnessFieldsInputNamesW934_count⟩

/-- Current W1389 nonterminal state. -/
structure ClosedMapUnitWitnessStableConvergenceStateW1389 :
    Type where
  seed : String
  declarations : List String
  objectwiseUnitResult : String
  coneIsoClosureResult : String
  isoClosureWitnessResult : String
  conflationWitnessResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- W1389 records W931-W934 convergence into the closed-map stable route. -/
def currentClosedMapUnitWitnessStableConvergenceStateW1389 :
    ClosedMapUnitWitnessStableConvergenceStateW1389 where
  seed := "w1389-closed-map-unit-witness-stable-convergence"
  declarations :=
    ["w931ConcreteLeavesRunThroughW930W1389",
      "w931RouteDataProviderRunsThroughW930W1389",
      "w931DirectCalculusRunsThroughW930W1389",
      "w931StablePackageRunsThroughW930W1389",
      "w932ConcreteLeavesRunThroughW931W1389",
      "w932RouteDataProviderRunsThroughW931W1389",
      "w932DirectCalculusRunsThroughW931W1389",
      "w932StablePackageRunsThroughW931W1389",
      "w933ConcreteLeavesRunThroughW932W1389",
      "w933RouteDataProviderRunsThroughW932W1389",
      "w933DirectCalculusRunsThroughW932W1389",
      "w933StablePackageRunsThroughW932W1389",
      "w934ConcreteLeavesRunThroughW933W1389",
      "w934RouteDataProviderRunsThroughW933W1389",
      "w934DirectCalculusRunsThroughW933W1389",
      "w934StablePackageRunsThroughW933W1389",
      "w1389ClosedMapW931ToW934InputCounts"]
  objectwiseUnitResult :=
    "proved: W931 objectwise localized-unit primitive delegates into W930"
  coneIsoClosureResult :=
    "proved: W932 unit cone iso-closure primitive delegates into W931"
  isoClosureWitnessResult :=
    "proved: W933 unit iso-closure witness primitive delegates into W932"
  conflationWitnessResult :=
    "proved: W934 unit conflation witness primitive delegates into W933"
  remainingInputs :=
    closedMapTargetCompactUnitConflationWitnessFieldsInputNamesW934
  productSuccessClaimed := false

theorem currentW1389ClosedMapUnitWitnessStableConvergence_productSuccess :
    currentClosedMapUnitWitnessStableConvergenceStateW1389.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
