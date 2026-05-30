import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import LeanLCAExactChallenge.Derived.TargetHomologyZeroStrictRealizationLeftCalculusRoute

/-!
W840 routes the W839 target-homology-zero left-calculus data through the
walking-parallel-pair finite-shape transfer construction.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/-- W840 closed-map left-calculus semantic fields selected by W839 data. -/
noncomputable def targetHomologyZeroLeftCalculusFieldsOfClosedMapW840
    (data :
      MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    Dbounded.MetrizableLeftCalculusSemanticFields := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data
  exact Dbounded.metrizableLeftCalculusSemanticFields

/-- W840 closed-embedding left-calculus semantic fields selected by W839 data. -/
noncomputable def targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839) :
    Dbounded.MetrizableLeftCalculusSemanticFields := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data
  exact Dbounded.metrizableLeftCalculusSemanticFields

/-!
The second field reuses the existing W532/W530 transfer-stable shape: a
walking-parallel-pair finite-shape transfer input plus the two triangulated
fields compatible with the selected left-calculus semantic fields.
-/

/-- W840 closed-map data for the finite-shape stable route. -/
structure MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840 :
    Type 2 where
  routeData :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839
  transferStableInputs :
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 routeData)

/-- W840 closed-embedding data for the finite-shape stable route. -/
structure MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840 :
    Type 2 where
  routeData :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839
  transferStableInputs :
    Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 routeData)

/-- W840 preserves the W839 closed-map direct-left-calculus theorem. -/
theorem directBoundedLeftCalculusOfClosedMapTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data.routeData

/-- W840 preserves the W839 closed-embedding direct-left-calculus theorem. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data.routeData

/-- W840 closed-map WPP transfer supplies the finite-limit/finite-colimit remainder. -/
noncomputable def
    finiteLimitColimitRemainderOfClosedMapTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus :=
  Dbounded.metrizableFiniteLimitColimitRemainderOfWalkingParallelPairTransfer
    data.transferStableInputs.transferInputs

/-- W840 closed-embedding WPP transfer supplies the finite-limit/finite-colimit remainder. -/
noncomputable def
    finiteLimitColimitRemainderOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    Dbounded.MetrizableFiniteLimitColimitRemainderAfterLeftCalculus :=
  Dbounded.metrizableFiniteLimitColimitRemainderOfWalkingParallelPairTransfer
    data.transferStableInputs.transferInputs

/-- W840 closed-map route derives the remaining stable fields from WPP transfer. -/
noncomputable def remainingStableFieldsOfClosedMapTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedMapTargetHomologyZeroW839 data.routeData
  exact Dbounded.metrizableRemainingStableSemanticFieldsOfWalkingParallelPairTransferForAvailable
    data.transferStableInputs

/-- W840 closed-embedding route derives the remaining stable fields from WPP transfer. -/
noncomputable def
    remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroW839 data.routeData
  exact Dbounded.metrizableRemainingStableSemanticFieldsOfWalkingParallelPairTransferForAvailable
    data.transferStableInputs

/-- W840 closed-map route derives finite limits from WPP finite-shape transfer. -/
@[reducible] noncomputable def finiteLimitsOfClosedMapTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    HasFiniteLimits (Dbounded MetrizableLCA.{0}) :=
  (remainingStableFieldsOfClosedMapTargetHomologyZeroFiniteShapeW840 data).finiteLimits

/-- W840 closed-map route derives finite colimits from WPP finite-shape transfer. -/
@[reducible] noncomputable def finiteColimitsOfClosedMapTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    HasFiniteColimits (Dbounded MetrizableLCA.{0}) :=
  (remainingStableFieldsOfClosedMapTargetHomologyZeroFiniteShapeW840 data).finiteColimits

/-- W840 closed-embedding route derives finite limits from WPP finite-shape transfer. -/
@[reducible] noncomputable def finiteLimitsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    HasFiniteLimits (Dbounded MetrizableLCA.{0}) :=
  (remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840 data).finiteLimits

/-- W840 closed-embedding route derives finite colimits from WPP finite-shape transfer. -/
@[reducible] noncomputable def finiteColimitsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    HasFiniteColimits (Dbounded MetrizableLCA.{0}) :=
  (remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840 data).finiteColimits

/-- W840 closed-map ordinary stable input assembled from W839 plus finite-shape transfer. -/
noncomputable def
    ordinaryStableInputOfClosedMapTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    Dbounded.MetrizableOrdinaryStableSemanticInput :=
  Dbounded.metrizableOrdinaryStableSemanticInputOfLeftCalculusFields
    (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840 data.routeData)
    (remainingStableFieldsOfClosedMapTargetHomologyZeroFiniteShapeW840 data)

/-- W840 closed-embedding ordinary stable input assembled from W839 plus finite-shape transfer. -/
noncomputable def
    ordinaryStableInputOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    Dbounded.MetrizableOrdinaryStableSemanticInput :=
  Dbounded.metrizableOrdinaryStableSemanticInputOfLeftCalculusFields
    (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840 data.routeData)
    (remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840 data)

/-- W840 stable category package for the closed-map target homology-zero route. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (ordinaryStableInputOfClosedMapTargetHomologyZeroFiniteShapeW840 data)

/-- W840 stable category package for the closed-embedding target homology-zero route. -/
noncomputable def
    boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840
    (data :
      MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (ordinaryStableInputOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840 data)

/-- W840 bundled input names. -/
def targetHomologyZeroFiniteShapeStableRouteInputNamesW840 : List String :=
  ["W839 target homology-zero strict-realization left-calculus route data",
    "WPP transfer-stable fields for the W839 selected left-calculus fields"]

/-- W840 keeps the finite-shape stable route to two bundled data inputs. -/
theorem targetHomologyZeroFiniteShapeStableRouteInputNamesW840_count :
    Dbounded.targetHomologyZeroFiniteShapeStableRouteInputNamesW840.length =
      2 :=
  rfl

/-- W840 requirements after finite limits and finite colimits are routed through WPP transfer. -/
def targetHomologyZeroFiniteShapeStableRouteRequiredFieldNamesW840 : List String :=
  ["closed-map or closed-embedding W839 target homology-zero data",
    "MetrizableWalkingParallelPairFiniteShapeTransferInputs",
    "Pretriangulated (Dbounded MetrizableLCA) for the W839 selected left-calculus fields",
    "IsTriangulated (Dbounded MetrizableLCA) for the W839 selected left-calculus fields"]

/-- W840 leaves four bundled finite-shape stable-route requirements. -/
theorem targetHomologyZeroFiniteShapeStableRouteRequiredFieldNamesW840_count :
    (let names := targetHomologyZeroFiniteShapeStableRouteRequiredFieldNamesW840;
      names.length) =
        4 :=
  rfl

/-- Expanded W840 requirements after replacing primitive finite limits/colimits by transfer. -/
def targetHomologyZeroFiniteShapeStableRouteExpandedRequiredFieldNamesW840 :
    List String :=
  Dbounded.targetHomologyZeroStrictRealizationLeftCalculusInputNamesW839 ++
    ["MetrizableWalkingParallelPairFiniteShapeTransferInputs",
      "Pretriangulated (Dbounded MetrizableLCA) for the W839 selected left-calculus fields",
      "IsTriangulated (Dbounded MetrizableLCA) for the W839 selected left-calculus fields"]

/-- The W840 expanded stable route has five concrete requirements. -/
theorem
    targetHomologyZeroFiniteShapeStableRouteExpandedRequiredFieldNamesW840_count :
    (let names := targetHomologyZeroFiniteShapeStableRouteExpandedRequiredFieldNamesW840;
      names.length) =
        5 :=
  rfl

/-- Current checked W840 state for the finite-shape target homology-zero route. -/
structure MetrizableTargetHomologyZeroFiniteShapeStableRouteStateW840 :
    Type where
  seed : String
  declarations : List String
  leftCalculusResult : String
  finiteShapeResult : String
  stablePackageResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W840 state. -/
def currentMetrizableTargetHomologyZeroFiniteShapeStableRouteStateW840 :
    Dbounded.MetrizableTargetHomologyZeroFiniteShapeStableRouteStateW840
    where
  seed := "w840-target-homology-zero-finite-shape-stable-route"
  declarations :=
    ["targetHomologyZeroLeftCalculusFieldsOfClosedMapW840",
      "targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840",
      "MetrizableClosedMapTargetHomologyZeroFiniteShapeStableRouteDataW840",
      "MetrizableClosedEmbeddingTargetHomologyZeroFiniteShapeStableRouteDataW840",
      "directBoundedLeftCalculusOfClosedMapTargetHomologyZeroFiniteShapeW840",
      "directBoundedLeftCalculusOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840",
      "finiteLimitColimitRemainderOfClosedMapTargetHomologyZeroFiniteShapeW840",
      "finiteLimitColimitRemainderOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840",
      "remainingStableFieldsOfClosedMapTargetHomologyZeroFiniteShapeW840",
      "remainingStableFieldsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840",
      "finiteLimitsOfClosedMapTargetHomologyZeroFiniteShapeW840",
      "finiteColimitsOfClosedMapTargetHomologyZeroFiniteShapeW840",
      "finiteLimitsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840",
      "finiteColimitsOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840",
      "ordinaryStableInputOfClosedMapTargetHomologyZeroFiniteShapeW840",
      "ordinaryStableInputOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840",
      "boundedDerivedInfinityCategoryOfClosedMapTargetHomologyZeroFiniteShapeW840",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingTargetHomologyZeroFiniteShapeW840",
      "targetHomologyZeroFiniteShapeStableRouteInputNamesW840",
      "targetHomologyZeroFiniteShapeStableRouteInputNamesW840_count",
      "targetHomologyZeroFiniteShapeStableRouteRequiredFieldNamesW840",
      "targetHomologyZeroFiniteShapeStableRouteRequiredFieldNamesW840_count",
      "targetHomologyZeroFiniteShapeStableRouteExpandedRequiredFieldNamesW840",
      "targetHomologyZeroFiniteShapeStableRouteExpandedRequiredFieldNamesW840_count"]
  leftCalculusResult :=
    "proved: W839 target homology-zero data still supply direct bounded left calculus"
  finiteShapeResult :=
    "proved: WPP finite-shape transfer derives finite limits and finite colimits " ++
      "for the selected left-calculus fields"
  stablePackageResult :=
    "proved: W840 assembles a bounded-derived infinity-category package from " ++
      "W839 plus WPP transfer-stable fields"
  derivedInputs :=
    ["HasFiniteLimits (Dbounded MetrizableLCA) from WPP finite-shape transfer",
      "HasFiniteColimits (Dbounded MetrizableLCA) from WPP finite-shape transfer"]
  remainingInputs :=
    Dbounded.targetHomologyZeroFiniteShapeStableRouteExpandedRequiredFieldNamesW840
  productSuccessClaimed := false

theorem currentW840TargetHomologyZeroFiniteShapeStableRoute_productSuccess :
    (let state := currentMetrizableTargetHomologyZeroFiniteShapeStableRouteStateW840;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
