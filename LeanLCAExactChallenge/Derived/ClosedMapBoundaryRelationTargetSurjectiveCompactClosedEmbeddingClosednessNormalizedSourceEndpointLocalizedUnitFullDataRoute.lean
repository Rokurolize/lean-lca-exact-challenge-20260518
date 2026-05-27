import LeanLCAExactChallenge.Derived.ClosedMapBoundaryRelationTargetSurjectiveCompactClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitDataFromFullDataRoute

/-!
W997 packages the remaining W996 target-surjective-compact and branch-full-data
inputs behind one nonterminal provider boundary. This is not product completion:
the new provider still contains W715 target surjective-compact data and W987
branch-specific full data.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open DirectWppLimitFiniteShapeTransfer
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpSelectedW461TransportedPointIsoProviderV370SupportW506
open WppOpClosedNatTransOrdinaryRelationTopologyV370SupportW511
open WppOpClosedNatTransOrdinaryRelationFieldsV370SupportW512
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484
open WppOpClosedRangeMappedCokernelPreservationV370SupportW519

namespace Dbounded

/--
W997 data surface: one branch-full-data provider containing the remaining W715
target surjective-compact data and W987 branch-specific full data.
-/
structure BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997 :
    Type 2 where
  targetSurjectiveCompactData :
    TargetSurjectiveCompactForTargetProviderW715
  branchFullData :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987

/-- W997 projects W715 target surjective-compact data. -/
def targetSurjectiveCompactDataOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    TargetSurjectiveCompactForTargetProviderW715 :=
  data.targetSurjectiveCompactData

/-- W997 projects W987 branch-specific full data. -/
def branchFullDataOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  data.branchFullData

/-- W997 builds the W996 data surface from one branch-full-data provider. -/
def targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    BoundaryRelationTargetSurjectiveCompactFullDataProviderW996
    where
  targetSurjectiveCompactData :=
    targetSurjectiveCompactDataOfTargetSurjectiveCompactBranchFullDataW997
      data
  fullData :=
    branchFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data

/-- W997 builds the W995 data surface through W996. -/
def targetProviderDataOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    BoundaryRelationTargetSurjectiveCompactTargetProviderDataProviderW995 :=
  targetProviderDataOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/-- W997 constructs the W994 normalized-source/endpoint data through W996. -/
def normalizedSourceEndpointDataOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    BoundaryRelationTargetSurjectiveCompactClosedEmbeddingNormalizedSourceEndpointLocalizedUnitDataProviderW994 :=
  normalizedSourceEndpointDataOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/-- W997 constructs W987 full data through W996. -/
def fullDataOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    BoundaryRelationTargetClosedEmbeddingClosednessNormalizedSourceEndpointLocalizedUnitFullDataProviderW987 :=
  fullDataOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/- W997 exposes W981 leaves through W996. -/
noncomputable def w981LeavesOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    MetrizableWppClosedEmbeddingEndpointLocalizedUnitFullDataLeavesW977 :=
  w981LeavesOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/- W997 exposes W971 component fields through W996. -/
noncomputable def componentFieldsOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    MetrizableWppClosedEmbeddingClosednessEndpointKernelCokernelTopUnitKernelCokernelTopBoundaryRelationDataNormalizedSourceTriangulationDataIsoComponentFieldLeavesW971 :=
  componentFieldsOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/-- W997 reconstructs endpoint strict exactness through W996. -/
noncomputable def endpointStrictExactOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      MetrizableLCA.strictShortExact (K.sc i) :=
  endpointStrictExactOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/-- W997 derives unit mapping-cone algebraic exactness through W996. -/
noncomputable def unitMappingConeAlgebraicExactOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ)
      (x₂ :
        (((componentFieldsOfTargetSurjectiveCompactBranchFullDataW997 data).unitMappingConeModel X).as.sc i).X₂),
        (((componentFieldsOfTargetSurjectiveCompactBranchFullDataW997 data).unitMappingConeModel X).as.sc i).g x₂ =
            0 →
          ∃ x₁ :
            (((componentFieldsOfTargetSurjectiveCompactBranchFullDataW997 data).unitMappingConeModel X).as.sc i).X₁,
            (((componentFieldsOfTargetSurjectiveCompactBranchFullDataW997 data).unitMappingConeModel X).as.sc i).f x₁ =
              x₂ :=
  unitMappingConeAlgebraicExactOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/-- W997 reconstructs unit mapping-cone strict short exactness through W996. -/
noncomputable def unitMappingConeStrictExactOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    ∀ (X : BoundedComplexCategory MetrizableLCA.{0}) (i : ℤ),
      MetrizableLCA.strictShortExact
        (((componentFieldsOfTargetSurjectiveCompactBranchFullDataW997 data).unitMappingConeModel X).as.sc i) :=
  unitMappingConeStrictExactOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

/-- W997 wraps the unit mapping-cone isomorphism through W996. -/
@[reducible]
noncomputable def unitMappingConeIsoNonemptyOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    ∀ X : BoundedComplexCategory MetrizableLCA.{0},
      Nonempty
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (CochainComplex.mappingCone
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map
                ((componentFieldsOfTargetSurjectiveCompactBranchFullDataW997 data).boundedHomotopyLocalizedAdjunction.unit.app X)))) ≅
          (componentFieldsOfTargetSurjectiveCompactBranchFullDataW997 data).unitMappingConeModel X) :=
  unitMappingConeIsoNonemptyOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

theorem directBoundedLeftCalculusOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

noncomputable def boundedDerivedInfinityCategoryOfTargetSurjectiveCompactBranchFullDataW997
    (data :
      BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfTargetSurjectiveCompactFullDataW996
    (targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997
      data)

def targetSurjectiveCompactBranchFullDataInputNamesW997 :
    List String :=
  ["W997 target-surjective-compact branch-full-data provider"]

theorem targetSurjectiveCompactBranchFullDataInputNamesW997_count :
    targetSurjectiveCompactBranchFullDataInputNamesW997.length = 1 :=
  rfl

structure MetrizableTargetSurjectiveCompactBranchFullDataRouteStateW997 :
    Type where
  seed : String
  declarations : List String
  branchFullDataProjectionResult : String
  exactAtResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableTargetSurjectiveCompactBranchFullDataRouteStateW997 :
    MetrizableTargetSurjectiveCompactBranchFullDataRouteStateW997
    where
  seed := "w997-target-surjective-compact-branch-full-data-route"
  declarations :=
    ["BoundaryRelationTargetSurjectiveCompactBranchFullDataProviderW997",
      "targetSurjectiveCompactDataOfTargetSurjectiveCompactBranchFullDataW997",
      "branchFullDataOfTargetSurjectiveCompactBranchFullDataW997",
      "targetSurjectiveCompactFullDataOfTargetSurjectiveCompactBranchFullDataW997",
      "targetProviderDataOfTargetSurjectiveCompactBranchFullDataW997",
      "normalizedSourceEndpointDataOfTargetSurjectiveCompactBranchFullDataW997",
      "fullDataOfTargetSurjectiveCompactBranchFullDataW997",
      "w981LeavesOfTargetSurjectiveCompactBranchFullDataW997",
      "componentFieldsOfTargetSurjectiveCompactBranchFullDataW997",
      "endpointStrictExactOfTargetSurjectiveCompactBranchFullDataW997",
      "unitMappingConeAlgebraicExactOfTargetSurjectiveCompactBranchFullDataW997",
      "unitMappingConeStrictExactOfTargetSurjectiveCompactBranchFullDataW997",
      "unitMappingConeIsoNonemptyOfTargetSurjectiveCompactBranchFullDataW997",
      "directBoundedLeftCalculusOfTargetSurjectiveCompactBranchFullDataW997",
      "boundedDerivedInfinityCategoryOfTargetSurjectiveCompactBranchFullDataW997",
      "targetSurjectiveCompactBranchFullDataInputNamesW997_count"]
  branchFullDataProjectionResult :=
    "proved: W997 projects W715 target surjective-compact data and W987\
      branch-specific full data from one provider, then feeds W996"
  exactAtResult :=
    "proved: the W997 target-surjective-compact branch-full-data surface feeds\
      the W996/W995/W994/W993/W988/W987/W986/W985/W984/W983/W982/W981/W980/\
      W979/W978/W977/W976/W975/W974/W973/W972/W971/W970/W969/W968/W967/\
      W966/W965/W964/W963/W962/W961/W959/W958/W957/W956/W955/W954/W953/\
      W952 stable ExactAt route"
  remainingInputs := targetSurjectiveCompactBranchFullDataInputNamesW997
  productSuccessClaimed := false

theorem currentW997TargetSurjectiveCompactBranchFullDataRoute_productSuccess :
    (let state :=
        currentMetrizableTargetSurjectiveCompactBranchFullDataRouteStateW997;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
