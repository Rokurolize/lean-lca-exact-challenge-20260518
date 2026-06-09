import LeanLCAExactChallenge.Derived.ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Dbounded
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439

#check Dbounded.targetCodomainCompactNoUnivMembershipPrimitiveOfCompactSpaceW930
#check Dbounded.targetNoUnivDataOfTargetDifferenceSurjectiveAndCompactSpaceProvidersW944

namespace Dbounded

def w944TargetNoUnivFromSurjectiveCompactSpaceProbe
    (targetDifferenceSurjectiveProvider :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
        targetDifferenceSurjectivePrimitiveW923 Y)
    (targetCodomainCompactSpaceProvider :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
        CompactSpace (wppOpCodomainW441 Y)) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfTargetDifferenceSurjectiveAndCompactSpaceProvidersW944
    targetDifferenceSurjectiveProvider
    targetCodomainCompactSpaceProvider

def attemptedNullarySurjectiveCompactSpaceTargetNoUnivDataW944 :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfTargetDifferenceSurjectiveAndCompactSpaceProvidersW944
    (by
      intro Y
      exact ?targetDifferenceSurjectiveProvider)
    (by
      intro Y
      exact ?targetCodomainCompactSpaceProvider)

end Dbounded
end LeanLCAExactChallenge
