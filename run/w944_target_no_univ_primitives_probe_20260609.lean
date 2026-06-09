import LeanLCAExactChallenge.Derived.ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Dbounded

#check Dbounded.TargetSurjectiveNoUnivMembershipForTargetProviderW944
#check Dbounded.targetNoUnivDataOfPrimitiveProvidersW944
#check Dbounded.targetDifferenceSurjectivePrimitiveW923
#check Dbounded.targetCodomainCompactNoUnivMembershipPrimitiveW930

namespace Dbounded

def w944TargetNoUnivFromPrimitiveProvidersProbe
    (targetDifferenceSurjectiveProvider :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
        targetDifferenceSurjectivePrimitiveW923 Y)
    (targetCompactNoUnivProvider :
      ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
        targetCodomainCompactNoUnivMembershipPrimitiveW930 Y) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfPrimitiveProvidersW944
    targetDifferenceSurjectiveProvider
    targetCompactNoUnivProvider

def attemptedNullaryTargetNoUnivDataW944 :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfPrimitiveProvidersW944
    (by
      intro Y
      exact ?targetDifferenceSurjectiveProvider)
    (by
      intro Y
      exact ?targetCompactNoUnivProvider)

end Dbounded
end LeanLCAExactChallenge
