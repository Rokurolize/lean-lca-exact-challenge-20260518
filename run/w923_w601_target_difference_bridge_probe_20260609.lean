import LeanLCAExactChallenge.Derived.ClosedMapTargetNoUnivMembershipDataClosednessDataBoundaryRelationDataNormalizedFixedTargetDataSourceTriangulationEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace Dbounded

#check Dbounded.targetDifferenceSurjectivePrimitiveOfSurjectiveW923
#check Dbounded.targetDifferenceSurjectivePrimitiveOfTargetProviderW923
#check Dbounded.targetDifferenceSurjectivePrimitiveOfTargetDifferenceProviderW601
#check Dbounded.targetNoUnivDataOfTargetDifferenceProviderAndCompactSpaceProviderW944

example
    (h : TargetDifferenceSurjectiveForTargetProviderW713) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y :=
  targetDifferenceSurjectivePrimitiveOfTargetProviderW923 h

example
    (h : TargetDifferenceSurjectiveProviderW601) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetDifferenceSurjectivePrimitiveW923 Y :=
  targetDifferenceSurjectivePrimitiveOfTargetDifferenceProviderW601 h

example
    (targetDifferenceProvider : TargetDifferenceSurjectiveProviderW601)
    (targetCompactProvider : TargetCodomainCompactSpaceProviderW601) :
    TargetSurjectiveNoUnivMembershipForTargetProviderW944 :=
  targetNoUnivDataOfTargetDifferenceProviderAndCompactSpaceProviderW944
    targetDifferenceProvider
    targetCompactProvider

example
    (targetDifferenceProvider : TargetDifferenceSurjectiveProviderW601)
    (targetCompactProvider : TargetCodomainCompactSpaceProviderW601)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    targetDifferenceSurjectivePrimitiveW923 Y :=
  (targetNoUnivDataOfTargetDifferenceProviderAndCompactSpaceProviderW944
    targetDifferenceProvider
    targetCompactProvider Y).1

example
    (targetDifferenceProvider : TargetDifferenceSurjectiveProviderW601)
    (targetCompactProvider : TargetCodomainCompactSpaceProviderW601)
    (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    targetCodomainCompactNoUnivMembershipPrimitiveW930 Y :=
  (targetNoUnivDataOfTargetDifferenceProviderAndCompactSpaceProviderW944
    targetDifferenceProvider
    targetCompactProvider Y).2

end Dbounded

end LeanLCAExactChallenge
