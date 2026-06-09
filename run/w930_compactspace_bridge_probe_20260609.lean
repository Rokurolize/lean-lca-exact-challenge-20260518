import LeanLCAExactChallenge.Derived.ClosedMapTargetCompactNoUnivMembershipPrimitiveFieldRoute

set_option autoImplicit false

namespace LeanLCAExactChallenge
namespace Dbounded

open CategoryTheory
open CategoryTheory.Limits
open Topology
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439

def w930_compactspace_bridge_probe_20260609
    (hcompact : ∀ Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0},
      CompactSpace (wppOpCodomainW441 Y)) :
    ∀ (Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}),
      targetCodomainCompactNoUnivMembershipPrimitiveW930 Y := by
  intro Y f hf
  letI : CompactSpace (wppOpCodomainW441 Y) := hcompact Y
  haveI : Filter.NeBot f := Filter.neBot_iff.2 hf
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace f
  exact ⟨x, Filter.neBot_iff.mp hx⟩

end Dbounded
end LeanLCAExactChallenge
