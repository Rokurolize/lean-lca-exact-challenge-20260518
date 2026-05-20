import LeanLCAExactChallenge.LCA.Quotient
import Mathlib.Topology.Maps.Basic

/-!
W363: target quotient closed-on-saturated support.

This standalone blocker file checks the missing target-side quotient fact from
W360.  For a quotient map, a subset of the quotient is closed exactly when its
preimage is closed.  If a closed set upstairs is saturated for the quotient map,
then the preimage of its image is the original set, so the image is closed.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace MetrizableLCA

universe u

/-- A set is saturated for a map when it contains every full fiber over its image. -/
def IsSaturatedForW363 {α β : Type _} (q : α → β) (S : Set α) : Prop :=
  q ⁻¹' (q '' S) ⊆ S

/--
For any quotient map, closed saturated sets have closed images.

This is the abstract topological core needed by the target quotient projection:
the quotient topology identifies closed subsets downstairs with closed
preimages upstairs, and saturation identifies that preimage with the original
closed set.
-/
theorem image_closed_of_isQuotientMap_and_saturatedW363
    {α β : Type _} [TopologicalSpace α] [TopologicalSpace β]
    {q : α → β} (hq : IsQuotientMap q) {S : Set α}
    (hS : IsClosed S) (hsaturated : IsSaturatedForW363 q S) :
    IsClosed (q '' S) := by
  have hpre_eq : q ⁻¹' (q '' S) = S := by
    apply le_antisymm hsaturated
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hpre_closed : IsClosed (q ⁻¹' (q '' S)) := by
    simpa [hpre_eq] using hS
  exact hq.1.isClosed_preimage.mp hpre_closed

/-- The local quotient map is a topological quotient map. -/
theorem quotientMap_isQuotientMapW363
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X)) :
    IsQuotientMap (quotientMap X N hN : X → quotientObj X N hN) := by
  change IsQuotientMap (QuotientAddGroup.mk' N : X → X ⧸ N)
  exact QuotientAddGroup.isQuotientMap_mk N

/--
The target quotient projection closes closed saturated sets.

This proves the theorem shape named as missing in W360, specialized to the
local closed-subgroup quotient API.
-/
theorem quotientMap_image_closed_of_closed_saturatedW363
    (X : MetrizableLCA.{u}) (N : AddSubgroup X) (hN : IsClosed (N : Set X))
    {S : Set X} (hS : IsClosed S)
    (hsaturated :
      IsSaturatedForW363
        (quotientMap X N hN : X → quotientObj X N hN) S) :
    IsClosed ((quotientMap X N hN : X → quotientObj X N hN) '' S) := by
  exact image_closed_of_isQuotientMap_and_saturatedW363
    (quotientMap_isQuotientMapW363 X N hN) hS hsaturated

/--
Named target quotient theorem package matching the W360 boundary.
-/
structure TargetQuotientClosedOnSaturatedSetsW363
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    Prop where
  closed_image :
    ∀ S : Set B', IsClosed S →
      IsSaturatedForW363 (quotientMap B' N' hN' : B' → quotientObj B' N' hN') S →
        IsClosed ((quotientMap B' N' hN' : B' → quotientObj B' N' hN') '' S)

/-- The checked theorem supplies the named target quotient package. -/
theorem targetQuotientClosedOnSaturatedSetsW363
    (B' : MetrizableLCA.{u}) (N' : AddSubgroup B') (hN' : IsClosed (N' : Set B')) :
    TargetQuotientClosedOnSaturatedSetsW363 B' N' hN' where
  closed_image := by
    intro S hS hsaturated
    exact quotientMap_image_closed_of_closed_saturatedW363 B' N' hN' hS hsaturated

/-- Machine-readable W363 state. -/
structure TargetQuotientClosedSaturatedV369SupportStateW363 : Type where
  seed : String
  checkedFacts : List String
  remainingIntegrationNotes : List String
  productSuccessClaimed : Bool

def currentTargetQuotientClosedSaturatedV369SupportStateW363 :
    TargetQuotientClosedSaturatedV369SupportStateW363 where
  seed := "62aa8e2016195deb3c2a9fdb466a80ae"
  checkedFacts :=
    ["MetrizableLCA.image_closed_of_isQuotientMap_and_saturatedW363",
      "MetrizableLCA.quotientMap_isQuotientMapW363",
      "MetrizableLCA.quotientMap_image_closed_of_closed_saturatedW363",
      "MetrizableLCA.targetQuotientClosedOnSaturatedSetsW363"]
  remainingIntegrationNotes :=
    ["W360 uses IsSaturatedForW360; consumers can port by definitional equality or replace it with IsSaturatedForW363.",
      "This file proves the target quotient closed-on-saturated theorem but does not mutate live target files."]
  productSuccessClaimed := false

end MetrizableLCA

end LeanLCAExactChallenge
