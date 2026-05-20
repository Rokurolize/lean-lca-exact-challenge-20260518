import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableProductReviewGateMap

/--
The durable owners in the stable bounded-derived infinity-category product review path.

The external audit may reject marker-only packets, but the first durable Lean owner of an
accepted stable product gate should be `audit/ProductSuccessDeclarations.lean`, after the
future stable certificate API is available.
-/
inductive ProductGateOwner where
  | externalAudit
  | requiredDeclarations
  | productSuccessDeclarations
  | terminalOutcome
  deriving DecidableEq, Repr

/-- W93 map result: current stable product acceptance should first land here. -/
def firstStableProductGateOwner : ProductGateOwner :=
  ProductGateOwner.productSuccessDeclarations

/--
Ordinary bounded derived infinity evidence currently available from `Dbounded`.

This is intentionally only the ordinary nerve/quasicategory witness. It should remain a
review rejection for stable infinity-category product success.
-/
structure OrdinaryNerveEvidence
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type where
  qcat : SSet.Quasicategory (Dbounded.infinityNerve C)

/--
The future semantic evidence required to pass stable product review.

These four projections are the Lean-side counterpart of the external audit's field-evidence
guard. A packet with only an ordinary nerve or a certificate name has no value of this shape.
-/
structure FourStableProjectionEvidence (Q : SSet.QCat) : Type where
  finiteLimits : Prop
  finiteColimits : Prop
  suspensionLoopEquivalence : Prop
  pushoutPullbackCompatibility : Prop
  finiteLimits_ready : finiteLimits
  finiteColimits_ready : finiteColimits
  suspensionLoopEquivalence_ready : suspensionLoopEquivalence
  pushoutPullbackCompatibility_ready : pushoutPullbackCompatibility

/-- The exact pass predicate future product declarations should expose. -/
def hasFourStableProjections {Q : SSet.QCat} (e : FourStableProjectionEvidence Q) : Prop :=
  e.finiteLimits ∧
    e.finiteColimits ∧
    e.suspensionLoopEquivalence ∧
    e.pushoutPullbackCompatibility

/-- Product review has a rejection branch for ordinary nerve evidence and a pass branch only
after the four stable projections are available. -/
inductive StableProductReviewDecision
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type where
  | rejectExternalMarkerOnly : StableProductReviewDecision C
  | rejectOrdinaryNerveOnly : OrdinaryNerveEvidence C → StableProductReviewDecision C
  | acceptFourStableProjections :
      FourStableProjectionEvidence (Dbounded.infinityCategory C) →
        StableProductReviewDecision C

def ordinaryNerveEvidence_current
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    OrdinaryNerveEvidence C :=
  ⟨Dbounded.infinityNerve_quasicategory (C := C)⟩

theorem acceptFourStableProjections_has_fields
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C]
    (e : FourStableProjectionEvidence (Dbounded.infinityCategory C)) :
    hasFourStableProjections e := by
  exact ⟨e.finiteLimits_ready, e.finiteColimits_ready,
    e.suspensionLoopEquivalence_ready, e.pushoutPullbackCompatibility_ready⟩

/-- The current ordinary nerve witness is mapped to the explicit rejection branch. -/
def currentOrdinaryNerveReviewDecision
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    StableProductReviewDecision C :=
  StableProductReviewDecision.rejectOrdinaryNerveOnly (ordinaryNerveEvidence_current C)

section Checks

#check firstStableProductGateOwner
#check OrdinaryNerveEvidence
#check ordinaryNerveEvidence_current
#check FourStableProjectionEvidence
#check FourStableProjectionEvidence.finiteLimits
#check FourStableProjectionEvidence.finiteColimits
#check FourStableProjectionEvidence.suspensionLoopEquivalence
#check FourStableProjectionEvidence.pushoutPullbackCompatibility
#check hasFourStableProjections
#check acceptFourStableProjections_has_fields
#check currentOrdinaryNerveReviewDecision
#check (Dbounded.infinityCategory (C := MetrizableLCA))
#check (Dbounded.infinityNerve_quasicategory (C := MetrizableLCA))

end Checks

end StableProductReviewGateMap

end LeanLCAExactChallenge
