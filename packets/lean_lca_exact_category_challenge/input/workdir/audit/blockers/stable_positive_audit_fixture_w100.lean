import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StablePositiveAuditFixtureW100

/--
The owner map for a future positive stable infinity-category product gate.

The external audit may reject malformed packets, but positive ownership should be a
Lean declaration in `audit/ProductSuccessDeclarations.lean` once the real stable
certificate API exists.
-/
inductive PositiveGateOwner where
  | externalAudit
  | productSuccessDeclarations
  | terminalOutcome
  deriving DecidableEq, Repr

/-- W100 fixture result: the first positive owner is the product declarations file. -/
def firstPositiveStableOwner : PositiveGateOwner :=
  PositiveGateOwner.productSuccessDeclarations

/--
Non-production shape for the future stable certificate API.

This is intentionally more concrete than a marker name: all four product-success
projections are predicates on one supplied certificate object.
-/
structure StableCertificateFieldShape (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  finiteLimits : stableCertificate → Prop
  finiteColimits : stableCertificate → Prop
  suspensionLoopEquivalence : stableCertificate → Prop
  pushoutPullbackCompatibility : stableCertificate → Prop

/--
Positive fixture input for the future `Dbounded` stable certificate gate.

The fields are shaped so that a future product declaration can destruct one
certificate and obtain finite limits, finite colimits, suspension/loop equivalence,
and pushout/pullback compatibility independently.
-/
structure DboundedPositiveStableInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  shape : StableCertificateFieldShape (Dbounded.infinityCategory C)
  certificate : shape.stableCertificate
  finiteLimits : shape.finiteLimits certificate
  finiteColimits : shape.finiteColimits certificate
  suspensionLoopEquivalence : shape.suspensionLoopEquivalence certificate
  pushoutPullbackCompatibility : shape.pushoutPullbackCompatibility certificate

/-- The exact pass predicate a future positive declaration should expose. -/
def DboundedPositiveStableInput.ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (input : DboundedPositiveStableInput C) : Prop :=
  input.shape.finiteLimits input.certificate ∧
    input.shape.finiteColimits input.certificate ∧
    input.shape.suspensionLoopEquivalence input.certificate ∧
    input.shape.pushoutPullbackCompatibility input.certificate

/--
The non-production positive smoke: field evidence from one stable certificate is
sufficient for the fixture predicate.
-/
theorem DboundedPositiveStableInput.ready_of_fields
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (input : DboundedPositiveStableInput C) :
    input.ready := by
  exact ⟨input.finiteLimits, input.finiteColimits, input.suspensionLoopEquivalence,
    input.pushoutPullbackCompatibility⟩

/--
Current bounded derived infinity evidence remains ordinary nerve evidence only.
This type deliberately has no route to `DboundedPositiveStableInput.ready`.
-/
structure OrdinaryNerveOnly
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type where
  qcat : SSet.Quasicategory (Dbounded.infinityNerve C)

/-- The current available witness is still the ordinary nerve/quasicategory witness. -/
def currentOrdinaryNerveOnly
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    OrdinaryNerveOnly C :=
  ⟨Dbounded.infinityNerve_quasicategory (C := C)⟩

/-- Review outcome for the fixture: ordinary nerve evidence is rejected, four fields pass. -/
inductive PositiveStableAuditDecision
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  | rejectOrdinaryNerveOnly : OrdinaryNerveOnly C → PositiveStableAuditDecision C
  | acceptFourProjectionCertificate :
      (input : DboundedPositiveStableInput C) → input.ready → PositiveStableAuditDecision C

/-- Current evidence lands only in the rejection branch of this positive fixture. -/
def currentDecisionRejectsOrdinaryNerve
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    PositiveStableAuditDecision C :=
  PositiveStableAuditDecision.rejectOrdinaryNerveOnly (currentOrdinaryNerveOnly C)

/--
Future product declaration shape. This is the line that should move into
`audit/ProductSuccessDeclarations.lean` only when a real stable certificate API replaces
this fixture shape.
-/
def productDeclarationCanUse
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (input : DboundedPositiveStableInput C) : Prop :=
  firstPositiveStableOwner = PositiveGateOwner.productSuccessDeclarations ∧ input.ready

theorem productDeclarationCanUse.of_ready
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (input : DboundedPositiveStableInput C) (h : input.ready) :
    productDeclarationCanUse input := by
  exact ⟨rfl, h⟩

section Checks

#check firstPositiveStableOwner
#check StableCertificateFieldShape
#check DboundedPositiveStableInput
#check DboundedPositiveStableInput.finiteLimits
#check DboundedPositiveStableInput.finiteColimits
#check DboundedPositiveStableInput.suspensionLoopEquivalence
#check DboundedPositiveStableInput.pushoutPullbackCompatibility
#check DboundedPositiveStableInput.ready
#check DboundedPositiveStableInput.ready_of_fields
#check OrdinaryNerveOnly
#check currentOrdinaryNerveOnly
#check PositiveStableAuditDecision.rejectOrdinaryNerveOnly
#check PositiveStableAuditDecision.acceptFourProjectionCertificate
#check currentDecisionRejectsOrdinaryNerve
#check productDeclarationCanUse
#check productDeclarationCanUse.of_ready
#check (Dbounded.infinityCategory (C := MetrizableLCA))
#check (Dbounded.infinityNerve_quasicategory (C := MetrizableLCA))

end Checks

end StablePositiveAuditFixtureW100

end LeanLCAExactChallenge
