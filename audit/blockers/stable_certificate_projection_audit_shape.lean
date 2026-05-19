import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableInfinityAudit

/--
Focused audit shape for the next stricter stable-certificate check.

The shape is intentionally projection-oriented: a future product-facing stable
certificate should expose independently checkable projections for finite limits, finite
colimits, suspension/loop equivalence, and pushout/pullback compatibility. This is only
an audit interface shape, not evidence that such a certificate is currently available
for `Dbounded`.
-/
structure ProjectionAuditShape (Q : SSet.QCat) : Type 2 where
  stableCertificate : Type
  finiteLimitsProjection : stableCertificate → Prop
  finiteColimitsProjection : stableCertificate → Prop
  suspensionLoopProjection : stableCertificate → Prop
  pushoutPullbackProjection : stableCertificate → Prop

/--
The future input a semantic audit could require after a concrete stable certificate
interface is ported. Each field is a projection from the same certificate object, so an
ordinary quasicategory witness cannot fill the shape unless the stable projections are
also supplied.
-/
structure DboundedProjectionAuditInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  shape : ProjectionAuditShape (Dbounded.infinityCategory C)
  certificate : shape.stableCertificate
  finiteLimits : shape.finiteLimitsProjection certificate
  finiteColimits : shape.finiteColimitsProjection certificate
  suspensionLoopEquivalence : shape.suspensionLoopProjection certificate
  pushoutPullbackCompatibility : shape.pushoutPullbackProjection certificate

/--
Projection bundle consumed by a future external audit after the stable certificate API
exists. The theorem is deliberately eliminative only: it checks that the four semantic
projections are separate fields on the provided input.
-/
theorem DboundedProjectionAuditInput.projections_available
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] (input : DboundedProjectionAuditInput C) :
    input.shape.finiteLimitsProjection input.certificate ∧
      input.shape.finiteColimitsProjection input.certificate ∧
      input.shape.suspensionLoopProjection input.certificate ∧
      input.shape.pushoutPullbackProjection input.certificate := by
  exact ⟨input.finiteLimits, input.finiteColimits, input.suspensionLoopEquivalence,
    input.pushoutPullbackCompatibility⟩

end StableInfinityAudit

section Checks

#check StableInfinityAudit.ProjectionAuditShape
#check StableInfinityAudit.DboundedProjectionAuditInput
#check StableInfinityAudit.DboundedProjectionAuditInput.finiteLimits
#check StableInfinityAudit.DboundedProjectionAuditInput.finiteColimits
#check StableInfinityAudit.DboundedProjectionAuditInput.suspensionLoopEquivalence
#check StableInfinityAudit.DboundedProjectionAuditInput.pushoutPullbackCompatibility
#check StableInfinityAudit.DboundedProjectionAuditInput.projections_available
#check Dbounded.infinityCategory

end Checks

end LeanLCAExactChallenge
