import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableInfinityAudit

/--
Current bounded-derived infinity-category evidence exposed by `Dbounded`.

This is deliberately ordinary evidence: a quasicategory witness for the nerve and the
ordinary homotopy-category comparison. It does not include stable finite-limit,
finite-colimit, suspension/loop, or pushout/pullback projections.
-/
structure OrdinaryDboundedEvidence
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  quasicategory : SSet.Quasicategory (Dbounded.infinityNerve C)
  homotopyCategoryIso : SSet.hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C)

/-- The currently available ordinary evidence for `Dbounded C`. -/
noncomputable def currentOrdinaryDboundedEvidence
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    OrdinaryDboundedEvidence C where
  quasicategory := Dbounded.infinityNerve_quasicategory (C := C)
  homotopyCategoryIso := Dbounded.homotopyCategoryIso (C := C)

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

/--
Compact map for the stable certificate frontier: the project currently has ordinary
`Dbounded` evidence, while the future stable audit gate consumes the four-projection
input above.
-/
structure DboundedStableProjectionGapMap
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max (max u v) 2) where
  current : OrdinaryDboundedEvidence C
  futureReadyPredicate : DboundedProjectionAuditInput C → Prop
  futureReadyPredicate_eq :
    futureReadyPredicate = fun input =>
      input.shape.finiteLimitsProjection input.certificate ∧
        input.shape.finiteColimitsProjection input.certificate ∧
        input.shape.suspensionLoopProjection input.certificate ∧
        input.shape.pushoutPullbackProjection input.certificate

/-- The current stable projection gap map, specialized to the available ordinary evidence. -/
noncomputable def currentStableProjectionGapMap
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    DboundedStableProjectionGapMap C where
  current := currentOrdinaryDboundedEvidence C
  futureReadyPredicate := fun input =>
    input.shape.finiteLimitsProjection input.certificate ∧
      input.shape.finiteColimitsProjection input.certificate ∧
      input.shape.suspensionLoopProjection input.certificate ∧
      input.shape.pushoutPullbackProjection input.certificate
  futureReadyPredicate_eq := rfl

end StableInfinityAudit

section Checks

#check StableInfinityAudit.OrdinaryDboundedEvidence
#check StableInfinityAudit.currentOrdinaryDboundedEvidence
#check StableInfinityAudit.ProjectionAuditShape
#check StableInfinityAudit.DboundedProjectionAuditInput
#check StableInfinityAudit.DboundedProjectionAuditInput.finiteLimits
#check StableInfinityAudit.DboundedProjectionAuditInput.finiteColimits
#check StableInfinityAudit.DboundedProjectionAuditInput.suspensionLoopEquivalence
#check StableInfinityAudit.DboundedProjectionAuditInput.pushoutPullbackCompatibility
#check StableInfinityAudit.DboundedProjectionAuditInput.projections_available
#check StableInfinityAudit.DboundedStableProjectionGapMap
#check StableInfinityAudit.currentStableProjectionGapMap
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check (StableInfinityAudit.currentOrdinaryDboundedEvidence (C := MetrizableLCA))
#check (StableInfinityAudit.currentStableProjectionGapMap (C := MetrizableLCA))

end Checks

end LeanLCAExactChallenge
