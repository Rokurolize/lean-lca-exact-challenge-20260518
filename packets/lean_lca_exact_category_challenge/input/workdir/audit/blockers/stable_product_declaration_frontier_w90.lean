import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableInfinityAudit

/--
Non-product skeleton for the certificate shape that `audit/ProductSuccessDeclarations.lean`
should eventually consume.

The real API is intentionally absent today. This audit skeleton records the review boundary:
the future certificate must expose four Lean projections from one stable certificate object,
not just the ordinary `Dbounded.infinityNerve_quasicategory` witness.
-/
structure DboundedStableObligations (Q : SSet.QCat) : Type where
  finiteLimits : Prop
  finiteColimits : Prop
  suspensionLoopEquivalence : Prop
  pushoutPullbackCompatibility : Prop

/--
Future stable certificate shape for a bounded derived infinity category.

Each field after `obligations` is a semantic projection. A product-success declaration can
consume this shape by projecting these four fields; an ordinary nerve witness has no field
with this type.
-/
structure DboundedStableCertificate (Q : SSet.QCat) : Type where
  obligations : DboundedStableObligations Q
  finiteLimits : obligations.finiteLimits
  finiteColimits : obligations.finiteColimits
  suspensionLoopEquivalence : obligations.suspensionLoopEquivalence
  pushoutPullbackCompatibility : obligations.pushoutPullbackCompatibility

end StableInfinityAudit

namespace ProductSuccessDeclarationFrontier

/--
The product-side checker shape that should move into `audit/ProductSuccessDeclarations.lean`
only after the real `StableInfinityAudit.DboundedStableCertificate` API exists.
-/
def DboundedStableCertificateReady
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C]
    (cert : StableInfinityAudit.DboundedStableCertificate (Dbounded.infinityCategory C)) :
    Prop :=
  cert.obligations.finiteLimits ∧
    cert.obligations.finiteColimits ∧
    cert.obligations.suspensionLoopEquivalence ∧
    cert.obligations.pushoutPullbackCompatibility

/--
The future product declaration should be this eliminator-shaped check: consume a single
stable certificate for `Dbounded C` and require all four stable projections.
-/
theorem DboundedStableCertificateReady.of_certificate
    {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C]
    (cert : StableInfinityAudit.DboundedStableCertificate (Dbounded.infinityCategory C)) :
    DboundedStableCertificateReady C cert := by
  exact ⟨cert.finiteLimits, cert.finiteColimits, cert.suspensionLoopEquivalence,
    cert.pushoutPullbackCompatibility⟩

/--
The current product-facing ordinary nerve evidence remains available, but it is intentionally
only an ordinary quasicategory witness and is not accepted by `DboundedStableCertificateReady`.
-/
theorem ordinary_nerve_only
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    SSet.Quasicategory (Dbounded.infinityNerve C) :=
  Dbounded.infinityNerve_quasicategory (C := C)

end ProductSuccessDeclarationFrontier

section Checks

#check StableInfinityAudit.DboundedStableCertificate
#check StableInfinityAudit.DboundedStableCertificate.finiteLimits
#check StableInfinityAudit.DboundedStableCertificate.finiteColimits
#check StableInfinityAudit.DboundedStableCertificate.suspensionLoopEquivalence
#check StableInfinityAudit.DboundedStableCertificate.pushoutPullbackCompatibility
#check ProductSuccessDeclarationFrontier.DboundedStableCertificateReady
#check ProductSuccessDeclarationFrontier.DboundedStableCertificateReady.of_certificate
#check ProductSuccessDeclarationFrontier.ordinary_nerve_only
#check (Dbounded.infinityCategory (C := MetrizableLCA))
#check (Dbounded.infinityNerve_quasicategory (C := MetrizableLCA))

end Checks

end LeanLCAExactChallenge
