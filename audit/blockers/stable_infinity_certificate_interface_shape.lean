import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableInfinityAudit

/--
Non-product interface shape for a future stable infinity-category certificate.

This structure intentionally contains obligations rather than proofs currently
available from the ordinary `Dbounded.infinityCategory` route. It keeps the
finite-limit, finite-colimit, and suspension/loop data separate from the
ordinary quasicategory witness so that an ordinary nerve cannot be mistaken for
a stable infinity-category certificate.
-/
structure CertificateShape (Q : SSet.QCat) : Type where
  finiteLimitObligation : Prop
  finiteColimitObligation : Prop
  suspensionLoopEquivalenceObligation : Prop
  pushoutPullbackCompatibilityObligation : Prop

/--
The theorem-shape input that a future stable certificate for `Dbounded C` would
have to provide. The `ordinaryQuasicategory` field records that the existing
ordinary nerve remains available, but it is not one of the stable obligations.
-/
structure DboundedCertificateInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] : Type (max u v) where
  stableShape : CertificateShape (Dbounded.infinityCategory C)
  ordinaryQuasicategory : SSet.Quasicategory (Dbounded.infinityNerve C)
  finiteLimits : stableShape.finiteLimitObligation
  finiteColimits : stableShape.finiteColimitObligation
  suspensionLoopEquivalence : stableShape.suspensionLoopEquivalenceObligation
  pushoutPullbackCompatibility : stableShape.pushoutPullbackCompatibilityObligation

/--
The existing route can supply only the ordinary quasicategory component of the
future input. This helper is deliberately one-way: it extracts no stable
obligation from `Dbounded.infinityNerve_quasicategory`.
-/
theorem DboundedCertificateInput.ordinary_only
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] :
    SSet.Quasicategory (Dbounded.infinityNerve C) :=
  Dbounded.infinityNerve_quasicategory (C := C)

end StableInfinityAudit

section Checks

#check StableInfinityAudit.CertificateShape
#check StableInfinityAudit.DboundedCertificateInput
#check StableInfinityAudit.DboundedCertificateInput.ordinary_only
#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory

end Checks

end LeanLCAExactChallenge
