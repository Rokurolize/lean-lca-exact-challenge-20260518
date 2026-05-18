import LeanLCAExactChallenge.ExactCategory.Basic

/-!
Small helpers around conflations.  The main public declarations live in
`ExactCategory.Basic`; this file gives a reusable bundled witness type for
handoff work.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace QuillenExactCategory

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [QuillenExactCategory C]

/-- A conflation together with its short complex. -/
structure ConflationData where
  complex : ShortComplex C
  is_conflation : QuillenExactCategory.Conflation complex

end QuillenExactCategory

end LeanLCAExactChallenge
