import LeanLCAExactChallenge.Infinity.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct

/-!
# Functor quasicategories

Mathlib v4.31 proves that simplicial internal hom into a quasicategory is again a quasicategory.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.MonoidalClosed
open Simplicial

/-- Simplicial internal hom into a quasicategory is unconditionally a quasicategory. -/
theorem quasicategory_ihom {K Q : SSet.{u}} [SSet.Quasicategory Q] :
    SSet.Quasicategory ((ihom K).obj Q) :=
  inferInstance

end Infinity
end LeanLCAExactChallenge
