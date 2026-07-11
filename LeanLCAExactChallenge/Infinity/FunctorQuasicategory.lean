import LeanLCAExactChallenge.Infinity.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# Functor quasicategories

The compatibility predicate `InnerHornPushoutProductIsInnerAnodyne` was introduced while the
project used mathlib v4.30, where the required cartesian pushout-product theorem was absent.
Mathlib v4.31 proves the stronger theorem for an arbitrary monomorphism. This file keeps the
compatibility predicate, inhabits it from the library theorem, and exposes unconditional closure
of quasicategories under simplicial internal hom.

The older conditional theorem is retained so downstream declarations do not need an API change.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.Arrow
open HomotopicalAlgebra
open Simplicial

/-- The inner-horn pushout-product compatibility statement used by the v4.30 development. -/
def InnerHornPushoutProductIsInnerAnodyne : Prop :=
  ∀ {n : ℕ} {i : Fin (n + 1)}, 0 < i → i < Fin.last n →
    (K : SSet.{u}) →
    SSet.innerAnodyneExtensions
      ((Arrow.mk Λ[n, i].ι □ Arrow.mk (initial.to K)).hom)

/-- Mathlib v4.31's cartesian pushout-product theorem inhabits the compatibility statement. -/
theorem innerHornPushoutProductIsInnerAnodyne :
    InnerHornPushoutProductIsInnerAnodyne.{u} := by
  intro n i h0 hn K
  let sq := Functor.PushoutObjObj.ofHasPushout
    (curriedTensor SSet.{u}) Λ[n, i].ι (initial.to K)
  change SSet.innerAnodyneExtensions sq.ι
  exact SSet.innerAnodyneExtensions_pushoutObjObjι' sq
    (SSet.innerAnodyneExtensions.horn_ι h0 hn)

/-- Compatibility wrapper for the former conditional internal-Hom closure theorem. -/
theorem quasicategory_ihom_of_innerHornPushoutProduct
    (_hprod : InnerHornPushoutProductIsInnerAnodyne.{u})
    {K Q : SSet.{u}} [SSet.Quasicategory Q] :
    SSet.Quasicategory ((ihom K).obj Q) :=
  inferInstance

/-- Simplicial internal hom into a quasicategory is unconditionally a quasicategory. -/
theorem quasicategory_ihom {K Q : SSet.{u}} [SSet.Quasicategory Q] :
    SSet.Quasicategory ((ihom K).obj Q) :=
  inferInstance

end Infinity
end LeanLCAExactChallenge
