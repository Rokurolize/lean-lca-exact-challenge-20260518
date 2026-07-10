import LeanLCAExactChallenge.Infinity.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

/-!
# Functor quasicategories from an explicit pushout-product hypothesis

Mathlib v4.30 has the categorical equivalence between pushout-product lifting and lifting
against an internal hom, but it does not yet prove that the pushout-product of an inner horn
inclusion with `⊥ ⟶ K` is inner anodyne. This file isolates exactly that missing statement
as `InnerHornPushoutProductIsInnerAnodyne` and proves the desired closure of quasicategories
under internal hom from it.

No term or instance of `InnerHornPushoutProductIsInnerAnodyne` is constructed here. In
particular, this module does not assert unconditionally that functor simplicial sets are
quasicategories in the pinned mathlib version.
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

/-- The inner-horn pushout-product statement missing from mathlib v4.30. -/
def InnerHornPushoutProductIsInnerAnodyne : Prop :=
  ∀ {n : ℕ} {i : Fin (n + 1)}, 0 < i → i < Fin.last n →
    (K : SSet.{u}) →
    SSet.innerAnodyneExtensions
      ((Arrow.mk Λ[n, i].ι □ Arrow.mk (initial.to K)).hom)

/-- Internal hom into a quasicategory is a quasicategory, assuming the explicit inner-horn
pushout-product statement absent from mathlib v4.30. -/
theorem quasicategory_ihom_of_innerHornPushoutProduct
    (hprod : InnerHornPushoutProductIsInnerAnodyne.{u})
    {K Q : SSet.{u}} [SSet.Quasicategory Q] :
    SSet.Quasicategory ((ihom K).obj Q) := by
  apply SSet.quasicategory_of_hasLiftingProperty _ terminalIsTerminal
  intro n i h0 hn
  rw [← PushoutProduct.hasLiftingProperty_mk_isInitial_isTerminal_iff'
    initialIsInitial terminalIsTerminal]
  exact hprod h0 hn K _
    (SSet.Quasicategory.from_innerFibrations Q terminalIsTerminal)

end Infinity
end LeanLCAExactChallenge
