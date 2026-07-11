import LeanLCAExactChallenge.Infinity.EquivalenceForcing
import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension
import LeanLCAExactChallenge.Infinity.MarkedRelativeLifting

/-!
# Product decomposition of equivalence-forcing mapping maps

This file records the componentwise part of the decomposition.  Each component of the
restriction map out of the coproduct of free equivalences is the single-interval restricted
map `Map(J,Q) ⟶ EqEdge(Q)`.  No lifting property for the unrestricted map is asserted.
-/

set_option autoImplicit false

noncomputable section

universe u v

namespace LeanLCAExactChallenge
namespace Infinity
namespace RelativeCategoryData

open CategoryTheory
open CategoryTheory.Limits
open Simplicial

variable {C : Type u} [Category.{v} C] (R : RelativeCategoryData C)

/-- Evaluation of maps out of the coproduct of free equivalences at one weak arrow. -/
def weakEquivalenceMappingComponent (Q : SSet.{max u v})
    (a : WeakEquivalenceArrow C R) :
    (ihom (∐ weakEquivalenceFamily R)).obj Q ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{max u v})).obj Q :=
  internalHomPrecomp (Sigma.ι (weakEquivalenceFamily R) a) Q

/-- Evaluation of maps out of the coproduct of intervals at one weak arrow. -/
def weakIntervalMappingComponent (Q : SSet.{max u v})
    (a : WeakEquivalenceArrow C R) :
    (ihom (∐ weakIntervalFamily R)).obj Q ⟶ (ihom (Δ[1] : SSet.{max u v})).obj Q :=
  internalHomPrecomp (Sigma.ι (weakIntervalFamily R) a) Q

/-- On every coproduct component, restriction along the family of interval inclusions is
exactly restriction along the single free-equivalence interval. -/
theorem weakEquivalenceMappingComponent_restriction
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R) :
    internalHomPrecomp (weakIntervalsToEquivalences R) Q ≫
        weakIntervalMappingComponent R Q a =
      weakEquivalenceMappingComponent R Q a ≫
        internalHomPrecomp equivalenceIntervalInclusion Q := by
  rw [weakEquivalenceMappingComponent, weakIntervalMappingComponent,
    internalHomPrecomp_comp, internalHomPrecomp_comp]
  congr 1
  exact Sigma.ι_desc (fun a ↦ equivalenceIntervalInclusion ≫
    Sigma.ι (weakEquivalenceFamily R) a) a

/-- The preceding component factors through the equivalence-edge subcomplex by the genuine
single-interval restricted map. -/
theorem weakEquivalenceMappingComponent_restriction_to_equivalenceEdges
    (Q : SSet.{max u v}) (a : WeakEquivalenceArrow C R) :
    weakEquivalenceMappingComponent R Q a ≫
        equivalenceIntervalRestrictionToEquivalenceEdges Q ≫
          (equivalenceEdgeInternalHom Q).ι =
      internalHomPrecomp (weakIntervalsToEquivalences R) Q ≫
        weakIntervalMappingComponent R Q a := by
  simpa only [Category.assoc,
    equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion] using
      (weakEquivalenceMappingComponent_restriction R Q a).symm

end RelativeCategoryData
end Infinity
end LeanLCAExactChallenge
