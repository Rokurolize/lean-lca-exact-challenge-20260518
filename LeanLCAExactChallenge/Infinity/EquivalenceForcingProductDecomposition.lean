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

open CategoryTheory.MorphismProperty

/-- The right lifting property against all monomorphisms is stable under arbitrary products
of maps. -/
theorem piMap_mem_monomorphisms_rlp {J : Type*} {A B : J → SSet.{max u v}}
    [CategoryTheory.Limits.HasProduct A] [CategoryTheory.Limits.HasProduct B]
    (f : (j : J) → A j ⟶ B j)
    (hf : ∀ j, (monomorphisms SSet.{max u v}).rlp (f j)) :
    (monomorphisms SSet.{max u v}).rlp (CategoryTheory.Limits.Pi.map f) := by
  intro K L i hi
  letI (j : J) : CategoryTheory.HasLiftingProperty i (f j) := hf j i hi
  infer_instance

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

/-- The presentation mapping object, identified with the standard pullback of the two family
restriction maps. -/
noncomputable def equivalenceForcingPresentationMappingPullbackIso
    (Q : SSet.{max u v}) :
    (ihom (equivalenceForcingPresentation R)).obj Q ≅
      pullback
        (internalHomPrecomp (weakIntervalsToEquivalences R) Q)
        (internalHomPrecomp (weakIntervalsToNerve R) Q) :=
  (equivalenceForcingPresentationMapping_isPullback R Q).isoPullback

/-- Under the standard pullback identification, the second projection is precomposition by
the map from the ordinary nerve to the equivalence-forcing presentation. -/
@[reassoc]
theorem equivalenceForcingPresentationMappingPullbackIso_hom_snd
    (Q : SSet.{max u v}) :
    (equivalenceForcingPresentationMappingPullbackIso R Q).hom ≫
        pullback.snd
          (internalHomPrecomp (weakIntervalsToEquivalences R) Q)
          (internalHomPrecomp (weakIntervalsToNerve R) Q) =
      internalHomPrecomp (toEquivalenceForcingPresentation R) Q :=
  (equivalenceForcingPresentationMapping_isPullback R Q).isoPullback_hom_snd

/-- Consequently, after forgetting the equivalence-edge witnesses, the genuine presentation
comparison is exactly the second projection of this pullback. -/
@[reassoc]
theorem equivalenceForcingPresentationMappingPullbackIso_hom_snd_eq_comparison
    (Q : SSet.QCat.{max u v}) :
    (equivalenceForcingPresentationMappingPullbackIso R Q.obj).hom ≫
        pullback.snd
          (internalHomPrecomp (weakIntervalsToEquivalences R) Q.obj)
          (internalHomPrecomp (weakIntervalsToNerve R) Q.obj) =
      equivalenceForcingPresentationMappingComparison R Q ≫
        (relativeInternalHom (relativeNerveEdgeMarking R) Q.obj).ι := by
  rw [equivalenceForcingPresentationMappingPullbackIso_hom_snd,
    equivalenceForcingPresentationMappingComparison_comp_inclusion]

end RelativeCategoryData
end Infinity
end LeanLCAExactChallenge
