import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Audit for inverse-image transfer for left calculi of fractions.

W217/W222 reduced the bounded homotopy left-calculus input to a categorical transfer:
if an ambient morphism property `W` has a left calculus of fractions, then so should
`W.inverseImage F` for the functor `F` defining the pullback weak equivalences.

The local/mathlib API search found Verdier left calculus for the ambient
`(exactAcyclicHomotopyIsoClosure C).trW`, and found mathlib's adjunction theorem for
classes inverted by an adjoint functor, with the ready-made inverse-image corollary only
for inverse images of isomorphisms. No theorem was found for arbitrary `W.inverseImage F`.

This file records both the reusable general theorem shape and the smallest exact bounded
homotopy assumption needed downstream.
-/

set_option autoImplicit false

universe v u vD uD

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace InverseImageLeftCalculusTransferW226

/-- The general theorem shape searched for in mathlib/local APIs. -/
structure InverseImageLeftCalculusTransfer
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) : Prop where
  transfer :
    W.HasLeftCalculusOfFractions →
      (W.inverseImage F).HasLeftCalculusOfFractions

/-- Applying the general transfer assumption is immediate once it is supplied. -/
theorem inverseImage_hasLeftCalculusOfFractions_of_transfer
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E)
    (T : InverseImageLeftCalculusTransfer F W)
    (hW : W.HasLeftCalculusOfFractions) :
    (W.inverseImage F).HasLeftCalculusOfFractions :=
  T.transfer hW

/-- The bounded homotopy weak equivalences are definitionally the required inverse image. -/
theorem boundedHomotopyExactWeakEquivalence_eq_inverseImage
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedHomotopyExactWeakEquivalence C =
      ((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
        (BoundedComplexCategory.homotopyQuotient C) :=
  rfl

/-- The exact reusable inverse-image transfer specialized to the bounded homotopy route. -/
abbrev BoundedHomotopyInverseImageLeftCalculusTransfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  InverseImageLeftCalculusTransfer
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)

/--
Smallest direct assumption needed after the definition of
`boundedHomotopyExactWeakEquivalence`: the inverse-image class itself has a left calculus.
-/
structure BoundedHomotopyInverseImageLeftCalculusInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  inverseImageLeftCalculus :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).HasLeftCalculusOfFractions

/-- The smallest direct input discharges the bounded homotopy left-calculus requirement. -/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_inverseImageInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : BoundedHomotopyInverseImageLeftCalculusInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  P.inverseImageLeftCalculus

/-- Existing ambient Verdier input: triangulated closedness gives left calculus for `trW`. -/
theorem ambientVerdierLeftCalculus_of_isoClosureClosed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasLeftCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 C

/--
The reusable inverse-image transfer, specialized to
`BoundedComplexCategory.homotopyQuotient C`, is sufficient with the ambient Verdier input.
-/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_transfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (T : BoundedHomotopyInverseImageLeftCalculusTransfer C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions := by
  exact inverseImage_hasLeftCalculusOfFractions_of_transfer
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)
    T
    (ambientVerdierLeftCalculus_of_isoClosureClosed2 C)

/-- Packaged sufficient assumptions for the bounded homotopy left-calculus route. -/
structure BoundedHomotopyLeftCalculusSufficientInputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  isoClosureClosed2 :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂
  inverseImageTransfer :
    BoundedHomotopyInverseImageLeftCalculusTransfer C

/-- The packaged assumptions discharge the bounded homotopy left-calculus input. -/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_inputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : BoundedHomotopyLeftCalculusSufficientInputs C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions := by
  letI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    P.isoClosureClosed2
  exact boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_transfer
    C P.inverseImageTransfer

/-- Concrete target specialization. -/
theorem metrizableLCABoundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_inputs
    (P : BoundedHomotopyLeftCalculusSufficientInputs MetrizableLCA.{0}) :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_inputs
    MetrizableLCA.{0} P

/-- Search findings recorded as checked data. -/
def inverseImageLeftCalculusSearchFindings : List String :=
  ["boundedHomotopyExactWeakEquivalence C is definitionally the inverse image of exactAcyclicHomotopyIsoClosure C trW along BoundedComplexCategory.homotopyQuotient C",
    "ambient Verdier left calculus is available from exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2",
    "mathlib CategoryTheory.Adjunction.hasLeftCalculusOfFractions handles classes inverted by an adjunction, with the ready-made inverse-image corollary for isomorphisms",
    "no local/mathlib theorem was found transferring HasLeftCalculusOfFractions through arbitrary W.inverseImage F",
    "smallest exact downstream input is BoundedHomotopyInverseImageLeftCalculusInput C"]

theorem inverseImageLeftCalculusSearchFindings_count :
    inverseImageLeftCalculusSearchFindings.length = 5 := rfl

section Checks

#check InverseImageLeftCalculusTransfer
#check inverseImage_hasLeftCalculusOfFractions_of_transfer
#check boundedHomotopyExactWeakEquivalence_eq_inverseImage
#check BoundedHomotopyInverseImageLeftCalculusTransfer
#check BoundedHomotopyInverseImageLeftCalculusInput
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_inverseImageInput
#check ambientVerdierLeftCalculus_of_isoClosureClosed2
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_transfer
#check BoundedHomotopyLeftCalculusSufficientInputs
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_inputs
#check metrizableLCABoundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_inputs
#check inverseImageLeftCalculusSearchFindings
#check inverseImageLeftCalculusSearchFindings_count
#check CategoryTheory.Adjunction.hasLeftCalculusOfFractions
#check CategoryTheory.Adjunction.hasLeftCalculusOfFractions'
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check boundedHomotopyExactWeakEquivalence
#check BoundedComplexCategory.homotopyQuotient

end Checks

end InverseImageLeftCalculusTransferW226

end LeanLCAExactChallenge
