import LeanLCAExactChallenge.Derived.Bounded

/-!
Audit for support worker w217: the second W212 input,
`(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions`.

The available local API supplies a Verdier left calculus for
`(exactAcyclicHomotopyIsoClosure C).trW` once the isomorphism closure is triangulated.
The remaining nontrivial step is transferring that calculus through the inverse image along
`BoundedComplexCategory.homotopyQuotient C`. This file packages that transfer as the exact
sufficient assumption.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace BoundedHomotopyLeftCalculusW217

/--
The missing categorical transfer needed to turn ambient Verdier calculus into the bounded
homotopy/Verdier pullback calculus.
-/
structure PullbackLeftCalculusTransfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  transfer :
    (exactAcyclicHomotopyIsoClosure C).trW.HasLeftCalculusOfFractions →
      (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
        (BoundedComplexCategory.homotopyQuotient C)).HasLeftCalculusOfFractions

/--
Existing local Verdier/TRW input: triangulating the isomorphism closure gives the ambient
homotopy-category left calculus.
-/
theorem ambientVerdierLeftCalculus_of_isoClosureClosed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasLeftCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 C

/-- The precise conditional theorem shape for the W212 second missing input. -/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_closed2_and_transfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (T : PullbackLeftCalculusTransfer C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions := by
  exact T.transfer (ambientVerdierLeftCalculus_of_isoClosureClosed2 C)

/-- A compact package of the exact sufficient assumptions surfaced by this audit. -/
structure BoundedHomotopyLeftCalculusSufficientPackage
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  isoClosureClosed2 :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂
  pullbackTransfer : PullbackLeftCalculusTransfer C

/-- The sufficient package discharges the bounded homotopy left-calculus input. -/
theorem boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : BoundedHomotopyLeftCalculusSufficientPackage C) :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions := by
  letI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    P.isoClosureClosed2
  exact boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_closed2_and_transfer
    C P.pullbackTransfer

/-- Concrete specialization of the sufficient package to the finite-product target. -/
theorem metrizableLCABoundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
    (P : BoundedHomotopyLeftCalculusSufficientPackage MetrizableLCA.{0}) :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
    MetrizableLCA.{0} P

/--
Search result encoded as data: these are the still-needed bridge facts for an unconditional
instance in this branch.
-/
def boundedHomotopyLeftCalculusObstructions : List String :=
  ["no local theorem found transferring HasLeftCalculusOfFractions through arbitrary inverseImage",
    "no adjunction found for BoundedComplexCategory.homotopyQuotient C suitable for Adjunction.hasLeftCalculusOfFractions",
    "need PullbackLeftCalculusTransfer C or a direct proof for boundedHomotopyExactWeakEquivalence C"]

theorem boundedHomotopyLeftCalculusObstructions_count :
    boundedHomotopyLeftCalculusObstructions.length = 3 := rfl

section Checks

#check PullbackLeftCalculusTransfer
#check ambientVerdierLeftCalculus_of_isoClosureClosed2
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_closed2_and_transfer
#check BoundedHomotopyLeftCalculusSufficientPackage
#check boundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
#check metrizableLCABoundedHomotopyExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
#check boundedHomotopyLeftCalculusObstructions
#check boundedHomotopyLeftCalculusObstructions_count
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check boundedHomotopyExactWeakEquivalence

end Checks

end BoundedHomotopyLeftCalculusW217

end LeanLCAExactChallenge
