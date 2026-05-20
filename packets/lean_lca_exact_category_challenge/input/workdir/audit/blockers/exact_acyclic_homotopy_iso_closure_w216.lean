import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
Boundary audit for exact-acyclic homotopy-object isomorphism closure.

Support worker w216 identified `(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms`
as one direct input needed before
`boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed` can transfer the
homotopy/Verdier left calculus back to direct bounded exact weak equivalences.

This file records the minimal compiling iso-closure collapse needed for that transfer, plus
the remaining strict-realization input that can supply the Verdier-side calculus.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ExactAcyclicHomotopyIsoClosureW216

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/--
The exact missing isomorphism-invariance theorem.

Equivalently, every object that is merely isomorphic in the homotopy category to an exact
acyclic representative must itself be exact acyclic through its selected `.as` representative.
-/
abbrev ExactAcyclicIsoClosureCollapse : Prop :=
  exactAcyclicHomotopyIsoClosure C ≤ exactAcyclicHomotopyObject C

/-- The collapse of the explicit iso-closure is exactly the requested typeclass input. -/
theorem exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
    (h : ExactAcyclicIsoClosureCollapse C) :
    (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms := by
  rw [ObjectProperty.isClosedUnderIsomorphisms_iff_isoClosure_eq_self]
  apply le_antisymm
  · exact h
  · exact ObjectProperty.le_isoClosure (exactAcyclicHomotopyObject C)

/--
A strict-realization boundary that isolates the two exact-side inputs still needed for a
fully intrinsic route: collapse the iso-closure back to the original exact predicate, and
realize distinguished triangles with exact-acyclic endpoints by strict cochain data.
-/
structure ExactAcyclicStrictRealizationBoundary
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  isoClosureCollapse : ExactAcyclicIsoClosureCollapse C
  exactRealize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C

/--
The strict-realization boundary supplies both exact-side closure facts currently used by the
Verdier route: original exact acyclicity is homotopy-category iso-invariant, and its explicit
iso-closure is closed under distinguished triangles.
-/
theorem exactSideClosures_of_strictRealizationBoundary
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : ExactAcyclicStrictRealizationBoundary C) :
    (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms ∧
      (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ := by
  constructor
  · exact exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
      C P.isoClosureCollapse
  · exact exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization
      C P.exactRealize

/--
The complete local package needed to make W212's direct bounded left-calculus transfer usable.

The first field is the new iso-closure theorem isolated above. The second field is still a
separate bounded homotopy/Verdier denominator-calculus input; the existing project code does
not derive it from the exact-side collapse alone.
-/
structure DirectBoundedLeftCalculusPackage
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  isoClosureCollapse : ExactAcyclicIsoClosureCollapse C
  homotopyWeakEquivalenceLeftCalculus :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions

/-- W212's transfer theorem after replacing the opaque iso-closed typeclass by the collapse. -/
theorem boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : DirectBoundedLeftCalculusPackage C) :
    (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions := by
  letI : (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms :=
    exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
      C P.isoClosureCollapse
  letI : (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
    P.homotopyWeakEquivalenceLeftCalculus
  exact boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C

/--
For the concrete finite-product target, this package gives the direct bounded left calculus
needed by `BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA`.
-/
noncomputable abbrev dboundedFiniteProducts_metrizableLCA_of_package
    (P : DirectBoundedLeftCalculusPackage MetrizableLCA.{0}) :
    HasFiniteProducts (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_package MetrizableLCA P
  exact BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA

/-- The remaining named inputs for an unconditional `MetrizableLCA` result. -/
def remainingMetrizableLCAInputs : List String :=
  ["exactAcyclicHomotopyIsoClosure MetrizableLCA ≤ exactAcyclicHomotopyObject MetrizableLCA",
    "(boundedHomotopyExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions"]

theorem remainingMetrizableLCAInputs_count :
    remainingMetrizableLCAInputs.length = 2 := rfl

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check ExactAcyclicIsoClosureCollapse
#check exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
#check ExactAcyclicStrictRealizationBoundary
#check exactSideClosures_of_strictRealizationBoundary
#check DirectBoundedLeftCalculusPackage
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
#check dboundedFiniteProducts_metrizableLCA_of_package
#check remainingMetrizableLCAInputs
#check remainingMetrizableLCAInputs_count
#check exactAcyclicHomotopyIsoClosure_isClosedUnderIsomorphisms
#check exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_triangleh_iso13_realization
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed
#check BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA

end Checks

end ExactAcyclicHomotopyIsoClosureW216

end LeanLCAExactChallenge
