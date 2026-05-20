import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
Boundary audit for collapsing the exact-acyclic homotopy iso-closure.

This follows w216 but minimizes the missing input: the requested inclusion
`exactAcyclicHomotopyIsoClosure C ≤ exactAcyclicHomotopyObject C` follows from exact
acyclicity being transported along homotopy equivalences of selected cochain complexes.
Mathlib exposes `HomotopyCategory.homotopyEquivOfIso`, so this is the strict realization
theorem needed for the collapse.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ExactAcyclicIsoClosureCollapseW221

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- The target collapse: the explicit homotopy-category isomorphism closure adds no objects. -/
abbrev ExactAcyclicIsoClosureCollapse : Prop :=
  exactAcyclicHomotopyIsoClosure C ≤ exactAcyclicHomotopyObject C

/--
Minimal strict-realization input for this collapse.

After extracting a `HomotopyEquiv` from a homotopy-category isomorphism, this theorem says
the selected target complex is again exact acyclic. It is exactly the homotopy-invariance
property still missing from the local exact-category API.
-/
abbrev ExactAcyclicTransportOfHomotopyEquiv : Prop :=
  ∀ {K L : CochainComplex C ℤ},
    exactAcyclic C K → HomotopyEquiv K L → exactAcyclic C L

/-- The homotopy-equivalence transport theorem collapses the iso-closure. -/
theorem exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport
    (transport : ExactAcyclicTransportOfHomotopyEquiv C) :
    ExactAcyclicIsoClosureCollapse C := by
  intro X hX
  rcases hX with ⟨Y, hY, ⟨e⟩⟩
  obtain ⟨X₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  exact transport hY (HomotopyCategory.homotopyEquivOfIso e.symm)

/-- The collapse is equivalent to the usual `IsClosedUnderIsomorphisms` typeclass input. -/
theorem exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
    (h : ExactAcyclicIsoClosureCollapse C) :
    (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms := by
  rw [ObjectProperty.isClosedUnderIsomorphisms_iff_isoClosure_eq_self]
  apply le_antisymm
  · exact h
  · exact ObjectProperty.le_isoClosure (exactAcyclicHomotopyObject C)

/-- The homotopy-equivalence transport theorem supplies the iso-closed typeclass directly. -/
theorem exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivTransport
    (transport : ExactAcyclicTransportOfHomotopyEquiv C) :
    (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms :=
  exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse C
    (exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport C transport)

/-- Once the object predicate is iso-closed, the iso-closure inclusion is automatic. -/
theorem exactAcyclicIsoClosureCollapse_of_isClosedUnderIsomorphisms
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    ExactAcyclicIsoClosureCollapse C := by
  dsimp [ExactAcyclicIsoClosureCollapse, exactAcyclicHomotopyIsoClosure]
  rw [ObjectProperty.isoClosure_le_iff]

/-- W216's strict-realization boundary, minimized by making the iso-collapse input explicit. -/
structure ExactAcyclicStrictRealizationBoundary
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  homotopyEquivTransport : ExactAcyclicTransportOfHomotopyEquiv C
  triangleRealization : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C

/--
The minimized boundary supplies both exact-side closure facts: exact acyclicity is invariant
under homotopy-category isomorphisms, and the existing w216 triangle realization closes the
Verdier-side iso-closure under distinguished triangles.
-/
theorem exactSideClosures_of_strictRealizationBoundary
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : ExactAcyclicStrictRealizationBoundary C) :
    (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms ∧
      (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ := by
  constructor
  · exact exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivTransport
      C P.homotopyEquivTransport
  · exact exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization
      C P.triangleRealization

/-- Direct bounded left-calculus package after replacing the opaque iso-closed input. -/
structure DirectBoundedLeftCalculusPackage
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  homotopyEquivTransport : ExactAcyclicTransportOfHomotopyEquiv C
  homotopyWeakEquivalenceLeftCalculus :
    (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions

/-- W212's transfer theorem using the minimized homotopy-equivalence transport input. -/
theorem boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : DirectBoundedLeftCalculusPackage C) :
    (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions := by
  letI : (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms :=
    exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivTransport
      C P.homotopyEquivTransport
  letI : (boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions :=
    P.homotopyWeakEquivalenceLeftCalculus
  exact boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C

/-- Concrete finite-product consumer for the `MetrizableLCA` target under the package. -/
noncomputable abbrev dboundedFiniteProducts_metrizableLCA_of_package
    (P : DirectBoundedLeftCalculusPackage MetrizableLCA.{0}) :
    HasFiniteProducts (Dbounded MetrizableLCA.{0}) := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
    boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_package MetrizableLCA P
  exact BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA

/-- Remaining named inputs for an unconditional `MetrizableLCA` result on this route. -/
def remainingMetrizableLCAInputs : List String :=
  ["exactAcyclic transport along HomotopyEquiv for MetrizableLCA",
    "(boundedHomotopyExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions"]

theorem remainingMetrizableLCAInputs_count :
    remainingMetrizableLCAInputs.length = 2 := rfl

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check ExactAcyclicIsoClosureCollapse
#check ExactAcyclicTransportOfHomotopyEquiv
#check exactAcyclicIsoClosureCollapse_of_homotopyEquivTransport
#check exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_isoClosureCollapse
#check exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivTransport
#check exactAcyclicIsoClosureCollapse_of_isClosedUnderIsomorphisms
#check ExactAcyclicStrictRealizationBoundary
#check exactSideClosures_of_strictRealizationBoundary
#check DirectBoundedLeftCalculusPackage
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_package
#check dboundedFiniteProducts_metrizableLCA_of_package
#check remainingMetrizableLCAInputs
#check remainingMetrizableLCAInputs_count
#check HomotopyCategory.homotopyEquivOfIso
#check exactAcyclicHomotopyIsoClosure_isClosedUnderIsomorphisms
#check exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed
#check BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA

end Checks

end ExactAcyclicIsoClosureCollapseW221

end LeanLCAExactChallenge
