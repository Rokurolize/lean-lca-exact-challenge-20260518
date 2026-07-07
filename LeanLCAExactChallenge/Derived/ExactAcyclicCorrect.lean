import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
# Correct cycle-object exact acyclicity

This file isolates the corrected exact-category acyclicity predicate for cochain
complexes. The legacy predicate in `Derived.Bounded` is degreewise:

```lean
∀ i, QuillenExactCategory.Conflation (K.sc i)
```

That is too strong and is not the usual exact-category definition of an acyclic
complex. The replacement below records cycle objects `Z i`, conflations
`Z i ⟶ K.X i ⟶ Z (i + 1)`, and the factorization of the differential through
those cycle objects.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Category
open CategoryTheory.Limits
open HomologicalComplex

universe w v u

namespace LeanLCAExactChallenge

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/--
Correct exact-category acyclicity data for a cochain complex.

For every degree `i`, there is a cycle object `Z i`, a conflation
`Z i ⟶ K.X i ⟶ Z (i + 1)`, and the differential factors as
`K.X i ⟶ Z (i + 1) ⟶ K.X (i + 1)`.
-/
structure ExactAcyclicWithCyclesData (K : CochainComplex C ℤ) where
  Z : ℤ → C
  incl : ∀ i : ℤ, Z i ⟶ K.X i
  proj : ∀ i : ℤ, K.X i ⟶ Z (i + 1)
  zero : ∀ i : ℤ, incl i ≫ proj i = 0
  conflation : ∀ i : ℤ,
    QuillenExactCategory.Conflation (ShortComplex.mk (incl i) (proj i) (zero i))
  d_eq : ∀ i : ℤ, proj i ≫ incl (i + 1) = K.d i (i + 1)

/-- The corrected acyclicity predicate, named as a predicate rather than as data. -/
def exactAcyclicWithCycles (K : CochainComplex C ℤ) : Prop :=
  Nonempty (ExactAcyclicWithCyclesData C K)

namespace ExactAcyclicWithCyclesData

variable {C}
variable {K : CochainComplex C ℤ}

/-- The actual short complex whose conflation is required in degree `i`. -/
def shortComplex (h : ExactAcyclicWithCyclesData C K) (i : ℤ) : ShortComplex C :=
  ShortComplex.mk (h.incl i) (h.proj i) (h.zero i)

@[simp]
theorem shortComplex_f (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    (h.shortComplex i).f = h.incl i := rfl

@[simp]
theorem shortComplex_g (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    (h.shortComplex i).g = h.proj i := rfl

/-- The corrected predicate gives a conflation in each cycle-object degree. -/
theorem conflation_shortComplex (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    QuillenExactCategory.Conflation (h.shortComplex i) :=
  h.conflation i

/-- The differential factors through the next cycle object. -/
theorem differential_factors (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    h.proj i ≫ h.incl (i + 1) = K.d i (i + 1) :=
  h.d_eq i

end ExactAcyclicWithCyclesData

/--
The legacy predicate from `Derived.Bounded`, given a descriptive name.
This is retained only to make the distinction explicit in later refactors.
-/
def degreewiseConflationAcyclic (K : CochainComplex C ℤ) : Prop :=
  ∀ i : ℤ, QuillenExactCategory.Conflation (K.sc i)

/-- The descriptive legacy name is definitionally the old `exactAcyclic`. -/
theorem degreewiseConflationAcyclic_eq_legacy (K : CochainComplex C ℤ) :
    degreewiseConflationAcyclic C K = exactAcyclic C K :=
  rfl

/--
Corrected weak equivalences for bounded complexes: the mapping cone is acyclic
in the cycle-object exact-category sense.
-/
def boundedExactWeakEquivalenceWithCycles [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  fun _K _L f =>
    exactAcyclicWithCycles C
      (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f))

set_option linter.unusedVariables false in
@[simp]
theorem boundedExactWeakEquivalenceWithCycles_iff
    [HasBinaryBiproducts C]
    {K L : BoundedComplexCategory C} (f : K ⟶ L) :
    boundedExactWeakEquivalenceWithCycles C f ↔
      exactAcyclicWithCycles C
        (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f)) :=
  Iff.rfl

namespace MetrizableLCA

/--
The corrected acyclicity predicate specialized to metrizable locally compact
abelian groups.
-/
abbrev challengeExactAcyclicWithCycles
    (K : CochainComplex MetrizableLCA.{u} ℤ) : Prop :=
  exactAcyclicWithCycles MetrizableLCA K

/--
For `MetrizableLCA`, the corrected predicate is exactly the existence of cycle
objects whose degreewise cycle short complexes satisfy `challengeExactSequence`,
and through which the complex differential factors.
-/
theorem exactAcyclicWithCycles_iff_challengeCycleExactSequences
    (K : CochainComplex MetrizableLCA.{u} ℤ) :
    exactAcyclicWithCycles MetrizableLCA K ↔
      ∃ (Z : ℤ → MetrizableLCA.{u})
        (incl : ∀ i : ℤ, Z i ⟶ K.X i)
        (proj : ∀ i : ℤ, K.X i ⟶ Z (i + 1))
        (zero : ∀ i : ℤ, incl i ≫ proj i = 0),
          (∀ i : ℤ,
            challengeExactSequence
              (ShortComplex.mk (incl i) (proj i) (zero i))) ∧
          (∀ i : ℤ, proj i ≫ incl (i + 1) = K.d i (i + 1)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.Z, h.incl, h.proj, h.zero,
      (fun i => (quillenConflation_iff_challengeExactSequence).1 (h.conflation i)),
      h.d_eq⟩
  · rintro ⟨Z, incl, proj, zero, hExact, hDiff⟩
    exact ⟨
      { Z := Z
        incl := incl
        proj := proj
        zero := zero
        conflation := fun i =>
          (quillenConflation_iff_challengeExactSequence).2 (hExact i)
        d_eq := hDiff }⟩

/--
The corrected mapping-cone weak equivalence for bounded complexes in
`MetrizableLCA`.
-/
def boundedExactWeakEquivalenceWithCycles :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{u}) :=
  LeanLCAExactChallenge.boundedExactWeakEquivalenceWithCycles MetrizableLCA

end MetrizableLCA

end LeanLCAExactChallenge
