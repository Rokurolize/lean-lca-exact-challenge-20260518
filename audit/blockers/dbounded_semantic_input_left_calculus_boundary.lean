import LeanLCAExactChallenge.Derived.Bounded

/-!
Left-calculus boundary audit for the semantic stable `Dbounded` route.

The previous semantic-input adapter names seven ordinary-category fields needed before the
strict `Dbounded` route can be reviewed as a stable infinity-category claim.  This file records
which of those fields are already available from the current left-calculus API and which fields
remain genuinely unconstructed.  It is a non-product blocker audit, not a product interface.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace DboundedSemanticInputLeftCalculusBoundary

/--
The part of the semantic stable input already supplied by the current strict `Dbounded`
left-calculus route.
-/
structure DboundedLeftCalculusAvailableInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] : Type (max u v) where
  preadditive : Preadditive (Dbounded C)
  zeroObject : HasZeroObject (Dbounded C)
  shiftAdditiveAll :
    letI : Preadditive (Dbounded C) := preadditive
    ∀ n : ℤ, (shiftFunctor (Dbounded C) n).Additive

/-- Assemble the available fields from declarations already present in `Derived.Bounded`. -/
noncomputable def currentLeftCalculusAvailableInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    DboundedLeftCalculusAvailableInput C where
  preadditive := Dbounded.preadditiveOfHasLeftCalculusOfFractions C
  zeroObject := Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions C
  shiftAdditiveAll := by
    intro n
    exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions C n

/-- Names of the semantic-input fields already derivable from the current left-calculus route. -/
def availableSemanticFieldNames : List String :=
  ["Preadditive (Dbounded C)", "HasZeroObject (Dbounded C)",
    "forall n, (shiftFunctor (Dbounded C) n).Additive"]

/-- The left-calculus route currently supplies three semantic-input fields. -/
theorem availableSemanticFieldNames_count :
    availableSemanticFieldNames.length = 3 := rfl

/--
The semantic stable fields still missing after consuming the current left-calculus API.

This list intentionally excludes fields proved available above.  The remaining gap is not an
ordinary infinity-nerve marker; it is ordinary categorical structure on the strict `Dbounded`
localization.
-/
def missingAfterLeftCalculusFieldNames : List String :=
  ["HasFiniteLimits (Dbounded C)", "HasFiniteColimits (Dbounded C)",
    "Pretriangulated (Dbounded C)", "IsTriangulated (Dbounded C)"]

/-- Four semantic-input fields remain after the left-calculus boundary is applied. -/
theorem missingAfterLeftCalculusFieldNames_count :
    missingAfterLeftCalculusFieldNames.length = 4 := rfl

/--
Current route status: existing declarations provide only the available subrecord, not the full
semantic stable input record.
-/
structure LeftCalculusBoundaryState
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] : Type (max (max u v) 2) where
  availableInput : DboundedLeftCalculusAvailableInput C
  finiteLimitsConstructor : Option String
  finiteColimitsConstructor : Option String
  pretriangulatedConstructor : Option String
  triangulatedConstructor : Option String

/-- Reproducible current boundary state: no constructor has been supplied for the four missing fields. -/
noncomputable def currentLeftCalculusBoundaryState
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    LeftCalculusBoundaryState C where
  availableInput := currentLeftCalculusAvailableInput C
  finiteLimitsConstructor := none
  finiteColimitsConstructor := none
  pretriangulatedConstructor := none
  triangulatedConstructor := none

theorem currentLeftCalculusBoundaryState_finiteLimits_missing
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (currentLeftCalculusBoundaryState C).finiteLimitsConstructor = none := rfl

theorem currentLeftCalculusBoundaryState_finiteColimits_missing
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (currentLeftCalculusBoundaryState C).finiteColimitsConstructor = none := rfl

theorem currentLeftCalculusBoundaryState_pretriangulated_missing
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (currentLeftCalculusBoundaryState C).pretriangulatedConstructor = none := rfl

theorem currentLeftCalculusBoundaryState_triangulated_missing
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (currentLeftCalculusBoundaryState C).triangulatedConstructor = none := rfl

section Checks

#check DboundedLeftCalculusAvailableInput
#check currentLeftCalculusAvailableInput
#check availableSemanticFieldNames
#check availableSemanticFieldNames_count
#check missingAfterLeftCalculusFieldNames
#check missingAfterLeftCalculusFieldNames_count
#check LeftCalculusBoundaryState
#check currentLeftCalculusBoundaryState
#check currentLeftCalculusBoundaryState_finiteLimits_missing
#check currentLeftCalculusBoundaryState_finiteColimits_missing
#check currentLeftCalculusBoundaryState_pretriangulated_missing
#check currentLeftCalculusBoundaryState_triangulated_missing
#check Dbounded.preadditiveOfHasLeftCalculusOfFractions
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions

end Checks

end DboundedSemanticInputLeftCalculusBoundary

end LeanLCAExactChallenge
