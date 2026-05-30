import LeanLCAExactChallenge.Derived.Bounded

/-!
Left-calculus route for the bounded-derived stable typeclass surface.

This module keeps the W828 typeclass route honest: preadditivity, zero object, and localized
shift additivity are not arbitrary stable evidence, but consequences of a concrete left calculus
of fractions for the direct bounded exact weak equivalences. The route is still nonterminal because
the left-calculus premise and the remaining finite-limit/finite-colimit/triangulated fields are
not constructed here.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/-- Stable fields supplied by direct bounded left calculus for `Dbounded MetrizableLCA`. -/
def metrizableLeftCalculusStableRouteSuppliedFieldNames : List String :=
  ["Preadditive (Dbounded MetrizableLCA)",
    "HasZeroObject (Dbounded MetrizableLCA)",
    "forall n, (shiftFunctor (Dbounded MetrizableLCA) n).Additive",
    "(shiftFunctor (Dbounded MetrizableLCA) 1).Additive"]

/-- Direct bounded left calculus supplies four stable fields. -/
theorem metrizableLeftCalculusStableRouteSuppliedFieldNames_count :
    Dbounded.metrizableLeftCalculusStableRouteSuppliedFieldNames.length = 4 :=
  rfl

/--
Required inputs for the left-calculus stable route. This replaces the first four W828 stable
typeclass fields by the concrete localization-calculus premise that supplies them.
-/
def metrizableLeftCalculusStableRouteRequiredFieldNames : List String :=
  ["(boundedExactWeakEquivalence MetrizableLCA).HasLeftCalculusOfFractions",
    "HasFiniteLimits (Dbounded MetrizableLCA)",
    "HasFiniteColimits (Dbounded MetrizableLCA)",
    "Pretriangulated (Dbounded MetrizableLCA)",
    "IsTriangulated (Dbounded MetrizableLCA)"]

/-- Five inputs remain on the left-calculus stable route. -/
theorem metrizableLeftCalculusStableRouteRequiredFieldNames_count :
    Dbounded.metrizableLeftCalculusStableRouteRequiredFieldNames.length = 5 :=
  rfl

/--
Left-calculus-resolved stable bounded-derived package for `MetrizableLCA`.

Compared with `boundedDerivedInfinityCategoryOfMetrizableStableInstances`, this route obtains
preadditivity, zero object, all-shift additivity, and suspension additivity from the direct
bounded left-calculus theorem. It still requires the left-calculus premise itself and the remaining
finite-limit, finite-colimit, pretriangulated, and triangulated structures, so it is not a product
success witness.
-/
noncomputable def boundedDerivedInfinityCategoryOfMetrizableLeftCalculusStableRoute
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions]
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions MetrizableLCA.{0} n
      Pretriangulated (Dbounded MetrizableLCA.{0}))
    (triangulated :
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions MetrizableLCA.{0} n
      letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
      IsTriangulated (Dbounded MetrizableLCA.{0})) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) where
  quasicategoryCarrier := rfl
  preadditive := Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
  finiteLimitInstance := finiteLimits
  finiteColimitInstance := finiteColimits
  zeroObjectInstance := Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
  shiftAdditiveAll := by
    intro n
    exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions MetrizableLCA.{0} n
  suspensionAdditive := by
    change (shiftFunctor (Dbounded MetrizableLCA.{0}) (1 : ℤ)).Additive
    exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions MetrizableLCA.{0} 1
  pretriangulatedStructure := pretriangulated
  triangulatedStructure := triangulated

end Dbounded

end LeanLCAExactChallenge
