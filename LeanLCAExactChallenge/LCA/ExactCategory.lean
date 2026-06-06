import LeanLCAExactChallenge.LCA.Pullback
import LeanLCAExactChallenge.LCA.Pushout

/-!
The intended exact-category structure on strict metrizable LCA sequences.

Pushout stability is proved by the explicit quotient construction in
`LCA.Pushout`; pullback stability is proved locally in `LCA.Pullback`.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

/-- The Quillen exact-category structure on strict metrizable LCA sequences. -/
@[reducible]
def quillenExactCategory : QuillenExactCategory MetrizableLCA.{u} where
  Conflation := strictShortExact
  conflation_iso e hS := strictShortExact_iso e hS
  split_conflation _ hS := split_strictShortExact hS
  pushout_inflation {S} hS {Y} a :=
    strictShortExact_categorical_pushout (S := S) hS (Y := Y) a
  pullback_deflation {S} hS {Y} a :=
    strictShortExact_categorical_pullback (S := S) hS (Y := Y) a

instance instQuillenExactCategory : QuillenExactCategory MetrizableLCA.{u} :=
  quillenExactCategory

/-- In the canonical exact-category instance, conflations are exactly strict
short exact sequences of metrizable LCA groups. -/
theorem quillenConflation_iff_strictShortExact {S : ShortComplex MetrizableLCA.{u}} :
    QuillenExactCategory.Conflation S ↔ strictShortExact S := by
  rfl

/-- Recover strict short exactness from a canonical Quillen conflation. -/
theorem strictShortExact_of_quillenConflation {S : ShortComplex MetrizableLCA.{u}}
    (hS : QuillenExactCategory.Conflation S) : strictShortExact S :=
  quillenConflation_iff_strictShortExact.mp hS

/-- Regard a strict short exact sequence as a canonical Quillen conflation. -/
theorem quillenConflation_of_strictShortExact {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) : QuillenExactCategory.Conflation S :=
  quillenConflation_iff_strictShortExact.mpr hS

/-- In the canonical exact-category instance, inflations are precisely maps that
occur as the left map of a strict short exact sequence. -/
theorem quillenInflation_iff_exists_strictShortExact {X Y : MetrizableLCA.{u}}
    (i : X ⟶ Y) :
    QuillenExactCategory.inflation i ↔
      ∃ (Z : MetrizableLCA.{u}) (g : Y ⟶ Z) (zero : i ≫ g = 0),
        strictShortExact (ShortComplex.mk i g zero) := by
  constructor
  · rintro ⟨Z, g, zero, hS⟩
    exact ⟨Z, g, zero, strictShortExact_of_quillenConflation hS⟩
  · rintro ⟨Z, g, zero, hS⟩
    exact ⟨Z, g, zero, quillenConflation_of_strictShortExact hS⟩

/-- In the canonical exact-category instance, deflations are precisely maps that
occur as the right map of a strict short exact sequence. -/
theorem quillenDeflation_iff_exists_strictShortExact {X Y : MetrizableLCA.{u}}
    (p : X ⟶ Y) :
    QuillenExactCategory.deflation p ↔
      ∃ (W : MetrizableLCA.{u}) (f : W ⟶ X) (zero : f ≫ p = 0),
        strictShortExact (ShortComplex.mk f p zero) := by
  constructor
  · rintro ⟨W, f, zero, hS⟩
    exact ⟨W, f, zero, strictShortExact_of_quillenConflation hS⟩
  · rintro ⟨W, f, zero, hS⟩
    exact ⟨W, f, zero, quillenConflation_of_strictShortExact hS⟩

end MetrizableLCA

end LeanLCAExactChallenge
