import LeanLCAExactChallenge.LCA.Pullback

/-!
The intended exact-category structure on strict metrizable LCA sequences.

The construction below is still parameterized by the remaining pushout
stability theorem. Pullback stability is proved locally in `LCA.Pullback`.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

/--
Remaining source-patch assumption needed to upgrade strict LCA sequences to a
Quillen exact category.
-/
structure StrictExactQuillenAxioms : Prop where
  pushout {S : ShortComplex MetrizableLCA.{u}} (hS : strictShortExact S) {Y : MetrizableLCA.{u}}
    (a : S.X₁ ⟶ Y) [HasPushout S.f a] :
    ∃ (Z : MetrizableLCA.{u}) (g : pushout S.f a ⟶ Z)
      (zero : pushout.inr S.f a ≫ g = 0),
      strictShortExact (ShortComplex.mk (pushout.inr S.f a) g zero)

/--
The Quillen exact-category structure obtained once the missing strict LCA
stability theorem is supplied.
-/
@[reducible]
def quillenExactCategory (h : StrictExactQuillenAxioms.{u}) :
    QuillenExactCategory MetrizableLCA.{u} where
  Conflation := strictShortExact
  conflation_iso e hS := strictShortExact_iso e hS
  split_conflation _ hS := split_strictShortExact hS
  pushout_inflation {S} hS {Y} a := h.pushout (S := S) hS (Y := Y) a
  pullback_deflation {S} hS {Y} a :=
    strictShortExact_categorical_pullback (S := S) hS (Y := Y) a

end MetrizableLCA

end LeanLCAExactChallenge
