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

end MetrizableLCA

end LeanLCAExactChallenge
