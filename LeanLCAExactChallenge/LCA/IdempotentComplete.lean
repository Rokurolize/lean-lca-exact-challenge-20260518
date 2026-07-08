import LeanLCAExactChallenge.LCA.Pullback
import Mathlib.CategoryTheory.Idempotents.Basic

/-!
Idempotent completeness of the category of metrizable locally compact abelian groups.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

instance instIsIdempotentComplete : IsIdempotentComplete MetrizableLCA.{u} := by
  rw [CategoryTheory.Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent]
  intro X p _hp
  infer_instance

end MetrizableLCA

end LeanLCAExactChallenge
