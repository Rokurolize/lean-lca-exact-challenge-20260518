import LeanLCAExactChallenge.LCA.ExactCategory

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory

/--
Resolved local theorem/API: strict short exact complexes of metrizable LCA
groups supply the local Quillen exact-category interface.
-/
def strict_lca_quillen_exact_category_statement : Prop :=
  Nonempty (QuillenExactCategory MetrizableLCA.{u})

/-- Checked boundary: the LCA exact-category instance is now available locally. -/
example : strict_lca_quillen_exact_category_statement.{u} :=
  ⟨MetrizableLCA.quillenExactCategory⟩

#check (inferInstance : QuillenExactCategory MetrizableLCA.{u})
#check MetrizableLCA.strictShortExact_biprod

end LeanLCAExactChallenge
