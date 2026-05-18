import LeanLCAExactChallenge.LCA.ExactCategory

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

/--
Missing local theorem: strict short exact complexes of metrizable LCA groups are
stable under the Quillen exact-category operations.
-/
def missing_strict_lca_quillen_axioms_statement : Prop :=
  StrictExactQuillenAxioms.{u}

/-- Checked frontier: the statement is expressible against local and mathlib APIs. -/
def strict_lca_quillen_axioms_is_a_proposition :
    Prop :=
  missing_strict_lca_quillen_axioms_statement.{u}

end MetrizableLCA

end LeanLCAExactChallenge
