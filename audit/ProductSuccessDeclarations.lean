import LeanLCAExactChallenge

/-!
Product-success contract for the exact LCA category challenge.

This file is intentionally a red audit for the present worktree.  It should
compile only after the four-part product theorem is implemented without the
source-patch boundary recorded in the historical handoff artifacts.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

/--
Product success requires a strict metrizable LCA exact-category structure
available without an explicit `StrictExactQuillenAxioms` argument.
-/
example : QuillenExactCategory MetrizableLCA := by
  exact MetrizableLCA.quillenExactCategory

/-
Product success requires exact-category Ext for the strict metrizable LCA exact
category, not only the abelian-category `CategoryTheory.Abelian.Ext` wrapper.
-/
#check (fun (X Y : MetrizableLCA) => YonedaExt (C := MetrizableLCA) X Y 1)

/-
Product success requires the bounded derived infinity-category construction for
the strict metrizable LCA exact category, not an externally supplied interface.
-/
#check (Dbounded (C := MetrizableLCA))

end LeanLCAExactChallenge
