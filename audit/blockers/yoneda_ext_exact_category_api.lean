import LeanLCAExactChallenge.Ext.Yoneda

set_option autoImplicit false
set_option linter.unusedVariables false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
Missing local theorem/API: Yoneda Ext groups for a general Quillen exact
category, independent of the abelian-category derived Ext API.
-/
def missing_exact_category_yoneda_ext_statement
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] : Prop :=
  ∀ X Y : C, ∀ n : ℕ, Nonempty (Type (max u v))

end LeanLCAExactChallenge
