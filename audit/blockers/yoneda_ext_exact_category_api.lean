import LeanLCAExactChallenge.Ext.Yoneda

set_option autoImplicit false
set_option linter.unusedVariables false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
Resolved local API boundary: Yoneda Ext groups are available for a general
Quillen exact category, independent of the abelian-category derived Ext API.
-/
def exact_category_yoneda_ext_family
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    Type (max (u + 1) (v + 1)) :=
  (X Y : C) → ℕ → Type (max u v)

example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    exact_category_yoneda_ext_family C :=
  fun X Y n => YonedaExt X Y n

#check YonedaExt.baer_sum
#check YonedaExt.zero_equiv_hom

end LeanLCAExactChallenge
