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
#check YonedaRelGenerator
#check yonedaRelationSubgroup
#check ShortExactExtension.BaerSumData
#check YonedaExt.ofExtension_eq_ofExtension_of_rel
#check YonedaExt.ofExtension_eq_ofExtension_of_relIso
#check YonedaExt.ofExtension_eq_zero_of_split
#check YonedaExtension.BaerSumData
#check YonedaExtension.RightSplitData
#check YonedaExtension.SplitFactorData
#check YonedaExtension.PositiveChain
#check YonedaExtension.PositiveChain.toYonedaExtension
#check YonedaExtension.PositiveChain.consLeftMap
#check YonedaExt.ofExtension_eq_add_of_relation_mem
#check YonedaExt.ofExtension_eq_add_of_baer
#check YonedaExt.ofExtension_eq_add_of_baerChain
#check YonedaExt.baer_sum_ofExtension_eq_of_relation_mem
#check YonedaExt.baer_sum_ofExtension_eq_of_baer
#check YonedaExt.baer_sum_ofExtension_eq_of_baerChain
#check YonedaExtension.consLeftMap
#check YonedaExt.ofExtension_cons_eq_zero_of_right_split
#check YonedaExt.ofExtension_eq_zero_of_rightSplitData
#check YonedaExt.ofExtension_eq_zero_of_splitFactorData
#check YonedaExt.leftProductByExtension
#check YonedaExt.leftProductByExtension_ofExtension
#check YonedaExt.leftProductByExtension_ofExtension_eq_zero_of_split
#check YonedaExt.positiveChainLeftFreeHom
#check YonedaExt.positiveChainLeft_relationSubgroup_le
#check YonedaExt.leftProductByPositiveChain
#check YonedaExt.leftProductByPositiveChain_ofExtension

end LeanLCAExactChallenge
