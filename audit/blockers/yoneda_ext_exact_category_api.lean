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
#check ShortExactExtension.PullbackData
#check ShortExactExtension.PushoutData
#check MetrizableLCA.biprodObjIsoBiprod
#check MetrizableLCA.biprodDiag
#check MetrizableLCA.biprodCodiag
#check MetrizableLCA.shortExactExtensionBiprod
#check MetrizableLCA.shortExactExtensionBiprod_i_fst
#check MetrizableLCA.shortExactExtensionBiprod_i_snd
#check MetrizableLCA.shortExactExtensionBiprod_p_fst
#check MetrizableLCA.shortExactExtensionBiprod_p_snd
#check MetrizableLCA.shortExactExtensionBinaryBiproduct
#check MetrizableLCA.shortExactExtensionBinaryBiproduct_i_fst
#check MetrizableLCA.shortExactExtensionBinaryBiproduct_i_snd
#check MetrizableLCA.shortExactExtensionBinaryBiproduct_p_fst
#check MetrizableLCA.shortExactExtensionBinaryBiproduct_p_snd
#check MetrizableLCA.shortExactExtensionPullback
#check MetrizableLCA.shortExactExtensionPullback_i_map
#check MetrizableLCA.shortExactExtensionPullback_map_p
#check MetrizableLCA.shortExactExtensionPullbackData
#check MetrizableLCA.shortExactExtensionPushout
#check MetrizableLCA.shortExactExtensionPushout_i
#check MetrizableLCA.shortExactExtensionPushout_map_p
#check MetrizableLCA.shortExactExtensionPushoutData
#check MetrizableLCA.shortExactExtensionBaerSum
#check MetrizableLCA.shortExactExtensionBaerSumData
#check YonedaExt.ofExtension_eq_ofExtension_of_rel
#check YonedaExt.ofExtension_eq_ofExtension_of_relIso
#check YonedaExt.ofExtension_eq_zero_of_split
#check YonedaExtension.BaerSumData
#check YonedaExtension.BaerSumData.head
#check YonedaExtension.Rel.refl
#check YonedaExtension.RightSplitData
#check YonedaExtension.SplitFactorData
#check YonedaExtension.HomTailData
#check YonedaExtension.HomTailData.one
#check YonedaExtension.HomTailData.cons
#check YonedaExtension.HomHeadData
#check YonedaExtension.HomHeadData.cons
#check YonedaExtension.pullbackHeadWith
#check YonedaExtension.pullbackHeadWithData
#check MetrizableLCA.yonedaExtensionPullbackHead
#check MetrizableLCA.yonedaExtensionPullbackHeadData
#check YonedaExtension.PositiveChain
#check YonedaExtension.PositiveChain.toYonedaExtension
#check YonedaExtension.PositiveChain.consLeftMap
#check YonedaExtension.PositiveChain.SplitFactorData
#check YonedaExtension.PositiveChain.SplitFactorData.toYonedaExtension
#check YonedaExtension.PositiveChain.SplitFactorData.consLeftMap
#check YonedaExt.ofExtension_eq_add_of_relation_mem
#check YonedaExt.ofExtension_eq_add_of_baer
#check YonedaExt.ofExtension_eq_add_of_baerChain
#check YonedaExt.ofExtension_eq_add_of_baerHead
#check YonedaExt.baer_sum_ofExtension_eq_of_relation_mem
#check YonedaExt.baer_sum_ofExtension_eq_of_baer
#check YonedaExt.baer_sum_ofExtension_eq_of_baerChain
#check YonedaExt.baer_sum_ofExtension_eq_of_baerHead
#check YonedaExtension.consLeftMap
#check YonedaExt.ofExtension_cons_eq_zero_of_right_split
#check YonedaExt.ofExtension_eq_zero_of_rightSplitData
#check YonedaExt.ofExtension_eq_zero_of_splitFactorData
#check YonedaExt.ofExtension_eq_ofExtension_of_homTailData
#check YonedaExt.ofExtension_cons_ofHom_eq_of_pushoutData
#check YonedaExt.pullbackHeadOfExtensionWith
#check YonedaExt.leftProductByExtension
#check YonedaExt.leftProductByExtension_ofExtension
#check YonedaExt.leftProductByExtension_ofExtension_eq_zero_of_split
#check YonedaExt.leftProductByExtension_ofExtension_eq_of_isoLeft
#check YonedaExt.leftProductByExtension_ofExtension_eq_add_of_baerLeft
#check YonedaExt.leftProductByExtension_baer_sum_ofExtension_eq_of_baerLeft
#check YonedaExt.positiveChainLeftFreeHom
#check YonedaExt.positiveChainLeft_relationSubgroup_le
#check YonedaExt.leftProductByPositiveChain
#check YonedaExt.leftProductByPositiveChain_ofExtension
#check YonedaExt.leftProductByPositiveChain_ofExtension_eq_zero_of_splitFactor
#check YonedaExt.leftProductByPositiveChain_cons_ofExtension_eq_of_isoHead
#check YonedaExt.leftProductByPositiveChain_cons_ofExtension_eq_add_of_baerHead
#check YonedaExt.leftProductByPositiveChain_cons_baer_sum_ofExtension_eq_of_baerHead

end LeanLCAExactChallenge
