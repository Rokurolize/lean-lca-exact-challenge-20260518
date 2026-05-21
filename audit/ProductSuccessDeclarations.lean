import LeanLCAExactChallenge

/-!
Product-success contract for the exact LCA category challenge.

This file checks that the public declarations used for the final product are
available from the strict metrizable LCA exact structure, without routing
through abelian-category Ext or an externally supplied derived construction.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

#check LeanLCAExactChallenge.QuillenExactCategory.inflation_of_conflation
#check LeanLCAExactChallenge.QuillenExactCategory.deflation_of_conflation
#check LeanLCAExactChallenge.QuillenExactCategory.conflation_of_splitting
#check LeanLCAExactChallenge.QuillenExactCategory.inflation_of_splitting
#check LeanLCAExactChallenge.QuillenExactCategory.deflation_of_splitting
#check LeanLCAExactChallenge.QuillenExactCategory.conflation_iso_transport

/--
The strict metrizable LCA exact-category structure is now available without
an extra premise argument.
-/
example : QuillenExactCategory MetrizableLCA := by
  exact MetrizableLCA.quillenExactCategory

/-- The strict metrizable LCA category has the biproducts needed for mapping cones. -/
example : HasBinaryBiproducts MetrizableLCA := by infer_instance

/-- The strict metrizable LCA category has a genuine zero object. -/
example : HasZeroObject MetrizableLCA := by infer_instance

/-- The strict metrizable LCA category has finite products from zero and binary products. -/
example : HasFiniteProducts MetrizableLCA := by infer_instance

/-- The strict metrizable LCA category has pullbacks from the explicit subgroup model. -/
example : HasPullbacks MetrizableLCA := by infer_instance

/-- The strict metrizable LCA category has finite limits from terminal objects and pullbacks. -/
example : HasFiniteLimits MetrizableLCA := by infer_instance

/-- The strict metrizable LCA category has cokernels from closed range-closure quotients. -/
example : HasCokernels MetrizableLCA := by infer_instance

/-- The strict metrizable LCA category has finite colimits from cokernels and finite coproducts. -/
example : HasFiniteColimits MetrizableLCA := by infer_instance

#check MetrizableLCA.zeroObj
#check MetrizableLCA.zeroObj_isZero
#check MetrizableLCA.instHasPullbacks
#check MetrizableLCA.instHasFiniteLimits
#check MetrizableLCA.cokernelIsColimit
#check MetrizableLCA.instHasCokernels
#check MetrizableLCA.instHasFiniteColimits
#check MetrizableLCA.pushoutCokernelMap_open_surjection
#check MetrizableLCA.pushoutCokernelMap_kernel_iff_range_inr
#check MetrizableLCA.shortExactExtensionPushout_kernel_iff_range_i
#check MetrizableLCA.strictShortExact_pushout
#check MetrizableLCA.forgetToAddCommGrpCat_exact_of_strict
#check (inferInstance : HasForget₂ MetrizableLCA AddCommGrpCat)
#check (inferInstance : (forget₂ MetrizableLCA AddCommGrpCat).Additive)
#check MetrizableLCA.strictShortExact_of_exact_of_topology
#check MetrizableLCA.cokernelSubgroup_eq_top_of_surjective
#check MetrizableLCA.cokernelSubgroup_eq_top_iff_cokernelObj_isZero
#check MetrizableLCA.underlyingAddCommGrpFunctor
#check MetrizableLCA.forgottenCokernelπ
#check MetrizableLCA.forgottenCokernelCofork
#check MetrizableLCA.forgottenCokernelCoforkIsColimit_of_closureKernel
#check MetrizableLCA.forgottenAlgebraicRangeSubgroup
#check MetrizableLCA.ClosureKernelInput
#check MetrizableLCA.forgottenMappedExplicitCokernelCocone
#check MetrizableLCA.forgottenMappedExplicitCokernelCoconeIsColimit_of_closureKernelInput
#check MetrizableLCA.forgottenMappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq
#check MetrizableLCA.forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
#check MetrizableLCA.forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
#check MetrizableLCA.forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosed_range
#check MetrizableLCA.preservesCokernelOf_isClosed_range
#check MetrizableLCA.preservesCokernelOf_isClosedMap
#check MetrizableLCA.preservesCokernelOf_isClosedEmbedding
#check MetrizableLCA.surjective_of_cokernelSubgroup_eq_top_of_isOpenMap
#check MetrizableLCA.surjective_iff_cokernelSubgroup_eq_top_of_isOpenMap
#check MetrizableLCA.CokernelTopStrictInput
#check MetrizableLCA.strictShortExact_of_cokernelTopStrictInput
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
#check MetrizableLCA.cokernelπ_eq_zero_iff_cokernelSubgroup_eq_top
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero
#check MetrizableLCA.cokernelπ_eq_zero_of_epi
#check MetrizableLCA.strictShortExact_of_kernel_open_closed_epi

noncomputable example (A B : MetrizableLCA) :
    MetrizableLCA.biprodObj A B ≅ A ⊞ B :=
  MetrizableLCA.biprodObjIsoBiprod A B

noncomputable example (A : MetrizableLCA) : A ⟶ A ⊞ A :=
  MetrizableLCA.biprodDiag A

noncomputable example (A : MetrizableLCA) : A ⊞ A ⟶ A :=
  MetrizableLCA.biprodCodiag A

noncomputable example (A : MetrizableLCA) :
    MetrizableLCA.biprodDiag A ≫ biprod.fst = 𝟙 A :=
  MetrizableLCA.biprodDiag_fst A

noncomputable example (A : MetrizableLCA) :
    biprod.inl ≫ MetrizableLCA.biprodCodiag A = 𝟙 A :=
  MetrizableLCA.biprodCodiag_inl A

noncomputable example {A B : MetrizableLCA} (f : A ⟶ B)
    (hbij : Function.Bijective (f : A → B)) (hopen : IsOpenMap (f : A → B)) : A ≃ₜ+ B :=
  MetrizableLCA.continuousAddEquivOfBijectiveOpenMap f hbij hopen

noncomputable example {A B : MetrizableLCA} (f : A ⟶ B)
    (hbij : Function.Bijective (f : A → B)) (hopen : IsOpenMap (f : A → B)) : A ≅ B :=
  MetrizableLCA.isoOfBijectiveOpenMap f hbij hopen

example {A B : MetrizableLCA} (f : A ⟶ B)
    (hbij : Function.Bijective (f : A → B)) (hopen : IsOpenMap (f : A → B)) : IsIso f :=
  MetrizableLCA.isIso_of_bijective_openMap f hbij hopen

example {A B C : MetrizableLCA} (q : A ⟶ B) (f : B ⟶ C)
    (hqs : Function.Surjective (q : A → B))
    (hcomp : IsOpenMap ((q ≫ f : A ⟶ C) : A → C)) : IsOpenMap (f : B → C) :=
  MetrizableLCA.isOpenMap_of_comp_surjective q f hqs hcomp

/--
Strict short exact sequences in the metrizable LCA model are stable under
coordinatewise binary biproducts.
-/
example {S T : ShortComplex MetrizableLCA}
    (hS : MetrizableLCA.strictShortExact S) (hT : MetrizableLCA.strictShortExact T) :
    MetrizableLCA.strictShortExact (MetrizableLCA.strictShortExactBiprodComplex S T) :=
  MetrizableLCA.strictShortExact_biprod hS hT

noncomputable example (K L : CochainComplex MetrizableLCA ℤ) (i : ℤ) :
    MetrizableLCA.strictShortExactBiprodComplex (K.sc i) (L.sc i) ≅ (K ⊞ L).sc i :=
  MetrizableLCA.exactAcyclicBiprodTransportIso K L i

example (K L : CochainComplex MetrizableLCA ℤ)
    (hK : exactAcyclic MetrizableLCA K) (hL : exactAcyclic MetrizableLCA L) :
    exactAcyclic MetrizableLCA (K ⊞ L) :=
  MetrizableLCA.exactAcyclic_biprod K L hK hL

/- WPP-op exact-acyclic frontier support is root-importable, but still conditional. -/
namespace WppOpExactAcyclicFrontierConsolidatedW318

#check exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure

end WppOpExactAcyclicFrontierConsolidatedW318

namespace AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475

#check W426PromotionFieldsProviderW475
#check W426OrdinaryMapProviderW475
#check W426OrdinaryEqualsCanonicalProviderW475
#check ProjectionFieldsProviderW475
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w475
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_projectionFields_w475
#check currentW426LeftClosedProjectionFieldsExactAcyclicV370SupportStateW475_productSuccess

end AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475

namespace AddCommGrpW426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportW477

#check ComponentwiseClosedRangeProjectionProviderW477
#check projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w477
#check exactAcyclic_of_w426Promotion_and_componentwiseClosedRangeProjection_w477
#check currentW426LeftClosedComponentwiseClosedRangeProjectionStateW477_productSuccess

end AddCommGrpW426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportW477

/-
Exact-category Ext is defined directly from the local conflation interface and
positive degrees are quotient groups of formal Yoneda chains by local relation
generators.
-/
#check (fun (X Y : MetrizableLCA) => YonedaExt (C := MetrizableLCA) X Y 1)
#check (fun (X Y : MetrizableLCA) => PositiveYonedaExtFree (C := MetrizableLCA) X Y 0)
#check (fun (X Y : MetrizableLCA) => yonedaRelationSubgroup (C := MetrizableLCA) X Y 0)
#check (fun (X Y : MetrizableLCA) => YonedaRelGenerator (C := MetrizableLCA) X Y)
#check (YonedaRelGenerator.homTailLeft (C := MetrizableLCA))
#check (fun (X Y : MetrizableLCA) =>
  ShortExactExtension.BaerSumData (C := MetrizableLCA) (X := X) (Y := Y))
#check (ShortExactExtension.BaerSumData.isoSum (C := MetrizableLCA))
#check (ShortExactExtension.PullbackData.isPullback (C := MetrizableLCA))
#check (ShortExactExtension.PullbackData.isoOut (C := MetrizableLCA))
#check (ShortExactExtension.PushoutData.isPushout (C := MetrizableLCA))
#check (ShortExactExtension.PushoutData.iso (C := MetrizableLCA))
#check (ShortExactExtension.PushoutData.isoOut (C := MetrizableLCA))

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    ShortExactExtension (C := MetrizableLCA)
      (MetrizableLCA.biprodObj X₁ X₂) (MetrizableLCA.biprodObj Y₁ Y₂) :=
  MetrizableLCA.shortExactExtensionBiprod e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    (MetrizableLCA.shortExactExtensionBiprod e₁ e₂).i ≫
        MetrizableLCA.biprodFst e₁.middle e₂.middle =
      MetrizableLCA.biprodFst Y₁ Y₂ ≫ e₁.i :=
  MetrizableLCA.shortExactExtensionBiprod_i_fst e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    (MetrizableLCA.shortExactExtensionBiprod e₁ e₂).i ≫
        MetrizableLCA.biprodSnd e₁.middle e₂.middle =
      MetrizableLCA.biprodSnd Y₁ Y₂ ≫ e₂.i :=
  MetrizableLCA.shortExactExtensionBiprod_i_snd e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    MetrizableLCA.biprodFst e₁.middle e₂.middle ≫ e₁.p =
      (MetrizableLCA.shortExactExtensionBiprod e₁ e₂).p ≫
        MetrizableLCA.biprodFst X₁ X₂ :=
  MetrizableLCA.shortExactExtensionBiprod_p_fst e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    MetrizableLCA.biprodSnd e₁.middle e₂.middle ≫ e₂.p =
      (MetrizableLCA.shortExactExtensionBiprod e₁ e₂).p ≫
        MetrizableLCA.biprodSnd X₁ X₂ :=
  MetrizableLCA.shortExactExtensionBiprod_p_snd e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    ShortExactExtension (C := MetrizableLCA) (X₁ ⊞ X₂) (Y₁ ⊞ Y₂) :=
  MetrizableLCA.shortExactExtensionBinaryBiproduct e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    (MetrizableLCA.shortExactExtensionBinaryBiproduct e₁ e₂).i ≫
        MetrizableLCA.biprodFst e₁.middle e₂.middle =
      biprod.fst ≫ e₁.i :=
  MetrizableLCA.shortExactExtensionBinaryBiproduct_i_fst e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    (MetrizableLCA.shortExactExtensionBinaryBiproduct e₁ e₂).i ≫
        MetrizableLCA.biprodSnd e₁.middle e₂.middle =
      biprod.snd ≫ e₂.i :=
  MetrizableLCA.shortExactExtensionBinaryBiproduct_i_snd e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    MetrizableLCA.biprodFst e₁.middle e₂.middle ≫ e₁.p =
      (MetrizableLCA.shortExactExtensionBinaryBiproduct e₁ e₂).p ≫ biprod.fst :=
  MetrizableLCA.shortExactExtensionBinaryBiproduct_p_fst e₁ e₂

noncomputable example (X₁ Y₁ X₂ Y₂ : MetrizableLCA)
    (e₁ : ShortExactExtension (C := MetrizableLCA) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA) X₂ Y₂) :
    MetrizableLCA.biprodSnd e₁.middle e₂.middle ≫ e₂.p =
      (MetrizableLCA.shortExactExtensionBinaryBiproduct e₁ e₂).p ≫ biprod.snd :=
  MetrizableLCA.shortExactExtensionBinaryBiproduct_p_snd e₁ e₂

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    ShortExactExtension (C := MetrizableLCA) X' Y :=
  MetrizableLCA.shortExactExtensionPullback e a

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    (MetrizableLCA.shortExactExtensionPullback e a).i ≫
        MetrizableLCA.pullbackSnd a e.p = e.i :=
  MetrizableLCA.shortExactExtensionPullback_i_map e a

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    MetrizableLCA.pullbackSnd a e.p ≫ e.p =
      (MetrizableLCA.shortExactExtensionPullback e a).p ≫ a :=
  MetrizableLCA.shortExactExtensionPullback_map_p e a

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    ShortExactExtension.PullbackData e a (MetrizableLCA.shortExactExtensionPullback e a) :=
  MetrizableLCA.shortExactExtensionPullbackData e a

noncomputable example (X Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) :
    ShortExactExtension.PullbackData e (𝟙 X) e :=
  MetrizableLCA.shortExactExtensionPullbackIdData e

noncomputable example (X Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) :
    ShortExactExtension.Iso
      (MetrizableLCA.shortExactExtensionPullback e (𝟙 X)) e :=
  MetrizableLCA.shortExactExtensionPullbackIdIso e

noncomputable example (X X' Y : MetrizableLCA)
    {e e' : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.Iso e e') (a : X' ⟶ X) :
    ShortExactExtension.Iso
      (MetrizableLCA.shortExactExtensionPullback e a)
      (MetrizableLCA.shortExactExtensionPullback e' a) :=
  MetrizableLCA.shortExactExtensionPullbackIso a h

noncomputable example (X X' Y Y' : MetrizableLCA) (β : Y ≅ Y')
    {e : ShortExactExtension (C := MetrizableLCA) X Y}
    {e' : ShortExactExtension (C := MetrizableLCA) X Y'}
    (h : ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X) β e e')
    (a : X' ⟶ X) :
    ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X') β
      (MetrizableLCA.shortExactExtensionPullback e a)
      (MetrizableLCA.shortExactExtensionPullback e' a) :=
  MetrizableLCA.shortExactExtensionPullbackIsoBetween a h

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X)
    (s : e.shortComplex.Splitting) :
    (MetrizableLCA.shortExactExtensionPullback e a).shortComplex.Splitting :=
  MetrizableLCA.shortExactExtensionPullbackSplitting e a s

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X)
    (s : e.shortComplex.Splitting) :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.shortExactExtensionPullback e a).toYonedaExtension =
      (0 : YonedaExt (C := MetrizableLCA) X' Y 1) :=
  YonedaExt.ofExtension_eq_zero_of_split
    (MetrizableLCA.shortExactExtensionPullback e a)
    (MetrizableLCA.shortExactExtensionPullbackSplitting e a s)

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X)
    (s : e.shortComplex.Splitting) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a)
        e.toYonedaExtension =
      (0 : YonedaExt (C := MetrizableLCA) X' Y 1) :=
  YonedaExt.pullbackHeadOfExtension_eq_zero_of_metrizable_split e s a

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData e) (a : X' ⟶ X) :
    YonedaExtension.RightSplitData (MetrizableLCA.yonedaExtensionPullbackHead a e) :=
  MetrizableLCA.yonedaExtensionPullbackHeadRightSplitData a h

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData e) (a : X' ⟶ X) :
    YonedaExtension.SplitFactorData (MetrizableLCA.yonedaExtensionPullbackHead a e) :=
  MetrizableLCA.yonedaExtensionPullbackHeadSplitFactorData a h

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData e) (a : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a) e =
      (0 : YonedaExt (C := MetrizableLCA) X' Y (n + 1)) :=
  YonedaExt.pullbackHeadOfExtension_eq_zero_of_metrizable_rightSplitData h a

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData e) (a : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a) e =
      (0 : YonedaExt (C := MetrizableLCA) X' Y (n + 1)) :=
  YonedaExt.pullbackHeadOfExtension_eq_zero_of_metrizable_splitFactorData h a

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    YonedaExtension.HomHeadData a e.toYonedaExtension
      (MetrizableLCA.shortExactExtensionPullback e a).toYonedaExtension :=
  YonedaExtension.HomHeadData.cons e (MetrizableLCA.shortExactExtensionPullbackData e a)
    (YonedaExtension.ofHom (𝟙 Y))

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    MetrizableLCA.yonedaExtensionPullbackHead a e.toYonedaExtension =
      (MetrizableLCA.shortExactExtensionPullback e a).toYonedaExtension :=
  rfl

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e e' : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.Rel e e') (a : X' ⟶ X) :
    YonedaExtension.Rel
      (MetrizableLCA.yonedaExtensionPullbackHead a e)
      (MetrizableLCA.yonedaExtensionPullbackHead a e') :=
  MetrizableLCA.yonedaExtensionPullbackHeadRel a h

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e e' : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.Rel e e') (a : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a) e =
      YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a) e' :=
  YonedaExt.pullbackHeadOfExtension_eq_of_metrizable_rel h a

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e e' : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) e e') (a : X' ⟶ X) :
    YonedaExtension.RelIso (CategoryTheory.Iso.refl X')
      (MetrizableLCA.yonedaExtensionPullbackHead a e)
      (MetrizableLCA.yonedaExtensionPullbackHead a e') :=
  MetrizableLCA.yonedaExtensionPullbackHeadRelIso a h

noncomputable example (X X' Y : MetrizableLCA) {n : ℕ}
    {e e' : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) e e') (a : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a) e =
      YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a) e' :=
  YonedaExt.pullbackHeadOfExtension_eq_of_metrizable_relIso h a

noncomputable example (X Y : MetrizableLCA) {n : ℕ}
    (e : YonedaExtension (C := MetrizableLCA) X Y (n + 1)) :
    YonedaExtension.Rel
      (YonedaExtension.pullbackHeadWith (C := MetrizableLCA) (𝟙 X)
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e (𝟙 X)) e)
      e :=
  MetrizableLCA.yonedaExtensionPullbackHeadIdRel e

noncomputable example (X Y : MetrizableLCA) {n : ℕ}
    (e : YonedaExtension (C := MetrizableLCA) X Y (n + 1)) :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.pullbackHeadWith (C := MetrizableLCA) (𝟙 X)
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e (𝟙 X)) e) =
      YonedaExt.ofExtension (C := MetrizableLCA) e :=
  YonedaExt.ofExtension_pullbackHeadId_eq e

noncomputable example (X Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) :
    YonedaExt.ofExtension
        (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)).toYonedaExtension =
      YonedaExt.ofExtension e.toYonedaExtension :=
  YonedaExt.ofExtension_pushoutTailId_eq e

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) :
    YonedaExt.ofExtension
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)) f).toYonedaExtension =
      YonedaExt.ofExtension (MetrizableLCA.shortExactExtensionPullback e f).toYonedaExtension :=
  YonedaExt.ofExtension_pullbackPushoutTailId_eq e f

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a)
        e.toYonedaExtension =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.shortExactExtensionPullback e a).toYonedaExtension :=
  rfl

example (X X' Y : MetrizableLCA) {n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) n
        (FreeAbelianGroup.of a) =
      FreeAbelianGroup.of
        (YonedaExtension.pullbackHeadWith f
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a) :=
  YonedaExt.pullbackHeadFreeHomWith_of f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a

example (X X' Y : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.Rel a b) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y n :=
  YonedaExt.pullbackHeadFreeHomWith_rel_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_} {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    h

example (X X' Y : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y n :=
  YonedaExt.pullbackHeadFreeHomWith_relIso_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_ _} {_} {_ _} h => MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    h

example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (s : e.shortComplex.Splitting) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) 0
        (FreeAbelianGroup.of e.toYonedaExtension) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y 0 :=
  YonedaExt.pullbackHeadFreeHomWith_split_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_} e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    e s

example (X X' Y Z : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Z)
    (g : ShortExactExtension (C := MetrizableLCA) Z Y)
    (s : g.shortComplex.Splitting) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) 1
        (FreeAbelianGroup.of (YonedaExtension.cons e g.toYonedaExtension)) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y 1 :=
  YonedaExt.pullbackHeadFreeHomWith_leftSplit_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    e g s

example (X X' Y : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) n
        (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y n :=
  YonedaExt.pullbackHeadFreeHomWith_rightSplit_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_} e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    h

example (X X' Y : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) n
        (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y n :=
  YonedaExt.pullbackHeadFreeHomWith_splitFactor_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_} e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    h

example (X X' Y : MetrizableLCA)
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) (f : X' ⟶ X)
    (pullBaer : ShortExactExtension.BaerSumData
      (MetrizableLCA.shortExactExtensionPullback e₁ f)
      (MetrizableLCA.shortExactExtensionPullback e₂ f)
      (MetrizableLCA.shortExactExtensionPullback sum f)) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) 0
        (FreeAbelianGroup.of sum.toYonedaExtension -
          FreeAbelianGroup.of e₁.toYonedaExtension -
          FreeAbelianGroup.of e₂.toYonedaExtension) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y 0 :=
  YonedaExt.pullbackHeadFreeHomWith_baer_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    h pullBaer

example (X X' Y Z : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Z) (g : Z ⟶ Y)
    {out : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.PushoutData e g out) (f : X' ⟶ X)
    (pullPushoutData : ShortExactExtension.PushoutData
      (MetrizableLCA.shortExactExtensionPullback e f) g
      (MetrizableLCA.shortExactExtensionPullback out f)) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) 0
        (FreeAbelianGroup.of (YonedaExtension.cons e (YonedaExtension.ofHom g)) -
          FreeAbelianGroup.of out.toYonedaExtension) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y 0 :=
  YonedaExt.pullbackHeadFreeHomWith_homTail_one_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    e g h pullPushoutData

example (X X' Y Z : MetrizableLCA) {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA) X Z)
    {a b sum : YonedaExtension (C := MetrizableLCA) Z Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) (n + 1)
        (FreeAbelianGroup.of (YonedaExtension.cons e sum) -
          FreeAbelianGroup.of (YonedaExtension.cons e a) -
          FreeAbelianGroup.of (YonedaExtension.cons e b)) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y (n + 1) :=
  YonedaExt.pullbackHeadFreeHomWith_baerChain_cons_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    e h

example (X X' Y Z : MetrizableLCA) {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA) X Z)
    {tail tail' : YonedaExtension (C := MetrizableLCA) Z Y (n + 1)}
    (h : YonedaExtension.HomTailData tail tail') (f : X' ⟶ X) :
    YonedaExt.pullbackHeadFreeHomWith (C := MetrizableLCA) (X := X) (Y := Y) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) (n + 1)
        (FreeAbelianGroup.of (YonedaExtension.cons e tail) -
          FreeAbelianGroup.of (YonedaExtension.cons e tail')) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X' Y (n + 1) :=
  YonedaExt.pullbackHeadFreeHomWith_homTail_cons_mem f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    e h

#check (YonedaExt.pullbackHeadFreeHomWith_baerChain_mem (C := MetrizableLCA))
#check (YonedaExt.pullbackHeadFreeHomWith_homTail_mem (C := MetrizableLCA))
#check (YonedaExtension.HomTailData.pullbackHeadWith (C := MetrizableLCA))
#check (YonedaExtension.pullbackHeadWith_spliceLeftWith (C := MetrizableLCA))
#check (YonedaExtension.composeTailHom_pullbackHeadWith (C := MetrizableLCA))
#check (YonedaExtension.composeTailHom_spliceLeftWith (C := MetrizableLCA))
#check (YonedaExt.ofExtension_eq_ofExtension_of_homTailLeftWith (C := MetrizableLCA))
#check MetrizableLCA.shortExactExtensionPullbackBaerSumData
#check MetrizableLCA.shortExactExtensionPushoutIso
#check MetrizableLCA.shortExactExtensionPushoutAssocIso
#check MetrizableLCA.shortExactExtensionPushoutBaerSumData
#check (YonedaExt.composeTailHomFreeHom_homTail_mem_metrizable)
#check (YonedaExt.pullbackHead_relationSubgroup_le (C := MetrizableLCA))
#check (YonedaExt.pullbackHeadMapWith (C := MetrizableLCA))
#check (YonedaExt.pullbackHeadMapWith_ofExtension (C := MetrizableLCA))
#check YonedaExt.pullbackHead_relationSubgroup_le_metrizableWithPushoutData
#check YonedaExt.pullbackHeadMap_metrizableWithPushoutData
#check YonedaExt.pullbackHeadMap_metrizableWithPushoutData_ofExtension
#check YonedaExt.pullbackHead_relationSubgroup_le_metrizable
#check YonedaExt.pullbackHeadMap_metrizable
#check YonedaExt.pullbackHeadMap_metrizable_ofExtension
#check (YonedaExt.composeTailHom_relationSubgroup_le (C := MetrizableLCA))
#check (YonedaExt.composeTailHomMapWith (C := MetrizableLCA))
#check (YonedaExt.composeTailHomMapWith_ofExtension (C := MetrizableLCA))
#check YonedaExt.composeTailHom_relationSubgroup_le_metrizable
#check YonedaExt.composeTailHomMap_metrizable
#check YonedaExt.composeTailHomMap_metrizable_ofExtension
#check YonedaExtension.spliceLeftWith
#check (YonedaExt.leftProductByYonedaExtensionFreeHomWith (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionFreeHomWith_of (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtension_relationSubgroup_leWith (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_ofExtension (C := MetrizableLCA))
#check (YonedaExtension.Rel.spliceLeftWith (C := MetrizableLCA))
#check (YonedaExtension.SplitFactorData.spliceLeftWith (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_ofExtension_eq_of_rel
  (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_eq_of_rel (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_ofExtension_eq_zero_of_splitFactor
  (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_eq_zero_of_splitFactor
  (C := MetrizableLCA))
#check (YonedaExtension.BaerSumData.spliceLeftWith (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_ofExtension_eq_add_of_baerLeftChain
  (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_eq_add_of_baerLeftChain
  (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_ofExtension_eq_of_homTailLeftChain
  (C := MetrizableLCA))
#check (YonedaExt.leftProductByYonedaExtensionWith_eq_of_homTailLeftChain
  (C := MetrizableLCA))
#check YonedaExt.leftProductByYonedaExtension_metrizableWithPushoutData
#check YonedaExt.leftProductByYonedaExtension_metrizableWithPushoutData_ofExtension
#check YonedaExt.leftProductByYonedaExtension_metrizableWithPushoutData_eq_of_rel
#check YonedaExt.leftProductByYonedaExtension_metrizableWithPushoutData_eq_zero_of_splitFactor
#check YonedaExt.leftProductByYonedaExtension_metrizableWithPushoutData_eq_add_of_baerLeftChain
#check YonedaExt.leftProductByYonedaExtension_metrizableWithPushoutData_eq_of_homTailLeftChain
#check YonedaExt.leftProductByYonedaExtension_metrizable
#check YonedaExt.leftProductByYonedaExtension_metrizable_ofExtension
#check YonedaExt.leftProductByYonedaExtension_metrizable_eq_of_rel
#check YonedaExt.leftProductByYonedaExtension_metrizable_eq_zero_of_splitFactor
#check YonedaExt.leftProductByYonedaExtension_metrizable_eq_add_of_baerLeftChain
#check YonedaExt.leftProductByYonedaExtension_metrizable_eq_of_homTailLeftChain

noncomputable example {X Y Z : MetrizableLCA} {m n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (m + 1)}
    (h : YonedaExtension.HomTailData (C := MetrizableLCA) a b) :
    YonedaExt.leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) a n =
      YonedaExt.leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) b n :=
  YonedaExt.leftProductByYonedaExtension_metrizable_eq_of_homTailLeftChain h n

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y') :
    ShortExactExtension (C := MetrizableLCA) X Y' :=
  MetrizableLCA.shortExactExtensionPushout e a

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y') :
    a ≫ (MetrizableLCA.shortExactExtensionPushout e a).i =
      e.i ≫ MetrizableLCA.pushoutInl
        (S := e.shortComplex) a (MetrizableLCA.pushoutSubgroup_closed e.conflation a) :=
  MetrizableLCA.shortExactExtensionPushout_i e a

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y') :
    MetrizableLCA.pushoutInl
        (S := e.shortComplex) a (MetrizableLCA.pushoutSubgroup_closed e.conflation a) ≫
      (MetrizableLCA.shortExactExtensionPushout e a).p = e.p :=
  MetrizableLCA.shortExactExtensionPushout_map_p e a

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y') :
    ShortExactExtension.PushoutData e a (MetrizableLCA.shortExactExtensionPushout e a) :=
  MetrizableLCA.shortExactExtensionPushoutData e a

noncomputable example (X Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) :
    ShortExactExtension.PushoutData e (𝟙 Y) e :=
  MetrizableLCA.shortExactExtensionPushoutIdData e

noncomputable example (X Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) :
    ShortExactExtension.Iso (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)) e :=
  MetrizableLCA.shortExactExtensionPushoutIdIso e

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) :
    ShortExactExtension.Iso
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)) f)
      (MetrizableLCA.shortExactExtensionPullback e f) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutIdIso e f

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) :
    ShortExactExtension.PushoutData
      (MetrizableLCA.shortExactExtensionPullback e f) (𝟙 Y)
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)) f) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutIdData e f

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    (MetrizableLCA.shortExactExtensionPullback e f).middle ⟶
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e g) f).middle :=
  MetrizableLCA.shortExactExtensionPullbackPushoutMiddleMap e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    MetrizableLCA.shortExactExtensionPullbackPushoutMiddleMap e f g ≫
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e g) f).p =
      (MetrizableLCA.shortExactExtensionPullback e f).p :=
  MetrizableLCA.shortExactExtensionPullbackPushoutMiddleMap_p e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    g ≫ (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e g) f).i =
      (MetrizableLCA.shortExactExtensionPullback e f).i ≫
        MetrizableLCA.shortExactExtensionPullbackPushoutMiddleMap e f g :=
  MetrizableLCA.shortExactExtensionPullbackPushoutMiddleMap_i e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    (MetrizableLCA.shortExactExtensionPushout
        (MetrizableLCA.shortExactExtensionPullback e f) g).middle ⟶
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e g) f).middle :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    (MetrizableLCA.shortExactExtensionPushout
        (MetrizableLCA.shortExactExtensionPullback e f) g).i ≫
        MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g =
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e g) f).i :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap_i e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g ≫
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e g) f).p =
      (MetrizableLCA.shortExactExtensionPushout
        (MetrizableLCA.shortExactExtensionPullback e f) g).p :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap_p e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    Function.Surjective
      (MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g :
        (MetrizableLCA.shortExactExtensionPushout
          (MetrizableLCA.shortExactExtensionPullback e f) g).middle →
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e g) f).middle) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap_surjective e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    Function.Injective
      (MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g :
        (MetrizableLCA.shortExactExtensionPushout
          (MetrizableLCA.shortExactExtensionPullback e f) g).middle →
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e g) f).middle) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap_injective e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    Function.Bijective
      (MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g :
        (MetrizableLCA.shortExactExtensionPushout
          (MetrizableLCA.shortExactExtensionPullback e f) g).middle →
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e g) f).middle) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap_bijective e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    IsOpenMap
      (MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g :
        (MetrizableLCA.shortExactExtensionPushout
          (MetrizableLCA.shortExactExtensionPullback e f) g).middle →
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e g) f).middle) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap_openMap e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    IsIso (MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap_isIso e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y')
    [IsIso (MetrizableLCA.shortExactExtensionPullbackPushoutComparisonMap e f g)] :
    ShortExactExtension.PushoutData
      (MetrizableLCA.shortExactExtensionPullback e f) g
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e g) f) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutDataOfIsIsoComparison e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    ShortExactExtension.PushoutData
      (MetrizableLCA.shortExactExtensionPullback e f) g
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e g) f) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutData e f g

noncomputable example (X X' Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) (g : Y ⟶ Y')
    {out : ShortExactExtension (C := MetrizableLCA) X Y'}
    (h : ShortExactExtension.PushoutData e g out) :
    ShortExactExtension.PushoutData
      (MetrizableLCA.shortExactExtensionPullback e f) g
      (MetrizableLCA.shortExactExtensionPullback out f) :=
  MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h

noncomputable example (X Y Y' : MetrizableLCA)
    {e e' : ShortExactExtension (C := MetrizableLCA) X Y}
    (a : Y ⟶ Y') (h : ShortExactExtension.Iso e e') :
    ShortExactExtension.Iso
      (MetrizableLCA.shortExactExtensionPushout e a)
      (MetrizableLCA.shortExactExtensionPushout e' a) :=
  MetrizableLCA.shortExactExtensionPushoutIso a h

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y') :
    YonedaExtension.HomTailData
      (YonedaExtension.cons e (YonedaExtension.ofHom a))
      (MetrizableLCA.shortExactExtensionPushout e a).toYonedaExtension :=
  YonedaExtension.HomTailData.one e a (MetrizableLCA.shortExactExtensionPushoutData e a)

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y')
    (s : e.shortComplex.Splitting) :
    (MetrizableLCA.shortExactExtensionPushout e a).shortComplex.Splitting :=
  MetrizableLCA.shortExactExtensionPushoutSplitting e a s

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y')
    (s : e.shortComplex.Splitting) :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.shortExactExtensionPushout e a).toYonedaExtension =
      (0 : YonedaExt (C := MetrizableLCA) X Y' 1) :=
  YonedaExt.ofExtension_eq_zero_of_split
    (MetrizableLCA.shortExactExtensionPushout e a)
    (MetrizableLCA.shortExactExtensionPushoutSplitting e a s)

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y')
    (s : e.shortComplex.Splitting) :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom a e.toYonedaExtension) =
      (0 : YonedaExt (C := MetrizableLCA) X Y' 1) :=
  YonedaExt.ofExtension_composeTailHom_eq_zero_of_metrizable_split e s a

noncomputable example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.cons e (YonedaExtension.ofHom a)) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.shortExactExtensionPushout e a).toYonedaExtension :=
  YonedaExt.ofExtension_cons_ofHom_eq_of_pushoutData e a
    (MetrizableLCA.shortExactExtensionPushoutData e a)

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)) (f : Y ⟶ Y') :
    YonedaExtension.HomTailData
      (YonedaExtension.composeTailHom f a)
      (MetrizableLCA.yonedaExtensionPushoutTail f a) :=
  MetrizableLCA.yonedaExtensionPushoutTailData f a

noncomputable example (X Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) :
    YonedaExtension.Rel
      (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)).toYonedaExtension
      e.toYonedaExtension :=
  MetrizableLCA.yonedaExtensionPushoutTailIdRel e

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (f : X' ⟶ X) :
    YonedaExtension.Rel
      (MetrizableLCA.shortExactExtensionPullback
        (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)) f).toYonedaExtension
      (MetrizableLCA.shortExactExtensionPullback e f).toYonedaExtension :=
  MetrizableLCA.yonedaExtensionPullbackPushoutTailIdRel e f

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : Y ⟶ Y') :
    YonedaExtension.RightSplitData (MetrizableLCA.yonedaExtensionPushoutTail f a) :=
  MetrizableLCA.yonedaExtensionPushoutTailRightSplitData f h

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : Y ⟶ Y') :
    YonedaExtension.SplitFactorData (MetrizableLCA.yonedaExtensionPushoutTail f a) :=
  MetrizableLCA.yonedaExtensionPushoutTailSplitFactorData f h

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.yonedaExtensionPushoutTail f a) =
      (0 : YonedaExt (C := MetrizableLCA) X Y' (n + 1)) :=
  YonedaExt.ofExtension_pushoutTailWith_eq_zero_of_metrizable_rightSplitData h f

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.yonedaExtensionPushoutTail f a) =
      (0 : YonedaExt (C := MetrizableLCA) X Y' (n + 1)) :=
  YonedaExt.ofExtension_pushoutTailWith_eq_zero_of_metrizable_splitFactorData h f

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom f a) =
      (0 : YonedaExt (C := MetrizableLCA) X Y' (n + 1)) :=
  YonedaExt.ofExtension_composeTailHom_eq_zero_of_metrizable_rightSplitData h f

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom f a) =
      (0 : YonedaExt (C := MetrizableLCA) X Y' (n + 1)) :=
  YonedaExt.ofExtension_composeTailHom_eq_zero_of_metrizable_splitFactorData h f

noncomputable example (X Y Y' : MetrizableLCA) {n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom f a) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.yonedaExtensionPushoutTail f a) :=
  YonedaExt.ofExtension_composeTailHom_eq_pushoutTailWith f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    a

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.Rel a b) (f : Y ⟶ Y') :
    YonedaExtension.Rel
      (YonedaExtension.composeTailHom f a)
      (YonedaExtension.composeTailHom f b) :=
  YonedaExtension.Rel.composeTailHom f h

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.Rel a b) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom f a) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom f b) :=
  YonedaExt.ofExtension_composeTailHom_eq_of_rel f h

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) (f : Y ⟶ Y') :
    YonedaExtension.RelIso (CategoryTheory.Iso.refl X)
      (YonedaExtension.composeTailHom f a)
      (YonedaExtension.composeTailHom f b) :=
  YonedaExtension.RelIso.composeTailHom f h

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom f a) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.composeTailHom f b) :=
  YonedaExt.ofExtension_composeTailHom_eq_of_relIso f h

example (X Y Y' : MetrizableLCA) {n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f n
        (FreeAbelianGroup.of a) =
      FreeAbelianGroup.of (YonedaExtension.composeTailHom f a) :=
  YonedaExt.composeTailHomFreeHom_of f a

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.Rel a b) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' n :=
  YonedaExt.composeTailHomFreeHom_rel_mem f h

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' n :=
  YonedaExt.composeTailHomFreeHom_relIso_mem f h

example (X Y Y' : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (s : e.shortComplex.Splitting) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f 0
        (FreeAbelianGroup.of e.toYonedaExtension) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' 0 :=
  YonedaExt.composeTailHomFreeHom_split_mem f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    (fun {_ _} e g s => MetrizableLCA.shortExactExtensionPushoutSplitting e g s)
    e s

example (X Y Y' Z : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Z)
    (g : ShortExactExtension (C := MetrizableLCA) Z Y)
    (s : g.shortComplex.Splitting) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f 1
        (FreeAbelianGroup.of (YonedaExtension.cons e g.toYonedaExtension)) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' 1 :=
  YonedaExt.composeTailHomFreeHom_leftSplit_mem f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    (fun {_ _} e g s => MetrizableLCA.shortExactExtensionPushoutSplitting e g s)
    e g s

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f n
        (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' n :=
  YonedaExt.composeTailHomFreeHom_rightSplit_mem f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    (fun {_ _} e g s => MetrizableLCA.shortExactExtensionPushoutSplitting e g s)
    h

example (X Y Y' : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f n
        (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' n :=
  YonedaExt.composeTailHomFreeHom_splitFactor_mem f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    (fun {_ _} e g s => MetrizableLCA.shortExactExtensionPushoutSplitting e g s)
    h

example (X Y Y' : MetrizableLCA)
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) (f : Y ⟶ Y')
    (pushBaer : ShortExactExtension.BaerSumData
      (MetrizableLCA.shortExactExtensionPushout e₁ f)
      (MetrizableLCA.shortExactExtensionPushout e₂ f)
      (MetrizableLCA.shortExactExtensionPushout sum f)) :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f 0
        (FreeAbelianGroup.of sum.toYonedaExtension -
          FreeAbelianGroup.of e₁.toYonedaExtension -
          FreeAbelianGroup.of e₂.toYonedaExtension) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' 0 :=
  YonedaExt.composeTailHomFreeHom_baer_mem f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    h pushBaer

example (X Y Y' Z : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Z) (g : Z ⟶ Y)
    {out : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.PushoutData e g out) (f : Y ⟶ Y')
    (pushAssocIso : ShortExactExtension.Iso
      (MetrizableLCA.shortExactExtensionPushout e (g ≫ f))
      (MetrizableLCA.shortExactExtensionPushout out f)) :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f 0
        (FreeAbelianGroup.of (YonedaExtension.cons e (YonedaExtension.ofHom g)) -
          FreeAbelianGroup.of out.toYonedaExtension) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' 0 :=
  YonedaExt.composeTailHomFreeHom_homTail_one_mem f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    e g h pushAssocIso

example (X Y Y' Z : MetrizableLCA) {n : ℕ}
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Z}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (tail : YonedaExtension (C := MetrizableLCA) Z Y (n + 1)) (f : Y ⟶ Y') :
    YonedaExt.composeTailHomFreeHom (C := MetrizableLCA) (X := X) f (n + 1)
        (FreeAbelianGroup.of (YonedaExtension.cons sum tail) -
          FreeAbelianGroup.of (YonedaExtension.cons e₁ tail) -
          FreeAbelianGroup.of (YonedaExtension.cons e₂ tail)) ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y' (n + 1) :=
  YonedaExt.composeTailHomFreeHom_baerChain_head_mem f h tail

#check (YonedaExt.composeTailHomFreeHom_baerChain_mem (C := MetrizableLCA))
#check (YonedaExt.composeTailHomFreeHom_homTail_mem (C := MetrizableLCA))

noncomputable example (X Y : MetrizableLCA)
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA) X Y) :
    ShortExactExtension (C := MetrizableLCA) X Y :=
  MetrizableLCA.shortExactExtensionBaerSum e₁ e₂

noncomputable example (X Y : MetrizableLCA)
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA) X Y) :
    ShortExactExtension.BaerSumData e₁ e₂
      (MetrizableLCA.shortExactExtensionBaerSum e₁ e₂) :=
  MetrizableLCA.shortExactExtensionBaerSumData e₁ e₂

noncomputable example (X Y : MetrizableLCA)
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA) X Y) :
    YonedaExt.baer_sum
        (YonedaExt.ofExtension (C := MetrizableLCA) e₁.toYonedaExtension)
        (YonedaExt.ofExtension (C := MetrizableLCA) e₂.toYonedaExtension) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.shortExactExtensionBaerSum e₁ e₂).toYonedaExtension :=
  YonedaExt.baer_sum_ofExtension_eq_of_baer
    (MetrizableLCA.shortExactExtensionBaerSumData e₁ e₂)

noncomputable example (X Y Z : MetrizableLCA) {n : ℕ}
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA) X Y)
    (tail : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExtension.BaerSumData
      (YonedaExtension.cons e₁ tail)
      (YonedaExtension.cons e₂ tail)
      (YonedaExtension.cons (MetrizableLCA.shortExactExtensionBaerSum e₁ e₂) tail) :=
  YonedaExtension.BaerSumData.head
    (MetrizableLCA.shortExactExtensionBaerSumData e₁ e₂) tail

noncomputable example (X Y Z : MetrizableLCA) {n : ℕ}
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA) X Y)
    (tail : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.cons (MetrizableLCA.shortExactExtensionBaerSum e₁ e₂) tail) =
      YonedaExt.ofExtension (C := MetrizableLCA) (YonedaExtension.cons e₁ tail) +
        YonedaExt.ofExtension (C := MetrizableLCA) (YonedaExtension.cons e₂ tail) :=
  YonedaExt.ofExtension_eq_add_of_baerHead
    (MetrizableLCA.shortExactExtensionBaerSumData e₁ e₂) tail

noncomputable example (X Y Z : MetrizableLCA) {n : ℕ}
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA) X Y)
    (tail : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.baer_sum
        (YonedaExt.ofExtension (C := MetrizableLCA) (YonedaExtension.cons e₁ tail))
        (YonedaExt.ofExtension (C := MetrizableLCA) (YonedaExtension.cons e₂ tail)) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.cons (MetrizableLCA.shortExactExtensionBaerSum e₁ e₂) tail) :=
  YonedaExt.baer_sum_ofExtension_eq_of_baerHead
    (MetrizableLCA.shortExactExtensionBaerSumData e₁ e₂) tail

example (X Y : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.Rel a b) :
    YonedaExt.ofExtension (C := MetrizableLCA) a =
      YonedaExt.ofExtension (C := MetrizableLCA) b :=
  YonedaExt.ofExtension_eq_ofExtension_of_rel h

example (X Y : MetrizableLCA) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) :
    YonedaExt.ofExtension (C := MetrizableLCA) a =
      YonedaExt.ofExtension (C := MetrizableLCA) b :=
  YonedaExt.ofExtension_eq_ofExtension_of_relIso h

example (X Y : MetrizableLCA) (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (s : e.shortComplex.Splitting) :
    YonedaExt.ofExtension (C := MetrizableLCA) e.toYonedaExtension =
      (0 : YonedaExt (C := MetrizableLCA) X Y 1) :=
  YonedaExt.ofExtension_eq_zero_of_split e s

example (X Y Z : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Z)
    (f : ShortExactExtension (C := MetrizableLCA) Z Y)
    (s : f.shortComplex.Splitting) :
    YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.cons e f.toYonedaExtension) =
      (0 : YonedaExt (C := MetrizableLCA) X Y 2) :=
  YonedaExt.ofExtension_cons_eq_zero_of_right_split e f s

example (X Y : MetrizableLCA) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) :
    YonedaExt.ofExtension (C := MetrizableLCA) a =
      (0 : YonedaExt (C := MetrizableLCA) X Y (n + 1)) :=
  YonedaExt.ofExtension_eq_zero_of_splitFactorData h

example (X Y : MetrizableLCA) {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
    YonedaExt.ofExtension (C := MetrizableLCA) sum.toYonedaExtension =
      YonedaExt.ofExtension (C := MetrizableLCA) e₁.toYonedaExtension +
        YonedaExt.ofExtension (C := MetrizableLCA) e₂.toYonedaExtension :=
  YonedaExt.ofExtension_eq_add_of_baer h

example (X Y : MetrizableLCA) {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
    YonedaExt.baer_sum
        (YonedaExt.ofExtension (C := MetrizableLCA) e₁.toYonedaExtension)
        (YonedaExt.ofExtension (C := MetrizableLCA) e₂.toYonedaExtension) =
      YonedaExt.ofExtension (C := MetrizableLCA) sum.toYonedaExtension :=
  YonedaExt.baer_sum_ofExtension_eq_of_baer h

example (X Y : MetrizableLCA) {n : ℕ}
    {a b sum : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y n) :
    YonedaExt.ofExtension (C := MetrizableLCA) sum =
      YonedaExt.ofExtension (C := MetrizableLCA) a +
        YonedaExt.ofExtension (C := MetrizableLCA) b :=
  YonedaExt.ofExtension_eq_add_of_relation_mem h

example (X Y : MetrizableLCA) {n : ℕ}
    {a b sum : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b ∈
      yonedaRelationSubgroup (C := MetrizableLCA) X Y n) :
    YonedaExt.baer_sum
        (YonedaExt.ofExtension (C := MetrizableLCA) a)
        (YonedaExt.ofExtension (C := MetrizableLCA) b) =
      YonedaExt.ofExtension (C := MetrizableLCA) sum :=
  YonedaExt.baer_sum_ofExtension_eq_of_relation_mem h

example (X Y : MetrizableLCA) {n : ℕ}
    {a b sum : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) :
    YonedaExt.ofExtension (C := MetrizableLCA) sum =
      YonedaExt.ofExtension (C := MetrizableLCA) a +
        YonedaExt.ofExtension (C := MetrizableLCA) b :=
  YonedaExt.ofExtension_eq_add_of_baerChain h

example (X Y : MetrizableLCA) {n : ℕ}
    {a b sum : YonedaExtension (C := MetrizableLCA) X Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) :
    YonedaExt.baer_sum
        (YonedaExt.ofExtension (C := MetrizableLCA) a)
        (YonedaExt.ofExtension (C := MetrizableLCA) b) =
      YonedaExt.ofExtension (C := MetrizableLCA) sum :=
  YonedaExt.baer_sum_ofExtension_eq_of_baerChain h

example (X Y Z : MetrizableLCA) {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (a : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) e n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (YonedaExtension.consLeftMap e n a) :=
  YonedaExt.leftProductByExtension_ofExtension e a

example (X Y Z : MetrizableLCA) {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (s : e.shortComplex.Splitting)
    (a : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) e n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      (0 : YonedaExt (C := MetrizableLCA) X Z ((n + 1) + 1)) :=
  YonedaExt.leftProductByExtension_ofExtension_eq_zero_of_split e s a

example (X Y Z : MetrizableLCA) {n : ℕ}
    {e e' : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.Iso e e')
    (a : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) e n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) e' n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) :=
  YonedaExt.leftProductByExtension_ofExtension_eq_of_isoLeft h a

example (X Y Z : MetrizableLCA) {n : ℕ}
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (a : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        sum n (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e₁ n (YonedaExt.ofExtension (C := MetrizableLCA) a) +
        YonedaExt.leftProductByExtension
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e₂ n (YonedaExt.ofExtension (C := MetrizableLCA) a) :=
  YonedaExt.leftProductByExtension_ofExtension_eq_add_of_baerLeft h a

example (X Y Z : MetrizableLCA) {n : ℕ}
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (a : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.baer_sum
        (YonedaExt.leftProductByExtension
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e₁ n (YonedaExt.ofExtension (C := MetrizableLCA) a))
        (YonedaExt.leftProductByExtension
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e₂ n (YonedaExt.ofExtension (C := MetrizableLCA) a)) =
      YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        sum n (YonedaExt.ofExtension (C := MetrizableLCA) a) :=
  YonedaExt.leftProductByExtension_baer_sum_ofExtension_eq_of_baerLeft h a

example (X Y Z : MetrizableLCA) {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (s : e.shortComplex.Splitting) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        e n =
      0 :=
  YonedaExt.leftProductByExtension_eq_zero_of_split e s n

example (X Y Z : MetrizableLCA) {n : ℕ}
    {e e' : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.Iso e e') :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        e n =
      YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        e' n :=
  YonedaExt.leftProductByExtension_eq_of_isoLeft h n

example (X Y Z : MetrizableLCA) {n : ℕ}
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        sum n =
      YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e₁ n +
        YonedaExt.leftProductByExtension
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e₂ n :=
  YonedaExt.leftProductByExtension_eq_add_of_baerLeft h n

example (X Y Z : MetrizableLCA) {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (a b : YonedaExt (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        e n (a + b) =
      YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e n a +
        YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
          e n b :=
  YonedaExt.leftProductByExtension_add e n a b

example (X Y Z : MetrizableLCA) {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA) X Y)
    (a b : YonedaExt (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByExtension (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z)
        e n (YonedaExt.baer_sum a b) =
      YonedaExt.baer_sum
        (YonedaExt.leftProductByExtension
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) e n a)
        (YonedaExt.leftProductByExtension
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) e n b) :=
  YonedaExt.leftProductByExtension_baer_sum e n a b

example (X Y : MetrizableLCA) {m : ℕ}
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) X Y m) :
    YonedaExtension (C := MetrizableLCA) X Y (m + 1) :=
  p.toYonedaExtension

example (X Y Z : MetrizableLCA) {m n : ℕ}
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) X Y m)
    (a : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (n := n + (m + 1)) (p.consLeftMap a) :=
  YonedaExt.leftProductByPositiveChain_ofExtension p a

example (X Y Z : MetrizableLCA) {m n : ℕ}
    {p : YonedaExtension.PositiveChain (C := MetrizableLCA) X Y m}
    (h : YonedaExtension.PositiveChain.SplitFactorData p)
    (a : YonedaExtension (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      (0 : YonedaExt (C := MetrizableLCA) X Z ((n + (m + 1)) + 1)) :=
  YonedaExt.leftProductByPositiveChain_ofExtension_eq_zero_of_splitFactor h a

example (X Y W Z : MetrizableLCA) {m n : ℕ}
    {e e' : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.Iso e e')
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) Y W m)
    (a : YonedaExtension (C := MetrizableLCA) W Z (n + 1)) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e p) n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e' p) n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) :=
  YonedaExt.leftProductByPositiveChain_cons_ofExtension_eq_of_isoHead h p a

example (X Y W Z : MetrizableLCA) {m n : ℕ}
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) Y W m)
    (a : YonedaExtension (C := MetrizableLCA) W Z (n + 1)) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons sum p) n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) =
      YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₁ p) n
          (YonedaExt.ofExtension (C := MetrizableLCA) a) +
        YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₂ p) n
          (YonedaExt.ofExtension (C := MetrizableLCA) a) :=
  YonedaExt.leftProductByPositiveChain_cons_ofExtension_eq_add_of_baerHead h p a

example (X Y W Z : MetrizableLCA) {m n : ℕ}
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) Y W m)
    (a : YonedaExtension (C := MetrizableLCA) W Z (n + 1)) :
    YonedaExt.baer_sum
        (YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₁ p) n
          (YonedaExt.ofExtension (C := MetrizableLCA) a))
        (YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₂ p) n
          (YonedaExt.ofExtension (C := MetrizableLCA) a)) =
      YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons sum p) n
        (YonedaExt.ofExtension (C := MetrizableLCA) a) :=
  YonedaExt.leftProductByPositiveChain_cons_baer_sum_ofExtension_eq_of_baerHead h p a

example (X Y Z : MetrizableLCA) {m n : ℕ}
    {p : YonedaExtension.PositiveChain (C := MetrizableLCA) X Y m}
    (h : YonedaExtension.PositiveChain.SplitFactorData p) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n =
      0 :=
  YonedaExt.leftProductByPositiveChain_eq_zero_of_splitFactor h n

example (X Y W Z : MetrizableLCA) {m n : ℕ}
    {e e' : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.Iso e e')
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) Y W m) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e p) n =
      YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e' p) n :=
  YonedaExt.leftProductByPositiveChain_cons_eq_of_isoHead h p n

example (X Y W Z : MetrizableLCA) {m n : ℕ}
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA) X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) Y W m) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons sum p) n =
      YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₁ p) n +
        YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₂ p) n :=
  YonedaExt.leftProductByPositiveChain_cons_eq_add_of_baerHead h p n

example (X Y Z : MetrizableLCA) {m n : ℕ}
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) X Y m)
    (a b : YonedaExt (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n (a + b) =
      YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n a +
        YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n b :=
  YonedaExt.leftProductByPositiveChain_add p n a b

example (X Y Z : MetrizableLCA) {m n : ℕ}
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA) X Y m)
    (a b : YonedaExt (C := MetrizableLCA) Y Z (n + 1)) :
    YonedaExt.leftProductByPositiveChain
        (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n
        (YonedaExt.baer_sum a b) =
      YonedaExt.baer_sum
        (YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n a)
        (YonedaExt.leftProductByPositiveChain
          (C := MetrizableLCA) (X := X) (Y := Y) (Z := Z) p n b) :=
  YonedaExt.leftProductByPositiveChain_baer_sum p n a b

#check (YonedaExtension.PositiveChain.Rel (C := MetrizableLCA))
#check (YonedaExtension.PositiveChain.Rel.toYonedaExtension (C := MetrizableLCA))
#check (YonedaExtension.PositiveChain.Rel.consLeftMap (C := MetrizableLCA))
#check (YonedaExtension.PositiveChain.BaerSumData (C := MetrizableLCA))
#check (YonedaExtension.PositiveChain.BaerSumData.toYonedaExtension (C := MetrizableLCA))
#check (YonedaExtension.PositiveChain.BaerSumData.consLeftMap (C := MetrizableLCA))
#check (YonedaExt.leftProductByPositiveChain_ofExtension_eq_of_rel (C := MetrizableLCA))
#check (YonedaExt.leftProductByPositiveChain_ofExtension_eq_add_of_baerLeftChain
  (C := MetrizableLCA))
#check (YonedaExt.leftProductByPositiveChain_baer_sum_ofExtension_eq_of_baerLeftChain
  (C := MetrizableLCA))
#check (YonedaExt.leftProductByPositiveChain_eq_of_rel (C := MetrizableLCA))
#check (YonedaExt.leftProductByPositiveChain_eq_add_of_baerLeftChain (C := MetrizableLCA))

#check MetrizableLCA.shortExactExtensionPullbackDomainIsoBetween
#check YonedaExtension.RelIso.refl
#check YonedaExtension.RightSplitData.toSplitFactorData
#check YonedaExtension.RelIso.pullbackHeadDomain_metrizable
#check YonedaExtension.RelIso.spliceLeftWith_metrizable
#check YonedaExt.leftProductByYonedaExtension_metrizable_eq_of_relIso
#check YonedaExt.yonedaProductLeftFreeHom
#check YonedaExt.yonedaProductLeftFreeHom_rel_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_relIso_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_split_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_rightSplit_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_splitFactor_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_baer_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_baerChain_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_leftSplit_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_homTail_eq_zero
#check YonedaExt.yonedaProductLeftFreeHom_homTailLeft_eq_zero
#check YonedaExt.yonedaProductLeft_relationSubgroup_le
#check YonedaExt.yonedaProduct
#check YonedaExt.yonedaProduct_ofExtension
#check YonedaExt.yonedaProduct_ofExtension_ofExtension
#check YonedaExt.positiveYonedaExtCast
#check YonedaExt.positiveYonedaExtCast_ofExtension
#check YonedaExt.positiveYonedaExtCast_spliceLeftWith_assoc
#check YonedaExt.yonedaProduct_ofExtension_assoc_cast
#check YonedaExt.yonedaProduct_add_left
#check YonedaExt.yonedaProduct_add_right

noncomputable example (X Y Z : MetrizableLCA) {m n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA) X Y (m + 1)}
    (h : YonedaExtension.RelIso (C := MetrizableLCA) (CategoryTheory.Iso.refl X) a b) :
    YonedaExt.yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) = 0 :=
  YonedaExt.yonedaProductLeftFreeHom_relIso_eq_zero h

noncomputable example (X Y : MetrizableLCA) :
    AddCommGroup (YonedaExt (C := MetrizableLCA) X Y 1) := by
  infer_instance

noncomputable example (X Y : MetrizableLCA) :
    YonedaExt (C := MetrizableLCA) X Y 0 ≃ (X ⟶ Y) :=
  YonedaExt.zero_equiv_hom

/-
Exact weak equivalences are the morphisms whose mapping cone is exact.
-/
#check (BoundedComplexCategory (C := MetrizableLCA))
#check (BoundedComplexCategory.ι (C := MetrizableLCA))
#check (boundedCochainComplex_containsZero (C := MetrizableLCA))
#check (boundedCochainComplex_isClosedUnderIsomorphisms (C := MetrizableLCA))
#check (boundedCochainComplex_isStableUnderShift (C := MetrizableLCA))
#check (boundedCochainComplex_mappingCone (C := MetrizableLCA))
#check (boundedComplexCategory_hasZeroObject (C := MetrizableLCA))
#check (boundedExactWeakEquivalence (C := MetrizableLCA))
#check (boundedExactWeakEquivalence_respectsIso (C := MetrizableLCA))
#check (exactAcyclic_of_iso (C := MetrizableLCA))
#check (exactAcyclic_of_splittings (C := MetrizableLCA))
#check (exactAcyclic_shift (C := MetrizableLCA))
#check (exactAcyclic_shift_iff (C := MetrizableLCA))
#check (exactAcyclic_zero (C := MetrizableLCA))
#check FiniteProductExactness.FiniteExactAcyclicProductClosure
#check FiniteProductExactness.finiteProductOptionDecompositionInput_of_w151
#check FiniteProductExactness.finiteExactAcyclicProductClosure_of_w151
#check (exactAcyclic_mappingCone_shift_iff (C := MetrizableLCA))
#check (mappingConeIsoOfCommIso (C := MetrizableLCA))
#check (exactAcyclic_mappingCone_congr_iff (C := MetrizableLCA))
#check (boundedCochainComplex_mappingCone_congr_iff (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_quotient_obj_iff (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_containsZero (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure_isClosedUnderIsomorphisms (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure_containsZero (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure_isStableUnderShift (C := MetrizableLCA))
#check exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
#check (exactAcyclicHomotopyIsoClosure_trW (C := MetrizableLCA))
#check exactAcyclicHomotopyObject_isStableUnderShift_of_isClosedUnderIsomorphisms
#check exactAcyclicHomotopyObject_isTriangulated_of_isTriangulatedClosed2
#check (exactAcyclicHomotopyObject_trW_quotient_map_of_exactAcyclic_mappingCone
  (C := MetrizableLCA))
#check exactAcyclicHomotopyObject_trW_quotient_map_iff_exactAcyclic_mappingCone
#check (exactAcyclicHomotopyIsoClosure_trW_quotient_map_of_exactAcyclic_mappingCone
  (C := MetrizableLCA))
#check exactAcyclicHomotopyIsoClosure_trW_quotient_map_iff_mappingCone
#check exactAcyclicHomotopyIsoClosure_trW_quotient_map_iff_exactAcyclic_mappingCone
#check (exactAcyclicHomotopyObject_triangleh_ext3 (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_triangleh_ext2 (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_triangleh_ext1 (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_triangleh_iso_ext3 (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_triangleh_iso_ext2 (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_triangleh_iso_ext1 (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_distinguished_ext3_of_triangleh_iso12
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_distinguished_ext2_of_triangleh_iso13
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_distinguished_ext1_of_triangleh_iso23
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosureTrianglehIso13Realization (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure_isTriangulated_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (boundedExactWeakEquivalence_shift_iff (C := MetrizableLCA))
#check (boundedExactWeakEquivalence_isCompatibleWithShift (C := MetrizableLCA))
#check (BoundedComplexCategory.homotopyQuotient (C := MetrizableLCA))
#check (boundedHomotopyObject (C := MetrizableLCA))
#check (boundedHomotopyObject_quotient_obj (C := MetrizableLCA))
#check (boundedCochainComplex_of_mappingCone_right (C := MetrizableLCA))
#check (boundedCochainComplex_of_mappingCone_left (C := MetrizableLCA))
#check (boundedHomotopyObject_mappingCone (C := MetrizableLCA))
#check (boundedHomotopyObject_mappingCone_congr_iff (C := MetrizableLCA))
#check (boundedHomotopyObject_of_mappingCone_right (C := MetrizableLCA))
#check (boundedHomotopyObject_of_mappingCone_left (C := MetrizableLCA))
#check (boundedHomotopyObject_triangleh_ext3 (C := MetrizableLCA))
#check (boundedHomotopyObject_triangleh_ext2 (C := MetrizableLCA))
#check (boundedHomotopyObject_triangleh_ext1 (C := MetrizableLCA))
#check (boundedHomotopyObject_triangleh_iso_ext3 (C := MetrizableLCA))
#check (boundedHomotopyObject_triangleh_iso_ext2 (C := MetrizableLCA))
#check (boundedHomotopyObject_triangleh_iso_ext1 (C := MetrizableLCA))
#check (boundedHomotopyObject_distinguished_ext3_of_triangleh_iso12 (C := MetrizableLCA))
#check (boundedHomotopyObject_distinguished_ext2_of_triangleh_iso13 (C := MetrizableLCA))
#check (boundedHomotopyObject_distinguished_ext1_of_triangleh_iso23 (C := MetrizableLCA))
#check boundedHomotopyObjectTrianglehIso13Realization
#check (boundedHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_triangleh_iso13_realizations
#check boundedHomotopyObject_isTriangulated_of_isTriangulatedClosed2
#check boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2
#check boundedHomotopyCategory_isTriangulated_of_isTriangulatedClosed2
#check boundedHomotopyCategory_pretriangulated_of_triangleh_iso13_realization
#check boundedHomotopyCategory_isTriangulated_of_triangleh_iso13_realization
#check boundedExactAcyclicHomotopyObject
#check boundedExactAcyclicHomotopyObject_isClosedUnderIsomorphisms
#check boundedExactAcyclicHomotopyObject_containsZero
#check boundedExactAcyclicHomotopyObject_isStableUnderShift
#check boundedExactAcyclicHomotopyObject_isTriangulated_of_closed2
#check BoundedExactAcyclicHomotopyVerdierCategory
#check BoundedExactAcyclicHomotopyVerdierQuasicategory
#check BoundedExactAcyclicHomotopyVerdierQuasicategory.homotopyCategoryIso
#check boundedExactAcyclicHomotopyObjectToIsoClosure_trW
#check boundedExactAcyclicHomotopyVerdierComparison
#check boundedExactAcyclicHomotopyVerdierComparisonLocalizationIso
#check boundedExactAcyclicHomotopyVerdierCategory_preadditive_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_localization_additive_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_hasZeroObject_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_hasShift_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_localization_commShift_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_pretriangulated_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_isTriangulated_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_preadditive_of_triangleh_iso13_realizations
#check boundedExactAcyclicHomotopyVerdierCategory_pretriangulated_of_triangleh_iso13_realizations
#check boundedExactAcyclicHomotopyVerdierCategory_isTriangulated_of_triangleh_iso13_realizations
#check (BoundedHomotopyCategory (C := MetrizableLCA))
#check (BoundedHomotopyCategory.ι (C := MetrizableLCA))
#check (boundedExactWeakEquivalence_le_exactAcyclicHomotopy_trW_inverseImage
  (C := MetrizableLCA))
#check boundedExactWeakEquivalence_eq_exactAcyclicHomotopy_trW_inverseImage
#check (boundedHomotopyExactWeakEquivalence (C := MetrizableLCA))
#check (boundedExactWeakEquivalence_le_boundedHomotopyExactWeakEquivalence
  (C := MetrizableLCA))
#check (boundedHomotopyExactWeakEquivalence_of_exactAcyclic_mappingCone
  (C := MetrizableLCA))
#check boundedHomotopyExactWeakEquivalence_iff_mappingCone_isoClosure
#check (boundedExactWeakEquivalence_of_mappingCone_splittings (C := MetrizableLCA))
#check (boundedHomotopyExactWeakEquivalence_of_mappingCone_splittings (C := MetrizableLCA))
#check boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed
#check boundedExactWeakEquivalence_iff_boundedHomotopyExactWeakEquivalence_of_isoClosed
#check boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed
#check boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed
#check boundedHomotopyExactWeakEquivalence_iff_exactAcyclic_mappingCone_of_isoClosed
#check (boundedHomotopyExactWeakEquivalence_isCompatibleWithShift (C := MetrizableLCA))
#check (boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence (C := MetrizableLCA))
#check boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed
#check boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed_localizedEquivalence
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isoClosureClosed2
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isoClosureClosed2
#check exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2
#check exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_homotopyObjectClosed2
#check (exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (ExactAcyclicHomotopyVerdierCategory (C := MetrizableLCA))
#check (ExactAcyclicHomotopyVerdierQuasicategory (C := MetrizableLCA))
#check (ExactAcyclicHomotopyVerdierQuasicategory.homotopyCategoryIso (C := MetrizableLCA))
#check exactAcyclicHomotopyVerdierCategory_preadditive_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_additive_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_hasShift_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_commShift_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_pretriangulated_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_isTriangulated_of_isTriangulatedClosed2
#check exactAcyclicHomotopyVerdierCategory_preadditive_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_additive_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_hasShift_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_localization_commShift_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_pretriangulated_of_homotopyObjectClosed2
#check exactAcyclicHomotopyVerdierCategory_isTriangulated_of_homotopyObjectClosed2
#check (exactAcyclicHomotopyVerdierCategory_preadditive_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyVerdierCategory_localization_additive_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyVerdierCategory_hasShift_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyVerdierCategory_localization_commShift_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyVerdierCategory_pretriangulated_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check (exactAcyclicHomotopyVerdierCategory_isTriangulated_of_triangleh_iso13_realization
  (C := MetrizableLCA))
#check Dbounded.preadditiveOfHasLeftCalculusOfFractions
#check Dbounded.localization_additiveOfHasLeftCalculusOfFractions
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.preadditiveOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.localization_additiveOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.hasZeroObjectOfHasLeftCalculusOfFractions
#check BoundedHomotopyDerivedCategory.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check Dbounded.preadditiveOfHomotopyLeftCalculusOfIsoClosed
#check Dbounded.localization_additiveOfHomotopyLeftCalculusOfIsoClosed
#check Dbounded.hasZeroObjectOfHomotopyLeftCalculusOfIsoClosed
#check Dbounded.shiftFunctor_additiveOfHomotopyLeftCalculusOfIsoClosed

noncomputable example : HasShift (BoundedComplexCategory (C := MetrizableLCA)) ℤ := by
  infer_instance

noncomputable example : HasZeroObject (BoundedComplexCategory (C := MetrizableLCA)) := by
  infer_instance

noncomputable example : HasZeroObject (BoundedHomotopyCategory (C := MetrizableLCA)) := by
  infer_instance

noncomputable example :
    (shiftFunctor (BoundedComplexCategory (C := MetrizableLCA)) (1 : ℤ)).Additive := by
  infer_instance

noncomputable example : HasShift (BoundedHomotopyCategory (C := MetrizableLCA)) ℤ := by
  infer_instance

noncomputable example : HasShift (Dbounded (C := MetrizableLCA)) ℤ := by
  infer_instance

noncomputable example : (Dbounded.localization (C := MetrizableLCA)).CommShift ℤ := by
  infer_instance

noncomputable example :
    (boundedHomotopyExactWeakEquivalence (C := MetrizableLCA)).IsCompatibleWithShift ℤ := by
  infer_instance

noncomputable example : HasShift (BoundedHomotopyDerivedCategory (C := MetrizableLCA)) ℤ := by
  infer_instance

noncomputable example :
    ((boundedHomotopyExactWeakEquivalence (C := MetrizableLCA)).Q).CommShift ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (BoundedHomotopyDerivedCategory C) :=
  BoundedHomotopyDerivedCategory.preadditiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    ((boundedHomotopyExactWeakEquivalence C).Q).Additive :=
  BoundedHomotopyDerivedCategory.localization_additiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (BoundedHomotopyDerivedCategory C) :=
  BoundedHomotopyDerivedCategory.hasZeroObjectOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (shiftFunctor (BoundedHomotopyDerivedCategory C) (1 : ℤ)).Additive :=
  BoundedHomotopyDerivedCategory.shiftFunctor_additiveOfHasLeftCalculusOfFractions C 1

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
  boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions] :
    (boundedExactWeakEquivalence C).HasRightCalculusOfFractions :=
  boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2 C

example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    (exactAcyclicHomotopyIsoClosure C).IsClosedUnderIsomorphisms := by
  infer_instance

example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] :
    (exactAcyclicHomotopyIsoClosure C).ContainsZero := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    (boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed
      C).IsLocalizedEquivalence := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    Dbounded C ≌ BoundedHomotopyDerivedCategory C :=
  Dbounded.homotopyComparisonEquivalenceOfIsoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Preadditive (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).Additive := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasZeroObject (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasShift (ExactAcyclicHomotopyVerdierCategory C) ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).CommShift ℤ := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (shiftFunctor (ExactAcyclicHomotopyVerdierCategory C) (1 : ℤ)).Additive := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Pretriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    IsTriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    Preadditive (ExactAcyclicHomotopyVerdierCategory C) :=
  exactAcyclicHomotopyVerdierCategory_preadditive_of_homotopyObjectClosed2 C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    IsTriangulated (ExactAcyclicHomotopyVerdierCategory C) :=
  exactAcyclicHomotopyVerdierCategory_isTriangulated_of_homotopyObjectClosed2 C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (Dbounded C) :=
  Dbounded.preadditiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (Dbounded.localization C).Additive :=
  Dbounded.localization_additiveOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [HasZeroObject C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (Dbounded C) :=
  Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasBinaryBiproducts C] [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (shiftFunctor (Dbounded C) (1 : ℤ)).Additive :=
  Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions C 1

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasFiniteLimits C] [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions]
    [(boundedExactWeakEquivalence C).IsStableUnderFiniteProducts] :
    HasFiniteProducts (Dbounded C) :=
  Dbounded.hasFiniteProductsOfStableFiniteProducts C

#check BoundedFiniteProducts.includedProductIso
#check BoundedFiniteProducts.includedProductMap_naturality
#check BoundedFiniteProducts.exactAcyclic_mappingCone_cochain_piMap
#check BoundedFiniteProducts.finiteProductMappingConeInput_metrizableLCA
#check BoundedFiniteProducts.isStableUnderFiniteProducts_metrizableLCA
#check BoundedFiniteProducts.dboundedHasFiniteProducts_metrizableLCA

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (Dbounded C) :=
  Dbounded.preadditiveOfHomotopyLeftCalculusOfIsoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
      boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
    (Dbounded.localization C).Additive :=
  Dbounded.localization_additiveOfHomotopyLeftCalculusOfIsoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (Dbounded C) :=
  Dbounded.hasZeroObjectOfHomotopyLeftCalculusOfIsoClosed C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
      boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
    (shiftFunctor (Dbounded C) (1 : ℤ)).Additive :=
  Dbounded.shiftFunctor_additiveOfHomotopyLeftCalculusOfIsoClosed C 1

/-
The bounded derived category is the localization at those exact weak equivalences.
-/
#check (BoundedDerivedCategory (C := MetrizableLCA))
#check (Dbounded (C := MetrizableLCA))

noncomputable example : Category (Dbounded (C := MetrizableLCA)) := by infer_instance

#check (Dbounded.localization (C := MetrizableLCA))
#check (BoundedHomotopyDerivedCategory (C := MetrizableLCA))
#check (BoundedHomotopyDerivedQuasicategory (C := MetrizableLCA))
#check (BoundedHomotopyDerivedQuasicategory.homotopyCategoryIso (C := MetrizableLCA))
#check (boundedHomotopyExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW
  (C := MetrizableLCA))
#check (boundedExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW
  (C := MetrizableLCA))
#check (BoundedHomotopyDerivedCategory.verdierComparison (C := MetrizableLCA))
#check (BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso (C := MetrizableLCA))
#check BoundedComplexCategory.homotopyQuotientBounded
#check BoundedComplexCategory.homotopyQuotientBounded_comp_ι_iso
#check boundedHomotopyExactWeakEquivalenceToBoundedExactAcyclicHomotopy_trW
#check boundedHomotopyExactWeakEquivalence_eq_boundedExactAcyclicHomotopy_trW_inverseImage
#check boundedExactWeakEquivalence_eq_boundedExactAcyclicHomotopy_trW_inverseImage_of_isoClosed
#check BoundedHomotopyDerivedCategory.boundedVerdierComparison
#check BoundedHomotopyDerivedCategory.boundedVerdierComparisonLocalizationIso
#check BoundedHomotopyDerivedCategory.boundedVerdierComparison_comp_ambientIso
#check (Dbounded.homotopyComparison (C := MetrizableLCA))
#check (Dbounded.homotopyComparisonLocalizationIso (C := MetrizableLCA))
#check (Dbounded.verdierComparison (C := MetrizableLCA))
#check (Dbounded.verdierComparisonLocalizationIso (C := MetrizableLCA))
#check (Dbounded.verdierComparisonDirect (C := MetrizableLCA))
#check (Dbounded.verdierComparisonDirectLocalizationIso (C := MetrizableLCA))
#check (Dbounded.verdierComparisonDirectIso (C := MetrizableLCA))
#check Dbounded.boundedVerdierComparison
#check Dbounded.boundedVerdierComparisonLocalizationIso
#check Dbounded.boundedVerdierComparisonDirect
#check Dbounded.boundedVerdierComparisonDirectLocalizationIso
#check Dbounded.boundedVerdierComparisonDirectIso
#check Dbounded.boundedVerdierComparison_comp_ambientIso
#check Dbounded.homotopyComparisonEquivalenceOfIsoClosed

noncomputable example :
    (BoundedHomotopyDerivedCategory (C := MetrizableLCA)) ⥤
      ExactAcyclicHomotopyVerdierCategory (C := MetrizableLCA) :=
  BoundedHomotopyDerivedCategory.verdierComparison (C := MetrizableLCA)

noncomputable example :
    (Dbounded (C := MetrizableLCA)) ⥤
      ExactAcyclicHomotopyVerdierCategory (C := MetrizableLCA) :=
  Dbounded.verdierComparison (C := MetrizableLCA)

noncomputable example :
    LocalizerMorphism (boundedExactWeakEquivalence (C := MetrizableLCA))
      (exactAcyclicHomotopyIsoClosure (C := MetrizableLCA)).trW :=
  boundedExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW (C := MetrizableLCA)

noncomputable example :
    BoundedComplexCategory.homotopyQuotient (C := MetrizableLCA) ⋙
        (exactAcyclicHomotopyIsoClosure (C := MetrizableLCA)).trW.Q ≅
      Dbounded.localization (C := MetrizableLCA) ⋙
        Dbounded.verdierComparisonDirect (C := MetrizableLCA) :=
  Dbounded.verdierComparisonDirectLocalizationIso (C := MetrizableLCA)

noncomputable example :
    Dbounded.verdierComparison (C := MetrizableLCA) ≅
      Dbounded.verdierComparisonDirect (C := MetrizableLCA) :=
  Dbounded.verdierComparisonDirectIso (C := MetrizableLCA)

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    Dbounded C ⥤ BoundedExactAcyclicHomotopyVerdierCategory C :=
  Dbounded.boundedVerdierComparison C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    Dbounded C ⥤ BoundedExactAcyclicHomotopyVerdierCategory C :=
  Dbounded.boundedVerdierComparisonDirect C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    BoundedComplexCategory.homotopyQuotientBounded C ⋙
        (boundedExactAcyclicHomotopyObject C).trW.Q ≅
      Dbounded.localization C ⋙ Dbounded.boundedVerdierComparison C :=
  Dbounded.boundedVerdierComparisonLocalizationIso C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    BoundedComplexCategory.homotopyQuotientBounded C ⋙
        (boundedExactAcyclicHomotopyObject C).trW.Q ≅
      Dbounded.localization C ⋙ Dbounded.boundedVerdierComparisonDirect C :=
  Dbounded.boundedVerdierComparisonDirectLocalizationIso C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    Dbounded.boundedVerdierComparison C ≅ Dbounded.boundedVerdierComparisonDirect C :=
  Dbounded.boundedVerdierComparisonDirectIso C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    Dbounded.boundedVerdierComparison C ⋙
        boundedExactAcyclicHomotopyVerdierComparison C ≅
      Dbounded.verdierComparison C :=
  Dbounded.boundedVerdierComparison_comp_ambientIso C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    LocalizerMorphism (boundedHomotopyExactWeakEquivalence C)
      (boundedExactAcyclicHomotopyObject C).trW :=
  boundedHomotopyExactWeakEquivalenceToBoundedExactAcyclicHomotopy_trW C

example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    boundedHomotopyExactWeakEquivalence C =
      (boundedExactAcyclicHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotientBounded C) :=
  boundedHomotopyExactWeakEquivalence_eq_boundedExactAcyclicHomotopy_trW_inverseImage C

example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    boundedExactWeakEquivalence C =
      (boundedExactAcyclicHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotientBounded C) :=
  boundedExactWeakEquivalence_eq_boundedExactAcyclicHomotopy_trW_inverseImage_of_isoClosed C

#check BoundedTrianglehIso13SelectedCochainPayload
#check boundedTrianglehIso13SelectedCochainStrictification
#check boundedTrianglehIso13CochainIsoPayload
#check boundedTrianglehIso13CochainDataStrictification
#check boundedTrianglehIso13CochainIsoPayload_iff_cochain_data
#check boundedHomotopyObjectTrianglehIso13Realization_of_cochain_iso_payload
#check boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data
#check boundedTrianglehIso13SelectedCochainStrictification_of_realization
#check boundedTrianglehIso13SelectedCochainStrictification_iff_realization
#check boundedTrianglehIso13CochainIsoPayload_of_realization
#check boundedTrianglehIso13CochainIsoPayload_iff_realization
#check boundedTrianglehIso13CochainDataStrictification_of_realization
#check boundedTrianglehIso13CochainDataStrictification_iff_realization
#check homotopyEndpointPayloadWithoutSelectedCochainIso
#check homotopyEndpointPayloadWithoutSelectedCochainIso_of_distinguished
#check endpointHomotopyEquivToSelectedCochainIsoStrictification
#check strictBoundednessTransport_of_endpointHomotopyEquivToSelectedCochainIsoStrictification
#check AlternatingTailExtendTransport.not_endpointHomotopyEquivToSelectedCochainIsoStrictification_intModuleCat

example (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13CochainDataStrictification C) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data C strictify

#check RightUnboundedContractibleComplex
#check StrictBoundednessTransportOfHomotopyEquiv
#check not_strictBoundednessTransport_of_rightUnboundedContractibleComplex
#check AlternatingTailExtendTransport.intAlternatingTailGERightUnboundedContractible
#check AlternatingTailExtendTransport.not_strictBoundednessTransport_intAlternatingTailGE

example : ¬ StrictBoundednessTransportOfHomotopyEquiv AlternatingTailExtendTransport.IntModuleCat :=
  AlternatingTailExtendTransport.not_strictBoundednessTransport_intAlternatingTailGE 0

example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C] :
    (boundedExactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms := by
  infer_instance

example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] :
    (boundedExactAcyclicHomotopyObject C).ContainsZero := by
  infer_instance

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    (boundedExactAcyclicHomotopyObject C).IsStableUnderShift ℤ :=
  boundedExactAcyclicHomotopyObject_isStableUnderShift C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    BoundedHomotopyDerivedCategory C ⥤ BoundedExactAcyclicHomotopyVerdierCategory C :=
  BoundedHomotopyDerivedCategory.boundedVerdierComparison C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    BoundedComplexCategory.homotopyQuotientBounded C ⋙
        (boundedExactAcyclicHomotopyObject C).trW.Q ≅
      (boundedHomotopyExactWeakEquivalence C).Q ⋙
        BoundedHomotopyDerivedCategory.boundedVerdierComparison C :=
  BoundedHomotopyDerivedCategory.boundedVerdierComparisonLocalizationIso C

noncomputable example (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    BoundedHomotopyDerivedCategory.boundedVerdierComparison C ⋙
        boundedExactAcyclicHomotopyVerdierComparison C ≅
      BoundedHomotopyDerivedCategory.verdierComparison C :=
  BoundedHomotopyDerivedCategory.boundedVerdierComparison_comp_ambientIso C

/-
The bounded derived infinity-category is exposed as a quasicategory, and its homotopy category
recovers the localized ordinary category.
-/
#check (BoundedDerivedInfinityCategory (C := MetrizableLCA))
#check (Dbounded.infinityCategory (C := MetrizableLCA))
#check (Dbounded.infinityNerve (C := MetrizableLCA))
#check (Dbounded.infinityNerve_quasicategory (C := MetrizableLCA))
#check (Dbounded.homotopyCategoryIso (C := MetrizableLCA))

noncomputable example : SSet.QCat :=
  BoundedDerivedInfinityCategory (C := MetrizableLCA)

noncomputable example :
    SSet.Quasicategory (Dbounded.infinityNerve (C := MetrizableLCA)) :=
  Dbounded.infinityNerve_quasicategory (C := MetrizableLCA)

end LeanLCAExactChallenge
