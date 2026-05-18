import LeanLCAExactChallenge

/-!
Product-success contract for the exact LCA category challenge.

This file checks that the public declarations used for the final product are
available from the strict metrizable LCA exact structure, without routing
through abelian-category Ext or an externally supplied derived construction.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

/--
The strict metrizable LCA exact-category structure is now available without
an extra premise argument.
-/
example : QuillenExactCategory MetrizableLCA := by
  exact MetrizableLCA.quillenExactCategory

/-- The strict metrizable LCA category has the biproducts needed for mapping cones. -/
example : HasBinaryBiproducts MetrizableLCA := by infer_instance

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

/--
Strict short exact sequences in the metrizable LCA model are stable under
coordinatewise binary biproducts.
-/
example {S T : ShortComplex MetrizableLCA}
    (hS : MetrizableLCA.strictShortExact S) (hT : MetrizableLCA.strictShortExact T) :
    MetrizableLCA.strictShortExact (MetrizableLCA.strictShortExactBiprodComplex S T) :=
  MetrizableLCA.strictShortExact_biprod hS hT

/-
Exact-category Ext is defined directly from the local conflation interface and
positive degrees are quotient groups of formal Yoneda chains by local relation
generators.
-/
#check (fun (X Y : MetrizableLCA) => YonedaExt (C := MetrizableLCA) X Y 1)
#check (fun (X Y : MetrizableLCA) => PositiveYonedaExtFree (C := MetrizableLCA) X Y 0)
#check (fun (X Y : MetrizableLCA) => yonedaRelationSubgroup (C := MetrizableLCA) X Y 0)
#check (fun (X Y : MetrizableLCA) => YonedaRelGenerator (C := MetrizableLCA) X Y)
#check (fun (X Y : MetrizableLCA) =>
  ShortExactExtension.BaerSumData (C := MetrizableLCA) (X := X) (Y := Y))

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

noncomputable example (X X' Y : MetrizableLCA)
    (e : ShortExactExtension (C := MetrizableLCA) X Y) (a : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA) a
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e a)
        e.toYonedaExtension =
      YonedaExt.ofExtension (C := MetrizableLCA)
        (MetrizableLCA.shortExactExtensionPullback e a).toYonedaExtension :=
  rfl

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

noncomputable example (X Y : MetrizableLCA) :
    AddCommGroup (YonedaExt (C := MetrizableLCA) X Y 1) := by
  infer_instance

noncomputable example (X Y : MetrizableLCA) :
    YonedaExt (C := MetrizableLCA) X Y 0 ≃ (X ⟶ Y) :=
  YonedaExt.zero_equiv_hom

/-
Exact weak equivalences are the morphisms whose mapping cone is exact.
-/
#check (boundedExactWeakEquivalence (C := MetrizableLCA))

/-
The bounded derived category is the localization at those exact weak equivalences.
-/
#check (Dbounded (C := MetrizableLCA))

noncomputable example : Category (Dbounded (C := MetrizableLCA)) := by infer_instance

#check (Dbounded.localization (C := MetrizableLCA))

end LeanLCAExactChallenge
