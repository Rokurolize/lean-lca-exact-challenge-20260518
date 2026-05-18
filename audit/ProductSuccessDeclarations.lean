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
