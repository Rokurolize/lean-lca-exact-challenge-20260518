import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.PiProd
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
Option product decomposition for cochain-complex products.

This module promotes the checked `Option J` product split from the audit route into the product
library namespace.  It constructs the selected product object over `Option J` as the binary
biproduct of the `none` entry and the product over the `some` tail, under the finite-product
instances needed by the finite-product induction route.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OptionProductDecompositionW151

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The tail family obtained by dropping the `none` summand from an `Option`-indexed family. -/
abbrev optionTail {J : Type w} (K : Option J → CochainComplex C ℤ) :
    J → CochainComplex C ℤ :=
  fun j => K (some j)

/-- The tail family at a fixed cochain degree after dropping the `none` entry. -/
abbrev optionTailDegree {J : Type w} (K : Option J → CochainComplex C ℤ) (n : ℤ) :
    J → C :=
  fun j => (K (some j)).X n

/-- The singleton subindex selecting only the `none` entry of an `Option J` family. -/
abbrev optionNoneIndex (J : Type w) : Type w :=
  {x : Option J // x = none}

instance optionNoneIndexUnique (J : Type w) : Unique (optionNoneIndex J) where
  default := ⟨none, rfl⟩
  uniq := by
    intro a
    cases a with
    | mk x hx =>
      cases x with
      | none => rfl
      | some j => cases hx

/-- The complement of the `none` index in `Option J` is canonically equivalent to `J`. -/
def optionSomeComplementEquiv (J : Type w) :
    {x : Option J // ¬ x = none} ≃ J where
  toFun x :=
    match h : x.1 with
    | none => False.elim (x.2 h)
    | some j => j
  invFun j := ⟨some j, by simp⟩
  left_inv := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact False.elim (hx rfl)
    | some j => rfl
  right_inv := by
    intro j
    rfl

/-- The inverse equivalence, displayed with its `some`-valued map definitionally exposed. -/
def optionSomeComplementEquivInverse (J : Type w) :
    J ≃ {x : Option J // ¬ x = none} where
  toFun j := ⟨some j, by simp⟩
  invFun := optionSomeComplementEquiv J
  left_inv := (optionSomeComplementEquiv J).right_inv
  right_inv := (optionSomeComplementEquiv J).left_inv

theorem optionSomeComplementEquiv_apply_some {J : Type w} (j : J) :
    optionSomeComplementEquiv J ⟨some j, by simp⟩ = j :=
  rfl

theorem optionSomeComplementEquiv_symm_apply {J : Type w} (j : J) :
    (optionSomeComplementEquiv J).symm j = ⟨some j, by simp⟩ :=
  rfl

theorem optionSomeComplementEquiv_value_eq_some {J : Type w}
    (x : {x : Option J // ¬ x = none}) :
    x.val = some (optionSomeComplementEquiv J x) := by
  cases x with
  | mk x hx =>
  cases x with
  | none => exact False.elim (hx rfl)
  | some j => rfl

/--
The complement subproduct can be reindexed along `optionSomeComplementEquiv` once its family is
written through that equivalence. The remaining packaging step is to identify this displayed family
with the original complement family `fun i => K i.val`.
-/
noncomputable def complementTailReindexIso {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct (optionTail C K)]
    [HasProduct (optionTail C K ∘ optionSomeComplementEquiv J)] :
    ∏ᶜ (optionTail C K ∘ optionSomeComplementEquiv J) ≅
      ∏ᶜ (optionTail C K) :=
  Limits.Pi.reindex (optionSomeComplementEquiv J) (optionTail C K)

omit [HasBinaryBiproducts C] in
/-- W149's displayed tail family directly supplies W151's named `optionTail` product. -/
theorem optionTailHasProduct_of_someTail {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct (fun j : J => K (some j))] :
    HasProduct (optionTail C K) := by
  simpa [optionTail] using (inferInstance : HasProduct (fun j : J => K (some j)))

omit [HasBinaryBiproducts C] in
/--
The complement subproduct over `{x : Option J // x != none}` is available from the named tail
product by reindexing along `optionSomeComplementEquiv`.
-/
theorem complementSubproductHasProduct_of_optionTail {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct (optionTail C K)] :
    HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val) :=
  hasProduct_of_equiv_of_iso (optionTail C K)
    (fun i : {x : Option J // ¬ x = none} => K i.val)
    (optionSomeComplementEquiv J)
    (fun i => eqToIso (by
      change K i.val = K (some ((optionSomeComplementEquiv J) i))
      rw [optionSomeComplementEquiv_value_eq_some (J := J) i]))

omit [HasBinaryBiproducts C] in
/--
Combined packaging used at W149-style call sites: the tail `HasProduct` hypothesis also provides
the complement-subtype product required by the W151 fan construction.
-/
theorem complementSubproductHasProduct_of_someTail {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct (fun j : J => K (some j))] :
    HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val) := by
  letI : HasProduct (optionTail C K) := optionTailHasProduct_of_someTail C K
  exact complementSubproductHasProduct_of_optionTail C K

omit [HasBinaryBiproducts C] in
/-- W149's displayed degreewise tail family directly supplies W151's named tail-degree product. -/
theorem optionTailDegreeHasProduct_of_someTailDegree {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun j : J => (K (some j)).X n)] :
    HasProduct (optionTailDegree C K n) := by
  simpa [optionTailDegree] using
    (inferInstance : HasProduct (fun j : J => (K (some j)).X n))

omit [HasBinaryBiproducts C] in
/--
The degreewise complement subproduct is available from the named tail-degree product by
reindexing along `optionSomeComplementEquiv`.
-/
theorem complementSubproductDegreeHasProduct_of_optionTailDegree {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (optionTailDegree C K n)] :
    HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n) :=
  hasProduct_of_equiv_of_iso (optionTailDegree C K n)
    (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
    (optionSomeComplementEquiv J)
    (fun i => eqToIso (by
      change (K i.val).X n = (K (some ((optionSomeComplementEquiv J) i))).X n
      rw [optionSomeComplementEquiv_value_eq_some (J := J) i]))

omit [HasBinaryBiproducts C] in
/--
Degreewise call-site packaging: the displayed degreewise `some`-tail product hypothesis also
provides the complement-subtype product required by the W151 fan construction.
-/
theorem complementSubproductDegreeHasProduct_of_someTailDegree {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun j : J => (K (some j)).X n)] :
    HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n) := by
  letI : HasProduct (optionTailDegree C K n) :=
    optionTailDegreeHasProduct_of_someTailDegree C K n
  exact complementSubproductDegreeHasProduct_of_optionTailDegree C K n

/--
The product-object decomposition needed by the finite exact-acyclic product induction:
an `Option J` product of cochain complexes should be the binary biproduct of the `none` complex
and the product over the `some` tail.
-/
abbrev OptionProductIsoBiprod :=
  ∀ (J : Type w)
    (K : Option J → CochainComplex C ℤ) [HasProduct K] [HasProduct (optionTail C K)],
      ∏ᶜ K ≅ K none ⊞ ∏ᶜ (optionTail C K)

/--
Generic cone-point uniqueness conversion: a limiting binary fan over `X,Y` has its point
canonically isomorphic to the selected binary biproduct object.
-/
noncomputable def binaryFanLimitPointIsoBiprod
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {X Y : D} [HasBinaryBiproduct X Y]
    (F : BinaryFan X Y) (hF : IsLimit F) :
    F.pt ≅ X ⊞ Y :=
  hF.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y)

/--
Convert a complex-level limiting Option-product binary fan into the biproduct-shaped product
object iso required by finite-product closure.
-/
noncomputable def optionProductIsoBiprod_of_complexFanIsLimit
    {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K] [HasProduct (optionTail C K)]
    [HasBinaryBiproduct (K none) (∏ᶜ (optionTail C K))]
    (F : BinaryFan (K none) (∏ᶜ (optionTail C K)))
    (hpt : F.pt = ∏ᶜ K)
    (hFan : IsLimit F) :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (optionTail C K) :=
  (eqToIso hpt.symm).trans (binaryFanLimitPointIsoBiprod F hFan)

/-- Transport a limiting binary fan across an equality of binary fans. -/
def binaryFanIsLimitOfEq {X Y : CochainComplex C ℤ} {s t : BinaryFan X Y}
    (h : s = t) (ht : IsLimit t) : IsLimit s := by
  subst h
  exact ht

/-- Transport a limiting cone across an equality of cones. -/
def coneIsLimitOfEq {J : Type w} [Category J]
    {F : J ⥤ CochainComplex C ℤ} {s t : Cone F}
    (h : s = t) (ht : IsLimit t) : IsLimit s := by
  subst h
  exact ht

/--
The degreewise product split exposed by mathlib's `PiProd` API.  It splits the product over
`Option J` into the subproduct over entries equal to `none` and the complementary subproduct.
-/
noncomputable abbrev optionProductBinaryFan {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)] :
    BinaryFan
      (∏ᶜ (fun i : {x : Option J // x = none} => K i.val))
      (∏ᶜ (fun i : {x : Option J // ¬ x = none} => K i.val)) :=
  Pi.binaryFanOfProp K (fun x : Option J => x = none)

/-- The `none` subproduct of cochain complexes is canonically the `none` complex. -/
noncomputable def noneSubproductIso {J : Type w}
    (K : Option J → CochainComplex C ℤ) :
    ∏ᶜ (fun i : {x : Option J // x = none} => K i.val) ≅ K none :=
  Limits.productUniqueIso (fun i : {x : Option J // x = none} => K i.val)

/-- The complement subproduct of cochain complexes reindexed to the `some` tail. -/
noncomputable def complementSubproductReindexIso {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    ∏ᶜ (fun i : {x : Option J // ¬ x = none} => K i.val) ≅ ∏ᶜ (optionTail C K) :=
  by
    letI : HasProduct
        ((fun i : {x : Option J // ¬ x = none} => K i.val) ∘
          ⇑(optionSomeComplementEquivInverse J)) := by
      change HasProduct (optionTail C K)
      infer_instance
    exact (Limits.Pi.reindex (optionSomeComplementEquivInverse J)
      (fun i : {x : Option J // ¬ x = none} => K i.val)).symm

/--
The complex-level binary fan after composing the raw `Option` product split with the singleton
reduction on the `none` side and the complement reindexing on the `some` side.
-/
noncomputable def transportedBinaryFan {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    BinaryFan (K none) (∏ᶜ (optionTail C K)) :=
  BinaryFan.mk
    ((optionProductBinaryFan C K).fst ≫ (noneSubproductIso C K).hom)
    ((optionProductBinaryFan C K).snd ≫ (complementSubproductReindexIso C K).hom)

omit [HasBinaryBiproducts C] in
theorem transportedBinaryFan_pt {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    (transportedBinaryFan C K).pt = ∏ᶜ K :=
  rfl

omit [HasBinaryBiproducts C] in
theorem transportedBinaryFan_fst {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    (transportedBinaryFan C K).fst =
      (optionProductBinaryFan C K).fst ≫ (noneSubproductIso C K).hom :=
  rfl

omit [HasBinaryBiproducts C] in
theorem transportedBinaryFan_snd {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    (transportedBinaryFan C K).snd =
      (optionProductBinaryFan C K).snd ≫ (complementSubproductReindexIso C K).hom :=
  rfl

/--
Assemble degreewise limit proofs for the evaluated transported Option-product fan into the
complex-level limiting fan.
-/
noncomputable def transportedBinaryFanIsLimit_of_eval
    {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)]
    (hEval :
      ∀ n : ℤ,
        IsLimit
          ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapCone
            (transportedBinaryFan C K))) :
    IsLimit (transportedBinaryFan C K) :=
  HomologicalComplex.isLimitOfEval (pair (K none) (∏ᶜ (optionTail C K)))
    (transportedBinaryFan C K) hEval

/--
Specialization of the cone-point uniqueness conversion to W151's transported complex fan.
-/
noncomputable def optionProductIsoBiprod_of_transportedFan
    {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)]
    [HasBinaryBiproduct (K none) (∏ᶜ (optionTail C K))]
    (hFan : IsLimit (transportedBinaryFan C K)) :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (optionTail C K) :=
  optionProductIsoBiprod_of_complexFanIsLimit C K
    (transportedBinaryFan C K)
    (transportedBinaryFan_pt C K)
    hFan

/--
Consumer wrapper: degreewise limit proofs for the evaluated transported fan already imply the
biproduct-shaped Option-product iso.
-/
noncomputable def optionProductIsoBiprod_of_evaluatedFan
    {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)]
    [HasBinaryBiproduct (K none) (∏ᶜ (optionTail C K))]
    (hEval :
      ∀ n : ℤ,
        IsLimit
          ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapCone
            (transportedBinaryFan C K))) :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (optionTail C K) :=
  optionProductIsoBiprod_of_transportedFan C K
    (transportedBinaryFanIsLimit_of_eval C K hEval)

noncomputable abbrev optionProductSplitPair {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct (optionTail C K)] :
    Discrete WalkingPair ⥤ CochainComplex C ℤ :=
  pair (K none) (∏ᶜ (optionTail C K))

/-- The same split at a fixed cochain degree. -/
noncomputable abbrev optionProductDegreeBinaryFan {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)] :
    BinaryFan
      (∏ᶜ (fun i : {x : Option J // x = none} => (K i.val).X n))
      (∏ᶜ (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)) :=
  Pi.binaryFanOfProp (fun i : Option J => (K i).X n) (fun x : Option J => x = none)

/-- The singleton reduction, specialized to a fixed cochain degree. -/
noncomputable def noneSubproductDegreeIso {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ) :
    ∏ᶜ (fun i : {x : Option J // x = none} => (K i.val).X n) ≅ (K none).X n :=
  Limits.productUniqueIso (fun i : {x : Option J // x = none} => (K i.val).X n)

/-- The complement reindexing, specialized to a fixed cochain degree. -/
noncomputable def complementSubproductDegreeReindexIso {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] :
    ∏ᶜ (fun i : {x : Option J // ¬ x = none} => (K i.val).X n) ≅
      ∏ᶜ (optionTailDegree C K n) :=
  by
    letI : HasProduct
        ((fun i : {x : Option J // ¬ x = none} => (K i.val).X n) ∘
          ⇑(optionSomeComplementEquivInverse J)) := by
      change HasProduct (optionTailDegree C K n)
      infer_instance
    exact (Limits.Pi.reindex (optionSomeComplementEquivInverse J)
      (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)).symm

noncomputable def optionProductDegreeTransportedBinaryFan {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] :
    BinaryFan ((K none).X n) (∏ᶜ (optionTailDegree C K n)) :=
  BinaryFan.mk
    ((optionProductDegreeBinaryFan C K n).fst ≫ (noneSubproductDegreeIso C K n).hom)
    ((optionProductDegreeBinaryFan C K n).snd ≫
      (complementSubproductDegreeReindexIso C K n).hom)

omit [HasBinaryBiproducts C] in
theorem optionProductDegreeTransportedBinaryFan_pt {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] :
    (optionProductDegreeTransportedBinaryFan C K n).pt =
      ∏ᶜ (fun i : Option J => (K i).X n) :=
  rfl

omit [HasBinaryBiproducts C] in
theorem optionProductDegreeTransportedBinaryFan_fst {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] :
    (optionProductDegreeTransportedBinaryFan C K n).fst =
      (optionProductDegreeBinaryFan C K n).fst ≫ (noneSubproductDegreeIso C K n).hom :=
  rfl

omit [HasBinaryBiproducts C] in
theorem optionProductDegreeTransportedBinaryFan_snd {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] :
    (optionProductDegreeTransportedBinaryFan C K n).snd =
      (optionProductDegreeBinaryFan C K n).snd ≫
        (complementSubproductDegreeReindexIso C K n).hom :=
  rfl

/-- The transported fixed-degree fan remains limiting, by reducing back to `Pi.binaryFanOfProp`. -/
noncomputable def optionProductDegreeTransportedBinaryFanIsLimit {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)]
    [∀ x : Option J, Decidable (x = none)] :
    IsLimit (optionProductDegreeTransportedBinaryFan C K n) := by
  let s₀ := optionProductDegreeBinaryFan C K n
  let eL := noneSubproductDegreeIso C K n
  let eR := complementSubproductDegreeReindexIso C K n
  let h₀ : IsLimit s₀ :=
    Pi.binaryFanOfPropIsLimit (fun i : Option J => (K i).X n)
      (fun x : Option J => x = none)
  refine BinaryFan.IsLimit.mk _
    (fun {T} f g => h₀.lift (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv))) ?_ ?_ ?_
  · intro T f g
    have hfac :=
      h₀.fac (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ⟨WalkingPair.left⟩
    simp [optionProductDegreeTransportedBinaryFan, s₀, eL, eR,
      Category.assoc]
  · intro T f g
    have hfac :=
      h₀.fac (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ⟨WalkingPair.right⟩
    simp [optionProductDegreeTransportedBinaryFan, s₀, eL, eR,
      Category.assoc]
  · intro T f g m hm₁ hm₂
    have hm₁' : m ≫ s₀.fst ≫ eL.hom = f := by
      simpa [optionProductDegreeTransportedBinaryFan, s₀, eL, eR, Category.assoc] using hm₁
    have hm₂' : m ≫ s₀.snd ≫ eR.hom = g := by
      simpa [optionProductDegreeTransportedBinaryFan, s₀, eL, eR, Category.assoc] using hm₂
    have hfac₁ :
        h₀.lift (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ≫ s₀.fst = f ≫ eL.inv := by
      simp
    have hfac₂ :
        h₀.lift (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ≫ s₀.snd = g ≫ eR.inv := by
      simp
    have hm₁base : m ≫ s₀.fst = f ≫ eL.inv := by
      calc
        m ≫ s₀.fst = (m ≫ s₀.fst ≫ eL.hom) ≫ eL.inv := by simp [Category.assoc]
        _ = f ≫ eL.inv := by rw [hm₁']
    have hm₂base : m ≫ s₀.snd = g ≫ eR.inv := by
      calc
        m ≫ s₀.snd = (m ≫ s₀.snd ≫ eR.hom) ≫ eR.inv := by simp [Category.assoc]
        _ = g ≫ eR.inv := by rw [hm₂']
    apply BinaryFan.IsLimit.hom_ext h₀
    · exact hm₁base.trans hfac₁.symm
    · exact hm₂base.trans hfac₂.symm

/--
Evaluation of a selected product complex is canonically the selected product of the evaluated
family at a fixed cochain degree.
-/
noncomputable def evalProductPointIso {I : Type w}
    (K : I → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [∀ m : ℤ, HasProduct (fun i : I => (K i).X m)] :
    ((∏ᶜ K).X n) ≅ ∏ᶜ (fun i : I => (K i).X n) := by
  letI :
      HasProduct
        (fun i : I => (HomologicalComplex.eval C (ComplexShape.up ℤ) n).obj
          (K i)) := by
    simpa using (inferInstance : HasProduct (fun i : I => (K i).X n))
  letI :
      ∀ m : ℤ,
        HasLimit ((Discrete.functor K) ⋙
          HomologicalComplex.eval C (ComplexShape.up ℤ) m) := by
    intro m
    let e : Discrete.functor (fun i : I => (K i).X m) ≅
        (Discrete.functor K) ⋙
          HomologicalComplex.eval C (ComplexShape.up ℤ) m :=
      Discrete.natIso (fun _ => Iso.refl _)
    exact hasLimit_of_iso e
  change (HomologicalComplex.eval C (ComplexShape.up ℤ) n).obj (∏ᶜ K) ≅
    ∏ᶜ (fun i : I => (HomologicalComplex.eval C (ComplexShape.up ℤ) n).obj
      (K i))
  exact PreservesProduct.iso (HomologicalComplex.eval C (ComplexShape.up ℤ) n) K

omit [HasBinaryBiproducts C] in
@[reassoc]
theorem evalProductPointIso_hom_π {I : Type w}
    (K : I → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [∀ m : ℤ, HasProduct (fun i : I => (K i).X m)] (i : I) :
    (evalProductPointIso C K n).hom ≫ Pi.π (fun i : I => (K i).X n) i =
      (Pi.π K i).f n := by
  letI :
      HasProduct
        (fun i : I => (HomologicalComplex.eval C (ComplexShape.up ℤ) n).obj
          (K i)) := by
    simpa using (inferInstance : HasProduct (fun i : I => (K i).X n))
  dsimp [evalProductPointIso]
  simpa using
    (piComparison_comp_π (HomologicalComplex.eval C (ComplexShape.up ℤ) n) K i)

/--
Evaluation of the selected tail product complex is canonically the selected product of the
evaluated tail family.
-/
noncomputable def evalTailProductPointIso {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] :
    ((∏ᶜ (optionTail C K)).X n) ≅ ∏ᶜ (optionTailDegree C K n) :=
  evalProductPointIso C (optionTail C K) n

omit [HasBinaryBiproducts C] in
@[reassoc]
theorem evalTailProductPointIso_hom_π {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] (j : J) :
    (evalTailProductPointIso C K n).hom ≫ Pi.π (optionTailDegree C K n) j =
      (Pi.π (optionTail C K) j).f n := by
  simpa [evalTailProductPointIso, optionTailDegree, optionTail] using
    (evalProductPointIso_hom_π C (optionTail C K) n j)

/--
The complex-level transported Option product fan evaluated at a fixed cochain degree and displayed
as a binary fan in the base category.
-/
noncomputable def evaluatedOptionProductComplexBinaryFan {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    BinaryFan ((K none).X n) ((∏ᶜ (optionTail C K)).X n) :=
  BinaryFan.mk
    ((transportedBinaryFan C K).fst.f n)
    ((transportedBinaryFan C K).snd.f n)

/--
The degreewise transported fan, with its cone point and right target transported back to the
objects appearing in the evaluated complex-level fan.
-/
noncomputable def optionProductDegreeFanWithEvaluatedTargets {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] :
    BinaryFan ((K none).X n) ((∏ᶜ (optionTail C K)).X n) :=
  BinaryFan.mk
    ((evalProductPointIso C K n).hom ≫
      (optionProductDegreeTransportedBinaryFan C K n).fst)
    ((evalProductPointIso C K n).hom ≫
      (optionProductDegreeTransportedBinaryFan C K n).snd ≫
      (evalTailProductPointIso C K n).inv)

/--
The transported degree fan remains limiting after moving its cone point and right target back to
the evaluated complex-level objects.
-/
noncomputable def optionProductDegreeFanWithEvaluatedTargetsIsLimit {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)]
    [∀ x : Option J, Decidable (x = none)] :
    IsLimit (optionProductDegreeFanWithEvaluatedTargets C K n) := by
  let s := optionProductDegreeTransportedBinaryFan C K n
  let eP := evalProductPointIso C K n
  let eR := evalTailProductPointIso C K n
  let hs : IsLimit s := optionProductDegreeTransportedBinaryFanIsLimit C K n
  let α :
      pair ((K none).X n) (∏ᶜ (optionTailDegree C K n)) ≅
        pair ((K none).X n) ((∏ᶜ (optionTail C K)).X n) :=
    mapPairIso (Iso.refl _) eR.symm
  let hs' : IsLimit ((Cone.postcompose α.hom).obj s) :=
    (IsLimit.postcomposeHomEquiv α s).symm hs
  exact IsLimit.ofIsoLimit hs' <|
    Cone.ext_inv eP.symm (by
      intro j
      rcases j with ⟨j⟩
      cases j
      · simp [Cone.postcompose, optionProductDegreeFanWithEvaluatedTargets, s, eP, eR, α,
          mapPairIso]
      · simp [Cone.postcompose, optionProductDegreeFanWithEvaluatedTargets, s, eP, eR, α,
          mapPairIso])

/-- The remaining typed comparison before transporting the degreewise `IsLimit` proof. -/
abbrev EvaluatedDegreeFanComparison {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] : Prop :=
  evaluatedOptionProductComplexBinaryFan C K n =
    optionProductDegreeFanWithEvaluatedTargets C K n

/-- The left-leg equality exposed by binary-fan extensionality. -/
abbrev EvaluatedDegreeFanComparisonLeft {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] : Prop :=
  (evaluatedOptionProductComplexBinaryFan C K n).fst =
    (optionProductDegreeFanWithEvaluatedTargets C K n).fst

/-- The right-leg equality exposed by binary-fan extensionality. -/
abbrev EvaluatedDegreeFanComparisonRight {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] : Prop :=
  (evaluatedOptionProductComplexBinaryFan C K n).snd =
    (optionProductDegreeFanWithEvaluatedTargets C K n).snd

omit [HasBinaryBiproducts C] in
/--
After composing the degreewise/evaluated-target right leg with the comparison isomorphism back to
the evaluated tail product, the trailing `evalTailProductPointIso.inv` cancels.
-/
theorem optionProductDegreeFanWithEvaluatedTargets_snd_evalTail_hom_π
    {J : Type w} (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] (j : J) :
    (optionProductDegreeFanWithEvaluatedTargets C K n).snd ≫
        (evalTailProductPointIso C K n).hom ≫ Pi.π (optionTailDegree C K n) j =
      (evalProductPointIso C K n).hom ≫
        (optionProductDegreeTransportedBinaryFan C K n).snd ≫
          Pi.π (optionTailDegree C K n) j := by
  simp [optionProductDegreeFanWithEvaluatedTargets, Category.assoc]

omit [HasBinaryBiproducts C] in
/--
The degree-side right leg projected to a tail component is the underlying `Pi.binaryFanOfProp`
right leg projected to the corresponding complement component.
-/
@[reassoc]
theorem optionProductDegreeTransportedBinaryFan_snd_π
    {J : Type w} (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] (j : J) :
    (optionProductDegreeTransportedBinaryFan C K n).snd ≫
        Pi.π (optionTailDegree C K n) j =
      (optionProductDegreeBinaryFan C K n).snd ≫
        Pi.π (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
          ((optionSomeComplementEquiv J).symm j) := by
  dsimp [optionProductDegreeTransportedBinaryFan, complementSubproductDegreeReindexIso]
  letI : HasProduct
      ((fun i : {x : Option J // ¬ x = none} => (K i.val).X n) ∘
        ⇑(optionSomeComplementEquivInverse J)) := by
    change HasProduct (optionTailDegree C K n)
    infer_instance
  have hπ :
      (Pi.reindex (optionSomeComplementEquivInverse J)
          (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)).inv ≫
          Pi.π (optionTailDegree C K n) j =
        Pi.π (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
          ((optionSomeComplementEquiv J).symm j) := by
    change
      (Pi.reindex (optionSomeComplementEquivInverse J)
          (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)).inv ≫
          Pi.π ((fun i : {x : Option J // ¬ x = none} => (K i.val).X n) ∘
            ⇑(optionSomeComplementEquivInverse J)) j =
        Pi.π (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
          (optionSomeComplementEquivInverse J j)
    exact Pi.reindex_inv_π (optionSomeComplementEquivInverse J)
      (fun i : {x : Option J // ¬ x = none} => (K i.val).X n) j
  simpa [Category.assoc] using
    congrArg (fun q => (optionProductDegreeBinaryFan C K n).snd ≫ q) hπ

omit [HasBinaryBiproducts C] in
/--
The complex-side right leg projected through evaluation and the tail comparison reduces to the
matching complex product projection at the complement index.
-/
theorem complementSubproductReindexIso_hom_evalTail_hom_π
    {J : Type w} (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] (j : J) :
    ((complementSubproductReindexIso C K).hom.f n) ≫
        (evalTailProductPointIso C K n).hom ≫ Pi.π (optionTailDegree C K n) j =
      (Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
        ((optionSomeComplementEquiv J).symm j)).f n := by
  simp only [complementSubproductReindexIso, evalTailProductPointIso_hom_π]
  letI : HasProduct
      ((fun i : {x : Option J // ¬ x = none} => K i.val) ∘
        ⇑(optionSomeComplementEquivInverse J)) := by
    change HasProduct (optionTail C K)
    infer_instance
  have hπ :
      (Pi.reindex (optionSomeComplementEquivInverse J)
          (fun i : {x : Option J // ¬ x = none} => K i.val)).inv ≫
          Pi.π (optionTail C K) j =
        Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
          ((optionSomeComplementEquiv J).symm j) := by
    change
      (Pi.reindex (optionSomeComplementEquivInverse J)
          (fun i : {x : Option J // ¬ x = none} => K i.val)).inv ≫
          Pi.π ((fun i : {x : Option J // ¬ x = none} => K i.val) ∘
            ⇑(optionSomeComplementEquivInverse J)) j =
        Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
          (optionSomeComplementEquivInverse J j)
    exact Pi.reindex_inv_π (optionSomeComplementEquivInverse J)
      (fun i : {x : Option J // ¬ x = none} => K i.val) j
  simpa [HomologicalComplex.comp_f] using congrArg (fun q => q.f n) hπ

omit [HasBinaryBiproducts C] in
/--
The complex-side evaluated right leg has the same tail-component normal form as the complex
product split projected at the corresponding complement index.
-/
theorem evaluatedOptionProductComplexBinaryFan_snd_evalTail_hom_π
    {J : Type w} (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] (j : J) :
    (evaluatedOptionProductComplexBinaryFan C K n).snd ≫
        (evalTailProductPointIso C K n).hom ≫ Pi.π (optionTailDegree C K n) j =
      (optionProductBinaryFan C K).snd.f n ≫
        (Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
          ((optionSomeComplementEquiv J).symm j)).f n := by
  dsimp [evaluatedOptionProductComplexBinaryFan, transportedBinaryFan]
  simpa [Category.assoc] using
    congrArg
      (fun q => (optionProductBinaryFan C K).snd.f n ≫ q)
      (complementSubproductReindexIso_hom_evalTail_hom_π C K n j)

omit [HasBinaryBiproducts C] in
/-- The right leg of the evaluated-degree fan comparison. -/
theorem evaluatedDegreeFanComparisonRight_direct {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] :
    EvaluatedDegreeFanComparisonRight C K n := by
  apply (cancel_mono (evalTailProductPointIso C K n).hom).mp
  apply Pi.hom_ext
  intro j
  have hright_complex :
      (Pi.binaryFanOfProp K (fun x : Option J => x = none)).snd ≫
          Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
            ((optionSomeComplementEquiv J).symm j) =
        Pi.π K ((optionSomeComplementEquiv J).symm j).val := by
    simp [Pi.binaryFanOfProp]
  have hright_complex_degree :
      (Pi.binaryFanOfProp K (fun x : Option J => x = none)).snd.f n ≫
          (Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
            ((optionSomeComplementEquiv J).symm j)).f n =
        (Pi.π K ((optionSomeComplementEquiv J).symm j).val).f n := by
    simpa using
      congrArg
        (fun f :
          ∏ᶜ K ⟶ K ((optionSomeComplementEquiv J).symm j).val => f.f n)
        hright_complex
  have hright_degree :
      (Pi.binaryFanOfProp (fun i : Option J => (K i).X n) (fun x : Option J => x = none)).snd ≫
          Pi.π (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
            ((optionSomeComplementEquiv J).symm j) =
        Pi.π (fun i : Option J => (K i).X n)
          ((optionSomeComplementEquiv J).symm j).val := by
    simp [Pi.binaryFanOfProp]
  have hright_complex_degree_limit :
      (Pi.binaryFanOfProp K (fun x : Option J => x = none)).snd.f n ≫
          (limit.π (Discrete.functor
            (fun i : {x : Option J // ¬ x = none} => K i.val))
            ⟨(optionSomeComplementEquiv J).symm j⟩).f n =
        (Pi.π K ((optionSomeComplementEquiv J).symm j).val).f n := by
    simpa [Pi.π] using hright_complex_degree
  have hright_degree_limit :
      (Pi.binaryFanOfProp (fun i : Option J => (K i).X n) (fun x : Option J => x = none)).snd ≫
          limit.π (Discrete.functor
            (fun i : {x : Option J // ¬ x = none} => (K i.val).X n))
            ⟨(optionSomeComplementEquiv J).symm j⟩ =
        Pi.π (fun i : Option J => (K i).X n)
          ((optionSomeComplementEquiv J).symm j).val := by
    simpa [Pi.π] using hright_degree
  have hcomplex :
      ((evaluatedOptionProductComplexBinaryFan C K n).snd ≫
          (evalTailProductPointIso C K n).hom) ≫
        Pi.π (optionTailDegree C K n) j =
        (optionProductBinaryFan C K).snd.f n ≫
          (Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
            ((optionSomeComplementEquiv J).symm j)).f n := by
    simpa [Category.assoc] using
      evaluatedOptionProductComplexBinaryFan_snd_evalTail_hom_π C K n j
  have hdegree_fan :
      ((optionProductDegreeFanWithEvaluatedTargets C K n).snd ≫
          (evalTailProductPointIso C K n).hom) ≫
        Pi.π (optionTailDegree C K n) j =
        ((evalProductPointIso C K n).hom ≫
          (optionProductDegreeTransportedBinaryFan C K n).snd) ≫
            Pi.π (optionTailDegree C K n) j := by
    simpa [Category.assoc] using
      optionProductDegreeFanWithEvaluatedTargets_snd_evalTail_hom_π C K n j
  have htransport :
      ((evalProductPointIso C K n).hom ≫
          (optionProductDegreeTransportedBinaryFan C K n).snd) ≫
            Pi.π (optionTailDegree C K n) j =
        ((evalProductPointIso C K n).hom ≫
          (optionProductDegreeBinaryFan C K n).snd) ≫
            Pi.π (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
              ((optionSomeComplementEquiv J).symm j) := by
    exact
      (Category.assoc (evalProductPointIso C K n).hom
        (optionProductDegreeTransportedBinaryFan C K n).snd
        (Pi.π (optionTailDegree C K n) j)).trans
        ((congrArg (fun f => (evalProductPointIso C K n).hom ≫ f)
          (optionProductDegreeTransportedBinaryFan_snd_π C K n j)).trans
          (Category.assoc (evalProductPointIso C K n).hom
            (optionProductDegreeBinaryFan C K n).snd
            (Pi.π (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
              ((optionSomeComplementEquiv J).symm j))).symm)
  have hmain :
      (optionProductBinaryFan C K).snd.f n ≫
          (Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
            ((optionSomeComplementEquiv J).symm j)).f n =
        ((evalProductPointIso C K n).hom ≫
          (optionProductDegreeBinaryFan C K n).snd) ≫
            Pi.π (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)
              ((optionSomeComplementEquiv J).symm j) := by
    refine hright_complex_degree_limit.trans ?_
    refine (evalProductPointIso_hom_π C K n
      ((optionSomeComplementEquiv J).symm j).val).symm.trans ?_
    simpa [Category.assoc] using
      congrArg (fun f => (evalProductPointIso C K n).hom ≫ f)
        hright_degree_limit.symm
  exact hcomplex.trans (hmain.trans (hdegree_fan.trans htransport).symm)

omit [HasBinaryBiproducts C] in
/-- The left leg of the evaluated-degree fan comparison. -/
theorem evaluatedDegreeFanComparisonLeft_direct {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] :
    EvaluatedDegreeFanComparisonLeft C K n := by
  have hleft_complex :
      (Pi.binaryFanOfProp K (fun x : Option J => x = none)).fst ≫
          Pi.π (fun i : {x : Option J // x = none} => K i.val) default =
        Pi.π K (default : {x : Option J // x = none}).val := by
    simp [Pi.binaryFanOfProp]
  have hleft_degree :
      (Pi.binaryFanOfProp K (fun x : Option J => x = none)).fst.f n ≫
          (Pi.π (fun i : {x : Option J // x = none} => K i.val) default).f n =
        (Pi.π K (default : {x : Option J // x = none}).val).f n := by
    simpa using
      congrArg
        (fun f :
          ∏ᶜ K ⟶ K (default : {x : Option J // x = none}).val => f.f n)
        hleft_complex
  have hright_degree :
      (Pi.binaryFanOfProp (fun i : Option J => (K i).X n) (fun x : Option J => x = none)).fst ≫
          Pi.π (fun i : {x : Option J // x = none} => (K i.val).X n) default =
        Pi.π (fun i : Option J => (K i).X n)
          (default : {x : Option J // x = none}).val := by
    simp [Pi.binaryFanOfProp]
  have hleft_degree_limit :
      (Pi.binaryFanOfProp K (fun x : Option J => x = none)).fst.f n ≫
          (limit.π (Discrete.functor fun i : {x : Option J // x = none} => K i.val)
            ⟨(default : {x : Option J // x = none})⟩).f n =
        (Pi.π K (default : {x : Option J // x = none}).val).f n := by
    simpa [Pi.π] using hleft_degree
  have hright_degree_limit :
      (Pi.binaryFanOfProp (fun i : Option J => (K i).X n) (fun x : Option J => x = none)).fst ≫
          limit.π (Discrete.functor fun i : {x : Option J // x = none} => (K i.val).X n)
            ⟨(default : {x : Option J // x = none})⟩ =
        Pi.π (fun i : Option J => (K i).X n)
          (default : {x : Option J // x = none}).val := by
    simpa [Pi.π] using hright_degree
  simp only [EvaluatedDegreeFanComparisonLeft, evaluatedOptionProductComplexBinaryFan,
    transportedBinaryFan, optionProductBinaryFan, Functor.const_obj_obj, pair_obj_left,
    noneSubproductIso, productUniqueIso_hom, pair_obj_right, BinaryFan.mk_pt,
    BinaryFan.mk_fst, HomologicalComplex.comp_f, BinaryFan.mk_snd,
    optionProductDegreeFanWithEvaluatedTargets, optionProductDegreeTransportedBinaryFan,
    optionProductDegreeBinaryFan, noneSubproductDegreeIso]
  refine hleft_degree_limit.trans ?_
  refine (evalProductPointIso_hom_π C K n
    (default : {x : Option J // x = none}).val).symm.trans ?_
  have h := congrArg (fun f => (evalProductPointIso C K n).hom ≫ f)
    hright_degree_limit.symm
  convert h using 1
  have hdefault : (default : Discrete {x : Option J // x = none}) =
      ⟨(default : {x : Option J // x = none})⟩ := Subsingleton.elim _ _
  cases hdefault
  rfl

omit [HasBinaryBiproducts C] in
/--
Binary-fan extensionality reduces the evaluated fan comparison to exactly the two projection legs.
-/
theorem evaluatedDegreeFanComparison_of_left_right {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)]
    (hleft : EvaluatedDegreeFanComparisonLeft C K n)
    (hright : EvaluatedDegreeFanComparisonRight C K n) :
    EvaluatedDegreeFanComparison C K n := by
  dsimp [EvaluatedDegreeFanComparison, EvaluatedDegreeFanComparisonLeft,
    EvaluatedDegreeFanComparisonRight, evaluatedOptionProductComplexBinaryFan,
    optionProductDegreeFanWithEvaluatedTargets] at hleft hright ⊢
  rw [hleft, hright]

omit [HasBinaryBiproducts C] in
/--
After `evaluatedDegreeFanComparisonLeft_direct`, only the right leg remains to prove the full
evaluated fan comparison.
-/
theorem evaluatedDegreeFanComparison_of_right {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)]
    (hright : EvaluatedDegreeFanComparisonRight C K n) :
    EvaluatedDegreeFanComparison C K n :=
  evaluatedDegreeFanComparison_of_left_right C K n
    (evaluatedDegreeFanComparisonLeft_direct C K n) hright

omit [HasBinaryBiproducts C] in
/-- Direct evaluated fan comparison, after closing both binary-fan projection legs. -/
theorem evaluatedDegreeFanComparison_direct {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)] :
    EvaluatedDegreeFanComparison C K n :=
  evaluatedDegreeFanComparison_of_right C K n
    (evaluatedDegreeFanComparisonRight_direct C K n)

/--
The evaluated complex-level Option product binary fan is limiting after transporting the
evaluated-target degree fan limit across the direct evaluated fan comparison.
-/
noncomputable def evaluatedOptionProductComplexBinaryFanIsLimit_direct {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)]
    [∀ x : Option J, Decidable (x = none)] :
    IsLimit (evaluatedOptionProductComplexBinaryFan C K n) := by
  rw [evaluatedDegreeFanComparison_direct C K n]
  exact optionProductDegreeFanWithEvaluatedTargetsIsLimit C K n

/--
The displayed evaluated complex-level binary fan is equivalent, for limit purposes, to the exact
cone produced by `Functor.mapCone`. The cones live over definitionally different displays of the
same binary diagram, so the bridge is an `IsLimit` equivalence rather than a cone equality.
-/
noncomputable def evaluatedOptionProductComplexBinaryFanIsLimitEquivEvalMapCone {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    IsLimit
        ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapCone
          (transportedBinaryFan C K)) ≃
      IsLimit (evaluatedOptionProductComplexBinaryFan C K n) := by
  simpa [evaluatedOptionProductComplexBinaryFan, transportedBinaryFan]
    using
      isLimitMapConeBinaryFanEquiv
        (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
        (transportedBinaryFan C K).fst
        (transportedBinaryFan C K).snd

/--
The exact evaluated `Functor.mapCone` consumer follows by applying the displayed-binary-fan
equivalence backwards to the direct evaluated binary fan limit.
-/
noncomputable def transportedBinaryFanEvalIsLimit_direct {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)]
    [∀ x : Option J, Decidable (x = none)] :
    IsLimit
      ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapCone
        (transportedBinaryFan C K)) :=
  (evaluatedOptionProductComplexBinaryFanIsLimitEquivEvalMapCone C K n).symm
    (evaluatedOptionProductComplexBinaryFanIsLimit_direct C K n)

/--
Package the degreewise mapCone limits into the complex-level transported Option-product binary fan.
-/
noncomputable def transportedBinaryFanIsLimit_direct {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [HasProduct (optionTail C K)]
    [∀ m : ℤ, HasProduct (optionTailDegree C K m)]
    [∀ x : Option J, Decidable (x = none)] :
    IsLimit (transportedBinaryFan C K) :=
  transportedBinaryFanIsLimit_of_eval C K
    (fun n => transportedBinaryFanEvalIsLimit_direct C K n)

/--
Finite-product call-site consumer for the Option induction shape.

This packages the direct fan limit through the existing biproduct-point wrapper and returns the
exact iso shape expected by `FiniteProductOptionDecompositionInput.optionProductIsoBiprod`, with
the remaining product and biproduct instances kept explicit.
-/
noncomputable def optionProductIsoBiprod_direct {J : Type w}
    [Finite J]
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (fun j : J => (K (some j)).X m)]
    [∀ x : Option J, Decidable (x = none)]
    [HasBinaryBiproduct (K none) (∏ᶜ (fun j : J => K (some j)))] :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j)) :=
  optionProductIsoBiprod_of_transportedFan C K
    (transportedBinaryFanIsLimit_direct C K)

/--
Remove the explicit complement-subproduct `HasProduct` requirement from the finite call site.
It is reconstructed from the tail product hypothesis by `optionSomeComplementEquiv`.
-/
noncomputable def optionProductIsoBiprod_tail_direct
    {J : Type w}
    [Finite J]
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (fun j : J => (K (some j)).X m)]
    [∀ x : Option J, Decidable (x = none)]
    [HasBinaryBiproduct (K none) (∏ᶜ (fun j : J => K (some j)))] :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j)) := by
  letI : HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val) :=
    complementSubproductHasProduct_of_someTail C K
  exact optionProductIsoBiprod_direct C K

/--
Remove the explicit degreewise complement-subproduct `HasProduct` family from the finite call
site. It is reconstructed degree by degree from the displayed degreewise tail product hypothesis.
-/
noncomputable def optionProductIsoBiprod_tailDegree_direct
    {J : Type w}
    [Finite J]
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun i : {x : Option J // x = none} => (K i.val).X m)]
    [∀ m : ℤ, HasProduct (fun j : J => (K (some j)).X m)]
    [∀ x : Option J, Decidable (x = none)]
    [HasBinaryBiproduct (K none) (∏ᶜ (fun j : J => K (some j)))] :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j)) := by
  letI : ∀ m : ℤ,
      HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X m) :=
    fun m => complementSubproductDegreeHasProduct_of_someTailDegree C K m
  exact optionProductIsoBiprod_tail_direct C K

/--
Remove the singleton-subproduct product requirements from the finite call site. The index
`{x : Option J // x = none}` is unique, so mathlib's unique-index product instance supplies both
the complex-level and fixed-degree singleton products.
-/
noncomputable def
  optionProductIsoBiprod_singletonTailDegree_direct
    {J : Type w}
    [Finite J]
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun j : J => (K (some j)).X m)]
    [∀ x : Option J, Decidable (x = none)]
    [HasBinaryBiproduct (K none) (∏ᶜ (fun j : J => K (some j)))] :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j)) := by
  letI : HasProduct (fun i : {x : Option J // x = none} => K i.val) :=
    inferInstance
  letI : ∀ m : ℤ,
      HasProduct (fun i : {x : Option J // x = none} => (K i.val).X m) :=
    fun _ => inferInstance
  exact optionProductIsoBiprod_tailDegree_direct C K

/--
Remove the selected binary-biproduct requirement from the finite call site. Binary biproducts in
the cochain-complex category are synthesized from the ambient binary biproducts in `C`.
-/
noncomputable def optionProductIsoBiprod_packaged_direct
    {J : Type w}
    [Finite J]
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m)]
    [∀ m : ℤ, HasProduct (fun j : J => (K (some j)).X m)]
    [∀ x : Option J, Decidable (x = none)] :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j)) := by
  letI : HasBinaryBiproduct (K none) (∏ᶜ (fun j : J => K (some j))) :=
    inferInstance
  exact optionProductIsoBiprod_singletonTailDegree_direct C K

/--
Close the finite Option call-site instance packaging under finite products in the base category.
For finite `J`, `[HasFiniteProducts C]` supplies the degreewise products indexed by both
`Option J` and `J`; the preceding wrappers discharge the singleton, complement, and selected
binary-biproduct requirements.
-/
noncomputable def optionProductIsoBiprod_finite_direct
    {J : Type w}
    [Finite J]
    (K : Option J → CochainComplex C ℤ)
    [HasFiniteProducts C]
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [∀ x : Option J, Decidable (x = none)] :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j)) := by
  letI : ∀ m : ℤ, HasProduct (fun i : Option J => (K i).X m) :=
    fun _ => inferInstance
  letI : ∀ m : ℤ, HasProduct (fun j : J => (K (some j)).X m) :=
    fun _ => inferInstance
  exact optionProductIsoBiprod_packaged_direct C K

end OptionProductDecompositionW151

end LeanLCAExactChallenge
