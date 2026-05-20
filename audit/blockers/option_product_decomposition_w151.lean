import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.PiProd
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
W151 audit: Option product decomposition for cochain-complex products.

The SSoT route selected `degreewise-product-api`.  This file records the concrete product APIs
available for splitting an `Option J`-indexed product into the `none` factor and the `some`
tail, and isolates the remaining constructor needed by W149's finite-product induction route.

This is a frontier/API guard, not a product-success proof.
-/

set_option autoImplicit false

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
          ⇑(optionSomeComplementEquiv J).symm) := by
      simpa [Function.comp, optionTail, optionSomeComplementEquiv]
        using (inferInstance : HasProduct (optionTail C K))
    simpa [Function.comp, optionTail, optionSomeComplementEquiv]
      using (Limits.Pi.reindex (optionSomeComplementEquiv J).symm
        (fun i : {x : Option J // ¬ x = none} => K i.val)).symm

/--
The complex-level binary fan after composing the raw `Option` product split with the singleton
reduction on the `none` side and the complement reindexing on the `some` side.
-/
noncomputable def optionProductComplexTransportedBinaryFan {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    BinaryFan (K none) (∏ᶜ (optionTail C K)) :=
  BinaryFan.mk
    ((optionProductBinaryFan C K).fst ≫ (noneSubproductIso C K).hom)
    ((optionProductBinaryFan C K).snd ≫ (complementSubproductReindexIso C K).hom)

theorem optionProductComplexTransportedBinaryFan_pt {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    (optionProductComplexTransportedBinaryFan C K).pt = ∏ᶜ K :=
  rfl

theorem optionProductComplexTransportedBinaryFan_fst {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    (optionProductComplexTransportedBinaryFan C K).fst =
      (optionProductBinaryFan C K).fst ≫ (noneSubproductIso C K).hom :=
  rfl

theorem optionProductComplexTransportedBinaryFan_snd {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)] :
    (optionProductComplexTransportedBinaryFan C K).snd =
      (optionProductBinaryFan C K).snd ≫ (complementSubproductReindexIso C K).hom :=
  rfl

/--
Specialization of the cone-point uniqueness conversion to W151's transported complex fan.
-/
noncomputable def optionProductIsoBiprod_of_optionProductComplexTransportedBinaryFanIsLimit
    {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct K]
    [HasProduct (fun i : {x : Option J // x = none} => K i.val)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => K i.val)]
    [HasProduct (optionTail C K)]
    [HasBinaryBiproduct (K none) (∏ᶜ (optionTail C K))]
    (hFan : IsLimit (optionProductComplexTransportedBinaryFan C K)) :
    ∏ᶜ K ≅ K none ⊞ ∏ᶜ (optionTail C K) :=
  optionProductIsoBiprod_of_complexFanIsLimit C K
    (optionProductComplexTransportedBinaryFan C K)
    (optionProductComplexTransportedBinaryFan_pt C K)
    hFan

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
          ⇑(optionSomeComplementEquiv J).symm) := by
      simpa [Function.comp, optionTailDegree, optionSomeComplementEquiv]
        using (inferInstance : HasProduct (optionTailDegree C K n))
    simpa [Function.comp, optionTailDegree, optionSomeComplementEquiv]
      using (Limits.Pi.reindex (optionSomeComplementEquiv J).symm
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

theorem optionProductDegreeTransportedBinaryFan_pt {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] :
    (optionProductDegreeTransportedBinaryFan C K n).pt =
      ∏ᶜ (fun i : Option J => (K i).X n) :=
  rfl

theorem optionProductDegreeTransportedBinaryFan_fst {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : Option J => (K i).X n)]
    [HasProduct (fun i : {x : Option J // x = none} => (K i.val).X n)]
    [HasProduct (fun i : {x : Option J // ¬ x = none} => (K i.val).X n)]
    [HasProduct (optionTailDegree C K n)] :
    (optionProductDegreeTransportedBinaryFan C K n).fst =
      (optionProductDegreeBinaryFan C K n).fst ≫ (noneSubproductDegreeIso C K n).hom :=
  rfl

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
    simpa [optionProductDegreeTransportedBinaryFan, s₀, eL, eR, Category.assoc]
      using congrArg (fun q => q ≫ eL.hom) hfac
  · intro T f g
    have hfac :=
      h₀.fac (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ⟨WalkingPair.right⟩
    simpa [optionProductDegreeTransportedBinaryFan, s₀, eL, eR, Category.assoc]
      using congrArg (fun q => q ≫ eR.hom) hfac
  · intro T f g m hm₁ hm₂
    have hm₁' : m ≫ s₀.fst ≫ eL.hom = f := by
      simpa [optionProductDegreeTransportedBinaryFan, s₀, eL, eR, Category.assoc] using hm₁
    have hm₂' : m ≫ s₀.snd ≫ eR.hom = g := by
      simpa [optionProductDegreeTransportedBinaryFan, s₀, eL, eR, Category.assoc] using hm₂
    have hfac₁ :
        h₀.lift (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ≫ s₀.fst = f ≫ eL.inv := by
      simpa using h₀.fac (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ⟨WalkingPair.left⟩
    have hfac₂ :
        h₀.lift (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ≫ s₀.snd = g ≫ eR.inv := by
      simpa using h₀.fac (BinaryFan.mk (f ≫ eL.inv) (g ≫ eR.inv)) ⟨WalkingPair.right⟩
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
    ((optionProductComplexTransportedBinaryFan C K).fst.f n)
    ((optionProductComplexTransportedBinaryFan C K).snd.f n)

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

/--
API state for the selected degreewise route.

The first three fields are available in mathlib/local imports; the final field is the missing
constructor that would turn the degreewise product split plus reindexing into the cochain-complex
iso needed by `OptionProductIsoBiprod`.
-/
structure DegreewiseProductApiState : Type where
  complexLimitBuilder : String
  complexLimitCone : String
  optionSplitProductCone : String
  productReindex : String
  singletonProductReduction : String
  complexTransportedFan : String
  degreewiseTransportedFan : String
  degreewiseTransportedFanIsLimit : String
  evalProductPointIso : String
  evalTailProductPointIso : String
  evaluatedComplexFan : String
  transportedDegreeFanWithEvaluatedTargets : String
  remainingEvaluatedFanComparison : String
  binaryFanLimitPointIsoBiprod : String
  optionProductIsoBiprodOfComplexFanIsLimit : String
  missingComplexIsoConstructor : Option String

/-- W151's current API frontier for the selected route. -/
def currentDegreewiseProductApiState : DegreewiseProductApiState where
  complexLimitBuilder := "HomologicalComplex.isLimitOfEval"
  complexLimitCone := "HomologicalComplex.coneOfHasLimitEval"
  optionSplitProductCone := "Limits.Pi.binaryFanOfProp / binaryFanOfPropIsLimit"
  productReindex := "Limits.Pi.reindex / map' over Option.some"
  singletonProductReduction := "Limits.productUniqueIso for the none-indexed subproduct"
  complexTransportedFan := "optionProductComplexTransportedBinaryFan"
  degreewiseTransportedFan := "optionProductDegreeTransportedBinaryFan"
  degreewiseTransportedFanIsLimit := "optionProductDegreeTransportedBinaryFanIsLimit"
  evalProductPointIso := "evalProductPointIso"
  evalTailProductPointIso := "evalTailProductPointIso"
  evaluatedComplexFan := "evaluatedOptionProductComplexBinaryFan"
  transportedDegreeFanWithEvaluatedTargets := "optionProductDegreeFanWithEvaluatedTargets"
  remainingEvaluatedFanComparison := "EvaluatedDegreeFanComparison"
  binaryFanLimitPointIsoBiprod := "binaryFanLimitPointIsoBiprod"
  optionProductIsoBiprodOfComplexFanIsLimit :=
    "optionProductIsoBiprod_of_optionProductComplexTransportedBinaryFanIsLimit"
  missingComplexIsoConstructor :=
    some "Prove EvaluatedDegreeFanComparison and transport the degreewise IsLimit proof through evalProductPointIso/evalTailProductPointIso; the binary-product limit can then be converted to ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j => K (some j)) by optionProductIsoBiprod_of_optionProductComplexTransportedBinaryFanIsLimit"

theorem currentDegreewiseProductApiState_missing :
    currentDegreewiseProductApiState.missingComplexIsoConstructor =
      some "Prove EvaluatedDegreeFanComparison and transport the degreewise IsLimit proof through evalProductPointIso/evalTailProductPointIso; the binary-product limit can then be converted to ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j => K (some j)) by optionProductIsoBiprod_of_optionProductComplexTransportedBinaryFanIsLimit" :=
  rfl

/-- Compact checklist of the next proof obligations after this API guard. -/
def optionProductDecompositionNextObligations : List String :=
  ["instantiate degreewise products for (fun i : Option J => (K i).X n)",
    "split that degreewise product with Pi.binaryFanOfProp at predicate x = none",
    "identify the none subproduct with (K none).X n using productUniqueIso",
    "reindex the complement subproduct along optionSomeComplementEquiv to the J-tail using Pi.reindex",
    "compare the evaluated tail product point with the degreewise tail product using evalTailProductPointIso",
    "show the evaluated transported complex fan matches the transported degreewise fan",
    "assemble the degreewise limiting fans into a complex-level limiting fan using isLimitOfEval",
    "convert the binary-product limit into the biproduct-shaped OptionProductIsoBiprod"]

theorem optionProductDecompositionNextObligations_count :
    optionProductDecompositionNextObligations.length = 8 :=
  rfl

section Checks

#check OptionProductIsoBiprod
#check binaryFanLimitPointIsoBiprod
#check optionProductIsoBiprod_of_complexFanIsLimit
#check optionSomeComplementEquiv
#check optionSomeComplementEquiv_apply_some
#check optionSomeComplementEquiv_symm_apply
#check optionSomeComplementEquiv_value_eq_some
#check complementTailReindexIso
#check optionProductBinaryFan
#check noneSubproductIso
#check complementSubproductReindexIso
#check optionProductComplexTransportedBinaryFan
#check optionProductComplexTransportedBinaryFan_pt
#check optionProductComplexTransportedBinaryFan_fst
#check optionProductComplexTransportedBinaryFan_snd
#check optionProductIsoBiprod_of_optionProductComplexTransportedBinaryFanIsLimit
#check optionProductSplitPair
#check optionProductDegreeBinaryFan
#check optionTailDegree
#check noneSubproductDegreeIso
#check complementSubproductDegreeReindexIso
#check optionProductDegreeTransportedBinaryFan
#check optionProductDegreeTransportedBinaryFan_pt
#check optionProductDegreeTransportedBinaryFan_fst
#check optionProductDegreeTransportedBinaryFan_snd
#check optionProductDegreeTransportedBinaryFanIsLimit
#check evalProductPointIso
#check evalProductPointIso_hom_π
#check evalTailProductPointIso
#check evalTailProductPointIso_hom_π
#check evaluatedOptionProductComplexBinaryFan
#check optionProductDegreeFanWithEvaluatedTargets
#check EvaluatedDegreeFanComparison
#check DegreewiseProductApiState
#check currentDegreewiseProductApiState
#check currentDegreewiseProductApiState_missing
#check optionProductDecompositionNextObligations
#check optionProductDecompositionNextObligations_count
#check HomologicalComplex.isLimitOfEval
#check HomologicalComplex.coneOfHasLimitEval
#check HomologicalComplex.isLimitConeOfHasLimitEval
#check Limits.Pi.map
#check Limits.Pi.map'
#check Limits.Pi.mapIso
#check Limits.Pi.reindex
#check Limits.Pi.binaryFanOfProp
#check Limits.Pi.binaryFanOfPropIsLimit
#check Limits.productUniqueIso

end Checks

end OptionProductDecompositionW151

end LeanLCAExactChallenge
