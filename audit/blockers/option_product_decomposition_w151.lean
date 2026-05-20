import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Shapes.PiProd

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
  missingComplexIsoConstructor : Option String

/-- W151's current API frontier for the selected route. -/
def currentDegreewiseProductApiState : DegreewiseProductApiState where
  complexLimitBuilder := "HomologicalComplex.isLimitOfEval"
  complexLimitCone := "HomologicalComplex.coneOfHasLimitEval"
  optionSplitProductCone := "Limits.Pi.binaryFanOfProp / binaryFanOfPropIsLimit"
  productReindex := "Limits.Pi.reindex / map' over Option.some"
  singletonProductReduction := "Limits.productUniqueIso for the none-indexed subproduct"
  complexTransportedFan := "optionProductComplexTransportedBinaryFan"
  missingComplexIsoConstructor :=
    some "Prove the transported complex fan is limiting via evaluated degreewise cones and convert the binary product limit to ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j => K (some j))"

theorem currentDegreewiseProductApiState_missing :
    currentDegreewiseProductApiState.missingComplexIsoConstructor =
      some "Prove the transported complex fan is limiting via evaluated degreewise cones and convert the binary product limit to ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j => K (some j))" :=
  rfl

/-- Compact checklist of the next proof obligations after this API guard. -/
def optionProductDecompositionNextObligations : List String :=
  ["instantiate degreewise products for (fun i : Option J => (K i).X n)",
    "split that degreewise product with Pi.binaryFanOfProp at predicate x = none",
    "identify the none subproduct with (K none).X n using productUniqueIso",
    "reindex the complement subproduct along optionSomeComplementEquiv to the J-tail using Pi.reindex",
    "show the evaluated transported complex fan matches the transported degreewise fan",
    "assemble the degreewise limiting fans into a complex-level limiting fan using isLimitOfEval",
    "convert the binary-product limit into the biproduct-shaped OptionProductIsoBiprod"]

theorem optionProductDecompositionNextObligations_count :
    optionProductDecompositionNextObligations.length = 7 :=
  rfl

section Checks

#check OptionProductIsoBiprod
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
#check optionProductSplitPair
#check optionProductDegreeBinaryFan
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
