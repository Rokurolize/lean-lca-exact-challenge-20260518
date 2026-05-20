import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Limits.Shapes.PiProd

/-!
W154 audit: complement-product reindexing for the `Option` product route.

The SSoT route selected `complement-product-reindex`. This file packages the actual product
reindex isomorphism from the non-`none` complement of `Option J` to the `J`-indexed `some` tail,
using the equivalence introduced by the target v198 W151 audit and mathlib's `Limits.Pi.reindex`.

The larger binary-fan composition and the `HomologicalComplex.isLimitOfEval` assembly into
`OptionProductIsoBiprod` remain open.
-/

set_option autoImplicit false

universe w v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace OptionComplementProductReindexW154

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The tail family obtained by dropping the `none` summand from an `Option`-indexed family. -/
abbrev optionTail {J : Type w} (K : Option J → CochainComplex C ℤ) :
    J → CochainComplex C ℤ :=
  fun j => K (some j)

/-- The complementary subindex used by `Pi.binaryFanOfProp`. -/
abbrev optionSomeComplementIndex (J : Type w) : Type w :=
  {x : Option J // ¬ x = none}

/--
The target v198 equivalence between the non-`none` complement of `Option J` and `J`.

This audit file is checked directly by path rather than imported as a module from W151, so the
definition is mirrored here to package the next product reindexing step in isolation.
-/
def optionSomeComplementEquiv (J : Type w) :
    optionSomeComplementIndex J ≃ J where
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

theorem optionSomeComplementEquiv_symm_apply {J : Type w} (j : J) :
    (optionSomeComplementEquiv J).symm j = ⟨some j, by simp⟩ :=
  rfl

/--
The complement subproduct of cochain complexes is canonically the product over the `some` tail.

Using the inverse equivalence makes the domain of `Limits.Pi.reindex` definitionally the tail
family `fun j => K (some j)`; reversing that isomorphism gives the direction needed after the
`Pi.binaryFanOfProp` split.
-/
noncomputable def complementSubproductReindexIso {J : Type w}
    (K : Option J → CochainComplex C ℤ)
    [HasProduct (fun i : optionSomeComplementIndex J => K i.val)]
    [HasProduct (optionTail C K)] :
    ∏ᶜ (fun i : optionSomeComplementIndex J => K i.val) ≅ ∏ᶜ (optionTail C K) :=
  by
    letI : HasProduct
        ((fun i : optionSomeComplementIndex J => K i.val) ∘
          ⇑(optionSomeComplementEquiv J).symm) := by
      simpa [Function.comp, optionTail, optionSomeComplementEquiv]
        using (inferInstance : HasProduct (optionTail C K))
    simpa [Function.comp, optionTail, optionSomeComplementEquiv]
      using (Limits.Pi.reindex (optionSomeComplementEquiv J).symm
        (fun i : optionSomeComplementIndex J => K i.val)).symm

/-- The same complement reindexing at a fixed cochain degree. -/
noncomputable def complementSubproductDegreeReindexIso {J : Type w}
    (K : Option J → CochainComplex C ℤ) (n : ℤ)
    [HasProduct (fun i : optionSomeComplementIndex J => (K i.val).X n)]
    [HasProduct (fun j : J => (K (some j)).X n)] :
    ∏ᶜ (fun i : optionSomeComplementIndex J => (K i.val).X n) ≅
      ∏ᶜ (fun j : J => (K (some j)).X n) :=
  by
    letI : HasProduct
        ((fun i : optionSomeComplementIndex J => (K i.val).X n) ∘
          ⇑(optionSomeComplementEquiv J).symm) := by
      simpa [Function.comp, optionSomeComplementEquiv]
        using (inferInstance : HasProduct (fun j : J => (K (some j)).X n))
    simpa [Function.comp, optionSomeComplementEquiv]
      using (Limits.Pi.reindex (optionSomeComplementEquiv J).symm
        (fun i : optionSomeComplementIndex J => (K i.val).X n)).symm

/-- Compact frontier state after packaging the complement product reindexing bridge. -/
structure ComplementProductReindexState : Type where
  indexEquivalence : String
  complexProductIso : String
  degreeProductIso : String
  remainingBinaryFanComposition : Option String
  remainingComplexIsoAssembly : Option String

/-- W154's current complement-product frontier. -/
def currentComplementProductReindexState : ComplementProductReindexState where
  indexEquivalence := "optionSomeComplementEquiv : {x : Option J // not x = none} ≃ J"
  complexProductIso := "complementSubproductReindexIso via Limits.Pi.reindex on the inverse equivalence"
  degreeProductIso := "complementSubproductDegreeReindexIso via the same inverse reindex"
  remainingBinaryFanComposition :=
    some "Compose Pi.binaryFanOfProp with W152 noneSubproductIso and complementSubproductReindexIso"
  remainingComplexIsoAssembly :=
    some "Assemble the OptionProductIsoBiprod body using HomologicalComplex.isLimitOfEval"

theorem currentComplementProductReindexState_complex_iso_done :
    currentComplementProductReindexState.complexProductIso =
      "complementSubproductReindexIso via Limits.Pi.reindex on the inverse equivalence" :=
  rfl

/-- Compact checklist for the next worker after the complement product reindexing bridge. -/
def complementProductReindexNextObligations : List String :=
  ["compose complementSubproductReindexIso with the right leg of Pi.binaryFanOfProp",
    "compose W152 noneSubproductIso with the left leg of Pi.binaryFanOfProp",
    "turn the reindexed binary fan into the target biproduct object K none biprod product tail",
    "promote or compare the fixed-degree split using HomologicalComplex.isLimitOfEval",
    "feed the resulting OptionProductIsoBiprod input into the finite exact-acyclic product closure"]

theorem complementProductReindexNextObligations_count :
    complementProductReindexNextObligations.length = 5 :=
  rfl

section Checks

#check optionTail
#check optionSomeComplementIndex
#check optionSomeComplementEquiv
#check optionSomeComplementEquiv_symm_apply
#check complementSubproductReindexIso
#check complementSubproductDegreeReindexIso
#check ComplementProductReindexState
#check currentComplementProductReindexState
#check currentComplementProductReindexState_complex_iso_done
#check complementProductReindexNextObligations
#check complementProductReindexNextObligations_count
#check Limits.Pi.reindex
#check Limits.Pi.map'
#check Limits.Pi.mapIso
#check Limits.Pi.binaryFanOfProp
#check HomologicalComplex.isLimitOfEval

end Checks

end OptionComplementProductReindexW154

end LeanLCAExactChallenge
