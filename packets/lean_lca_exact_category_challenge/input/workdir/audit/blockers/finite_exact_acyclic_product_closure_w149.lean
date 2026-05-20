import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.OptionProductDecomposition

/-!
W149 obstruction audit: finite exact-acyclic product closure.

The binary closure theorem promoted in `Derived.Bounded` is strong enough for the induction step
once a finite product can be decomposed into an `Option` head and a tail product. This file
records that boundary as a compiling consumer: the remaining missing input is product
decomposition/reindexing, not another exactness theorem.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace FiniteExactAcyclicProductClosureW149

/--
Product-object comparisons needed to turn binary exact-acyclic closure into finite closure.

The `optionProductIsoBiprod` field is the induction-step comparison: a product over `Option J`
should identify with the head factor and the product over the tail. The `emptyProductExact`
field is kept as the base-case exactness input.
-/
structure FiniteProductDecompositionInput : Type (u + 1) where
  emptyProductExact :
    ∀ {J : Type u} [IsEmpty J]
      (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K],
        exactAcyclic MetrizableLCA (∏ᶜ K)
  optionProductIsoBiprod :
    ∀ {J : Type u} [Finite J]
      (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
      [HasProduct K] [HasProduct (fun j : J => K (some j))],
        ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j))

/-- The exact-acyclic closure target needed by the finite-product route. -/
abbrev FiniteExactAcyclicProductClosure : Prop :=
  ∀ {J : Type u} [Finite J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K],
      (∀ j, exactAcyclic MetrizableLCA (K j)) → exactAcyclic MetrizableLCA (∏ᶜ K)

/-- Empty products of cochain complexes are canonically the zero complex. -/
noncomputable def emptyProductIsoZero
    {J : Type u} [IsEmpty J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K] :
    ∏ᶜ K ≅ (0 : CochainComplex MetrizableLCA.{u} ℤ) := by
  refine IsTerminal.uniqueUpToIso ?h
    ((isZero_zero (CochainComplex MetrizableLCA.{u} ℤ) :
      IsZero (0 : CochainComplex MetrizableLCA.{u} ℤ)).isTerminal)
  refine IsTerminal.ofUniqueHom (fun X => Pi.lift (fun j => False.elim (isEmptyElim j))) ?_
  intro X f
  apply Pi.hom_ext
  intro j
  exact False.elim (isEmptyElim j)

/-- The finite-product base case follows from the selected empty product being zero. -/
theorem exactAcyclic_emptyProduct
    {J : Type u} [IsEmpty J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K] :
    exactAcyclic MetrizableLCA (∏ᶜ K) :=
  exactAcyclic_of_iso MetrizableLCA (emptyProductIsoZero K).symm
    (exactAcyclic_zero MetrizableLCA)

/--
After v208, the product-decomposition input no longer needs an empty-product exactness field:
the base case is supplied by `exactAcyclic_emptyProduct`.
-/
structure FiniteProductOptionDecompositionInput : Type (u + 1) where
  optionProductIsoBiprod :
    ∀ {J : Type u} [Finite J]
      (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
      [HasProduct K] [HasProduct (fun j : J => K (some j))],
        ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j))

/-- Package the original W149 input from the now-proved empty base case plus the Option step. -/
def finiteProductDecompositionInput_of_optionProductIsoBiprod
    (input : FiniteProductOptionDecompositionInput.{u}) :
    FiniteProductDecompositionInput.{u} where
  emptyProductExact := by
    intro J _ K _
    exact exactAcyclic_emptyProduct K
  optionProductIsoBiprod := by
    intro J _ K _ _
    exact input.optionProductIsoBiprod K

/--
W151's promoted Option-product decomposition supplies the W149 Option-step input for
metrizable LCA cochain-complex products.
-/
noncomputable def finiteProductOptionDecompositionInput_of_w151 :
    FiniteProductOptionDecompositionInput.{u} where
  optionProductIsoBiprod := by
    intro J _ K _ _
    exact
      LeanLCAExactChallenge.OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
          MetrizableLCA K

/--
Base case once the empty-product comparison is supplied.

This audit keeps the base case as an input because the selected frontier is the finite induction
shape. The binary step below is the first nontrivial exactness consumer.
-/
theorem exactAcyclic_emptyProduct_of_decomposition
    (input : FiniteProductDecompositionInput.{u})
    {J : Type u} [IsEmpty J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K] :
    exactAcyclic MetrizableLCA (∏ᶜ K) := by
  exact input.emptyProductExact K

/--
Induction step once the `Option` product comparison and tail closure are supplied.

The proof consumes only the promoted binary theorem `MetrizableLCA.exactAcyclic_biprod` plus
isomorphism transport, making the missing theorem precise: construct the comparison for products
of cochain complexes.
-/
theorem exactAcyclic_optionProduct_of_decomposition
    (input : FiniteProductDecompositionInput.{u})
    {J : Type u} [Finite J]
    (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
    [HasProduct K] [HasProduct (fun j : J => K (some j))]
    (hK : ∀ j, exactAcyclic MetrizableLCA (K j))
    (hTail : exactAcyclic MetrizableLCA (∏ᶜ (fun j : J => K (some j)))) :
    exactAcyclic MetrizableLCA (∏ᶜ K) := by
  exact exactAcyclic_of_iso MetrizableLCA (input.optionProductIsoBiprod K).symm
    (MetrizableLCA.exactAcyclic_biprod (K none) (∏ᶜ (fun j : J => K (some j)))
      (hK none) hTail)

/--
The Option induction step after the empty-product base case has been removed from the input.
-/
theorem exactAcyclic_optionProduct_of_optionProductIsoBiprod
    (input : FiniteProductOptionDecompositionInput.{u})
    {J : Type u} [Finite J]
    (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
    [HasProduct K] [HasProduct (fun j : J => K (some j))]
    (hK : ∀ j, exactAcyclic MetrizableLCA (K j))
    (hTail : exactAcyclic MetrizableLCA (∏ᶜ (fun j : J => K (some j)))) :
    exactAcyclic MetrizableLCA (∏ᶜ K) :=
  exactAcyclic_optionProduct_of_decomposition
    (finiteProductDecompositionInput_of_optionProductIsoBiprod input) K hK hTail

/--
Finite exact-acyclic product closure follows from the empty product base case and the promoted
Option-product decomposition step.
-/
theorem finiteExactAcyclicProductClosure_of_optionProductIsoBiprod
    (input : FiniteProductOptionDecompositionInput.{u}) :
    FiniteExactAcyclicProductClosure.{u} := by
  let P : Type u → Prop :=
    fun J =>
      ∀ (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K],
        (∀ j, exactAcyclic MetrizableLCA (K j)) → exactAcyclic MetrizableLCA (∏ᶜ K)
  refine Finite.induction_empty_option (P := P) ?of_equiv ?h_empty ?h_option
  · intro α β e hα K _ hK
    letI : HasProduct (K ∘ e) :=
      hasProduct_of_equiv_of_iso K (K ∘ e) e (fun _ => Iso.refl _)
    exact exactAcyclic_of_iso MetrizableLCA (Pi.reindex e K)
      (hα (K ∘ e) (fun j => hK (e j)))
  · intro K _ _
    exact exactAcyclic_emptyProduct K
  · intro α _ hα K _ hK
    letI : HasProduct (fun j : α => K (some j)) := by infer_instance
    exact exactAcyclic_optionProduct_of_optionProductIsoBiprod input K hK
      (hα (fun j : α => K (some j)) (fun j => hK (some j)))

/-- The W151 Option-product comparison closes W149's finite-product exactness target. -/
theorem finiteExactAcyclicProductClosure_of_w151 :
    FiniteExactAcyclicProductClosure.{u} :=
  finiteExactAcyclicProductClosure_of_optionProductIsoBiprod
    finiteProductOptionDecompositionInput_of_w151

/-- The earliest missing theorem isolated by this audit. -/
def earliestMissingTheorem : String :=
  "mapping-cone finite-product stability after finite exact-acyclic product closure"

/-- Why this is the first obstruction after the binary exactness theorem. -/
def obstructionRouteMap : List String :=
  ["emptyProductIsoZero and exactAcyclic_zero prove the empty product base case",
    "MetrizableLCA.exactAcyclic_biprod proves the Option induction step after product decomposition",
    "Finite.induction_empty_option closes finite exact-acyclic product closure from the W151 Option comparison",
    "the remaining missing input is the mapping-cone finite-product stability connection"]

theorem obstructionRouteMap_count :
    obstructionRouteMap.length = 4 := rfl

section Checks

#check FiniteProductDecompositionInput
#check FiniteExactAcyclicProductClosure
#check emptyProductIsoZero
#check exactAcyclic_emptyProduct
#check FiniteProductOptionDecompositionInput
#check finiteProductDecompositionInput_of_optionProductIsoBiprod
#check finiteProductOptionDecompositionInput_of_w151
#check exactAcyclic_emptyProduct_of_decomposition
#check exactAcyclic_optionProduct_of_decomposition
#check exactAcyclic_optionProduct_of_optionProductIsoBiprod
#check finiteExactAcyclicProductClosure_of_optionProductIsoBiprod
#check finiteExactAcyclicProductClosure_of_w151
#check earliestMissingTheorem
#check obstructionRouteMap
#check obstructionRouteMap_count
#check exactAcyclic_zero
#check exactAcyclic_of_iso
#check MetrizableLCA.exactAcyclic_biprod
#check Limits.Pi.map

end Checks

end FiniteExactAcyclicProductClosureW149

end LeanLCAExactChallenge
