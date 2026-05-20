import LeanLCAExactChallenge.Derived.Bounded

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

/-- The earliest missing theorem isolated by this audit. -/
def earliestMissingTheorem : String :=
  "FiniteProductDecompositionInput.optionProductIsoBiprod for cochain-complex products"

/-- Why this is the first obstruction after the binary exactness theorem. -/
def obstructionRouteMap : List String :=
  ["emptyProductIsoZero and exactAcyclic_zero prove the empty product base case",
    "MetrizableLCA.exactAcyclic_biprod proves the Option induction step after product decomposition",
    "the remaining missing input is the Option product-object comparison, not empty-product exactness or exactness of biproducts"]

theorem obstructionRouteMap_count :
    obstructionRouteMap.length = 3 := rfl

section Checks

#check FiniteProductDecompositionInput
#check FiniteExactAcyclicProductClosure
#check emptyProductIsoZero
#check exactAcyclic_emptyProduct
#check FiniteProductOptionDecompositionInput
#check finiteProductDecompositionInput_of_optionProductIsoBiprod
#check exactAcyclic_emptyProduct_of_decomposition
#check exactAcyclic_optionProduct_of_decomposition
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
