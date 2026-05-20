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
  ["exactAcyclic_zero proves the empty product after an empty-product/zero comparison",
    "MetrizableLCA.exactAcyclic_biprod proves the Option induction step after product decomposition",
    "the remaining missing input is the product-object comparison, not exactness of biproducts"]

theorem obstructionRouteMap_count :
    obstructionRouteMap.length = 3 := rfl

section Checks

#check FiniteProductDecompositionInput
#check FiniteExactAcyclicProductClosure
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
