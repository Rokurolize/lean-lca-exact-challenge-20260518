import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.OptionProductDecomposition

/-!
Finite exact-acyclic product closure for metrizable LCA cochain complexes.

This file packages the empty product base case, the promoted Option-product decomposition, and
`Finite.induction_empty_option` into a reusable finite-family closure theorem.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace FiniteProductExactness

/-- The finite exact-acyclic product closure target for metrizable LCA cochain complexes. -/
abbrev FiniteExactAcyclicProductClosure : Prop :=
  ∀ {J : Type u} [Finite J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K],
      (∀ j, exactAcyclic MetrizableLCA (K j)) → exactAcyclic MetrizableLCA (∏ᶜ K)

/-- The finite Option-product comparison needed for the induction step. -/
structure FiniteProductOptionDecompositionInput : Type (u + 1) where
  optionProductIsoBiprod :
    ∀ {J : Type u} [Finite J]
      (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
      [HasProduct K] [HasProduct (fun j : J => K (some j))],
        ∏ᶜ K ≅ K none ⊞ ∏ᶜ (fun j : J => K (some j))

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

/-- W151's promoted Option-product decomposition supplies the finite Option step. -/
noncomputable def finiteProductOptionDecompositionInput_of_w151 :
    FiniteProductOptionDecompositionInput.{u} where
  optionProductIsoBiprod := by
    intro J _ K _ _
    exact
      OptionProductDecompositionW151.optionProductIsoBiprod_finite_direct
        MetrizableLCA K

/-- The Option induction step from product decomposition and binary exact-acyclic closure. -/
theorem exactAcyclic_optionProduct_of_optionProductIsoBiprod
    (input : FiniteProductOptionDecompositionInput.{u})
    {J : Type u} [Finite J]
    (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
    [HasProduct K] [HasProduct (fun j : J => K (some j))]
    (hK : ∀ j, exactAcyclic MetrizableLCA (K j))
    (hTail : exactAcyclic MetrizableLCA (∏ᶜ (fun j : J => K (some j)))) :
    exactAcyclic MetrizableLCA (∏ᶜ K) := by
  exact exactAcyclic_of_iso MetrizableLCA (input.optionProductIsoBiprod K).symm
    (MetrizableLCA.exactAcyclic_biprod (K none) (∏ᶜ (fun j : J => K (some j)))
      (hK none) hTail)

/-- Finite exact-acyclic product closure from the empty product base case and Option step. -/
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

/-- The W151 Option-product comparison closes finite exact-acyclic product closure. -/
theorem finiteExactAcyclicProductClosure_of_w151 :
    FiniteExactAcyclicProductClosure.{u} :=
  finiteExactAcyclicProductClosure_of_optionProductIsoBiprod
    finiteProductOptionDecompositionInput_of_w151

end FiniteProductExactness

end LeanLCAExactChallenge
