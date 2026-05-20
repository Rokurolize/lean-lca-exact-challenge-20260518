import LeanLCAExactChallenge.Derived.OptionProductDecomposition
import LeanLCAExactChallenge.Derived.MappingConeBiprod
import LeanLCAExactChallenge.Derived.FiniteProductExactness

/-!
W146 audit: Option-step consumer for finite mapping-cone product comparison.

After v225, the upper exactness consumer has finite exact-acyclic product closure available. This
file isolates the next lower finite-product comparison step: for an `Option J` product map, the
binary mapping-cone comparison and the recursive tail comparison are enough once the promoted
Option-product decomposition is known to commute with `Limits.Pi.map`.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MappingConeOptionProductStepW146

/--
Naturality needed from the promoted Option-product decomposition for product maps.

This is the concrete lower input that lets the `Option J` product map be transported to a
binary product map on the head and tail products.
-/
structure OptionProductMapNaturalityInput : Type (u + 1) where
  commute : ∀ {J : Type u} [Finite J]
    {K L : Option J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun j : J => L (some j))]
    [∀ x : Option J, Decidable (x = none)]
    (f : ∀ j, K j ⟶ L j),
      Limits.Pi.map f ≫
        (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
          MetrizableLCA L).hom =
      (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
          MetrizableLCA K).hom ≫
        biprod.map (f none) (Limits.Pi.map (fun j : J => f (some j)))

/--
Recursive tail comparison input for finite mapping-cone products.

The final finite comparison should prove this input by finite induction; this audit consumes it
only to show that no further exactness theorem is missing in the Option step.
-/
structure TailFiniteMappingConeComparisonInput : Type (u + 1) where
  iso : ∀ {J : Type u} [Finite J]
    {K L : J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j)
    [HasProduct (fun j => CochainComplex.mappingCone (f j))],
      CochainComplex.mappingCone (Limits.Pi.map f) ≅
        ∏ᶜ (fun j => CochainComplex.mappingCone (f j))

/--
Option-step exactness consumer.

Given Option-product-map naturality and the recursive tail comparison, component exactness
implies exactness of the mapping cone of the `Option J` product map.
-/
theorem exactAcyclic_optionPiMap_of_naturality_and_tailComparison
    (naturality : OptionProductMapNaturalityInput.{u})
    (tailComparison : TailFiniteMappingConeComparisonInput.{u})
    {J : Type u} [Finite J]
    {K L : Option J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun j : J => L (some j))]
    (f : ∀ j, K j ⟶ L j)
    [HasProduct (fun j : J => CochainComplex.mappingCone (f (some j)))]
    [∀ x : Option J, Decidable (x = none)]
    (hf : ∀ j, exactAcyclic MetrizableLCA (CochainComplex.mappingCone (f j))) :
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map f)) := by
  let tailMap : ∀ j : J, K (some j) ⟶ L (some j) := fun j => f (some j)
  have hTailProduct :
      exactAcyclic MetrizableLCA (∏ᶜ fun j : J => CochainComplex.mappingCone (tailMap j)) :=
    FiniteProductExactness.finiteExactAcyclicProductClosure_of_w151
      (fun j : J => CochainComplex.mappingCone (tailMap j))
      (fun j => hf (some j))
  have hTailCone :
      exactAcyclic MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map tailMap)) :=
    exactAcyclic_of_iso MetrizableLCA (tailComparison.iso tailMap).symm hTailProduct
  have hBiprod :
      exactAcyclic MetrizableLCA
        (CochainComplex.mappingCone (biprod.map (f none) (Limits.Pi.map tailMap))) :=
    exactAcyclic_of_iso MetrizableLCA
      (MappingConeBiprodComparison.binaryMappingConeBiprodIso (f none)
        (Limits.Pi.map tailMap)).symm
      (MetrizableLCA.exactAcyclic_biprod
        (CochainComplex.mappingCone (f none))
        (CochainComplex.mappingCone (Limits.Pi.map tailMap))
        (hf none) hTailCone)
  let eK :=
    OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
      MetrizableLCA K
  let eL :=
    OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
      MetrizableLCA L
  have hcomm :
      Limits.Pi.map f ≫ eL.hom =
        eK.hom ≫ biprod.map (f none) (Limits.Pi.map tailMap) :=
    naturality.commute f
  exact (exactAcyclic_mappingCone_congr_iff MetrizableLCA eK eL hcomm).2 hBiprod

/-- The exact lower inputs still missing after the Option-step exactness consumer. -/
def optionMappingConeComparisonStepMissingInputs : List String :=
  ["OptionProductMapNaturalityInput.commutes optionProductIsoBiprod with Limits.Pi.map",
    "recursive TailFiniteMappingConeComparisonInput for the tail index type"]

theorem optionMappingConeComparisonStepMissingInputs_count :
    optionMappingConeComparisonStepMissingInputs.length = 2 := rfl

section Checks

#check OptionProductMapNaturalityInput
#check TailFiniteMappingConeComparisonInput
#check exactAcyclic_optionPiMap_of_naturality_and_tailComparison
#check optionMappingConeComparisonStepMissingInputs
#check optionMappingConeComparisonStepMissingInputs_count
#check OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
#check MappingConeBiprodComparison.binaryMappingConeBiprodIso
#check FiniteProductExactness.finiteExactAcyclicProductClosure_of_w151
#check exactAcyclic_mappingCone_congr_iff
#check Limits.Pi.map
#check biprod.map

end Checks

end MappingConeOptionProductStepW146

end LeanLCAExactChallenge
