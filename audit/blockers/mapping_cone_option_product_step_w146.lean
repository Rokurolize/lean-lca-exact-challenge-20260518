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
The promoted Option-product isomorphism has the transported fan's `fst` projection.

This removes the cone-point uniqueness wrapper from the naturality problem.
-/
theorem optionProductIsoBiprod_finiteProducts_hom_fst {J : Type u} [Finite J]
    (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [∀ x : Option J, Decidable (x = none)] :
    (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
      MetrizableLCA K).hom ≫ biprod.fst =
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).fst := by
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_packaged_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_singletonTailDegreeComplement_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_tailDegreeComplement_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_tailComplement_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_of_optionProductComplexTransportedBinaryFanIsLimit
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_of_complexFanIsLimit
  unfold OptionProductDecompositionW151.binaryFanLimitPointIsoBiprod
  simp only [OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan_pt,
    Iso.trans_hom, eqToIso.hom]
  simpa [BinaryFan.π_app_left, BinaryBicone.toCone_π_app_left] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFanIsLimit_direct
        MetrizableLCA K)
      (BinaryBiproduct.isLimit (K none)
        (∏ᶜ OptionProductDecompositionW151.optionTail MetrizableLCA K))
      (⟨WalkingPair.left⟩ : Discrete WalkingPair)

/--
The promoted Option-product isomorphism has the transported fan's `snd` projection.

This removes the cone-point uniqueness wrapper from the naturality problem.
-/
theorem optionProductIsoBiprod_finiteProducts_hom_snd {J : Type u} [Finite J]
    (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [∀ x : Option J, Decidable (x = none)] :
    (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
      MetrizableLCA K).hom ≫ biprod.snd =
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd := by
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_packaged_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_singletonTailDegreeComplement_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_tailDegreeComplement_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_tailComplement_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_of_direct
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_of_optionProductComplexTransportedBinaryFanIsLimit
  unfold OptionProductDecompositionW151.optionProductIsoBiprod_of_complexFanIsLimit
  unfold OptionProductDecompositionW151.binaryFanLimitPointIsoBiprod
  simp only [OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan_pt,
    Iso.trans_hom, eqToIso.hom]
  simpa [BinaryFan.π_app_right, BinaryBicone.toCone_π_app_right] using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFanIsLimit_direct
        MetrizableLCA K)
      (BinaryBiproduct.isLimit (K none)
        (∏ᶜ OptionProductDecompositionW151.optionTail MetrizableLCA K))
      (⟨WalkingPair.right⟩ : Discrete WalkingPair)

/--
Projection-level naturality for the transported binary fan.

This is the lower remaining API problem after the cone-point uniqueness wrapper has been removed.
-/
structure OptionTransportedFanMapProjectionNaturalityInput : Type (u + 1) where
  fst_comm : ∀ {J : Type u} [Finite J]
    {K L : Option J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun j : J => L (some j))]
    [∀ x : Option J, Decidable (x = none)]
    (f : ∀ j, K j ⟶ L j),
      Limits.Pi.map f ≫
        (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).fst =
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).fst ≫
        f none
  snd_comm : ∀ {J : Type u} [Finite J]
    {K L : Option J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun j : J => L (some j))]
    [∀ x : Option J, Decidable (x = none)]
    (f : ∀ j, K j ⟶ L j),
      Limits.Pi.map f ≫
        (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).snd =
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
        Limits.Pi.map (fun j : J => f (some j))

/--
Projection-level transported-fan naturality implies the existing Option-product map naturality
input used by the Option-step exactness consumer.
-/
def optionProductMapNaturalityInput_of_projectionNaturality
    (projectionNaturality : OptionTransportedFanMapProjectionNaturalityInput.{u}) :
    OptionProductMapNaturalityInput.{u} where
  commute := by
    intro J _ K L _ _ _ _ _ f
    apply biprod.hom_ext
    · have h₁ :
          (Limits.Pi.map f ≫
              (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
                MetrizableLCA L).hom) ≫ biprod.fst =
              Limits.Pi.map f ≫
                (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).fst := by
          simpa [Category.assoc] using
            congrArg (fun g => Limits.Pi.map f ≫ g)
              (optionProductIsoBiprod_finiteProducts_hom_fst L)
      have h₂ :
          Limits.Pi.map f ≫
              (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).fst =
            (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).fst ≫
              f none :=
        projectionNaturality.fst_comm f
      have h₃ :
          (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).fst ≫
              f none =
            ((OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
                MetrizableLCA K).hom ≫ biprod.fst) ≫ f none := by
          simpa [Category.assoc] using
            congrArg (fun g => g ≫ f none)
              (optionProductIsoBiprod_finiteProducts_hom_fst K).symm
      have h₄ :
          ((OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
              MetrizableLCA K).hom ≫ biprod.fst) ≫ f none =
            ((OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
                MetrizableLCA K).hom ≫
              biprod.map (f none) (Limits.Pi.map (fun j : J => f (some j)))) ≫ biprod.fst := by
          simp [Category.assoc]
      exact h₁.trans (h₂.trans (h₃.trans h₄))
    · have h₁ :
          (Limits.Pi.map f ≫
              (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
                MetrizableLCA L).hom) ≫ biprod.snd =
              Limits.Pi.map f ≫
                (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).snd := by
          simpa [Category.assoc] using
            congrArg (fun g => Limits.Pi.map f ≫ g)
              (optionProductIsoBiprod_finiteProducts_hom_snd L)
      have h₂ :
          Limits.Pi.map f ≫
              (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).snd =
            (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
              Limits.Pi.map (fun j : J => f (some j)) :=
        projectionNaturality.snd_comm f
      have h₃ :
          (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
              Limits.Pi.map (fun j : J => f (some j)) =
            ((OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
                MetrizableLCA K).hom ≫ biprod.snd) ≫
              Limits.Pi.map (fun j : J => f (some j)) := by
          simpa [Category.assoc] using
            congrArg (fun g => g ≫ Limits.Pi.map (fun j : J => f (some j)))
              (optionProductIsoBiprod_finiteProducts_hom_snd K).symm
      have h₄ :
          ((OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
              MetrizableLCA K).hom ≫ biprod.snd) ≫
              Limits.Pi.map (fun j : J => f (some j)) =
            ((OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
                MetrizableLCA K).hom ≫
              biprod.map (f none) (Limits.Pi.map (fun j : J => f (some j)))) ≫ biprod.snd := by
          simp [Category.assoc]
      exact h₁.trans (h₂.trans (h₃.trans h₄))

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
  ["OptionTransportedFanMapProjectionNaturalityInput.fst_comm for singleton none projection",
    "OptionTransportedFanMapProjectionNaturalityInput.snd_comm for complement/tail projection",
    "recursive TailFiniteMappingConeComparisonInput for the tail index type"]

theorem optionMappingConeComparisonStepMissingInputs_count :
    optionMappingConeComparisonStepMissingInputs.length = 3 := rfl

section Checks

#check OptionProductMapNaturalityInput
#check optionProductIsoBiprod_finiteProducts_hom_fst
#check optionProductIsoBiprod_finiteProducts_hom_snd
#check OptionTransportedFanMapProjectionNaturalityInput
#check optionProductMapNaturalityInput_of_projectionNaturality
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
