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
open scoped ZeroObject

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
The `none`/singleton projection of the transported Option-product fan is natural in product
maps. This closes the `fst` half of `OptionTransportedFanMapProjectionNaturalityInput`.
-/
theorem optionTransportedFanMapFstNaturality {J : Type u} [Finite J]
    {K L : Option J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun j : J => L (some j))]
    [∀ x : Option J, Decidable (x = none)]
    (f : ∀ j, K j ⟶ L j) :
    Limits.Pi.map f ≫
        (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).fst =
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).fst ≫
        f none := by
  simp only [OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan,
    OptionProductDecompositionW151.noneSubproductIso, Limits.Pi.binaryFanOfProp,
    BinaryFan.mk_fst, Limits.productUniqueIso_hom]
  change (Limits.Pi.map f ≫ (Pi.map' Subtype.val fun x => 𝟙 (L ↑x))) ≫
      limit.π (Discrete.functor fun i : {x : Option J // x = none} => L ↑i) default =
    ((Pi.map' Subtype.val fun x => 𝟙 (K ↑x)) ≫
      limit.π (Discrete.functor fun i : {x : Option J // x = none} => K ↑i) default) ≫ f none
  rw [Limits.Pi.map_comp_map']
  simp only [Category.comp_id]
  have hleft :
      (Pi.map' Subtype.val (fun b : {x : Option J // x = none} => f ↑b)) ≫
        limit.π (Discrete.functor fun i : {x : Option J // x = none} => L ↑i) default =
      limit.π (Discrete.functor K) (Discrete.mk none) ≫ f none := by
    have h := Limits.Pi.map'_comp_π (p := Subtype.val)
      (q := fun b : {x : Option J // x = none} => f b.val)
      (b := (default : Discrete {x : Option J // x = none}).as)
    have hval : ((default : Discrete {x : Option J // x = none}).as).val = none :=
      ((default : Discrete {x : Option J // x = none}).as).property
    simpa [Pi.π, hval] using h
  have hright :
      ((Pi.map' Subtype.val fun x : {x : Option J // x = none} => 𝟙 (K ↑x)) ≫
        limit.π (Discrete.functor fun i : {x : Option J // x = none} => K ↑i) default) ≫ f none =
      limit.π (Discrete.functor K) (Discrete.mk none) ≫ f none := by
    have h := Limits.Pi.map'_comp_π (p := Subtype.val)
      (q := fun b : {x : Option J // x = none} => 𝟙 (K b.val))
      (b := (default : Discrete {x : Option J // x = none}).as)
    have hval : ((default : Discrete {x : Option J // x = none}).as).val = none :=
      ((default : Discrete {x : Option J // x = none}).as).property
    simpa [Pi.π, hval, Category.assoc] using congrArg (fun g => g ≫ f none) h
  rw [hleft, hright]

/--
Projection formula for the tail side of the transported Option-product fan.

After reindexing the complement by `Option.some`, the `j`-th tail projection is the original
product projection at `some j`.
-/
theorem optionProductComplexTransportedBinaryFan_snd_π {J : Type u} [Finite J]
    (K : Option J → CochainComplex MetrizableLCA.{u} ℤ)
    [HasProduct K]
    [HasProduct (fun j : J => K (some j))]
    [∀ x : Option J, Decidable (x = none)] (j : J) :
    (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
      Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA K) j =
    Pi.π K (some j) := by
  simp only [OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan,
    OptionProductDecompositionW151.complementSubproductReindexIso, Limits.Pi.binaryFanOfProp,
    BinaryFan.mk_snd, Iso.symm_hom]
  letI : HasProduct
      ((fun i : {x : Option J // ¬ x = none} => K i.val) ∘
        ⇑(OptionProductDecompositionW151.optionSomeComplementEquiv J).symm) := by
    simpa [Function.comp, OptionProductDecompositionW151.optionTail,
      OptionProductDecompositionW151.optionSomeComplementEquiv]
      using (inferInstance : HasProduct (OptionProductDecompositionW151.optionTail MetrizableLCA K))
  have hreindex :
      (Pi.reindex (OptionProductDecompositionW151.optionSomeComplementEquiv J).symm
          (fun i : {x : Option J // ¬ x = none} => K i.val)).inv ≫
          Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA K) j =
        Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
          ((OptionProductDecompositionW151.optionSomeComplementEquiv J).symm j) := by
    simpa [OptionProductDecompositionW151.optionTail,
      OptionProductDecompositionW151.optionSomeComplementEquiv] using
      (Pi.reindex_inv_π (OptionProductDecompositionW151.optionSomeComplementEquiv J).symm
        (fun i : {x : Option J // ¬ x = none} => K i.val) j)
  change (Pi.map' Subtype.val (fun x : {x : Option J // ¬ x = none} => 𝟙 (K ↑x))) ≫
      ((Pi.reindex (OptionProductDecompositionW151.optionSomeComplementEquiv J).symm
          (fun i : {x : Option J // ¬ x = none} => K i.val)).inv ≫
        Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA K) j) =
    Pi.π K (some j)
  rw [hreindex]
  have hraw :
      (Pi.map' Subtype.val fun x : {x : Option J // ¬ x = none} => 𝟙 (K ↑x)) ≫
          Pi.π (fun i : {x : Option J // ¬ x = none} => K i.val)
            ((OptionProductDecompositionW151.optionSomeComplementEquiv J).symm j) =
        Pi.π K ((OptionProductDecompositionW151.optionSomeComplementEquiv J).symm j).val := by
    simpa [Pi.π] using
      (Pi.map'_comp_π (p := Subtype.val)
        (q := fun x : {x : Option J // ¬ x = none} => 𝟙 (K x.val))
        (b := (OptionProductDecompositionW151.optionSomeComplementEquiv J).symm j))
  exact hraw.trans (by
    simp [OptionProductDecompositionW151.optionSomeComplementEquiv_symm_apply])

/--
The tail projection of the transported Option-product fan is natural in product maps.

Together with `optionTransportedFanMapFstNaturality`, this closes the promoted Option-product
map naturality input.
-/
theorem optionTransportedFanMapSndNaturality {J : Type u} [Finite J]
    {K L : Option J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun j : J => L (some j))]
    [∀ x : Option J, Decidable (x = none)]
    (f : ∀ j, K j ⟶ L j) :
    Limits.Pi.map f ≫
        (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).snd =
      (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
        Limits.Pi.map (fun j : J => f (some j)) := by
  apply Limits.Pi.hom_ext
  intro j
  have hL := optionProductComplexTransportedBinaryFan_snd_π (K := L) j
  have hK := optionProductComplexTransportedBinaryFan_snd_π (K := K) j
  calc
    (Limits.Pi.map f ≫
        (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA L).snd) ≫
        Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA L) j =
      Limits.Pi.map f ≫ Pi.π L (some j) := by
        simpa [Category.assoc] using congrArg (fun g => Limits.Pi.map f ≫ g) hL
    _ = Pi.π K (some j) ≫ f (some j) := by
        simpa using (Pi.map_π f (some j))
    _ =
      ((OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
        Limits.Pi.map (fun j : J => f (some j))) ≫
        Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA L) j := by
        have htail := Pi.map_π (fun j : J => f (some j)) j
        calc
          Pi.π K (some j) ≫ f (some j) =
              ((OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
                Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA K) j) ≫ f (some j) := by
                simpa [Category.assoc] using congrArg (fun g => g ≫ f (some j)) hK.symm
          _ =
              (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
                (Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA K) j ≫ f (some j)) := by
                simp [Category.assoc]
          _ =
              (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
                (Limits.Pi.map (fun j : J => f (some j)) ≫
                  Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA L) j) := by
                simpa [Category.assoc, OptionProductDecompositionW151.optionTail] using
                  congrArg (fun g =>
                    (OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫ g)
                    htail.symm
          _ =
              ((OptionProductDecompositionW151.optionProductComplexTransportedBinaryFan MetrizableLCA K).snd ≫
                Limits.Pi.map (fun j : J => f (some j))) ≫
                Pi.π (OptionProductDecompositionW151.optionTail MetrizableLCA L) j := by
                simp [Category.assoc]

/-- The remaining transported fan naturality input after the singleton projection is proved. -/
structure OptionTransportedFanMapTailProjectionNaturalityInput : Type (u + 1) where
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
The proved singleton projection plus the remaining tail projection naturality provide the full
transported fan projection naturality input.
-/
def optionTransportedFanMapProjectionNaturalityInput_of_tailProjection
    (tailProjectionNaturality : OptionTransportedFanMapTailProjectionNaturalityInput.{u}) :
    OptionTransportedFanMapProjectionNaturalityInput.{u} where
  fst_comm := by
    intro J _ K L _ _ _ _ _ f
    exact optionTransportedFanMapFstNaturality f
  snd_comm := by
    intro J _ K L _ _ _ _ _ f
    exact tailProjectionNaturality.snd_comm f

/-- The transported fan projection naturality input is now provided directly. -/
def optionTransportedFanMapProjectionNaturalityInput_direct :
    OptionTransportedFanMapProjectionNaturalityInput.{u} where
  fst_comm := by
    intro J _ K L _ _ _ _ _ f
    exact optionTransportedFanMapFstNaturality f
  snd_comm := by
    intro J _ K L _ _ _ _ _ f
    exact optionTransportedFanMapSndNaturality f

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

/-- The promoted Option-product decomposition is natural for product maps. -/
def optionProductMapNaturalityInput_direct : OptionProductMapNaturalityInput.{u} :=
  optionProductMapNaturalityInput_of_projectionNaturality
    optionTransportedFanMapProjectionNaturalityInput_direct

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

/-- Empty-index base case for the finite mapping-cone/product comparison induction. -/
structure EmptyMappingConeProductComparisonInput : Type (u + 1) where
  iso : ∀ {J : Type u} [IsEmpty J]
    {K L : J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    (f : ∀ j, K j ⟶ L j)
    [HasProduct (fun j => CochainComplex.mappingCone (f j))],
      CochainComplex.mappingCone (Limits.Pi.map f) ≅
        ∏ᶜ (fun j => CochainComplex.mappingCone (f j))

/--
The mapping cone of any morphism between the explicit zero cochain complex and itself is the
explicit zero cochain complex.
-/
noncomputable def mappingConeZeroZeroIsoZero
    (f : (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ) ⟶
      (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ)) :
    CochainComplex.mappingCone f ≅
      (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ) := by
  refine HomologicalComplex.Hom.isoOfComponents (C₁ := CochainComplex.mappingCone f)
    (C₂ := (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ)) (fun i => ?_) ?_
  · have hX : IsZero ((CochainComplex.mappingCone f).X i) := by
      rw [CochainComplex.mappingCone.isZero_X_iff]
      constructor <;> dsimp [HomologicalComplex.zero] <;> exact isZero_zero MetrizableLCA.{u}
    simpa [HomologicalComplex.zero] using hX.isoZero
  · intro i j hij
    apply (isZero_zero MetrizableLCA.{u}).eq_of_tgt

/-- The chosen zero complex is isomorphic to the explicit `HomologicalComplex.zero`. -/
noncomputable def zeroComplexIsoHomologicalZero :
    (0 : CochainComplex MetrizableLCA.{u} ℤ) ≅
      (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ) :=
  IsTerminal.uniqueUpToIso
    ((isZero_zero (CochainComplex MetrizableLCA.{u} ℤ) :
      IsZero (0 : CochainComplex MetrizableLCA.{u} ℤ)).isTerminal)
    ((HomologicalComplex.isZero_zero :
      IsZero (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ)).isTerminal)

/-- Empty products of cochain complexes as the explicit zero complex. -/
noncomputable def emptyProductIsoHomologicalZero
    {J : Type u} [IsEmpty J]
    (K : J → CochainComplex MetrizableLCA.{u} ℤ) [HasProduct K] :
    ∏ᶜ K ≅ (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ) :=
  FiniteProductExactness.emptyProductIsoZero K ≪≫ zeroComplexIsoHomologicalZero

/-- The empty-index base case for finite mapping-cone/product comparison. -/
noncomputable def emptyMappingConeProductComparisonInput_direct :
    EmptyMappingConeProductComparisonInput.{u} where
  iso := by
    intro J _ K L _ _ f _
    let eK := emptyProductIsoHomologicalZero K
    let eL := emptyProductIsoHomologicalZero L
    let f0 : (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ) ⟶
        (HomologicalComplex.zero : CochainComplex MetrizableLCA.{u} ℤ) :=
      eK.inv ≫ Limits.Pi.map f ≫ eL.hom
    have hcomm : Limits.Pi.map f ≫ eL.hom = eK.hom ≫ f0 := by
      dsimp [f0]
      simp
    exact mappingConeIsoOfCommIso MetrizableLCA eK eL hcomm ≪≫
      mappingConeZeroZeroIsoZero f0 ≪≫
        (emptyProductIsoHomologicalZero (fun j : J => CochainComplex.mappingCone (f j))).symm

/-- Product-map naturality for reindexing along a type equivalence. -/
theorem piMap_reindex_hom_naturality {α β : Type u} (e : α ≃ β)
    {K L : β → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L] [HasProduct (K ∘ e)] [HasProduct (L ∘ e)]
    [HasProduct (fun a : α => K (e a))] [HasProduct (fun a : α => L (e a))]
    (f : ∀ b, K b ⟶ L b) :
    Limits.Pi.map (fun a : α => (f (e a) : (K ∘ e) a ⟶ (L ∘ e) a)) ≫
        (Pi.reindex e L).hom =
      (Pi.reindex e K).hom ≫ Limits.Pi.map f := by
  apply Limits.Pi.hom_ext
  intro b
  rw [← e.apply_symm_apply b]
  have hL :
      (Pi.reindex e L).hom ≫ Pi.π L (e (e.symm b)) =
        Pi.π (L ∘ e) (e.symm b) :=
    Pi.reindex_hom_π e L (e.symm b)
  have hK :
      (Pi.reindex e K).hom ≫ Pi.π K (e (e.symm b)) =
        Pi.π (K ∘ e) (e.symm b) :=
    Pi.reindex_hom_π e K (e.symm b)
  have hleft :
      ((Limits.Pi.map (fun a : α => (f (e a) : (K ∘ e) a ⟶ (L ∘ e) a)) ≫
          (Pi.reindex e L).hom) ≫
          Pi.π L (e (e.symm b))) =
        Pi.π (K ∘ e) (e.symm b) ≫ f (e (e.symm b)) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg
        (fun g =>
          Limits.Pi.map
            (fun a : α => (f (e a) : (K ∘ e) a ⟶ (L ∘ e) a)) ≫ g)
        hL).trans
      (Pi.map_π
        (fun a : α => (f (e a) : (K ∘ e) a ⟶ (L ∘ e) a)) (e.symm b)))
  have hright :
      ((Pi.reindex e K).hom ≫ Limits.Pi.map f) ≫ Pi.π L (e (e.symm b)) =
        Pi.π (K ∘ e) (e.symm b) ≫ f (e (e.symm b)) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun g => (Pi.reindex e K).hom ≫ g)
        (Pi.map_π f (e (e.symm b)))).trans
      (congrArg (fun g => g ≫ f (e (e.symm b))) hK))
  exact hleft.trans hright.symm

/-- Reindexing along an equivalence transports the finite mapping-cone product comparison. -/
noncomputable def mappingConeProductComparisonIso_of_equiv
    (tailComparison : TailFiniteMappingConeComparisonInput.{u})
    {α β : Type u} [Finite α] [Finite β] (e : α ≃ β)
    {K L : β → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    (f : ∀ b, K b ⟶ L b)
    [HasProduct (fun b => CochainComplex.mappingCone (f b))] :
    CochainComplex.mappingCone (Limits.Pi.map f) ≅
      ∏ᶜ (fun b => CochainComplex.mappingCone (f b)) := by
  letI : HasProduct (K ∘ e) :=
    hasProduct_of_equiv_of_iso K (K ∘ e) e (fun _ => Iso.refl _)
  letI : HasProduct (fun a : α => K (e a)) :=
    hasProduct_of_equiv_of_iso K (fun a : α => K (e a)) e (fun _ => Iso.refl _)
  letI : HasProduct (L ∘ e) :=
    hasProduct_of_equiv_of_iso L (L ∘ e) e (fun _ => Iso.refl _)
  letI : HasProduct (fun a : α => L (e a)) :=
    hasProduct_of_equiv_of_iso L (fun a : α => L (e a)) e (fun _ => Iso.refl _)
  let coneFamily : β → CochainComplex MetrizableLCA.{u} ℤ :=
    fun b => CochainComplex.mappingCone (f b)
  letI : HasProduct (coneFamily ∘ e) :=
    hasProduct_of_equiv_of_iso coneFamily (coneFamily ∘ e) e (fun _ => Iso.refl _)
  letI : HasProduct (fun a : α => coneFamily (e a)) :=
    hasProduct_of_equiv_of_iso coneFamily (fun a : α => coneFamily (e a)) e
      (fun _ => Iso.refl _)
  let fα : ∀ a : α, (K ∘ e) a ⟶ (L ∘ e) a :=
    fun a => f (e a)
  letI : HasProduct (fun a : α => CochainComplex.mappingCone (fα a)) := by
    simpa [fα, coneFamily, Function.comp] using
      (inferInstance : HasProduct (fun a : α => coneFamily (e a)))
  have hcomm :
      Limits.Pi.map fα ≫ (Pi.reindex e L).hom =
        (Pi.reindex e K).hom ≫ Limits.Pi.map f := by
    simpa [fα] using piMap_reindex_hom_naturality e f
  exact
    (mappingConeIsoOfCommIso MetrizableLCA (Pi.reindex e K) (Pi.reindex e L) hcomm).symm ≪≫
      tailComparison.iso fα ≪≫
      Pi.reindex e coneFamily

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

/--
Option-step exactness consumer after proving Option-product-map naturality directly.

The only remaining Option-step input is the recursive tail comparison.
-/
theorem exactAcyclic_optionPiMap_of_tailComparison
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
    exactAcyclic MetrizableLCA (CochainComplex.mappingCone (Limits.Pi.map f)) :=
  exactAcyclic_optionPiMap_of_naturality_and_tailComparison
    optionProductMapNaturalityInput_direct tailComparison f hf

/--
Option-step comparison iso after proving Option-product-map naturality directly.

This is the iso-level version of `exactAcyclic_optionPiMap_of_tailComparison`: transport the
`Option J` product map to a binary biproduct map, use the binary mapping-cone comparison, replace
the tail cone by the recursive finite-product comparison, then fold the resulting biproduct back
to the Option-indexed product of component cones.
-/
noncomputable def optionMappingConeProductComparisonIso_of_tailComparison
    (tailComparison : TailFiniteMappingConeComparisonInput.{u})
    {J : Type u} [Finite J]
    {K L : Option J → CochainComplex MetrizableLCA.{u} ℤ}
    [HasProduct K] [HasProduct L]
    [HasProduct (fun j : J => K (some j))]
    [HasProduct (fun j : J => L (some j))]
    (f : ∀ j, K j ⟶ L j)
    [HasProduct (fun j : J => CochainComplex.mappingCone (f (some j)))]
    [HasProduct (fun j : Option J => CochainComplex.mappingCone (f j))]
    [∀ x : Option J, Decidable (x = none)] :
    CochainComplex.mappingCone (Limits.Pi.map f) ≅
      ∏ᶜ (fun j : Option J => CochainComplex.mappingCone (f j)) := by
  let tailMap : ∀ j : J, K (some j) ⟶ L (some j) := fun j => f (some j)
  let eK :=
    OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
      MetrizableLCA K
  let eL :=
    OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
      MetrizableLCA L
  have hcomm :
      Limits.Pi.map f ≫ eL.hom =
        eK.hom ≫ biprod.map (f none) (Limits.Pi.map tailMap) :=
    optionProductMapNaturalityInput_direct.commute f
  exact
    mappingConeIsoOfCommIso MetrizableLCA eK eL hcomm ≪≫
      MappingConeBiprodComparison.binaryMappingConeBiprodIso (f none) (Limits.Pi.map tailMap) ≪≫
        biprod.mapIso (Iso.refl (CochainComplex.mappingCone (f none)))
          (tailComparison.iso tailMap) ≪≫
          (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
            MetrizableLCA (fun j : Option J => CochainComplex.mappingCone (f j))).symm

/-- The full finite mapping-cone/product comparison from empty base, equivalence, and Option step. -/
noncomputable def tailFiniteMappingConeComparisonInput_direct :
    TailFiniteMappingConeComparisonInput.{u} where
  iso := by
    intro J _ K L _ _ f _
    let P : Type u → Prop :=
      fun J =>
        ∀ {K L : J → CochainComplex MetrizableLCA.{u} ℤ}
          [HasProduct K] [HasProduct L]
          (f : ∀ j, K j ⟶ L j)
          [HasProduct (fun j => CochainComplex.mappingCone (f j))],
            Nonempty
              (CochainComplex.mappingCone (Limits.Pi.map f) ≅
                ∏ᶜ (fun j => CochainComplex.mappingCone (f j)))
    have hP : P J := by
      refine (Finite.induction_empty_option (P := P) ?of_equiv ?h_empty ?h_option) J
      · intro α β e hα K L _ _ f _
        letI : HasProduct (K ∘ e) :=
          hasProduct_of_equiv_of_iso K (K ∘ e) e (fun _ => Iso.refl _)
        letI : HasProduct (fun a : α => K (e a)) :=
          hasProduct_of_equiv_of_iso K (fun a : α => K (e a)) e (fun _ => Iso.refl _)
        letI : HasProduct (L ∘ e) :=
          hasProduct_of_equiv_of_iso L (L ∘ e) e (fun _ => Iso.refl _)
        letI : HasProduct (fun a : α => L (e a)) :=
          hasProduct_of_equiv_of_iso L (fun a : α => L (e a)) e (fun _ => Iso.refl _)
        let coneFamily : β → CochainComplex MetrizableLCA.{u} ℤ :=
          fun b => CochainComplex.mappingCone (f b)
        letI : HasProduct (coneFamily ∘ e) :=
          hasProduct_of_equiv_of_iso coneFamily (coneFamily ∘ e) e (fun _ => Iso.refl _)
        letI : HasProduct (fun a : α => coneFamily (e a)) :=
          hasProduct_of_equiv_of_iso coneFamily (fun a : α => coneFamily (e a)) e
            (fun _ => Iso.refl _)
        let fα : ∀ a : α, (K ∘ e) a ⟶ (L ∘ e) a :=
          fun a => f (e a)
        letI : HasProduct (fun a : α => CochainComplex.mappingCone (fα a)) := by
          simpa [fα, coneFamily, Function.comp] using
            (inferInstance : HasProduct (fun a : α => coneFamily (e a)))
        have hcomm :
            Limits.Pi.map fα ≫ (Pi.reindex e L).hom =
              (Pi.reindex e K).hom ≫ Limits.Pi.map f := by
          simpa [fα] using piMap_reindex_hom_naturality e f
        exact ⟨
          (mappingConeIsoOfCommIso MetrizableLCA (Pi.reindex e K) (Pi.reindex e L) hcomm).symm ≪≫
            Classical.choice (hα fα) ≪≫
            Pi.reindex e coneFamily⟩
      · intro K L _ _ f _
        exact ⟨emptyMappingConeProductComparisonInput_direct.iso f⟩
      · intro α _ hα K L _ _ f _
        letI : HasProduct (fun j : α => K (some j)) := by infer_instance
        letI : HasProduct (fun j : α => L (some j)) := by infer_instance
        letI : HasProduct (fun j : α => CochainComplex.mappingCone (f (some j))) := by infer_instance
        let tailMap : ∀ j : α, K (some j) ⟶ L (some j) := fun j => f (some j)
        let eK :=
          OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
            MetrizableLCA K
        let eL :=
          OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
            MetrizableLCA L
        have hcomm :
            Limits.Pi.map f ≫ eL.hom =
              eK.hom ≫ biprod.map (f none) (Limits.Pi.map tailMap) :=
          optionProductMapNaturalityInput_direct.commute f
        exact ⟨
          mappingConeIsoOfCommIso MetrizableLCA eK eL hcomm ≪≫
            MappingConeBiprodComparison.binaryMappingConeBiprodIso (f none)
              (Limits.Pi.map tailMap) ≪≫
              biprod.mapIso (Iso.refl (CochainComplex.mappingCone (f none)))
                (Classical.choice (hα tailMap)) ≪≫
                (OptionProductDecompositionW151.optionProductIsoBiprod_finiteProductCallsite_finiteProducts_of_direct
                  MetrizableLCA (fun j : Option α => CochainComplex.mappingCone (f j))).symm⟩
    exact Classical.choice (hP (K := K) (L := L) f)

/-- The exact lower inputs still missing after the Option-step exactness consumer. -/
def optionMappingConeComparisonStepMissingInputs : List String :=
  []

theorem optionMappingConeComparisonStepMissingInputs_count :
    optionMappingConeComparisonStepMissingInputs.length = 0 := rfl

section Checks

#check OptionProductMapNaturalityInput
#check optionProductIsoBiprod_finiteProducts_hom_fst
#check optionProductIsoBiprod_finiteProducts_hom_snd
#check OptionTransportedFanMapProjectionNaturalityInput
#check optionTransportedFanMapFstNaturality
#check optionProductComplexTransportedBinaryFan_snd_π
#check optionTransportedFanMapSndNaturality
#check OptionTransportedFanMapTailProjectionNaturalityInput
#check optionTransportedFanMapProjectionNaturalityInput_of_tailProjection
#check optionTransportedFanMapProjectionNaturalityInput_direct
#check optionProductMapNaturalityInput_of_projectionNaturality
#check optionProductMapNaturalityInput_direct
#check TailFiniteMappingConeComparisonInput
#check EmptyMappingConeProductComparisonInput
#check mappingConeZeroZeroIsoZero
#check zeroComplexIsoHomologicalZero
#check emptyProductIsoHomologicalZero
#check emptyMappingConeProductComparisonInput_direct
#check piMap_reindex_hom_naturality
#check mappingConeProductComparisonIso_of_equiv
#check exactAcyclic_optionPiMap_of_naturality_and_tailComparison
#check exactAcyclic_optionPiMap_of_tailComparison
#check optionMappingConeProductComparisonIso_of_tailComparison
#check tailFiniteMappingConeComparisonInput_direct
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
