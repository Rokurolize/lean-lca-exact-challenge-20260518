import LeanLCAExactChallenge.Derived.Bounded

/-!
V189 probe: component maps for the binary mapping-cone/biproduct comparison.

This file records the lower construction needed after W142: the candidate degreewise maps
between `mappingCone (biprod.map f₁ f₂)` and the binary biproduct of the component mapping
cones.  The remaining hard part is proving these component maps commute with the differentials
and packaging them as a complex isomorphism.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MappingConeBiprodComparisonProbeV189

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

variable {K₁ K₂ L₁ L₂ : CochainComplex C ℤ}
variable (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)

noncomputable abbrev coneBiprodMap : CochainComplex C ℤ :=
  CochainComplex.mappingCone (biprod.map f₁ f₂)

noncomputable abbrev biprodCone : CochainComplex C ℤ :=
  CochainComplex.mappingCone f₁ ⊞ CochainComplex.mappingCone f₂

noncomputable def coneBiprodMapToLeftComponent (n : ℤ) :
    (coneBiprodMap f₁ f₂).X n ⟶ (CochainComplex.mappingCone f₁).X n :=
  (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl ≫
      (biprod.fst : K₁ ⊞ K₂ ⟶ K₁).f (n + 1) ≫
        (CochainComplex.mappingCone.inl f₁).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v n n (add_zero n) ≫
      (biprod.fst : L₁ ⊞ L₂ ⟶ L₁).f n ≫
        (CochainComplex.mappingCone.inr f₁).f n

noncomputable def coneBiprodMapToRightComponent (n : ℤ) :
    (coneBiprodMap f₁ f₂).X n ⟶ (CochainComplex.mappingCone f₂).X n :=
  (CochainComplex.mappingCone.fst (biprod.map f₁ f₂)).1.v n (n + 1) rfl ≫
      (biprod.snd : K₁ ⊞ K₂ ⟶ K₂).f (n + 1) ≫
        (CochainComplex.mappingCone.inl f₂).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd (biprod.map f₁ f₂)).v n n (add_zero n) ≫
      (biprod.snd : L₁ ⊞ L₂ ⟶ L₂).f n ≫
        (CochainComplex.mappingCone.inr f₂).f n

noncomputable def coneBiprodMapToBiprodConeX (n : ℤ) :
    (coneBiprodMap f₁ f₂).X n ⟶ (biprodCone f₁ f₂).X n :=
  biprod.lift
      (coneBiprodMapToLeftComponent f₁ f₂ n)
      (coneBiprodMapToRightComponent f₁ f₂ n) ≫
    (HomologicalComplex.biprodXIso
      (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).inv

noncomputable def leftComponentToConeBiprodMap (n : ℤ) :
    (CochainComplex.mappingCone f₁).X n ⟶ (coneBiprodMap f₁ f₂).X n :=
  (CochainComplex.mappingCone.fst f₁).1.v n (n + 1) rfl ≫
      (biprod.inl : K₁ ⟶ K₁ ⊞ K₂).f (n + 1) ≫
        (CochainComplex.mappingCone.inl (biprod.map f₁ f₂)).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd f₁).v n n (add_zero n) ≫
      (biprod.inl : L₁ ⟶ L₁ ⊞ L₂).f n ≫
        (CochainComplex.mappingCone.inr (biprod.map f₁ f₂)).f n

noncomputable def rightComponentToConeBiprodMap (n : ℤ) :
    (CochainComplex.mappingCone f₂).X n ⟶ (coneBiprodMap f₁ f₂).X n :=
  (CochainComplex.mappingCone.fst f₂).1.v n (n + 1) rfl ≫
      (biprod.inr : K₂ ⟶ K₁ ⊞ K₂).f (n + 1) ≫
        (CochainComplex.mappingCone.inl (biprod.map f₁ f₂)).v (n + 1) n (by omega) +
    (CochainComplex.mappingCone.snd f₂).v n n (add_zero n) ≫
      (biprod.inr : L₂ ⟶ L₁ ⊞ L₂).f n ≫
        (CochainComplex.mappingCone.inr (biprod.map f₁ f₂)).f n

noncomputable def biprodConeToConeBiprodMapX (n : ℤ) :
    (biprodCone f₁ f₂).X n ⟶ (coneBiprodMap f₁ f₂).X n :=
  (HomologicalComplex.biprodXIso
      (CochainComplex.mappingCone f₁) (CochainComplex.mappingCone f₂) n).hom ≫
    biprod.desc
      (leftComponentToConeBiprodMap f₁ f₂ n)
      (rightComponentToConeBiprodMap f₁ f₂ n)

structure BinaryMappingConeBiprodDifferentialCompatibility : Prop where
  left_to_right :
    ∀ (n : ℤ),
      coneBiprodMapToBiprodConeX f₁ f₂ n ≫ (biprodCone f₁ f₂).d n (n + 1) =
        (coneBiprodMap f₁ f₂).d n (n + 1) ≫ coneBiprodMapToBiprodConeX f₁ f₂ (n + 1)
  right_to_left :
    ∀ (n : ℤ),
      biprodConeToConeBiprodMapX f₁ f₂ n ≫ (coneBiprodMap f₁ f₂).d n (n + 1) =
        (biprodCone f₁ f₂).d n (n + 1) ≫ biprodConeToConeBiprodMapX f₁ f₂ (n + 1)

structure BinaryMappingConeBiprodInverseCompatibility : Prop where
  cone_biprod_cone :
    ∀ (n : ℤ),
      coneBiprodMapToBiprodConeX f₁ f₂ n ≫ biprodConeToConeBiprodMapX f₁ f₂ n = 𝟙 _
  biprod_cone_biprod :
    ∀ (n : ℤ),
      biprodConeToConeBiprodMapX f₁ f₂ n ≫ coneBiprodMapToBiprodConeX f₁ f₂ n = 𝟙 _

def v189ComponentMapFrontier : List String :=
  ["component maps from mappingCone (biprod.map f₁ f₂) to the biproduct cone",
    "component maps from the biproduct cone to mappingCone (biprod.map f₁ f₂)",
    "remaining: differential compatibility for both component-map families",
    "remaining: inverse identities after the differential-compatible complex morphisms exist"]

theorem v189ComponentMapFrontier_count :
    v189ComponentMapFrontier.length = 4 := rfl

section Checks

#check coneBiprodMapToLeftComponent
#check coneBiprodMapToRightComponent
#check coneBiprodMapToBiprodConeX
#check leftComponentToConeBiprodMap
#check rightComponentToConeBiprodMap
#check biprodConeToConeBiprodMapX
#check BinaryMappingConeBiprodDifferentialCompatibility
#check BinaryMappingConeBiprodInverseCompatibility
#check v189ComponentMapFrontier
#check v189ComponentMapFrontier_count
#check CochainComplex.mappingCone.ext_to
#check CochainComplex.mappingCone.ext_from
#check HomologicalComplex.biprodXIso

end Checks

end MappingConeBiprodComparisonProbeV189

end LeanLCAExactChallenge
