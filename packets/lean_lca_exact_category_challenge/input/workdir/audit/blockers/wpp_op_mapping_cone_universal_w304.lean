import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import LeanLCAExactChallenge.Derived.WppOpMappingConeUniqueMediator
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W304: unique-mediating-map boundary for the fixed WPP-op mapping-cone cocone.

W303 reduced the fixed concrete mapping-cone cocone colimit input to explicit
`desc`/`fac`/`uniq` universal data.  This file keeps that compilable boundary
self-contained and adds the next proof boundary: it is enough to prove the usual
unique existence of a mediating morphism from the fixed mapping-cone cocone point
to each test cocone.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeFixedCoconeW303

/-- The direct bounded exact weak-equivalence class for metrizable LCAs. -/
abbrev metrizableLCAWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/-- The fixed objectwise mapping-cone diagram from W302. -/
noncomputable def mappingConeDiagram {J : Type} [Category J]
    (X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}) (f : X₁ ⟶ X₂) :
    J ⥤ CochainComplex MetrizableLCA.{0} ℤ where
  obj j :=
    CochainComplex.mappingCone
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
  map {j j'} α :=
    CochainComplex.mappingCone.map
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
      (by
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congrArg
          (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
          (f.naturality α).symm)
  map_id j := by
    simpa using
      CochainComplex.mappingCone.map_id
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
  map_comp {i j k} α β := by
    simpa [Functor.map_comp] using
      (CochainComplex.mappingCone.map_comp
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app i))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app k))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
            (f.naturality α).symm)
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map β))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map β))
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
            (f.naturality β).symm))

/-- The fixed diagram has the expected objectwise mapping cones. -/
theorem mappingConeDiagram_obj
    (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (f : X₁ ⟶ X₂) (j : WalkingParallelPairᵒᵖ) :
    (mappingConeDiagram X₁ X₂ f).obj j =
      CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) :=
  rfl

/-- The fixed mapping-cone cocone from W302. -/
noncomputable def mappingConeCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    Cocone (mappingConeDiagram X₁ X₂ f) where
  pt :=
    CochainComplex.mappingCone
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
  ι :=
    { app := fun j =>
        CochainComplex.mappingCone.map
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j))
          (by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg
              (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
              (hφ j).symm)
      naturality := by
        intro j j' α
        dsimp [mappingConeDiagram]
        rw [← CochainComplex.mappingCone.map_comp]
        congr 2
        · exact congrArg (fun g => g.hom) (c₁.w α)
        · exact congrArg (fun g => g.hom) (c₂.w α) }

/-- The fixed cocone point is definitionally the mapping cone of the comparison map. -/
theorem mappingConeCocone_pt
    {X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    (mappingConeCocone c₁ c₂ f φ hφ).pt =
      CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) :=
  rfl

/-- The W302 fixed-cocone input: prove that the concrete mapping-cone cocone is colimiting. -/
abbrev walkingParallelPairOp_mappingCone_fixedCoconeColimitInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j),
        Nonempty (IsColimit (mappingConeCocone c₁ c₂ f φ hφ))

/-- Explicit universal-property data for the fixed mapping-cone cocone. -/
structure FixedMappingConeCoconeUniversalData
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : Type 2 where
  desc : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt
  fac : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f)) (j : J),
    (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ desc s = s.ι.app j
  uniq : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f))
    (m : (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt),
      (∀ j : J, (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j) →
        m = desc s

/-- The explicit universal-property package builds an `IsColimit` proof. -/
noncomputable def isColimitOfFixedMappingConeCoconeUniversalData
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (D : FixedMappingConeCoconeUniversalData c₁ c₂ f φ hφ) :
    IsColimit (mappingConeCocone c₁ c₂ f φ hφ) where
  desc := D.desc
  fac := D.fac
  uniq := D.uniq

/-- Any `IsColimit` proof for the fixed cocone gives the explicit desc/fac/uniq package. -/
noncomputable def fixedMappingConeCoconeUniversalDataOfIsColimit
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (h : IsColimit (mappingConeCocone c₁ c₂ f φ hφ)) :
    FixedMappingConeCoconeUniversalData c₁ c₂ f φ hφ where
  desc := h.desc
  fac := h.fac
  uniq := h.uniq

/-- The reduced W303 input: prove the explicit universal-property package. -/
abbrev walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j),
        Nonempty (FixedMappingConeCoconeUniversalData c₁ c₂ f φ hφ)

/-- The reduced universal-property input supplies W302's fixed-cocone colimit input. -/
theorem walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_universalInput
    (h : walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput) :
    walkingParallelPairOp_mappingCone_fixedCoconeColimitInput := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  rcases h X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ with ⟨D⟩
  exact ⟨isColimitOfFixedMappingConeCoconeUniversalData D⟩

/-- Conversely, W302's fixed-cocone colimit input supplies the reduced universal package. -/
theorem walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput_of_colimitInput
    (h : walkingParallelPairOp_mappingCone_fixedCoconeColimitInput) :
    walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  rcases h X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ with ⟨hc⟩
  exact ⟨fixedMappingConeCoconeUniversalDataOfIsColimit hc⟩

/-- W303 reduces the target exactly to the explicit desc/fac/uniq package. -/
theorem walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_iff_universalInput :
    walkingParallelPairOp_mappingCone_fixedCoconeColimitInput ↔
      walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput := by
  constructor
  · exact walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput_of_colimitInput
  · exact walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_universalInput

/-- Machine-readable frontier state for WppOpMappingConeFixedCoconeW303. -/
structure WppOpMappingConeFixedCoconeState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W303 boundary state. -/
def currentWppOpMappingConeFixedCoconeState : WppOpMappingConeFixedCoconeState where
  seed := "w303-parent-20260520T1624Z"
  selectedRoute :=
    "fixed mapping-cone cocone reduced to explicit desc/fac/uniq universal data"
  checkedBoundary :=
    "walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput"
  provedConsumer :=
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_iff_universalInput"
  remainingInputs :=
    ["construct desc/fac/uniq for the concrete mappingConeCocone c₁ c₂ f φ hφ",
      "or prove a genuine WPP-op mapping-cone colimit theorem that supplies those fields"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeFixedCoconeState_productSuccess :
    currentWppOpMappingConeFixedCoconeState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpMappingConeFixedCoconeDeclarationNames : List String :=
  ["mappingConeDiagram",
    "mappingConeCocone",
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput",
    "FixedMappingConeCoconeUniversalData",
    "isColimitOfFixedMappingConeCoconeUniversalData",
    "fixedMappingConeCoconeUniversalDataOfIsColimit",
    "walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput",
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_iff_universalInput",
    "currentWppOpMappingConeFixedCoconeState"]

theorem wppOpMappingConeFixedCoconeDeclarationNames_count :
    wppOpMappingConeFixedCoconeDeclarationNames.length = 9 := rfl

section Checks

#check metrizableLCAWeakEquivalence
#check mappingConeDiagram
#check mappingConeDiagram_obj
#check mappingConeCocone
#check mappingConeCocone_pt
#check walkingParallelPairOp_mappingCone_fixedCoconeColimitInput
#check FixedMappingConeCoconeUniversalData
#check isColimitOfFixedMappingConeCoconeUniversalData
#check fixedMappingConeCoconeUniversalDataOfIsColimit
#check walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput
#check walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_universalInput
#check walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput_of_colimitInput
#check walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_iff_universalInput
#check currentWppOpMappingConeFixedCoconeState
#check currentWppOpMappingConeFixedCoconeState_productSuccess
#check wppOpMappingConeFixedCoconeDeclarationNames
#check wppOpMappingConeFixedCoconeDeclarationNames_count
#check MappingConeFiniteProduct.tailFiniteMappingConeComparisonInput_direct
#check MappingConeBiprodComparison.binaryMappingConeBiprodIso
#check IsColimit.mk

end Checks

end WppOpMappingConeFixedCoconeW303

namespace WppOpMappingConeUniversalW304

/--
For each test cocone over the fixed mapping-cone diagram, there is a unique
mediating map out of the fixed mapping-cone cocone point.
-/
abbrev FixedMappingConeCoconeUniqueMediatingInput
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : Prop :=
  ∀ s : Cocone (WppOpMappingConeFixedCoconeW303.mappingConeDiagram X₁ X₂ f),
    ∃! m : (WppOpMappingConeFixedCoconeW303.mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt,
      ∀ j : J, (WppOpMappingConeFixedCoconeW303.mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j

/--
Unique mediating maps construct W303's explicit `desc`/`fac`/`uniq` data.
-/
noncomputable def fixedMappingConeCoconeUniversalDataOfUniqueMediating
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (huniq : FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ) :
    WppOpMappingConeFixedCoconeW303.FixedMappingConeCoconeUniversalData c₁ c₂ f φ hφ where
  desc s := Classical.choose (huniq s)
  fac s j := (Classical.choose_spec (huniq s)).1 j
  uniq s m hm := (Classical.choose_spec (huniq s)).2 m hm

/-- The W304 reduced input: prove unique mediating maps for the fixed cocone. -/
abbrev walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j),
        FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ

/--
The W304 unique-mediating-map input supplies W303's explicit universal-data
input.
-/
theorem walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput_of_uniqueMediating
    (h : walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput) :
    WppOpMappingConeFixedCoconeW303.walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  exact ⟨fixedMappingConeCoconeUniversalDataOfUniqueMediating
    (h X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ)⟩

/--
The W304 unique-mediating-map input supplies W303's fixed-cocone colimit input.
-/
theorem walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_uniqueMediating
    (h : walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput) :
    WppOpMappingConeFixedCoconeW303.walkingParallelPairOp_mappingCone_fixedCoconeColimitInput :=
  WppOpMappingConeFixedCoconeW303.walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_universalInput
    (walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput_of_uniqueMediating h)

/--
The included-colimit W308 theorem supplies the W304 unique-mediating-map input
for the actual WPP-op fixed mapping-cone cocone.
-/
theorem walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput_of_includedColimits :
    walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  have huniq :=
    WppOpMappingConeUniqueMediatorW308.uniqueMediatingInput_of_includedColimits
      (X₁ := X₁) (X₂ := X₂) (c₁ := c₁) (c₂ := c₂) (f := f)
      (isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₁)
      hc₂ φ hφ
  simpa [FixedMappingConeCoconeUniqueMediatingInput,
    WppOpMappingConeUniqueMediatorW308.FixedMappingConeCoconeUniqueMediatingInput,
    WppOpMappingConeFixedCoconeW303.mappingConeDiagram,
    WppOpMappingConeUniqueMediatorW308.mappingConeDiagram,
    WppOpMappingConeFixedCoconeW303.mappingConeCocone,
    WppOpMappingConeUniqueMediatorW308.mappingConeCocone] using huniq

/--
The included-colimit W308 theorem supplies W303's fixed-cocone colimit input.
-/
theorem walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits :
    WppOpMappingConeFixedCoconeW303.walkingParallelPairOp_mappingCone_fixedCoconeColimitInput :=
  walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_uniqueMediating
    walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput_of_includedColimits

/-- Machine-readable frontier state for W304. -/
structure WppOpMappingConeUniversalState : Type where
  seed : String
  selectedRoute : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W304 boundary state. -/
def currentWppOpMappingConeUniversalState : WppOpMappingConeUniversalState where
  seed := "w304-parent-20260521T0123Z"
  selectedRoute :=
    "fixed mapping-cone cocone universal data reduced to unique mediating maps"
  provedConsumer :=
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits"
  remainingInputs :=
    ["wire W303/W304 fixed-cocone colimit input into W302/W276 mapping-cone comparison consumer",
      "continue the remaining W318 topological/algebraic exactness frontier if mapping-cone comparison is fully consumed"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeUniversalState_productSuccess :
    currentWppOpMappingConeUniversalState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpMappingConeUniversalDeclarationNames : List String :=
  ["FixedMappingConeCoconeUniqueMediatingInput",
    "fixedMappingConeCoconeUniversalDataOfUniqueMediating",
    "walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput",
    "walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput_of_uniqueMediating",
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_uniqueMediating",
    "walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput_of_includedColimits",
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits",
    "currentWppOpMappingConeUniversalState"]

theorem wppOpMappingConeUniversalDeclarationNames_count :
    wppOpMappingConeUniversalDeclarationNames.length = 8 := rfl

section Checks

#check WppOpMappingConeFixedCoconeW303.mappingConeDiagram
#check WppOpMappingConeFixedCoconeW303.mappingConeCocone
#check WppOpMappingConeFixedCoconeW303.FixedMappingConeCoconeUniversalData
#check WppOpMappingConeFixedCoconeW303.walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput
#check WppOpMappingConeFixedCoconeW303.walkingParallelPairOp_mappingCone_fixedCoconeColimitInput
#check FixedMappingConeCoconeUniqueMediatingInput
#check fixedMappingConeCoconeUniversalDataOfUniqueMediating
#check walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput
#check walkingParallelPairOp_mappingCone_fixedCoconeUniversalInput_of_uniqueMediating
#check walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_uniqueMediating
#check walkingParallelPairOp_mappingCone_fixedCoconeUniqueMediatingInput_of_includedColimits
#check walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits
#check currentWppOpMappingConeUniversalState
#check currentWppOpMappingConeUniversalState_productSuccess
#check wppOpMappingConeUniversalDeclarationNames
#check wppOpMappingConeUniversalDeclarationNames_count
#check ExistsUnique
#check IsColimit.mk

end Checks

end WppOpMappingConeUniversalW304

end LeanLCAExactChallenge
