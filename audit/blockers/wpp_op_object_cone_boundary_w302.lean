import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import LeanLCAExactChallenge.Derived.WppOpMappingConeUniqueMediator
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W302: concrete object-level WPP-op mapping-cone boundary.

W276 reduced the W271 mapping-cone comparison input to an object-level boundary
that still allowed an arbitrary comparison diagram.  This file follows the useful
signal from support W278 and fixes the diagram: its object at `j` is the mapping
cone of the `j`-component of a natural transformation of bounded-complex
diagrams.  The remaining input is only the colimit proof for this concrete
mapping-cone cocone.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpObjectConeBoundaryW302

/-- The direct bounded exact weak-equivalence class for metrizable LCAs. -/
abbrev metrizableLCAWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{0}) :=
  boundedExactWeakEquivalence MetrizableLCA.{0}

/--
The concrete diagram whose object at `j` is the mapping cone of the `j`-component
of a natural transformation of bounded-complex diagrams.
-/
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

/-- The fixed diagram has exactly the W276 component mapping cones as its objects. -/
theorem mappingConeDiagram_obj
    (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (f : X₁ ⟶ X₂) (j : WalkingParallelPairᵒᵖ) :
    (mappingConeDiagram X₁ X₂ f).obj j =
      CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) :=
  rfl

/--
The concrete cocone over `mappingConeDiagram X₁ X₂ f` induced by compatible
colimit cocones `c₁`, `c₂`, and comparison map `φ`.
-/
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

/-- The concrete cocone point is definitionally the mapping cone of the comparison map. -/
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

/-- W276's object-level boundary, restated locally. -/
abbrev walkingParallelPairOp_mappingCone_objectComparisonBoundary : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt),
      (∀ j : WalkingParallelPairᵒᵖ,
        c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
        ∃ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
          (ck : Cocone K),
            Nonempty (IsColimit ck) ∧
              (∀ j : WalkingParallelPairᵒᵖ,
                Nonempty
                  (CochainComplex.mappingCone
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≅
                      K.obj j)) ∧
              Nonempty
                (CochainComplex.mappingCone
                  ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/--
The smaller remaining input after fixing the component mapping-cone diagram.
-/
abbrev walkingParallelPairOp_mappingCone_fixedDiagramColimitInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt),
      (∀ j : WalkingParallelPairᵒᵖ,
        c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
        ∃ (ck : Cocone (mappingConeDiagram X₁ X₂ f)),
          Nonempty (IsColimit ck) ∧
            Nonempty
              (CochainComplex.mappingCone
                ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/--
The sharper remaining input after both the component mapping-cone diagram and its
induced cocone are fixed.
-/
abbrev walkingParallelPairOp_mappingCone_fixedCoconeColimitInput : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : WalkingParallelPairᵒᵖ,
      c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j),
        Nonempty (IsColimit (mappingConeCocone c₁ c₂ f φ hφ))

/-- Local unique-mediating-map package for the fixed mapping-cone cocone. -/
abbrev FixedMappingConeCoconeUniqueMediatingInput
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : Prop :=
  ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    ∃! m : (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt,
      ∀ j : J, (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j

/-- Unique mediating maps build the fixed mapping-cone cocone colimit proof. -/
noncomputable def isColimitOfFixedMappingConeCoconeUniqueMediating
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (huniq : FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ) :
    IsColimit (mappingConeCocone c₁ c₂ f φ hφ) where
  desc s := Classical.choose (huniq s)
  fac s j := (Classical.choose_spec (huniq s)).1 j
  uniq s m hm := (Classical.choose_spec (huniq s)).2 m hm

/-- The W308 included-colimit theorem supplies W302's fixed-cocone colimit input. -/
theorem walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits :
    walkingParallelPairOp_mappingCone_fixedCoconeColimitInput := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  have huniq308 :=
    WppOpMappingConeUniqueMediatorW308.uniqueMediatingInput_of_includedColimits
      (X₁ := X₁) (X₂ := X₂) (c₁ := c₁) (c₂ := c₂) (f := f)
      (isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₁)
      hc₂ φ hφ
  have huniq :
      FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ := by
    simpa [FixedMappingConeCoconeUniqueMediatingInput,
      WppOpMappingConeUniqueMediatorW308.FixedMappingConeCoconeUniqueMediatingInput,
      mappingConeDiagram,
      WppOpMappingConeUniqueMediatorW308.mappingConeDiagram,
      mappingConeCocone,
      WppOpMappingConeUniqueMediatorW308.mappingConeCocone] using huniq308
  exact ⟨isColimitOfFixedMappingConeCoconeUniqueMediating huniq⟩

/-- The fixed-cocone colimit input supplies the fixed-diagram colimit input. -/
theorem walkingParallelPairOp_mappingCone_fixedDiagramColimitInput_of_fixedCoconeColimit
    (hfixed : walkingParallelPairOp_mappingCone_fixedCoconeColimitInput) :
    walkingParallelPairOp_mappingCone_fixedDiagramColimitInput := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  refine ⟨mappingConeCocone c₁ c₂ f φ hφ,
    hfixed X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ, ?_⟩
  exact ⟨Iso.refl _⟩

/--
The fixed concrete diagram colimit input formally supplies W276's object-level
comparison boundary.
-/
theorem walkingParallelPairOp_mappingCone_objectComparisonBoundary_of_fixedDiagramColimit
    (hfixed : walkingParallelPairOp_mappingCone_fixedDiagramColimitInput) :
    walkingParallelPairOp_mappingCone_objectComparisonBoundary := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ
  rcases hfixed X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ with ⟨ck, hck, hcone⟩
  refine ⟨mappingConeDiagram X₁ X₂ f, ck, hck, ?_, hcone⟩
  intro j
  exact ⟨Iso.refl _⟩

/-- W276's full mapping-cone comparison input, restated locally. -/
abbrev mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison : Prop :=
  ∀ (X₁ X₂ : WalkingParallelPairᵒᵖ ⥤ BoundedComplexCategory MetrizableLCA.{0})
    (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (_ : IsColimit c₁) (_ : IsColimit c₂) (f : X₁ ⟶ X₂),
      (metrizableLCAWeakEquivalence).functorCategory WalkingParallelPairᵒᵖ f →
        ∀ (φ : c₁.pt ⟶ c₂.pt),
          (∀ j : WalkingParallelPairᵒᵖ,
            c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) →
            ∃ (K : WalkingParallelPairᵒᵖ ⥤ CochainComplex MetrizableLCA.{0} ℤ)
              (ck : Cocone K),
                Nonempty (IsColimit ck) ∧
                  (∀ j : WalkingParallelPairᵒᵖ,
                    exactAcyclic MetrizableLCA (K.obj j)) ∧
                  Nonempty
                    (CochainComplex.mappingCone
                        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≅ ck.pt)

/-- The fixed-diagram colimit input supplies W276's full comparison input. -/
theorem mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_fixedDiagramColimit
    (hfixed : walkingParallelPairOp_mappingCone_fixedDiagramColimitInput) :
    mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  rcases
    walkingParallelPairOp_mappingCone_objectComparisonBoundary_of_fixedDiagramColimit hfixed
      X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ with
    ⟨K, ck, hck, hK, hcone⟩
  refine ⟨K, ck, hck, ?_, hcone⟩
  intro j
  rcases hK j with ⟨e⟩
  exact exactAcyclic_of_iso MetrizableLCA e (by
    change exactAcyclic MetrizableLCA
      (CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)))
    exact hf j)

/--
The W308 included-colimit theorem supplies W276's full mapping-cone comparison
input through the W302 fixed-cocone route.
-/
theorem mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_includedColimits :
    mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison :=
  mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_fixedDiagramColimit
    (walkingParallelPairOp_mappingCone_fixedDiagramColimitInput_of_fixedCoconeColimit
      walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits)

/-- Machine-readable frontier state for W302. -/
structure WppOpObjectConeBoundaryState : Type where
  seed : String
  selectedRoute : String
  checkedBoundary : String
  provedConsumer : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W302 boundary state. -/
def currentWppOpObjectConeBoundaryState : WppOpObjectConeBoundaryState where
  seed := "w302-parent-20260520T1620Z"
  selectedRoute :=
    "fixed WPP-op objectwise mapping-cone diagram and consumed included-colimit cocone proof"
  checkedBoundary :=
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison"
  provedConsumer :=
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_includedColimits"
  remainingInputs :=
    ["consume this comparison theorem in the W271 exact-acyclic WPP-op colimit closure route",
      "continue any remaining non-mapping-cone exactness/topology blockers"]
  productSuccessClaimed := false

theorem currentWppOpObjectConeBoundaryState_productSuccess :
    currentWppOpObjectConeBoundaryState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def wppOpObjectConeBoundaryDeclarationNames : List String :=
  ["mappingConeDiagram",
    "mappingConeDiagram_obj",
    "mappingConeCocone",
    "mappingConeCocone_pt",
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput",
    "FixedMappingConeCoconeUniqueMediatingInput",
    "isColimitOfFixedMappingConeCoconeUniqueMediating",
    "walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits",
    "walkingParallelPairOp_mappingCone_fixedDiagramColimitInput_of_fixedCoconeColimit",
    "walkingParallelPairOp_mappingCone_fixedDiagramColimitInput",
    "walkingParallelPairOp_mappingCone_objectComparisonBoundary_of_fixedDiagramColimit",
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_fixedDiagramColimit",
    "mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_includedColimits",
    "currentWppOpObjectConeBoundaryState"]

theorem wppOpObjectConeBoundaryDeclarationNames_count :
    wppOpObjectConeBoundaryDeclarationNames.length = 14 := rfl

section Checks

#check mappingConeDiagram
#check mappingConeDiagram_obj
#check mappingConeCocone
#check mappingConeCocone_pt
#check walkingParallelPairOp_mappingCone_objectComparisonBoundary
#check walkingParallelPairOp_mappingCone_fixedDiagramColimitInput
#check walkingParallelPairOp_mappingCone_fixedCoconeColimitInput
#check FixedMappingConeCoconeUniqueMediatingInput
#check isColimitOfFixedMappingConeCoconeUniqueMediating
#check walkingParallelPairOp_mappingCone_fixedCoconeColimitInput_of_includedColimits
#check walkingParallelPairOp_mappingCone_fixedDiagramColimitInput_of_fixedCoconeColimit
#check walkingParallelPairOp_mappingCone_objectComparisonBoundary_of_fixedDiagramColimit
#check mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison
#check mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_fixedDiagramColimit
#check mappingCone_bounded_inclusion_walkingParallelPairOp_colimit_comparison_of_includedColimits
#check currentWppOpObjectConeBoundaryState
#check currentWppOpObjectConeBoundaryState_productSuccess
#check wppOpObjectConeBoundaryDeclarationNames
#check wppOpObjectConeBoundaryDeclarationNames_count
#check CochainComplex.mappingCone.map
#check CochainComplex.mappingCone.map_comp
#check exactAcyclic_of_iso

end Checks

end WppOpObjectConeBoundaryW302

end LeanLCAExactChallenge
