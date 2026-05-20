import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
W308: narrowing the fixed mapping-cone cocone unique mediator.

Starting from W304's unique-mediating-map boundary, this file constructs the
part of any mediator that is forced by the second supplied colimit proof
`IsColimit c₂`: for each test cocone `s` over the mapping-cone diagram, the
right-leg composite through `mappingCone.inr` is a cocone over `X₂`, hence has a
canonical desc out of `c₂.pt`.

The remaining obstruction is the left/cochain datum and compatibility equation
needed by `CochainComplex.mappingCone.desc`, plus the proof that these data
recover every leg of `s` and are unique.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeUniqueMediatorW308

/-- The fixed objectwise mapping-cone diagram from W303/W304. -/
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

/-- The fixed mapping-cone cocone from W303/W304. -/
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

/-- W304's unique mediator target, restated locally. -/
abbrev FixedMappingConeCoconeUniqueMediatingInput
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : Prop :=
  ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    ∃! m : (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt,
      ∀ j : J, (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j

/--
Bounded lift data for the right-leg target of a test cocone.

The attempted direct construction `Cocone X₂` with point `s.pt` is ill-typed:
`s.pt` is a `CochainComplex`, whereas `X₂` takes values in
`BoundedComplexCategory`.  Thus `hc₂.desc` can only be used after supplying a
bounded point whose inclusion is isomorphic to `s.pt`, plus strict lifts of the
right-leg maps.
-/
structure TestCoconeBoundedRightLift {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    (s : Cocone (mappingConeDiagram X₁ X₂ f)) : Type 2 where
  rightCocone : Cocone X₂
  ptIso :
    (BoundedComplexCategory.ι MetrizableLCA.{0}).obj rightCocone.pt ≅ s.pt
  right_fac : ∀ j : J,
    (BoundedComplexCategory.ι MetrizableLCA.{0}).map (rightCocone.ι.app j) ≫ ptIso.hom =
      CochainComplex.mappingCone.inr
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ s.ι.app j

/-- The right-leg component forced by `IsColimit c₂`, once bounded lift data is supplied. -/
noncomputable def rightLegMediator {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    {s : Cocone (mappingConeDiagram X₁ X₂ f)}
    (L : TestCoconeBoundedRightLift (X₁ := X₁) (X₂ := X₂) (f := f) s) :
    (BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt ⟶ s.pt :=
  (BoundedComplexCategory.ι MetrizableLCA.{0}).map (hc₂.desc L.rightCocone) ≫ L.ptIso.hom

/-- The forced right leg has the expected fac equation after applying the inclusion functor. -/
theorem rightLegMediator_fac {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    {c₂ : Cocone X₂} (hc₂ : IsColimit c₂)
    {s : Cocone (mappingConeDiagram X₁ X₂ f)}
    (L : TestCoconeBoundedRightLift (X₁ := X₁) (X₂ := X₂) (f := f) s) (j : J) :
    (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫
        rightLegMediator hc₂ L =
      CochainComplex.mappingCone.inr
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ s.ι.app j := by
  calc
    (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫
        rightLegMediator hc₂ L =
        (BoundedComplexCategory.ι MetrizableLCA.{0}).map
          (c₂.ι.app j ≫ hc₂.desc L.rightCocone) ≫ L.ptIso.hom := by
          simp [rightLegMediator, Category.assoc]
    _ = (BoundedComplexCategory.ι MetrizableLCA.{0}).map
          (L.rightCocone.ι.app j) ≫ L.ptIso.hom := by
          simpa using congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g ≫ L.ptIso.hom)
            (hc₂.fac L.rightCocone j)
    _ = CochainComplex.mappingCone.inr
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ s.ι.app j :=
          L.right_fac j

/--
Additional data still needed to turn the forced right-leg component into the
full `mappingCone` desc morphism.
-/
structure FixedMappingConeCoconeDescAssemblyData {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    (hc₂ : IsColimit c₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : Type 2 where
  rightLift : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    TestCoconeBoundedRightLift (X₁ := X₁) (X₂ := X₂) (f := f) s
  leftCochain : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    CochainComplex.HomComplex.Cochain
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt) s.pt (-1)
  descEq : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    CochainComplex.HomComplex.δ (-1) 0 (leftCochain s) =
      CochainComplex.HomComplex.Cochain.ofHom
        (((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫
          rightLegMediator hc₂ (rightLift s))
  fac : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f)) (j : J),
    (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫
      CochainComplex.mappingCone.desc
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
        (leftCochain s)
        (rightLegMediator hc₂ (rightLift s))
        (descEq s) = s.ι.app j
  uniq : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f))
    (m : (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt),
      (∀ j : J, (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j) →
        m =
          CochainComplex.mappingCone.desc
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
            (leftCochain s)
            (rightLegMediator hc₂ (rightLift s))
            (descEq s)

/-- The assembled mediator obtained from the right lift and remaining cochain data. -/
noncomputable def assembledMediator {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    {hc₂ : IsColimit c₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (D : FixedMappingConeCoconeDescAssemblyData c₁ c₂ f hc₂ φ hφ)
    (s : Cocone (mappingConeDiagram X₁ X₂ f)) :
    (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt :=
  CochainComplex.mappingCone.desc
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
    (D.leftCochain s)
    (rightLegMediator hc₂ (D.rightLift s))
    (D.descEq s)

/--
The W308 desc-assembly data is not merely diagnostic: it is sufficient to prove
the unique-mediating-map input required by the fixed mapping-cone cocone
universal-property route.
-/
theorem uniqueMediatingInput_of_descAssemblyData {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    {hc₂ : IsColimit c₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (D : FixedMappingConeCoconeDescAssemblyData c₁ c₂ f hc₂ φ hφ) :
    FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ := by
  intro s
  refine ⟨assembledMediator D s, ?_, ?_⟩
  · intro j
    simpa [assembledMediator] using D.fac s j
  · intro m hm
    simpa [assembledMediator] using D.uniq s m hm

/-- Machine-readable frontier state for W308. -/
structure WppOpMappingConeUniqueMediatorState : Type where
  seed : String
  provedRightLeg : String
  narrowedBoundary : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W308 boundary state. -/
def currentWppOpMappingConeUniqueMediatorState :
    WppOpMappingConeUniqueMediatorState where
  seed := "w308-worker-20260521"
  provedRightLeg :=
    "rightLegMediator hc₂ s := hc₂.desc (rightLegCocone s), with fac theorem"
  narrowedBoundary :=
    "FixedMappingConeCoconeDescAssemblyData"
  remainingInputs :=
    ["supply bounded right-target lift data for arbitrary cochain-complex test cocones",
      "construct the left degree -1 cochain for each test cocone s",
      "prove the mappingCone.desc compatibility equation δ left = ofHom (φ ≫ rightLegMediator)",
      "prove the mappingCone.desc leg equations against every fixed cocone leg",
      "prove uniqueness by mappingCone.ext_from plus colimit uniqueness for c₁ and c₂"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeUniqueMediatorState_productSuccess :
    currentWppOpMappingConeUniqueMediatorState.productSuccessClaimed = false := rfl

section Checks

#check mappingConeDiagram
#check mappingConeCocone
#check FixedMappingConeCoconeUniqueMediatingInput
#check TestCoconeBoundedRightLift
#check rightLegMediator
#check rightLegMediator_fac
#check FixedMappingConeCoconeDescAssemblyData
#check assembledMediator
#check uniqueMediatingInput_of_descAssemblyData
#check currentWppOpMappingConeUniqueMediatorState
#check currentWppOpMappingConeUniqueMediatorState_productSuccess
#check CochainComplex.mappingCone.desc
#check CochainComplex.mappingCone.ext_from
#check IsColimit.desc
#check IsColimit.fac
#check IsColimit.uniq

end Checks

end WppOpMappingConeUniqueMediatorW308

end LeanLCAExactChallenge
