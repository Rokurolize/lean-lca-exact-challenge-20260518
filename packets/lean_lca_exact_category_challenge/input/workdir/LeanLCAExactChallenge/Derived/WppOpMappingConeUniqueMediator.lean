import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct
import LeanLCAExactChallenge.Derived.WppOpMappingConeBoundedLeftCochain
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

/-- Naturality of test legs over the W308 bounded-inclusion mapping-cone diagram. -/
abbrev MappingConeTestLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      CochainComplex.mappingCone
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T) : Prop :=
  ∀ {j j' : J} (α : j ⟶ j'),
    CochainComplex.mappingCone.map
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
            (f.naturality α).symm) ≫
      leg j' = leg j

/-- Every W308 test cocone supplies the naturality input needed by the global descEq wrapper. -/
theorem testCoconeLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    (s : Cocone (mappingConeDiagram X₁ X₂ f)) :
    MappingConeTestLegNaturality f (fun j => s.ι.app j) := by
  intro j j' α
  simpa [mappingConeDiagram] using s.w α

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
Ambient right-leg cocone data in `CochainComplex`.

This is weaker than `TestCoconeBoundedRightLift`: it does not require the test
cocone point to be the image of a bounded complex. The remaining proof is only
the naturality/fac package for the right legs in the ambient category.
-/
structure AmbientRightLegCoconeData {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    (s : Cocone (mappingConeDiagram X₁ X₂ f)) : Type 2 where
  rightCocone : Cocone (X₂ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
  pt_eq : rightCocone.pt = s.pt
  right_fac : ∀ j : J,
    rightCocone.ι.app j ≫ eqToHom pt_eq =
      CochainComplex.mappingCone.inr
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ s.ι.app j

/-- The ambient right leg forced directly by the preserved colimit of `c₂`. -/
noncomputable def ambientRightLegMediator {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    {c₂ : Cocone X₂} [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    {s : Cocone (mappingConeDiagram X₁ X₂ f)}
    (L : AmbientRightLegCoconeData (X₁ := X₁) (X₂ := X₂) (f := f) s) :
    (BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt ⟶ s.pt :=
  (isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₂).desc L.rightCocone ≫
    eqToHom L.pt_eq

/-- The ambient right leg has the expected fac equation without bounded lift data. -/
theorem ambientRightLegMediator_fac {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    {c₂ : Cocone X₂} [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    {s : Cocone (mappingConeDiagram X₁ X₂ f)}
    (L : AmbientRightLegCoconeData (X₁ := X₁) (X₂ := X₂) (f := f) s) (j : J) :
    (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫
        ambientRightLegMediator hc₂ L =
      CochainComplex.mappingCone.inr
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ s.ι.app j := by
  have h₁ :
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫
          ambientRightLegMediator hc₂ L =
        L.rightCocone.ι.app j ≫ eqToHom L.pt_eq := by
    simpa [ambientRightLegMediator] using
      congrArg (fun q => q ≫ eqToHom L.pt_eq)
        ((isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₂).fac
          L.rightCocone j)
  exact h₁.trans (L.right_fac j)

/-- Naturality of `mappingCone.map` against the right inclusion for this fixed diagram. -/
theorem mappingConeDiagram_inr_naturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    {j j' : J} (α : j ⟶ j') :
    (BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α) ≫
        CochainComplex.mappingCone.inr
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j')) =
      CochainComplex.mappingCone.inr
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫
        (mappingConeDiagram X₁ X₂ f).map α := by
  dsimp [mappingConeDiagram]
  have hcomm :
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α)) =
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α)) ≫
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j')) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg
      (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
      (f.naturality α).symm
  simpa [hcomm, CochainComplex.mappingCone.map] using
    (show
      CochainComplex.mappingCone.inr
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫
        CochainComplex.mappingCone.map
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
          hcomm =
        (BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α) ≫
          CochainComplex.mappingCone.inr
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j')) from by
      simp [CochainComplex.mappingCone.map]).symm

/-- Every test cocone supplies the ambient right-leg cocone data automatically. -/
noncomputable def ambientRightLegCoconeDataOfTestCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}} {f : X₁ ⟶ X₂}
    (s : Cocone (mappingConeDiagram X₁ X₂ f)) :
    AmbientRightLegCoconeData (X₁ := X₁) (X₂ := X₂) (f := f) s where
  rightCocone :=
    { pt := s.pt
      ι :=
        { app := fun j =>
            CochainComplex.mappingCone.inr
              ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ s.ι.app j
          naturality := by
            intro j j' α
            have hnat := mappingConeDiagram_inr_naturality (X₁ := X₁) (X₂ := X₂) (f := f) α
            have hs :
                (mappingConeDiagram X₁ X₂ f).map α ≫ s.ι.app j' = s.ι.app j := by
              simpa using s.w α
            change
              (BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α) ≫
                  (CochainComplex.mappingCone.inr
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j')) ≫
                    s.ι.app j') =
                CochainComplex.mappingCone.inr
                  ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ s.ι.app j
            rw [← Category.assoc, hnat]
            calc
              (CochainComplex.mappingCone.inr
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫
                  (mappingConeDiagram X₁ X₂ f).map α) ≫ s.ι.app j' =
                  CochainComplex.mappingCone.inr
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫
                    ((mappingConeDiagram X₁ X₂ f).map α ≫ s.ι.app j') := by
                simp [Category.assoc]
              _ =
                  CochainComplex.mappingCone.inr
                    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫
                    s.ι.app j := by
                exact congrArg
                  (fun q =>
                    CochainComplex.mappingCone.inr
                        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ q)
                  hs } }
  pt_eq := rfl
  right_fac := by
    intro j
    simp

/--
Ambient desc-assembly data for the fixed mapping-cone cocone.

Unlike `FixedMappingConeCoconeDescAssemblyData`, this version does not ask for
bounded right-target lift data. The right leg is supplied in the ambient
cochain-complex category from every test cocone, then descended from the
included colimit of `c₂`.
-/
structure AmbientFixedMappingConeCoconeDescAssemblyData {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : Type 2 where
  leftCochain : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    CochainComplex.HomComplex.Cochain
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt) s.pt (-1)
  descEq : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    CochainComplex.HomComplex.δ (-1) 0 (leftCochain s) =
      CochainComplex.HomComplex.Cochain.ofHom
        (((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫
          ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
  fac : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f)) (j : J),
    (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫
      CochainComplex.mappingCone.desc
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
        (leftCochain s)
        (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
        (descEq s) = s.ι.app j
  uniq : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f))
    (m : (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt),
      (∀ j : J, (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j) →
        m =
          CochainComplex.mappingCone.desc
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
            (leftCochain s)
            (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
            (descEq s)

/-- The ambient assembled mediator, using the automatically supplied right leg. -/
noncomputable def ambientAssembledMediator {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    {hc₂ : IsColimit c₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (D : AmbientFixedMappingConeCoconeDescAssemblyData c₁ c₂ f hc₂ φ hφ)
    (s : Cocone (mappingConeDiagram X₁ X₂ f)) :
    (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt :=
  CochainComplex.mappingCone.desc
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
    (D.leftCochain s)
    (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
    (D.descEq s)

/--
Uniqueness of the ambient assembled mapping-cone mediator after the left
`mappingCone.inl` cochain component has been identified.

The right `mappingCone.inr` component is forced by the preserved included
`c₂` colimit and the fixed test-leg equations.
-/
theorem ambientAssembledMediator_unique_of_left {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    {hc₂ : IsColimit c₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    {s : Cocone (mappingConeDiagram X₁ X₂ f)}
    (α : CochainComplex.HomComplex.Cochain
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt) s.pt (-1))
    (eq :
      CochainComplex.HomComplex.δ (-1) 0 α =
        CochainComplex.HomComplex.Cochain.ofHom
          (((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫
            ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s)))
    (m : (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt)
    (hm : ∀ j : J, (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j)
    (hleft :
      (CochainComplex.mappingCone.inl
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
          (CochainComplex.HomComplex.Cochain.ofHom m) (add_zero (-1)) = α) :
    m =
      CochainComplex.mappingCone.desc
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
        α
        (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
        eq := by
  let β :=
    ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s)
  let desc :=
    CochainComplex.mappingCone.desc
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) α β eq
  have hright :
      CochainComplex.mappingCone.inr
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ m =
        β := by
    apply (isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₂).hom_ext
    intro j
    let inrj :=
      CochainComplex.mappingCone.inr
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
    have hfixed :
        inrj ≫ ((mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m) =
          inrj ≫ s.ι.app j := by
      simpa [Category.assoc] using
        congrArg (fun q => inrj ≫ q) (hm j)
    have hcanonical :
        inrj ≫ s.ι.app j =
          (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β := by
      simpa [inrj] using (ambientRightLegMediator_fac hc₂
        (ambientRightLegCoconeDataOfTestCocone s) j).symm
    simpa [inrj, mappingConeCocone, CochainComplex.mappingCone.map, Category.assoc] using
      hfixed.trans hcanonical
  apply HomologicalComplex.hom_ext
  intro p
  apply CochainComplex.mappingCone.ext_from
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) (p + 1) p rfl
  · have hdesc_left :
        (CochainComplex.mappingCone.inl
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
            (CochainComplex.HomComplex.Cochain.ofHom desc) (add_zero (-1)) = α := by
        simpa [desc, β] using
          (CochainComplex.mappingCone.inl_desc
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) α β eq)
    have hcochain :
        (CochainComplex.mappingCone.inl
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
            (CochainComplex.HomComplex.Cochain.ofHom m) (add_zero (-1)) =
          (CochainComplex.mappingCone.inl
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
              (CochainComplex.HomComplex.Cochain.ofHom desc) (add_zero (-1)) :=
      hleft.trans hdesc_left.symm
    replace hcochain := CochainComplex.HomComplex.Cochain.congr_v
      hcochain (p + 1) p (by omega)
    simpa [desc] using hcochain
  · have hright' :
        CochainComplex.mappingCone.inr
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ m =
          CochainComplex.mappingCone.inr
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ desc := by
        simpa [desc, β] using hright.trans
          (CochainComplex.mappingCone.inr_desc
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) α β eq).symm
    simpa [desc] using congrArg (fun q => q.f p) hright'

/--
Ambient desc-assembly data where uniqueness is reduced to the left
`mappingCone.inl` cochain component.
-/
structure AmbientFixedMappingConeCoconeDescAssemblyLeftUniqData {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (c₁ : Cocone X₁) (c₂ : Cocone X₂) (f : X₁ ⟶ X₂)
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) : Type 2 where
  leftCochain : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    CochainComplex.HomComplex.Cochain
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt) s.pt (-1)
  descEq : ∀ s : Cocone (mappingConeDiagram X₁ X₂ f),
    CochainComplex.HomComplex.δ (-1) 0 (leftCochain s) =
      CochainComplex.HomComplex.Cochain.ofHom
        (((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫
          ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
  fac : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f)) (j : J),
    (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫
      CochainComplex.mappingCone.desc
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
        (leftCochain s)
        (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
        (descEq s) = s.ι.app j
  left_uniq : ∀ (s : Cocone (mappingConeDiagram X₁ X₂ f))
    (m : (mappingConeCocone c₁ c₂ f φ hφ).pt ⟶ s.pt),
      (∀ j : J, (mappingConeCocone c₁ c₂ f φ hφ).ι.app j ≫ m = s.ι.app j) →
        (CochainComplex.mappingCone.inl
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
            (CochainComplex.HomComplex.Cochain.ofHom m) (add_zero (-1)) =
          leftCochain s

/-- Left-uniqueness assembly data supplies the original ambient assembly data. -/
def AmbientFixedMappingConeCoconeDescAssemblyLeftUniqData.toAmbientData
    {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    {hc₂ : IsColimit c₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (D : AmbientFixedMappingConeCoconeDescAssemblyLeftUniqData c₁ c₂ f hc₂ φ hφ) :
    AmbientFixedMappingConeCoconeDescAssemblyData c₁ c₂ f hc₂ φ hφ where
  leftCochain := D.leftCochain
  descEq := D.descEq
  fac := D.fac
  uniq := by
    intro s m hm
    exact ambientAssembledMediator_unique_of_left
      (D.leftCochain s) (D.descEq s) m hm (D.left_uniq s m hm)

/-- Left-uniqueness assembly data is sufficient for the fixed cocone universal property. -/
theorem uniqueMediatingInput_of_ambientDescAssemblyLeftUniqData {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    {hc₂ : IsColimit c₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (D : AmbientFixedMappingConeCoconeDescAssemblyLeftUniqData c₁ c₂ f hc₂ φ hφ) :
    FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ := by
  intro s
  refine ⟨ambientAssembledMediator D.toAmbientData s, ?_, ?_⟩
  · intro j
    simpa [ambientAssembledMediator, AmbientFixedMappingConeCoconeDescAssemblyLeftUniqData.toAmbientData]
      using D.fac s j
  · intro m hm
    simpa [ambientAssembledMediator, AmbientFixedMappingConeCoconeDescAssemblyLeftUniqData.toAmbientData]
      using ambientAssembledMediator_unique_of_left
        (D.leftCochain s) (D.descEq s) m hm (D.left_uniq s m hm)

/-- Ambient desc-assembly data is sufficient for the fixed cocone universal property. -/
theorem uniqueMediatingInput_of_ambientDescAssemblyData {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    {hc₂ : IsColimit c₂}
    {φ : c₁.pt ⟶ c₂.pt}
    {hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j}
    (D : AmbientFixedMappingConeCoconeDescAssemblyData c₁ c₂ f hc₂ φ hφ) :
    FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ := by
  intro s
  refine ⟨ambientAssembledMediator D s, ?_, ?_⟩
  · intro j
    simpa [ambientAssembledMediator] using D.fac s j
  · intro m hm
    simpa [ambientAssembledMediator] using D.uniq s m hm

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

/--
The W341 bounded-inclusion assembly supplies W308's ambient desc-assembly data
from the included `c₁` colimit, evaluation-colimit preservation, and the
preserved included `c₂` colimit.
-/
noncomputable def ambientDescAssemblyDataOfIncludedColimits {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    (hc₁i : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c₁))
    [∀ p : ℤ, PreservesColimit (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    AmbientFixedMappingConeCoconeDescAssemblyData c₁ c₂ f hc₂ φ hφ where
  leftCochain := fun s =>
    WppOpMappingConeBoundedLeftCochainW341.leftCochainOfBoundedTestCocone
      hc₁i f (fun j => s.ι.app j)
      (testCoconeLegNaturality f s)
  descEq := by
    intro s
    exact WppOpMappingConeBoundedLeftCochainW341.globalDescEqOfBoundedTestCocone
      hc₁i f φ hφ
      (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
      (fun j => s.ι.app j)
      (testCoconeLegNaturality f s)
      (fun j => ambientRightLegMediator_fac hc₂ (ambientRightLegCoconeDataOfTestCocone s) j)
  fac := by
    intro s j
    exact WppOpMappingConeBoundedLeftCochainW341.boundedMappingConeDesc_fac
      hc₁i f φ hφ
      (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
      (fun j => s.ι.app j)
      (testCoconeLegNaturality f s)
      (fun j => ambientRightLegMediator_fac hc₂ (ambientRightLegCoconeDataOfTestCocone s) j)
      j
  uniq := by
    intro s m hm
    exact WppOpMappingConeBoundedLeftCochainW341.boundedMappingConeDesc_unique
      hc₁i
      (isColimitOfPreserves (BoundedComplexCategory.ι MetrizableLCA.{0}) hc₂)
      f φ hφ
      (ambientRightLegMediator hc₂ (ambientRightLegCoconeDataOfTestCocone s))
      (fun j => s.ι.app j)
      (testCoconeLegNaturality f s)
      (fun j => ambientRightLegMediator_fac hc₂ (ambientRightLegCoconeDataOfTestCocone s) j)
      m hm

/--
Included colimit/evaluation inputs are now sufficient for W308's fixed
mapping-cone cocone unique-mediating-map input.
-/
theorem uniqueMediatingInput_of_includedColimits {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁} {c₂ : Cocone X₂} {f : X₁ ⟶ X₂}
    (hc₁i : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c₁))
    [∀ p : ℤ, PreservesColimit (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    [PreservesColimit X₂ (BoundedComplexCategory.ι MetrizableLCA.{0})]
    (hc₂ : IsColimit c₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j) :
    FixedMappingConeCoconeUniqueMediatingInput c₁ c₂ f φ hφ :=
  uniqueMediatingInput_of_ambientDescAssemblyData
    (ambientDescAssemblyDataOfIncludedColimits hc₁i hc₂ φ hφ)

/-- Machine-readable W308 state. -/
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
    "uniqueMediatingInput_of_includedColimits"
  remainingInputs :=
    ["supply the included c₁ colimit and evaluation-preservation instances for the actual WPP-op source cocone",
      "apply uniqueMediatingInput_of_includedColimits inside the W303/W304 fixed-cocone colimit route"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeUniqueMediatorState_productSuccess :
    currentWppOpMappingConeUniqueMediatorState.productSuccessClaimed = false := rfl

end WppOpMappingConeUniqueMediatorW308

end LeanLCAExactChallenge
