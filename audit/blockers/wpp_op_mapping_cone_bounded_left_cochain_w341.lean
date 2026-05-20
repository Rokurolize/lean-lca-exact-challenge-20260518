import LeanLCAExactChallenge.Derived.MappingConeFiniteProduct

/-!
W341: bounded-inclusion left cochain for W308 test cocones.

W333 constructs the left cochain in the ambient cochain-complex setting.  W308
needs the same construction after applying `BoundedComplexCategory.ι` to the
source bounded-complex cocone.  This file packages that exact bounded-inclusion
form: any W308 test cocone supplies compatible objectwise `mappingCone.inl`
left cochains, and these descend along the included `c₁` colimit.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpMappingConeBoundedLeftCochainW341

open CochainComplex

/-- Naturality of test legs over the W308 bounded-inclusion mapping-cone diagram. -/
abbrev BoundedMappingConeTestLegNaturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T) : Prop :=
  ∀ {j j' : J} (α : j ⟶ j'),
    mappingCone.map
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

/-- Objectwise left cochain from a bounded-inclusion mapping-cone test leg. -/
noncomputable def objectwiseLeftFromBoundedLeg
    {K L T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (leg : mappingCone φ ⟶ T) :
    HomComplex.Cochain K T (-1) :=
  (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom leg) (add_zero (-1))

/-- Compatibility of objectwise left cochains induced by natural bounded test legs. -/
theorem objectwiseLeftFromBoundedLeg_compatible {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T)
    (hleg : BoundedMappingConeTestLegNaturality f leg)
    {j j' : J} (α : j ⟶ j') (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α)).f p ≫
        (objectwiseLeftFromBoundedLeg
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j')) (leg j')).v p q hpq =
      (objectwiseLeftFromBoundedLeg
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) (leg j)).v p q hpq := by
  calc
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α)).f p ≫
        (objectwiseLeftFromBoundedLeg
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j')) (leg j')).v p q hpq =
        (mappingCone.inl ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v p q hpq ≫
          (mappingCone.map
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j'))
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₁.map α))
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (X₂.map α))
            (by
              rw [← Functor.map_comp, ← Functor.map_comp]
              exact congrArg
                (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
                (f.naturality α).symm) ≫ leg j').f q := by
        simp [objectwiseLeftFromBoundedLeg, mappingCone.map, Category.assoc]
    _ = (mappingCone.inl ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v p q hpq ≫
          (leg j).f q := by
        rw [hleg α]
    _ =
      (objectwiseLeftFromBoundedLeg
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) (leg j)).v p q hpq := by
        simp [objectwiseLeftFromBoundedLeg]

/-- The evaluation cocone used to descend the bounded objectwise left cochains. -/
noncomputable def boundedLeftEvalCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T)
    (hleg : BoundedMappingConeTestLegNaturality f leg)
    (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    Cocone ((X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0}) ⋙
      HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) where
  pt := T.X q
  ι :=
    { app := fun j =>
        (objectwiseLeftFromBoundedLeg
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) (leg j)).v p q hpq
      naturality := by
        intro j j' α
        exact objectwiseLeftFromBoundedLeg_compatible f leg hleg α p q hpq }

/-- Descended bounded-inclusion left cochain for a W308 test cocone. -/
noncomputable def leftCochainOfBoundedTestCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁}
    (hc₁i : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c₁))
    [∀ p : ℤ, PreservesColimit (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T)
    (hleg : BoundedMappingConeTestLegNaturality f leg) :
    HomComplex.Cochain ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₁.pt) T (-1) :=
  HomComplex.Cochain.mk (fun p q hpq =>
    (isColimitOfPreserves
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hc₁i).desc
      (boundedLeftEvalCocone f leg hleg p q hpq))

/-- The descended bounded left cochain has the expected `mappingCone.inl` leg equation. -/
theorem leftCochainOfBoundedTestCocone_comp_fac {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁}
    (hc₁i : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c₁))
    [∀ p : ℤ, PreservesColimit (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    (f : X₁ ⟶ X₂)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T)
    (hleg : BoundedMappingConeTestLegNaturality f leg)
    (j : J) :
    (HomComplex.Cochain.ofHom ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))).comp
        (leftCochainOfBoundedTestCocone hc₁i f leg hleg) (zero_add (-1)) =
      objectwiseLeftFromBoundedLeg
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) (leg j) := by
  apply HomComplex.Cochain.ext
  intro p q hpq
  simpa [leftCochainOfBoundedTestCocone, HomComplex.Cochain.ofHom_comp] using
    (isColimitOfPreserves
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hc₁i).fac
      (boundedLeftEvalCocone f leg hleg p q hpq) j

/-- Objectwise descEq for the bounded left cochain candidate. -/
theorem objectwiseLeftFromBoundedLeg_descEq
    {K L T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ : K ⟶ L) (leg : mappingCone φ ⟶ T) :
    HomComplex.δ (-1) 0 (objectwiseLeftFromBoundedLeg φ leg) =
      HomComplex.Cochain.ofHom (φ ≫ mappingCone.inr φ ≫ leg) := by
  simp [objectwiseLeftFromBoundedLeg, HomComplex.Cochain.ofHom_comp]

/-- Cech-style extensionality for cochains out of an included bounded colimit. -/
theorem cochain_ext_of_included_colimit_legs {J : Type} [Category J]
    {X : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {cX : Cocone X}
    (hcXi : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone cX))
    [∀ p : ℤ, PreservesColimit (X ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {T : CochainComplex MetrizableLCA.{0} ℤ} {n : ℤ}
    {z₁ z₂ : HomComplex.Cochain
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).obj cX.pt) T n}
    (hlegs : ∀ j : J,
      (HomComplex.Cochain.ofHom
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (cX.ι.app j))).comp z₁ (zero_add n) =
        (HomComplex.Cochain.ofHom
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (cX.ι.app j))).comp z₂ (zero_add n)) :
    z₁ = z₂ := by
  apply HomComplex.Cochain.ext
  intro p q hpq
  apply (isColimitOfPreserves
    (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p) hcXi).hom_ext
  intro j
  have h := HomComplex.Cochain.congr_v (hlegs j) p q hpq
  simpa [HomComplex.Cochain.ofHom_comp] using h

/-- `δ` commutes with precomposition by an included bounded colimit leg. -/
theorem delta_of_included_colimit_leg_comp
    {A B T : CochainComplex MetrizableLCA.{0} ℤ}
    (ι : A ⟶ B) (z : HomComplex.Cochain B T (-1)) :
    HomComplex.δ (-1) 0
        ((HomComplex.Cochain.ofHom ι).comp z (zero_add (-1))) =
      (HomComplex.Cochain.ofHom ι).comp
        (HomComplex.δ (-1) 0 z) (zero_add 0) := by
  simp

/-- Rewrites the global differential after an included bounded colimit leg. -/
theorem included_colimit_leg_delta_eq_of_precomp_eq
    {A B T : CochainComplex MetrizableLCA.{0} ℤ}
    (ι : A ⟶ B) (z : HomComplex.Cochain B T (-1))
    (zObj : HomComplex.Cochain A T (-1))
    (h : (HomComplex.Cochain.ofHom ι).comp z (zero_add (-1)) = zObj) :
    (HomComplex.Cochain.ofHom ι).comp
        (HomComplex.δ (-1) 0 z) (zero_add 0) =
      HomComplex.δ (-1) 0 zObj := by
  rw [← h, delta_of_included_colimit_leg_comp]

/-- Bounded-inclusion global descEq for the W308 left cochain. -/
theorem globalDescEqOfBoundedTestCocone {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁}
    (hc₁i : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c₁))
    [∀ p : ℤ, PreservesColimit (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {c₂ : Cocone X₂}
    (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (β : (BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt ⟶ T)
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T)
    (hleg : BoundedMappingConeTestLegNaturality f leg)
    (hβ : ∀ j : J,
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β =
        mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ leg j) :
    HomComplex.δ (-1) 0 (leftCochainOfBoundedTestCocone hc₁i f leg hleg) =
      HomComplex.Cochain.ofHom ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ ≫ β) := by
  apply cochain_ext_of_included_colimit_legs hc₁i
  intro j
  have hleft := included_colimit_leg_delta_eq_of_precomp_eq
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))
    (leftCochainOfBoundedTestCocone hc₁i f leg hleg)
    (objectwiseLeftFromBoundedLeg
      ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) (leg j))
    (leftCochainOfBoundedTestCocone_comp_fac hc₁i f leg hleg j)
  have hobj := objectwiseLeftFromBoundedLeg_descEq
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) (leg j)
  have hmorph :
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j) ≫
          mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ leg j =
        (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j) ≫
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ ≫ β) := by
    symm
    calc
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j) ≫
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ ≫ β) =
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j) ≫
            (BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ≫ β := by
          simp [Category.assoc]
      _ = (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j ≫ φ) ≫ β := by
          simp
      _ = (BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j ≫ c₂.ι.app j) ≫ β := by
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g ≫ β)
            (hφ j)
      _ = ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j) ≫
            (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j)) ≫ β := by
          simp
      _ = (BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j) ≫
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β) := by
          simp [Category.assoc]
      _ = (BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j) ≫
            (mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ leg j) := by
          rw [hβ j]
      _ = (BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j) ≫
            mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ leg j := by
          simp
  calc
    (HomComplex.Cochain.ofHom
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))).comp
        (HomComplex.δ (-1) 0 (leftCochainOfBoundedTestCocone hc₁i f leg hleg)) (zero_add 0) =
        HomComplex.δ (-1) 0
          (objectwiseLeftFromBoundedLeg
            ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) (leg j)) := hleft
    _ = HomComplex.Cochain.ofHom
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j) ≫
          mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ leg j) := hobj
    _ = (HomComplex.Cochain.ofHom
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))).comp
        (HomComplex.Cochain.ofHom ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ ≫ β))
        (zero_add 0) := by
        rw [hmorph]
        simp [HomComplex.Cochain.ofHom_comp]

/-- Local mapping-cone fac split used to package W308 leg equations. -/
theorem mappingCone_map_desc_fac_of_left_right
    {K₁ K₂ L₁ L₂ T : CochainComplex MetrizableLCA.{0} ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂)
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (comm : φ₁ ≫ b = a ≫ φ₂)
    (α : HomComplex.Cochain K₂ T (-1)) (β : L₂ ⟶ T)
    (eq : HomComplex.δ (-1) 0 α = HomComplex.Cochain.ofHom (φ₂ ≫ β))
    (sleg : mappingCone φ₁ ⟶ T)
    (hleft :
      (mappingCone.inl φ₁).comp (HomComplex.Cochain.ofHom sleg) (add_zero (-1)) =
        (HomComplex.Cochain.ofHom a).comp α (zero_add (-1)))
    (hright : mappingCone.inr φ₁ ≫ sleg = b ≫ β) :
    mappingCone.map φ₁ φ₂ a b comm ≫ mappingCone.desc φ₂ α β eq = sleg := by
  apply HomologicalComplex.hom_ext
  intro p
  apply mappingCone.ext_from φ₁ (p + 1) p rfl
  · replace hleft := HomComplex.Cochain.congr_v hleft (p + 1) p (by omega)
    calc
      (mappingCone.inl φ₁).v (p + 1) p (by omega) ≫
          (mappingCone.map φ₁ φ₂ a b comm).f p ≫
          (mappingCone.desc φ₂ α β eq).f p =
          a.f (p + 1) ≫ α.v (p + 1) p (by omega) := by
        simp [mappingCone.map, Category.assoc]
      _ = (mappingCone.inl φ₁).v (p + 1) p (by omega) ≫ sleg.f p := by
        simpa [HomComplex.Cochain.ofHom_comp] using hleft.symm
  · simpa [Category.assoc, mappingCone.map] using congrArg (fun q => q.f p) hright.symm

/-- Bounded-inclusion mapping-cone desc fac for each W308 test-cocone leg. -/
theorem boundedMappingConeDesc_fac {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁}
    (hc₁i : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c₁))
    [∀ p : ℤ, PreservesColimit (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {c₂ : Cocone X₂}
    (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (β : (BoundedComplexCategory.ι MetrizableLCA.{0}).obj c₂.pt ⟶ T)
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T)
    (hleg : BoundedMappingConeTestLegNaturality f leg)
    (hβ : ∀ j : J,
      (BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j) ≫ β =
        mappingCone.inr ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ≫ leg j)
    (j : J) :
    mappingCone.map
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j))
        (by
          rw [← Functor.map_comp, ← Functor.map_comp]
          exact congrArg
            (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
            (hφ j).symm) ≫
      mappingCone.desc
        ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
        (leftCochainOfBoundedTestCocone hc₁i f leg hleg)
        β
        (globalDescEqOfBoundedTestCocone hc₁i f φ hφ β leg hleg hβ) =
      leg j := by
  apply mappingCone_map_desc_fac_of_left_right
  · exact (leftCochainOfBoundedTestCocone_comp_fac hc₁i f leg hleg j).symm
  · exact (hβ j).symm

/-- Naturality of `mappingCone.inl` for the bounded-inclusion mapping-cone map. -/
theorem bounded_mappingCone_inl_naturality {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    (f : X₁ ⟶ X₂)
    {c₁ : Cocone X₁} {c₂ : Cocone X₂}
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    (j : J) (p q : ℤ) (hpq : p + (-1 : ℤ) = q) :
    ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j)).f p ≫
        (mappingCone.inl ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).v p q hpq =
      (mappingCone.inl ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))).v p q hpq ≫
        (mappingCone.map
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j))
          (by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg
              (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
              (hφ j).symm)).f q := by
  simp [mappingCone.map]

/--
An arbitrary mediator satisfying the fixed test-cocone fac equations has the
same left `mappingCone.inl` cochain component as the descended W341 left
cochain.
-/
theorem arbitraryMediator_leftCochain_eq {J : Type} [Category J]
    {X₁ X₂ : J ⥤ BoundedComplexCategory MetrizableLCA.{0}}
    {c₁ : Cocone X₁}
    (hc₁i : IsColimit ((BoundedComplexCategory.ι MetrizableLCA.{0}).mapCocone c₁))
    [∀ p : ℤ, PreservesColimit (X₁ ⋙ BoundedComplexCategory.ι MetrizableLCA.{0})
      (HomologicalComplex.eval MetrizableLCA.{0} (ComplexShape.up ℤ) p)]
    {c₂ : Cocone X₂}
    (f : X₁ ⟶ X₂)
    (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j : J, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    {T : CochainComplex MetrizableLCA.{0} ℤ}
    (leg : ∀ j : J,
      mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j)) ⟶ T)
    (hleg : BoundedMappingConeTestLegNaturality f leg)
    (m : mappingCone ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ) ⟶ T)
    (hm : ∀ j : J,
      mappingCone.map
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j))
          (by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg
              (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
              (hφ j).symm) ≫ m = leg j) :
    (mappingCone.inl ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)).comp
        (HomComplex.Cochain.ofHom m) (add_zero (-1)) =
      leftCochainOfBoundedTestCocone hc₁i f leg hleg := by
  apply cochain_ext_of_included_colimit_legs hc₁i
  intro j
  apply HomComplex.Cochain.ext
  intro p q hpq
  have hfac := congrArg (fun g => g.f q) (hm j)
  have hfacq :
      (mappingCone.map
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (f.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map φ)
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₁.ι.app j))
          ((BoundedComplexCategory.ι MetrizableLCA.{0}).map (c₂.ι.app j))
          (by
            rw [← Functor.map_comp, ← Functor.map_comp]
            exact congrArg
              (fun g => (BoundedComplexCategory.ι MetrizableLCA.{0}).map g)
              (hφ j).symm)).f q ≫ m.f q = (leg j).f q := by
    simpa using hfac
  have h₄ := HomComplex.Cochain.congr_v
    (leftCochainOfBoundedTestCocone_comp_fac hc₁i f leg hleg j).symm p q hpq
  have hnat := bounded_mappingCone_inl_naturality f φ hφ j p q hpq
  simp [objectwiseLeftFromBoundedLeg] at h₄ hnat hfacq ⊢
  have hA := congrArg (fun u => u ≫ m.f q) hnat
  simp [Category.assoc] at hA
  rw [hA]
  rw [hfacq]
  exact h₄

/-- Machine-readable W341 state. -/
structure WppOpMappingConeBoundedLeftCochainState : Type where
  checkedLemma : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W341 state. -/
def currentWppOpMappingConeBoundedLeftCochainState :
    WppOpMappingConeBoundedLeftCochainState where
  checkedLemma := "arbitraryMediator_leftCochain_eq"
  remainingInputs :=
    ["derive hc₁i from W324's preservation of the included bounded c₁ colimit",
      "package final uniqueness field using W330/right colimit equality"]
  productSuccessClaimed := false

theorem currentWppOpMappingConeBoundedLeftCochainState_productSuccess :
    currentWppOpMappingConeBoundedLeftCochainState.productSuccessClaimed = false := rfl

section Checks

#check leftCochainOfBoundedTestCocone
#check leftCochainOfBoundedTestCocone_comp_fac
#check globalDescEqOfBoundedTestCocone
#check boundedMappingConeDesc_fac
#check arbitraryMediator_leftCochain_eq
#check currentWppOpMappingConeBoundedLeftCochainState
#check currentWppOpMappingConeBoundedLeftCochainState_productSuccess

end Checks

end WppOpMappingConeBoundedLeftCochainW341

end LeanLCAExactChallenge
