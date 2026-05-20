import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W379: AddCommGrp degreewise cokernel data support.

This standalone audit file builds the concrete component cokernel cofork data
needed by the W373/W376 bridge from the ordinary AddCommGrp categorical
cokernels of the three components of `u - v`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpDegreewiseCokernelDataV370SupportW379

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- W376-shaped concrete componentwise cokernel-cofork data. -/
structure ConcreteDegreewiseCokernelCoforkData
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  q₁ : L₂.X₁ ⟶ T.X₁
  q₂ : L₂.X₂ ⟶ T.X₂
  q₃ : L₂.X₃ ⟶ T.X₃
  comm₁₂ : q₁ ≫ T.f = L₂.f ≫ q₂ := by cat_disch
  comm₂₃ : q₂ ≫ T.g = L₂.g ≫ q₃ := by cat_disch
  w₁ : (u.τ₁ - v.τ₁) ≫ q₁ = 0 := by cat_disch
  w₂ : (u.τ₂ - v.τ₂) ≫ q₂ = 0 := by cat_disch
  w₃ : (u.τ₃ - v.τ₃) ≫ q₃ = 0 := by cat_disch
  h₁ : IsColimit (CokernelCofork.ofπ q₁ w₁)
  h₂ : IsColimit (CokernelCofork.ofπ q₂ w₂)
  h₃ : IsColimit (CokernelCofork.ofπ q₃ w₃)

/-- The three component quotient maps assemble to a short-complex morphism. -/
def ConcreteDegreewiseCokernelCoforkData.qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : L₂ ⟶ T where
  τ₁ := D.q₁
  τ₂ := D.q₂
  τ₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃

/-- The component zero equations assemble to the short-complex cofork equation. -/
theorem ConcreteDegreewiseCokernelCoforkData.wT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (u - v) ≫ D.qT = 0 := by
  apply ShortComplex.hom_ext
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₁
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₂
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₃

/-- W359-compatible degreewise mapped-cocone data. -/
structure DegreewiseCokernelCoforkData
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  qT : L₂ ⟶ T
  wT : (u - v) ≫ qT = 0 := by cat_disch
  hπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))
  hπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))
  hπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ qT wT))

/-- Degreewise mapped cofork proofs assemble to a short-complex cokernel cofork. -/
def DegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : DegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  ShortComplex.isColimitOfIsColimitπ
    (CokernelCofork.ofπ D.qT D.wT) D.hπ₁ D.hπ₂ D.hπ₃

abbrev component₁Map {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    L₁.X₁ ⟶ L₂.X₁ :=
  u.τ₁ - v.τ₁

abbrev component₂Map {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    L₁.X₂ ⟶ L₂.X₂ :=
  u.τ₂ - v.τ₂

abbrev component₃Map {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    L₁.X₃ ⟶ L₂.X₃ :=
  u.τ₃ - v.τ₃

theorem component₁_to_component₂_zero
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    component₁Map u v ≫ L₂.f ≫ cokernel.π (component₂Map u v) = 0 := by
  have hcomp : component₁Map u v ≫ L₂.f = L₁.f ≫ component₂Map u v := by
    simp [component₁Map, component₂Map, Preadditive.sub_comp, Preadditive.comp_sub,
      u.comm₁₂, v.comm₁₂]
  rw [← Category.assoc, hcomp, Category.assoc, cokernel.condition, comp_zero]

theorem component₂_to_component₃_zero
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    component₂Map u v ≫ L₂.g ≫ cokernel.π (component₃Map u v) = 0 := by
  have hcomp : component₂Map u v ≫ L₂.g = L₁.g ≫ component₃Map u v := by
    simp [component₂Map, component₃Map, Preadditive.sub_comp, Preadditive.comp_sub,
      u.comm₂₃, v.comm₂₃]
  rw [← Category.assoc, hcomp, Category.assoc, cokernel.condition, comp_zero]

/-- The canonical degree-1-to-degree-2 map between component cokernels. -/
def canonicalCokernelF {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    cokernel (component₁Map u v) ⟶ cokernel (component₂Map u v) :=
  cokernel.desc (component₁Map u v)
    (L₂.f ≫ cokernel.π (component₂Map u v))
    (component₁_to_component₂_zero u v)

/-- The canonical degree-2-to-degree-3 map between component cokernels. -/
def canonicalCokernelG {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    cokernel (component₂Map u v) ⟶ cokernel (component₃Map u v) :=
  cokernel.desc (component₂Map u v)
    (L₂.g ≫ cokernel.π (component₃Map u v))
    (component₂_to_component₃_zero u v)

@[reassoc (attr := simp)]
theorem component₁_π_canonicalCokernelF
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    cokernel.π (component₁Map u v) ≫ canonicalCokernelF u v =
      L₂.f ≫ cokernel.π (component₂Map u v) :=
  cokernel.π_desc (component₁Map u v)
    (L₂.f ≫ cokernel.π (component₂Map u v))
    (component₁_to_component₂_zero u v)

@[reassoc (attr := simp)]
theorem component₂_π_canonicalCokernelG
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    cokernel.π (component₂Map u v) ≫ canonicalCokernelG u v =
      L₂.g ≫ cokernel.π (component₃Map u v) :=
  cokernel.π_desc (component₂Map u v)
    (L₂.g ≫ cokernel.π (component₃Map u v))
    (component₂_to_component₃_zero u v)

/-- The component cokernels form a short complex. -/
def canonicalCokernelShortComplex {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) : ShortComplex AddCommGrpCat.{0} where
  X₁ := cokernel (component₁Map u v)
  X₂ := cokernel (component₂Map u v)
  X₃ := cokernel (component₃Map u v)
  f := canonicalCokernelF u v
  g := canonicalCokernelG u v
  zero := by
    rw [← cancel_epi (cokernel.π (component₁Map u v))]
    simp

/-- Canonical concrete degreewise cokernel cofork data in AddCommGrp. -/
def canonicalConcreteDegreewiseCokernelCoforkData
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    ConcreteDegreewiseCokernelCoforkData u v (canonicalCokernelShortComplex u v) where
  q₁ := cokernel.π (component₁Map u v)
  q₂ := cokernel.π (component₂Map u v)
  q₃ := cokernel.π (component₃Map u v)
  comm₁₂ := component₁_π_canonicalCokernelF u v
  comm₂₃ := component₂_π_canonicalCokernelG u v
  w₁ := cokernel.condition (component₁Map u v)
  w₂ := cokernel.condition (component₂Map u v)
  w₃ := cokernel.condition (component₃Map u v)
  h₁ := cokernelIsCokernel (component₁Map u v)
  h₂ := cokernelIsCokernel (component₂Map u v)
  h₃ := cokernelIsCokernel (component₃Map u v)

/-- The component cofork is the `π₁` mapped short-complex cofork. -/
def pi1CokernelCoforkMapCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (Cocone.precompose
        (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
          parallelPair (u.τ₁ - v.τ₁) 0 ≅
            (parallelPair (u - v) 0) ⋙
              (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})).inv).obj
        (CokernelCofork.ofπ D.q₁ D.w₁) ≅
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [ConcreteDegreewiseCokernelCoforkData.qT]
    · simp [ConcreteDegreewiseCokernelCoforkData.qT])

/-- The component cofork is the `π₂` mapped short-complex cofork. -/
def pi2CokernelCoforkMapCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (Cocone.precompose
        (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
          parallelPair (u.τ₂ - v.τ₂) 0 ≅
            (parallelPair (u - v) 0) ⋙
              (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})).inv).obj
        (CokernelCofork.ofπ D.q₂ D.w₂) ≅
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [ConcreteDegreewiseCokernelCoforkData.qT]
    · simp [ConcreteDegreewiseCokernelCoforkData.qT])

/-- The component cofork is the `π₃` mapped short-complex cofork. -/
def pi3CokernelCoforkMapCoconeIso
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (Cocone.precompose
        (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
          parallelPair (u.τ₃ - v.τ₃) 0 ≅
            (parallelPair (u - v) 0) ⋙
              (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})).inv).obj
        (CokernelCofork.ofπ D.q₃ D.w₃) ≅
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [ConcreteDegreewiseCokernelCoforkData.qT]
    · simp [ConcreteDegreewiseCokernelCoforkData.qT])

def ConcreteDegreewiseCokernelCoforkData.hπ₁
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
      parallelPair (u.τ₁ - v.τ₁) 0 ≅
        (parallelPair (u - v) 0) ⋙
          (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))
    (CokernelCofork.ofπ D.q₁ D.w₁)
    ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (CokernelCofork.ofπ D.qT D.wT))
    (pi1CokernelCoforkMapCoconeIso D)) D.h₁

def ConcreteDegreewiseCokernelCoforkData.hπ₂
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
      parallelPair (u.τ₂ - v.τ₂) 0 ≅
        (parallelPair (u - v) 0) ⋙
          (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))
    (CokernelCofork.ofπ D.q₂ D.w₂)
    ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (CokernelCofork.ofπ D.qT D.wT))
    (pi2CokernelCoforkMapCoconeIso D)) D.h₂

def ConcreteDegreewiseCokernelCoforkData.hπ₃
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (CokernelCofork.ofπ D.qT D.wT)) :=
  (IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
      parallelPair (u.τ₃ - v.τ₃) 0 ≅
        (parallelPair (u - v) 0) ⋙
          (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}))
    (CokernelCofork.ofπ D.q₃ D.w₃)
    ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (CokernelCofork.ofπ D.qT D.wT))
    (pi3CokernelCoforkMapCoconeIso D)) D.h₃

/-- Concrete component cokernel data supplies the exact degreewise input W359 expects. -/
def ConcreteDegreewiseCokernelCoforkData.toDegreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    DegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := D.hπ₁
  hπ₂ := D.hπ₂
  hπ₃ := D.hπ₃

/-- Concrete component cokernels give a short-complex cokernel cofork. -/
def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  D.toDegreewise.shortComplexCokernel

/-- Target cokernel-row presentation for the same difference map. -/
structure TargetCokernelRowPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  qT : L₂ ⟶ T
  wT : (u - v) ≫ qT = 0 := by cat_disch
  hT : IsColimit (CokernelCofork.ofπ qT wT)

def targetCokernelRowPresentation_of_concreteDegreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    TargetCokernelRowPresentation u v T where
  qT := D.qT
  wT := D.wT
  hT := D.shortComplexCokernel

/-- Canonical AddCommGrp component cokernels supply W376's target presentation. -/
def canonicalTargetCokernelRowPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    TargetCokernelRowPresentation u v (canonicalCokernelShortComplex u v) :=
  targetCokernelRowPresentation_of_concreteDegreewise
    (canonicalConcreteDegreewiseCokernelCoforkData u v)

/-- Local W376/W350-shaped boundary input package. -/
structure DifferenceSnakeBoundaryInputs
    (T : ShortComplex AddCommGrpCat.{0}) : Type 1 where
  differenceKernelRow : ShortComplex AddCommGrpCat.{0}
  differenceMiddleRow : ShortComplex AddCommGrpCat.{0}
  differenceCokernelRow : ShortComplex AddCommGrpCat.{0}
  differenceData :
    ParallelPairDifferenceStrictCokernelData
      differenceKernelRow differenceMiddleRow differenceCokernelRow
  cokernelRowIso : differenceCokernelRow ≅ T

def cokernelRowIsoOfConcreteDegreewise
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : ConcreteDegreewiseCokernelCoforkData D.u D.v T) :
    L₃ ≅ T :=
  IsColimit.coconePointUniqueUpToIso D.h₃
    (targetCokernelRowPresentation_of_concreteDegreewise P).hT

/-- Consumer theorem into W376's boundary-input shape. -/
def differenceSnakeBoundaryInputs_of_concreteDegreewise
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : ConcreteDegreewiseCokernelCoforkData D.u D.v T) :
    DifferenceSnakeBoundaryInputs T where
  differenceKernelRow := L₁
  differenceMiddleRow := L₂
  differenceCokernelRow := L₃
  differenceData := D
  cokernelRowIso := cokernelRowIsoOfConcreteDegreewise D P

/-- Direct consumer into W318's strict SnakeInput cokernel certificate. -/
def strictSnakeCokernelData_of_concreteDegreewise
    {L₁ L₂ L₃ T : ShortComplex AddCommGrpCat.{0}}
    (D : ParallelPairDifferenceStrictCokernelData L₁ L₂ L₃)
    (P : ConcreteDegreewiseCokernelCoforkData D.u D.v T) :
    AddCommGrpStrictSnakeCokernelData T :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    D (cokernelRowIsoOfConcreteDegreewise D P)

/-- W379 checked support state. -/
structure AddCommGrpDegreewiseCokernelDataV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  degreewiseCokernelDataResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpDegreewiseCokernelDataV370SupportState :
    AddCommGrpDegreewiseCokernelDataV370SupportState where
  seed := "W379-SoT-1d8f7c0a4b23e651"
  checkedConstructors :=
    ["canonicalCokernelShortComplex",
      "canonicalConcreteDegreewiseCokernelCoforkData",
      "ConcreteDegreewiseCokernelCoforkData.toDegreewise",
      "ConcreteDegreewiseCokernelCoforkData.shortComplexCokernel",
      "canonicalTargetCokernelRowPresentation",
      "differenceSnakeBoundaryInputs_of_concreteDegreewise",
      "strictSnakeCokernelData_of_concreteDegreewise"]
  degreewiseCokernelDataResult := "proved"
  remainingInputs :=
    ["construct the strict difference kernel/cokernel rows",
      "identify the resulting canonical AddCommGrp cokernel row with the forgotten WPP-op colimit row",
      "promote the standalone audit schemas into importable modules if needed outside audit/blockers"]
  productSuccessClaimed := false

theorem currentAddCommGrpDegreewiseCokernelDataV370SupportState_productSuccess :
    currentAddCommGrpDegreewiseCokernelDataV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check canonicalCokernelShortComplex
#check canonicalConcreteDegreewiseCokernelCoforkData
#check ConcreteDegreewiseCokernelCoforkData.toDegreewise
#check ConcreteDegreewiseCokernelCoforkData.shortComplexCokernel
#check canonicalTargetCokernelRowPresentation
#check differenceSnakeBoundaryInputs_of_concreteDegreewise
#check strictSnakeCokernelData_of_concreteDegreewise
#check currentAddCommGrpDegreewiseCokernelDataV370SupportState_productSuccess

end Checks

end AddCommGrpDegreewiseCokernelDataV370SupportW379

end LeanLCAExactChallenge
