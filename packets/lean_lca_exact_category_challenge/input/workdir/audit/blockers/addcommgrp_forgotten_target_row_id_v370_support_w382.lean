import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
W382: AddCommGrp forgotten target row identification support.

The adjacent W379 and W376 audit files are checked by path and are not importable
Lean modules in this worktree.  This standalone bridge therefore repeats only
the small schemas needed to identify their duplicate concrete degreewise
cokernel-cofork packages, then exposes the remaining WPP-op target-row
identification as a single named isomorphism field.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgottenTargetRowIdV370SupportW382

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

namespace W379Source

/-- W379-shaped concrete componentwise cokernel-cofork data. -/
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

def ConcreteDegreewiseCokernelCoforkData.qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : L₂ ⟶ T where
  τ₁ := D.q₁
  τ₂ := D.q₂
  τ₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃

theorem ConcreteDegreewiseCokernelCoforkData.wT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (u - v) ≫ D.qT = 0 := by
  apply ShortComplex.hom_ext
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₁
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₂
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₃

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

def canonicalCokernelF {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    cokernel (component₁Map u v) ⟶ cokernel (component₂Map u v) :=
  cokernel.desc (component₁Map u v)
    (L₂.f ≫ cokernel.π (component₂Map u v))
    (component₁_to_component₂_zero u v)

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

def ConcreteDegreewiseCokernelCoforkData.toDegreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    DegreewiseCokernelCoforkData u v T where
  qT := D.qT
  wT := D.wT
  hπ₁ := D.hπ₁
  hπ₂ := D.hπ₂
  hπ₃ := D.hπ₃

def ConcreteDegreewiseCokernelCoforkData.shortComplexCokernel
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    IsColimit (CokernelCofork.ofπ D.qT D.wT) :=
  D.toDegreewise.shortComplexCokernel

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

def canonicalTargetCokernelRowPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    TargetCokernelRowPresentation u v (canonicalCokernelShortComplex u v) :=
  targetCokernelRowPresentation_of_concreteDegreewise
    (canonicalConcreteDegreewiseCokernelCoforkData u v)

end W379Source

namespace W376Target

/-- W376-shaped duplicate of the concrete componentwise cokernel-cofork data. -/
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

def ConcreteDegreewiseCokernelCoforkData.qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) : L₂ ⟶ T where
  τ₁ := D.q₁
  τ₂ := D.q₂
  τ₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃

theorem ConcreteDegreewiseCokernelCoforkData.wT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : ConcreteDegreewiseCokernelCoforkData u v T) :
    (u - v) ≫ D.qT = 0 := by
  apply ShortComplex.hom_ext
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₁
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₂
  · simpa [ConcreteDegreewiseCokernelCoforkData.qT] using D.w₃

structure WppOpForgottenTargetCokernelCoforkPresentation
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}}
    (u v : L₁ ⟶ L₂) : Type 1 where
  S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}
  cs : Cocone S
  hcs : IsColimit cs
  C : ShortComplex AddCommGrpCat.{0}
  qC : L₂ ⟶ C
  wC : (u - v) ≫ qC = 0 := by cat_disch
  hC : IsColimit (CokernelCofork.ofπ qC wC)
  targetIso :
    C ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

end W376Target

/-- Field-by-field bridge from W379's duplicate data schema to W376's duplicate schema. -/
def w379ConcreteDegreewise_to_w376ConcreteDegreewise
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : W379Source.ConcreteDegreewiseCokernelCoforkData u v T) :
    W376Target.ConcreteDegreewiseCokernelCoforkData u v T where
  q₁ := D.q₁
  q₂ := D.q₂
  q₃ := D.q₃
  comm₁₂ := D.comm₁₂
  comm₂₃ := D.comm₂₃
  w₁ := D.w₁
  w₂ := D.w₂
  w₃ := D.w₃
  h₁ := D.h₁
  h₂ := D.h₂
  h₃ := D.h₃

@[simp]
theorem w379_to_w376_qT
    {L₁ L₂ T : ShortComplex AddCommGrpCat.{0}} {u v : L₁ ⟶ L₂}
    (D : W379Source.ConcreteDegreewiseCokernelCoforkData u v T) :
    (w379ConcreteDegreewise_to_w376ConcreteDegreewise D).qT = D.qT :=
  rfl

/--
The exact remaining input for turning W379's canonical AddCommGrp cokernel row
into W376's forgotten WPP-op target-row presentation.
-/
structure ForgottenTargetRowIsoInput
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) : Type 1 where
  cs : Cocone S
  hcs : IsColimit cs
  targetIso :
    W379Source.canonicalCokernelShortComplex u v ≅
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/--
Checked consumer: W379's canonical concrete row plus the single named
`targetIso` field produces W376's forgotten target cokernel-cofork shape.
-/
def wppOpForgottenTargetCokernelCoforkPresentation_of_w379Canonical
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂)
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (I : ForgottenTargetRowIsoInput u v S) :
    W376Target.WppOpForgottenTargetCokernelCoforkPresentation u v where
  S := S
  cs := I.cs
  hcs := I.hcs
  C := W379Source.canonicalCokernelShortComplex u v
  qC := (W379Source.canonicalConcreteDegreewiseCokernelCoforkData u v).qT
  wC := (W379Source.canonicalConcreteDegreewiseCokernelCoforkData u v).wT
  hC := (W379Source.canonicalConcreteDegreewiseCokernelCoforkData u v).shortComplexCokernel
  targetIso := I.targetIso

/-- The W376 concrete schema obtained from W379's canonical concrete row. -/
def canonicalW376ConcreteDegreewiseCokernelCoforkData
    {L₁ L₂ : ShortComplex AddCommGrpCat.{0}} (u v : L₁ ⟶ L₂) :
    W376Target.ConcreteDegreewiseCokernelCoforkData u v
      (W379Source.canonicalCokernelShortComplex u v) :=
  w379ConcreteDegreewise_to_w376ConcreteDegreewise
    (W379Source.canonicalConcreteDegreewiseCokernelCoforkData u v)

/-- W382 checked support state. -/
structure AddCommGrpForgottenTargetRowIdV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  targetRowIdentificationResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgottenTargetRowIdV370SupportState :
    AddCommGrpForgottenTargetRowIdV370SupportState where
  seed := "W382-SoT-03d35a830c2d4344"
  checkedConstructors :=
    ["W379Source.canonicalConcreteDegreewiseCokernelCoforkData",
      "W379Source.canonicalTargetCokernelRowPresentation",
      "w379ConcreteDegreewise_to_w376ConcreteDegreewise",
      "canonicalW376ConcreteDegreewiseCokernelCoforkData",
      "ForgottenTargetRowIsoInput.targetIso",
      "wppOpForgottenTargetCokernelCoforkPresentation_of_w379Canonical"]
  targetRowIdentificationResult := "partial"
  remainingInputs :=
    ["provide ForgottenTargetRowIsoInput.targetIso : W379Source.canonicalCokernelShortComplex u v ≅ cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})",
      "promote the duplicate standalone audit schemas into importable modules if downstream consumers must reference W379/W376 declarations directly"]
  productSuccessClaimed := false

theorem currentAddCommGrpForgottenTargetRowIdV370SupportState_productSuccess :
    currentAddCommGrpForgottenTargetRowIdV370SupportState.productSuccessClaimed = false := rfl

section Checks

#check W379Source.canonicalConcreteDegreewiseCokernelCoforkData
#check W379Source.canonicalTargetCokernelRowPresentation
#check w379ConcreteDegreewise_to_w376ConcreteDegreewise
#check w379_to_w376_qT
#check canonicalW376ConcreteDegreewiseCokernelCoforkData
#check ForgottenTargetRowIsoInput.targetIso
#check wppOpForgottenTargetCokernelCoforkPresentation_of_w379Canonical
#check currentAddCommGrpForgottenTargetRowIdV370SupportState_productSuccess

end Checks

end AddCommGrpForgottenTargetRowIdV370SupportW382

end LeanLCAExactChallenge
