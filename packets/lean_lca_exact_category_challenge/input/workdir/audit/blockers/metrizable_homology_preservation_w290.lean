import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Homology.ShortComplex.RightHomology

/-!
W290: MetrizableLCA forgetful homology-preservation frontier.

The full instance
`(forget₂ MetrizableLCA AddCommGrpCat).PreservesHomology` is not synthesized by
the current local API.  This audit records the exact global shape and proves a
smaller local replacement: for a fixed short complex, preserving one concrete
left-homology datum and one concrete right-homology datum is enough to recover
the faithful-forgetful exactness bridge consumed by W258/W287.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableHomologyPreservationW290

abbrev ForgetMetrizableToAddCommGrp : MetrizableLCA.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}

/-- Concrete kernel/range equality used by the strict-exactness bridge. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/--
The full forgetful homology-preservation instance is exactly kernel and
cokernel preservation for every morphism.  This is the smallest global route
mathlib's `PreservesHomology` class accepts.
-/
theorem forgetPreservesHomology_of_preservesKernelCokernel
    (hker : ∀ {X Y : MetrizableLCA.{u}} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) ForgetMetrizableToAddCommGrp.{u})
    (hcoker : ∀ {X Y : MetrizableLCA.{u}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) ForgetMetrizableToAddCommGrp.{u}) :
    ForgetMetrizableToAddCommGrp.{u}.PreservesHomology where
  preservesKernels := by
    intro X Y f
    exact hker (X := X) (Y := Y) f
  preservesCokernels := by
    intro X Y f
    exact hcoker (X := X) (Y := Y) f

/--
The local replacement for full homology preservation: if the forgetful functor
preserves one chosen left-homology datum and one chosen right-homology datum for
`T`, then exactness of `T` is equivalent to exactness after forgetting.
-/
theorem exact_iff_exact_map_forget_of_localHomologyData
    (T : ShortComplex MetrizableLCA.{u})
    (hhom : T.HasHomology)
    (hleft : T.LeftHomologyData)
    (hleftPres : hleft.IsPreservedBy ForgetMetrizableToAddCommGrp.{u})
    (hright : T.RightHomologyData)
    (hrightPres : hright.IsPreservedBy ForgetMetrizableToAddCommGrp.{u}) :
    T.Exact ↔ (T.map ForgetMetrizableToAddCommGrp.{u}).Exact := by
  letI : T.HasHomology := hhom
  letI : hleft.IsPreservedBy ForgetMetrizableToAddCommGrp.{u} := hleftPres
  letI : hright.IsPreservedBy ForgetMetrizableToAddCommGrp.{u} := hrightPres
  letI : ForgetMetrizableToAddCommGrp.{u}.PreservesLeftHomologyOf T :=
    Functor.PreservesLeftHomologyOf.mk' ForgetMetrizableToAddCommGrp.{u} hleft
  letI : ForgetMetrizableToAddCommGrp.{u}.PreservesRightHomologyOf T :=
    Functor.PreservesRightHomologyOf.mk' ForgetMetrizableToAddCommGrp.{u} hright
  exact (T.exact_map_iff_of_faithful ForgetMetrizableToAddCommGrp.{u}).symm

/--
Local cycles/opcycles consumer back to the W258/W287 element bridge.  This
avoids a global `PreservesHomology` assumption, but exposes the exact local
kernel/cokernel preservation data that must still be supplied.
-/
theorem targetKernelEquality_of_exact_of_localHomologyData
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hleft : T.LeftHomologyData)
    (hleftPres : hleft.IsPreservedBy ForgetMetrizableToAddCommGrp.{u})
    (hright : T.RightHomologyData)
    (hrightPres : hright.IsPreservedBy ForgetMetrizableToAddCommGrp.{u})
    (hT : T.Exact) :
    TargetKernelEquality T := by
  intro x₂
  constructor
  · intro hx₂
    have hmap : (T.map ForgetMetrizableToAddCommGrp.{u}).Exact :=
      (exact_iff_exact_map_forget_of_localHomologyData T hhom hleft hleftPres hright
        hrightPres).1 hT
    exact (ShortComplex.ab_exact_iff (T.map ForgetMetrizableToAddCommGrp.{u})).mp hmap x₂ hx₂
  · rintro ⟨x₁, rfl⟩
    change (T.f ≫ T.g : T.X₁ ⟶ T.X₃) x₁ = (0 : T.X₁ ⟶ T.X₃) x₁
    exact congrArg (fun h : T.X₁ ⟶ T.X₃ => h x₁) T.zero

/-- Machine-readable frontier state for this audit. -/
structure HomologyPreservationFrontierState : Type where
  seed : String
  fullInstanceChecked : String
  localReplacement : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W290 boundary state. -/
def currentHomologyPreservationFrontierState : HomologyPreservationFrontierState where
  seed := "w290-parent-20260520T1715Z"
  fullInstanceChecked :=
    "no local synthesis for (forget₂ MetrizableLCA AddCommGrpCat).PreservesHomology"
  localReplacement :=
    "one preserved LeftHomologyData and one preserved RightHomologyData recover exactness after forgetting for a fixed short complex"
  remainingInputs :=
    ["global route: preserve kernels and cokernels of all MetrizableLCA morphisms under forget₂",
      "local route: provide a concrete preserved left-homology datum for the strict-exactness short complex",
      "local route: provide a concrete preserved right-homology datum for the strict-exactness short complex",
      "then feed targetKernelEquality_of_exact_of_localHomologyData into the W258/W287 algebraic-exactness consumer"]
  productSuccessClaimed := false

theorem currentHomologyPreservationFrontierState_productSuccess :
    currentHomologyPreservationFrontierState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def homologyPreservationFrontierDeclarationNames : List String :=
  ["ForgetMetrizableToAddCommGrp",
    "TargetKernelEquality",
    "forgetPreservesHomology_of_preservesKernelCokernel",
    "exact_iff_exact_map_forget_of_localHomologyData",
    "targetKernelEquality_of_exact_of_localHomologyData",
    "currentHomologyPreservationFrontierState"]

theorem homologyPreservationFrontierDeclarationNames_count :
    homologyPreservationFrontierDeclarationNames.length = 6 := rfl

section Checks

#check ForgetMetrizableToAddCommGrp
#check TargetKernelEquality
#check forgetPreservesHomology_of_preservesKernelCokernel
#check exact_iff_exact_map_forget_of_localHomologyData
#check targetKernelEquality_of_exact_of_localHomologyData
#check currentHomologyPreservationFrontierState
#check currentHomologyPreservationFrontierState_productSuccess
#check homologyPreservationFrontierDeclarationNames
#check homologyPreservationFrontierDeclarationNames_count
#check Functor.PreservesHomology
#check Functor.preservesHomologyOfExact
#check Functor.PreservesHomology.preservesKernel
#check Functor.PreservesHomology.preservesCokernel
#check Functor.PreservesLeftHomologyOf.mk'
#check Functor.PreservesRightHomologyOf.mk'
#check ShortComplex.LeftHomologyData.IsPreservedBy
#check ShortComplex.RightHomologyData.IsPreservedBy
#check ShortComplex.exact_map_iff_of_faithful
#check ShortComplex.ab_exact_iff
#check ShortComplex.fromOpcycles

end Checks

end MetrizableHomologyPreservationW290

end LeanLCAExactChallenge
