import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W433: frontier for preservation of `WalkingParallelPair` coequalizers by
`forget₂ MetrizableLCA AddCommGrpCat`.

W430 isolated this as the remaining non-preadditive input for finite-colimit
preservation.  This file pushes the boundary to the local quotient/cokernel
construction: for each `f`, the source cokernel is the quotient by
`MetrizableLCA.cokernelSubgroup f`, and preservation of that mapped concrete
cokernel cofork is enough to preserve the corresponding cokernel.  Mathlib's
preadditive reduction then turns such cokernel preservation into preservation
of all `WalkingParallelPair` coequalizers.

The missing theorem is intentionally stated as an input: the mapped explicit
closed-range quotient cofork is colimiting in `AddCommGrpCat` for every `f`.
This is stronger than the local API currently proves and is exactly the point
where the topological closure quotient must be compared with the algebraic
abelian-group cokernel.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgetfulPreservesWalkingParallelPairV370SupportW433

/-- The forgetful functor whose coequalizer preservation is needed after W430. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The explicit local cokernel cofork, before forgetting topology. -/
def explicitMetrizableCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (MetrizableLCA.cokernelπ f) (MetrizableLCA.comp_cokernelπ f)

/-- The existing quotient/cokernel API proves the explicit cofork is colimiting. -/
def explicitMetrizableCokernelCoforkIsColimit {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    IsColimit (explicitMetrizableCokernelCofork f) :=
  MetrizableLCA.cokernelIsColimit f

/--
The mapped concrete cokernel cocone.  Its vertex is the underlying abelian group
of the quotient of `Y` by the topological closure of the range of `f`.
-/
def mappedExplicitCokernelCocone {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Cocone (parallelPair f 0 ⋙ underlyingForgetfulFunctor) :=
  underlyingForgetfulFunctor.mapCocone (explicitMetrizableCokernelCofork f)

/-- The mapped concrete cokernel leg at `one` is the forgotten quotient projection. -/
theorem mappedExplicitCokernelCocone_ι_one {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelCocone f).ι.app WalkingParallelPair.one =
      underlyingForgetfulFunctor.map (MetrizableLCA.cokernelπ f) :=
  rfl

/--
Preservation of the single cokernel `f` follows from the checked source
colimit and the missing mapped-concrete-cofork colimit proof.
-/
@[reducible] def preservesCokernelOfMappedExplicitCokernelCoconeIsColimit
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hMapped : IsColimit (mappedExplicitCokernelCocone f)) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  preservesColimit_of_preserves_colimit_cocone
    (explicitMetrizableCokernelCoforkIsColimit f) hMapped

/--
If every mapped explicit closed-range quotient cofork is an abelian-group
cokernel, then the forgetful functor preserves all cokernels.
-/
@[reducible] def preservesAllCokernelsOfMappedExplicitCokernelCocones
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCocone f)) :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  fun f => preservesCokernelOfMappedExplicitCokernelCoconeIsColimit f (hMapped f)

/--
Preadditive reduction: preserving the mapped explicit cokernel cofork for every
`f` is enough for the W430 `WalkingParallelPair` input.
-/
theorem underlyingForgetfulPreservesWalkingParallelPair_of_mappedExplicitCokernelCoforks
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCocone f)) :
    PreservesColimitsOfShape WalkingParallelPair underlyingForgetfulFunctor := by
  haveI :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
        PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
    preservesAllCokernelsOfMappedExplicitCokernelCocones hMapped
  exact CategoryTheory.Functor.preservesCoequalizers_of_preservesCokernels
    underlyingForgetfulFunctor

/-- The same input also closes the W430 finite-colimit goal. -/
theorem underlyingForgetfulPreservesFiniteColimits_of_mappedExplicitCokernelCoforks
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCocone f)) :
    PreservesFiniteColimits underlyingForgetfulFunctor := by
  haveI :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
        PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
    preservesAllCokernelsOfMappedExplicitCokernelCocones hMapped
  exact CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels
    underlyingForgetfulFunctor

/-- Checked summary for downstream audit scripts and review packets. -/
structure AddCommGrpForgetfulPreservesWalkingParallelPairV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  forgetful_preserves_walking_parallel_pair_result : String
  missingTheoremNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgetfulPreservesWalkingParallelPairV370SupportState :
    AddCommGrpForgetfulPreservesWalkingParallelPairV370SupportState where
  seed := "e61b3ad82818c4e05c3e0572ffb425be"
  checkedConstructors :=
    ["explicitMetrizableCokernelCofork",
      "explicitMetrizableCokernelCoforkIsColimit",
      "mappedExplicitCokernelCocone",
      "mappedExplicitCokernelCocone_ι_one",
      "preservesCokernelOfMappedExplicitCokernelCoconeIsColimit",
      "preservesAllCokernelsOfMappedExplicitCokernelCocones",
      "underlyingForgetfulPreservesWalkingParallelPair_of_mappedExplicitCokernelCoforks",
      "underlyingForgetfulPreservesFiniteColimits_of_mappedExplicitCokernelCoforks"]
  forgetful_preserves_walking_parallel_pair_result := "partial"
  missingTheoremNames :=
    ["mappedExplicitCokernelCocone_isColimit",
      "forall_mappedExplicitCokernelCocone_isColimit",
      "closed_range_quotient_forgetful_addcommgrp_cokernel_comparison",
      "mappedExplicitCokernelCocone_iso_addcommgrp_cokernelCofork"]
  remainingInputs :=
    ["For every `f : X ⟶ Y` in `MetrizableLCA`, prove `IsColimit (mappedExplicitCokernelCocone f)` in `AddCommGrpCat`.",
      "Equivalently, compare the abelian group underlying `Y ⧸ MetrizableLCA.cokernelSubgroup f` with the algebraic cokernel of the underlying homomorphism.",
      "The local source API proves `MetrizableLCA.cokernelIsColimit f`; the missing input is preservation of that explicit closed-range quotient after applying `forget₂ MetrizableLCA AddCommGrpCat`."]
  productSuccessClaimed := false

theorem currentAddCommGrpForgetfulPreservesWalkingParallelPairV370SupportState_productSuccess :
    currentAddCommGrpForgetfulPreservesWalkingParallelPairV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check explicitMetrizableCokernelCofork
#check explicitMetrizableCokernelCoforkIsColimit
#check mappedExplicitCokernelCocone
#check mappedExplicitCokernelCocone_ι_one
#check preservesCokernelOfMappedExplicitCokernelCoconeIsColimit
#check preservesAllCokernelsOfMappedExplicitCokernelCocones
#check underlyingForgetfulPreservesWalkingParallelPair_of_mappedExplicitCokernelCoforks
#check underlyingForgetfulPreservesFiniteColimits_of_mappedExplicitCokernelCoforks
#check currentAddCommGrpForgetfulPreservesWalkingParallelPairV370SupportState_productSuccess

end Checks

end AddCommGrpForgetfulPreservesWalkingParallelPairV370SupportW433

end LeanLCAExactChallenge
