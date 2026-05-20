import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
W430: frontier for finite-colimit preservation of the underlying forgetful
functor `forget₂ MetrizableLCA AddCommGrpCat`.

W428 reduced the WPP-op preservation needed downstream to
`PreservesFiniteColimits (forget₂ MetrizableLCA AddCommGrpCat)`.  This file
checks the next available boundary: mathlib can reduce that finite-colimit
preservation either to coequalizer plus finite-coproduct preservation, or in the
preadditive setting to preservation of all cokernel coforks.  The actual
instance is not synthesized by the local imports.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportW430

/-- The underlying forgetful functor isolated by W428. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The source has finite colimits, supplied by the cokernel implementation. -/
theorem source_hasFiniteColimits : HasFiniteColimits MetrizableLCA.{0} :=
  inferInstance

/-- The forgetful functor already preserves finite coproducts from local imports. -/
theorem underlyingForgetfulPreservesFiniteCoproducts :
    PreservesFiniteCoproducts underlyingForgetfulFunctor :=
  inferInstance

/--
Finite-colimit preservation follows from preservation of coequalizers and finite
coproducts.  This is the non-preadditive decomposition exposed by mathlib.
-/
theorem underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
    [PreservesColimitsOfShape WalkingParallelPair underlyingForgetfulFunctor]
    [PreservesFiniteCoproducts underlyingForgetfulFunctor] :
    PreservesFiniteColimits underlyingForgetfulFunctor :=
  preservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts underlyingForgetfulFunctor

/--
Since finite-coproduct preservation already synthesizes, the remaining
non-preadditive input is preservation of coequalizers.
-/
theorem underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers
    [PreservesColimitsOfShape WalkingParallelPair underlyingForgetfulFunctor] :
    PreservesFiniteColimits underlyingForgetfulFunctor := by
  haveI : PreservesFiniteCoproducts underlyingForgetfulFunctor :=
    underlyingForgetfulPreservesFiniteCoproducts
  exact
    underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts

/--
Because the categories involved are preadditive, finite-colimit preservation
also follows from preservation of every cokernel cofork.
-/
theorem underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels
    [∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor] :
    PreservesFiniteColimits underlyingForgetfulFunctor :=
  CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels underlyingForgetfulFunctor

/--
The checked frontier state: the reduction exists, but the direct instance and
the smaller preservation inputs are still the remaining API boundary.
-/
structure AddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  forgetfulPreservesFiniteColimitsFrontierResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportState :
    AddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportState where
  seed := "w430-c1e73cbd629af23c2f35a734"
  checkedConstructors :=
    ["source_hasFiniteColimits",
      "underlyingForgetfulPreservesFiniteCoproducts",
      "underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts",
      "underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers",
      "underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels"]
  forgetfulPreservesFiniteColimitsFrontierResult := "partial"
  remainingInputs :=
    ["missing checked instance/API: `[PreservesFiniteColimits (forget₂ MetrizableLCA AddCommGrpCat)]`",
      "exact remaining non-preadditive input: `[PreservesColimitsOfShape WalkingParallelPair (forget₂ MetrizableLCA AddCommGrpCat)]`",
      "preadditive sufficient input: `∀ {X Y : MetrizableLCA} (f : X ⟶ Y), PreservesColimit (parallelPair f 0) (forget₂ MetrizableLCA AddCommGrpCat)`",
      "local imports synthesize `HasFiniteColimits MetrizableLCA` and `[PreservesFiniteCoproducts (forget₂ MetrizableLCA AddCommGrpCat)]`, but not the forgetful finite-colimit or coequalizer-preservation instance"]
  productSuccessClaimed := false

theorem currentAddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportState_productSuccess :
    currentAddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check source_hasFiniteColimits
#check underlyingForgetfulPreservesFiniteCoproducts
#check underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers_and_finiteCoproducts
#check underlyingForgetfulPreservesFiniteColimits_of_preservesCoequalizers
#check underlyingForgetfulPreservesFiniteColimits_of_preservesCokernels
#check currentAddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportState_productSuccess

end Checks

end AddCommGrpForgetfulPreservesFiniteColimitsFrontierV370SupportW430

end LeanLCAExactChallenge
