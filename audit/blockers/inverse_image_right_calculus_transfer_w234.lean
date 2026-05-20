import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction

/-!
Worker W234: inverse-image right-calculus transfer.

W226/W228 isolated the left-handed pullback problem. This file records the
right-handed analogue needed by W230: transfer `HasRightCalculusOfFractions`
from an ambient class `W` to `W.inverseImage F`, especially for
`(exactAcyclicHomotopyIsoClosure C).trW` pulled back along
`BoundedComplexCategory.homotopyQuotient C`.

No arbitrary inverse-image right-calculus transfer was found in the local or
mathlib API. The available mathlib theorem is the adjunction-specialized dual:
if the localized composite is a right adjoint, and the adjunction counit lies in
the pullback class, then the pullback class has a right calculus. Since the
composite uses `W.Q`, this route also requires the ambient left calculus that
constructs that localization functor.
-/

set_option autoImplicit false

noncomputable section

universe v u vD uD

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace InverseImageRightCalculusTransferW234

/-- The general theorem shape searched for in mathlib/local APIs. -/
structure InverseImageRightCalculusTransfer
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) : Prop where
  transfer :
    W.HasRightCalculusOfFractions →
      (W.inverseImage F).HasRightCalculusOfFractions

/-- Applying the general transfer assumption is immediate once it is supplied. -/
theorem inverseImage_hasRightCalculusOfFractions_of_transfer
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E)
    (T : InverseImageRightCalculusTransfer F W)
    (hW : W.HasRightCalculusOfFractions) :
    (W.inverseImage F).HasRightCalculusOfFractions :=
  T.transfer hW

/--
If `W.Q` is available, the localized composite `F ⋙ W.Q` inverts the pullback
class `W.inverseImage F`.
-/
theorem inverseImage_isInvertedBy_localizedFunctor
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions] :
    (W.inverseImage F).IsInvertedBy (F ⋙ W.Q) := by
  intro X Y f hf
  exact Localization.inverts W.Q W (F.map f) hf

/--
Adjunction-specialized inverse-image right-calculus transfer. This is the
provable bridge found in mathlib: apply
`CategoryTheory.Adjunction.hasRightCalculusOfFractions` with the localized
composite as the right adjoint.
-/
theorem inverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
    {D : Type uD} {E : Type u} [Category.{vD} D] [Category.{v} E]
    (F : D ⥤ E) (W : MorphismProperty E) [W.HasLeftCalculusOfFractions]
    (L : MorphismProperty.Localization W ⥤ D)
    (adj : L ⊣ F ⋙ W.Q)
    (hcounit : (W.inverseImage F).functorCategory D adj.counit) :
    (W.inverseImage F).HasRightCalculusOfFractions :=
  CategoryTheory.Adjunction.hasRightCalculusOfFractions adj (W.inverseImage F)
    (inverseImage_isInvertedBy_localizedFunctor F W) hcounit

/-- The bounded homotopy weak equivalences are definitionally the required inverse image. -/
theorem boundedHomotopyExactWeakEquivalence_eq_inverseImage
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedHomotopyExactWeakEquivalence C =
      ((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
        (BoundedComplexCategory.homotopyQuotient C) :=
  rfl

/-- The exact reusable inverse-image transfer specialized to the bounded homotopy route. -/
abbrev BoundedHomotopyInverseImageRightCalculusTransfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  InverseImageRightCalculusTransfer
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)

/--
Smallest direct downstream input after the definition of
`boundedHomotopyExactWeakEquivalence`: the inverse-image class itself has a
right calculus.
-/
structure BoundedHomotopyInverseImageRightCalculusInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  inverseImageRightCalculus :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).HasRightCalculusOfFractions

/-- The smallest direct input discharges the bounded homotopy right-calculus requirement. -/
theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_inverseImageInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : BoundedHomotopyInverseImageRightCalculusInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
  P.inverseImageRightCalculus

/-- Existing ambient Verdier input: triangulated closedness gives right calculus for `trW`. -/
theorem ambientVerdierRightCalculus_of_isoClosureClosed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2 C

/-- Existing ambient Verdier input needed only by the `W.Q` adjunction route. -/
theorem ambientVerdierLeftCalculus_of_isoClosureClosed2
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasLeftCalculusOfFractions :=
  exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 C

/--
The reusable inverse-image right transfer, specialized to
`BoundedComplexCategory.homotopyQuotient C`, is sufficient with the ambient
Verdier right-calculus input.
-/
theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_transfer
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (T : BoundedHomotopyInverseImageRightCalculusTransfer C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions := by
  exact inverseImage_hasRightCalculusOfFractions_of_transfer
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)
    T
    (ambientVerdierRightCalculus_of_isoClosureClosed2 C)

/-- The localized functor whose right-adjoint status would discharge the bounded case. -/
abbrev boundedHomotopyLocalizedFunctor
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions] :
    BoundedComplexCategory C ⥤
      MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) :=
  BoundedComplexCategory.homotopyQuotient C ⋙
    ((exactAcyclicHomotopyIsoClosure C).trW).Q

/--
The explicit adjunction-style input left after applying the mathlib right-handed
theorem: a left adjoint to the localized composite, plus counit membership in
the inverse-image class.
-/
structure BoundedHomotopyLocalizedRightAdjunctionInput
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions] : Type (max u v) where
  leftAdjoint :
    MorphismProperty.Localization ((exactAcyclicHomotopyIsoClosure C).trW) ⥤
      BoundedComplexCategory C
  adjunction :
    leftAdjoint ⊣ boundedHomotopyLocalizedFunctor C
  counit_mem :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).functorCategory
        (BoundedComplexCategory C) adjunction.counit

/--
The bounded inverse-image class follows from the localized right-adjunction
input. This is not a general arbitrary-functor transfer; it is the smallest
mathlib-backed adjunction package found for the right-handed case.
-/
theorem boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedRightAdjunctionInput C) :
    (((exactAcyclicHomotopyIsoClosure C).trW).inverseImage
      (BoundedComplexCategory.homotopyQuotient C)).HasRightCalculusOfFractions :=
  inverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicHomotopyIsoClosure C).trW)
    I.leftAdjoint I.adjunction I.counit_mem

/--
Since `boundedHomotopyExactWeakEquivalence` is definitionally this inverse
image, the same adjunction input discharges W230's right-calculus target.
-/
theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedAdjunction
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedRightAdjunctionInput C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions :=
  boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_localizedAdjunction C I

/-- Concrete finite-product target, still conditional on the adjunction-style input. -/
theorem metrizableLCABoundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions
    [((exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyLocalizedRightAdjunctionInput MetrizableLCA.{0}) :
    (boundedHomotopyExactWeakEquivalence MetrizableLCA.{0}).HasRightCalculusOfFractions :=
  boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedAdjunction
    MetrizableLCA.{0} I

/-- Packaged sufficient assumptions for the direct right-calculus transfer route. -/
structure BoundedHomotopyRightCalculusSufficientInputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop where
  isoClosureClosed2 :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂
  inverseImageRightTransfer :
    BoundedHomotopyInverseImageRightCalculusTransfer C

/-- The packaged assumptions discharge the bounded homotopy right-calculus input. -/
theorem boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_inputs
    (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (P : BoundedHomotopyRightCalculusSufficientInputs C) :
    (boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions := by
  letI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    P.isoClosureClosed2
  exact boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_transfer
    C P.inverseImageRightTransfer

/-- Search findings recorded as checked data. -/
def inverseImageRightCalculusSearchFindings : List String :=
  ["boundedHomotopyExactWeakEquivalence C is definitionally the inverse image of exactAcyclicHomotopyIsoClosure C trW along BoundedComplexCategory.homotopyQuotient C",
    "ambient Verdier right calculus is available from exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2",
    "no local/mathlib theorem was found transferring HasRightCalculusOfFractions through arbitrary W.inverseImage F",
    "CategoryTheory.Adjunction.hasRightCalculusOfFractions gives a right-handed adjunction route when the localized composite is a right adjoint and the counit lies in the pullback class",
    "because the route uses W.Q, the adjunction package also needs ambient left calculus, available from the same triangulated-closedness hypothesis",
    "smallest exact downstream input is BoundedHomotopyInverseImageRightCalculusInput C; smallest W230-style transfer field is PullbackRightCalculusTransfer C"]

theorem inverseImageRightCalculusSearchFindings_count :
    inverseImageRightCalculusSearchFindings.length = 6 := rfl

/-- Reproducible audit state for this worker. -/
structure InverseImageRightCalculusTransferState : Type where
  selectedRoute : Nat
  seedHash : String
  directTransferField : String
  adjunctionInput : String
  downstreamInput : String
  productSuccessClaimed : Bool

/-- Current state encoded as Lean data. -/
def currentInverseImageRightCalculusTransferState : InverseImageRightCalculusTransferState where
  selectedRoute := 4
  seedHash := "c01d62df871f5eb7f07e42e2c7e7a409eecfd6efdf52316a21f7d1c642906c5f"
  directTransferField := "W.HasRightCalculusOfFractions -> (W.inverseImage F).HasRightCalculusOfFractions"
  adjunctionInput := "left adjoint to F ⋙ W.Q plus counit membership in W.inverseImage F"
  downstreamInput := "(((exactAcyclicHomotopyIsoClosure C).trW).inverseImage (BoundedComplexCategory.homotopyQuotient C)).HasRightCalculusOfFractions"
  productSuccessClaimed := false

theorem currentInverseImageRightCalculusTransferState_route :
    currentInverseImageRightCalculusTransferState.selectedRoute = 4 := rfl

theorem currentInverseImageRightCalculusTransferState_productSuccess :
    currentInverseImageRightCalculusTransferState.productSuccessClaimed = false := rfl

section Checks

#check InverseImageRightCalculusTransfer
#check inverseImage_hasRightCalculusOfFractions_of_transfer
#check inverseImage_isInvertedBy_localizedFunctor
#check CategoryTheory.Adjunction.hasRightCalculusOfFractions
#check CategoryTheory.Adjunction.hasRightCalculusOfFractions'
#check inverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
#check boundedHomotopyExactWeakEquivalence_eq_inverseImage
#check BoundedHomotopyInverseImageRightCalculusTransfer
#check BoundedHomotopyInverseImageRightCalculusInput
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_inverseImageInput
#check ambientVerdierRightCalculus_of_isoClosureClosed2
#check ambientVerdierLeftCalculus_of_isoClosureClosed2
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_transfer
#check boundedHomotopyLocalizedFunctor
#check BoundedHomotopyLocalizedRightAdjunctionInput
#check boundedHomotopyInverseImage_hasRightCalculusOfFractions_of_localizedAdjunction
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_localizedAdjunction
#check metrizableLCABoundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions
#check BoundedHomotopyRightCalculusSufficientInputs
#check boundedHomotopyExactWeakEquivalence_hasRightCalculusOfFractions_of_inputs
#check inverseImageRightCalculusSearchFindings
#check inverseImageRightCalculusSearchFindings_count
#check currentInverseImageRightCalculusTransferState
#check exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
#check exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
#check boundedHomotopyExactWeakEquivalence
#check BoundedComplexCategory.homotopyQuotient

end Checks

end InverseImageRightCalculusTransferW234

end LeanLCAExactChallenge
