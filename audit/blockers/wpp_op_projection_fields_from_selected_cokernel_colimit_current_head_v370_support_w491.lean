import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

/-!
W491: derive W475 projection fields from a selected forgotten-target cokernel
colimit proof.

The W475/W481 branch currently asks for three component projection colimit
fields.  This support file narrows that surface to one whole short-complex
cokernel colimit proof, so the W435 preservation route can be connected without
also carrying componentwise projection data as a separate final input.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportW491

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W491 projection-field narrowing. -/
def supportSeedW491 : String :=
  "w491-selected-cokernel-colimit-to-projection-fields"

/--
Transport a selected forgotten-target cokernel colimit proof across the
precomposition iso to the mapped short-complex cokernel cofork used by W475.
-/
def selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h :
      IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    IsColimit
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) := by
  let p : parallelPair
      (forgottenShortComplexFunctor.map
        (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
      parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
    parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
  let hPre :
      IsColimit
        ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) :=
    (IsColimit.precomposeHomEquiv p (selectedForgottenTargetCokernelCofork S cs)).symm h
  exact
    IsColimit.ofIsoColimit hPre
      (precomposeSelectedForgottenCokernelCoforkIsoMap S cs)

/--
One selected forgotten-target cokernel colimit proof supplies all three W475
projection fields by applying the short-complex projection functors.
-/
def selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h :
      IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  let hMapped :=
    selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491 h
  ⟨isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      hMapped,
    isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      hMapped,
    isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      hMapped⟩

/-- Provider form of the W491 narrowing. -/
def projectionFieldsProvider_of_selectedCokernelColimitProvider_w491
    (hselected :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    ProjectionFieldsProviderW475 :=
  fun S cs hcs =>
    selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491
      (hselected S cs hcs)

/--
W491 composition endpoint: a selected cokernel-colimit provider can replace the
component projection-field provider in W475.
-/
theorem exactAcyclic_of_w426Promotion_and_selectedCokernelColimitProvider_w491
    (hfields : W426PromotionFieldsProviderW475)
    (hordinaryMap : W426OrdinaryMapProviderW475)
    (heq : W426OrdinaryEqualsCanonicalProviderW475 hfields hordinaryMap)
    (hselected :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_projectionFields_w475
    hfields hordinaryMap heq
    (projectionFieldsProvider_of_selectedCokernelColimitProvider_w491 hselected)

/-- Checked nonterminal state for W491. -/
structure ProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 :
    Type where
  seed : String
  declarations : List String
  projectionFieldNarrowingResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W491 state. -/
def currentProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 :
    ProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 where
  seed := supportSeedW491
  declarations :=
    ["selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491",
      "selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491",
      "projectionFieldsProvider_of_selectedCokernelColimitProvider_w491",
      "exactAcyclic_of_w426Promotion_and_selectedCokernelColimitProvider_w491"]
  projectionFieldNarrowingResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs :=
    ["construct W426PromotionFieldsProviderW475",
      "construct W426OrdinaryMapProviderW475",
      "construct W426OrdinaryEqualsCanonicalProviderW475",
      "construct selected forgotten-target cokernel colimit provider, e.g. from W435 preservation"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW491State :
    ProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 :=
  currentProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491

theorem currentProjectionFieldsFromSelectedCokernelColimitStateW491_productSuccess :
    currentW491State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW491
#check selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491
#check selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491
#check projectionFieldsProvider_of_selectedCokernelColimitProvider_w491
#check exactAcyclic_of_w426Promotion_and_selectedCokernelColimitProvider_w491
#check currentProjectionFieldsFromSelectedCokernelColimitStateW491_productSuccess

end Checks

end WppOpProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportW491

end LeanLCAExactChallenge
