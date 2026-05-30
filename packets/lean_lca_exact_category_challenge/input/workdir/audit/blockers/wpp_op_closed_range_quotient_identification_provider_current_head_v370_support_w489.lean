import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open MetrizableLCA

namespace WppOpClosedRangeQuotientIdentificationProviderCurrentHeadV370SupportW489

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Transport a projected first-component colimit proof back to the selected component cofork. -/
def selectedComponentπ₁_isColimit_of_projection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₁ :
      IsColimit
        ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))) :
    IsColimit (selectedForgottenComponentπ₁CokernelCoforkW485 S cs) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₁DiagramIsoW485 S)
    (selectedForgottenComponentπ₁CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₁CoforkIsoW485 S cs)).symm hπ₁

/-- Transport a projected second-component colimit proof back to the selected component cofork. -/
def selectedComponentπ₂_isColimit_of_projection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₂ :
      IsColimit
        ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))) :
    IsColimit (selectedForgottenComponentπ₂CokernelCoforkW485 S cs) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₂DiagramIsoW485 S)
    (selectedForgottenComponentπ₂CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₂CoforkIsoW485 S cs)).symm hπ₂

/-- Transport a projected third-component colimit proof back to the selected component cofork. -/
def selectedComponentπ₃_isColimit_of_projection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₃ :
      IsColimit
        ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))) :
    IsColimit (selectedForgottenComponentπ₃CokernelCoforkW485 S cs) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₃DiagramIsoW485 S)
    (selectedForgottenComponentπ₃CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₃CoforkIsoW485 S cs)).symm hπ₃

/-- First selected component point isomorphism from projected and explicit cokernel colimits. -/
def selectedComponentπ₁PointIso_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₁W485 S)) :=
  (selectedComponentπ₁_isColimit_of_projection_w489 H.hπ₁).coconePointUniqueUpToIso
    (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₁W485 S) (by
        simpa [selectedMetrizableDifferenceπ₁W481, selectedMetrizableDifferenceπ₁W485]
          using H.hclosedπ₁))

/-- Second selected component point isomorphism from projected and explicit cokernel colimits. -/
def selectedComponentπ₂PointIso_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₂W485 S)) :=
  (selectedComponentπ₂_isColimit_of_projection_w489 H.hπ₂).coconePointUniqueUpToIso
    (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₂W485 S) (by
        simpa [selectedMetrizableDifferenceπ₂W481, selectedMetrizableDifferenceπ₂W485]
          using H.hclosedπ₂))

/-- Third selected component point isomorphism from projected and explicit cokernel colimits. -/
def selectedComponentπ₃PointIso_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₃W485 S)) :=
  (selectedComponentπ₃_isColimit_of_projection_w489 H.hπ₃).coconePointUniqueUpToIso
    (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₃W485 S) (by
        simpa [selectedMetrizableDifferenceπ₃W481, selectedMetrizableDifferenceπ₃W485]
          using H.hclosedπ₃))

/-- First selected component leg equation from colimit-point uniqueness. -/
theorem selectedComponentπ₁Leg_eq_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      (selectedComponentπ₁PointIso_of_componentwiseProjection_w489 H).hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₁W485 S) := by
  simpa [selectedComponentπ₁PointIso_of_componentwiseProjection_w489,
    selectedForgottenComponentπ₁CokernelCoforkW485, forgottenExplicitCokernelCoforkW485] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (selectedComponentπ₁_isColimit_of_projection_w489 H.hπ₁)
        (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
          (selectedMetrizableDifferenceπ₁W485 S) (by
            simpa [selectedMetrizableDifferenceπ₁W481, selectedMetrizableDifferenceπ₁W485]
              using H.hclosedπ₁))
        WalkingParallelPair.one)

/-- Second selected component leg equation from colimit-point uniqueness. -/
theorem selectedComponentπ₂Leg_eq_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      (selectedComponentπ₂PointIso_of_componentwiseProjection_w489 H).hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₂W485 S) := by
  simpa [selectedComponentπ₂PointIso_of_componentwiseProjection_w489,
    selectedForgottenComponentπ₂CokernelCoforkW485, forgottenExplicitCokernelCoforkW485] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (selectedComponentπ₂_isColimit_of_projection_w489 H.hπ₂)
        (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
          (selectedMetrizableDifferenceπ₂W485 S) (by
            simpa [selectedMetrizableDifferenceπ₂W481, selectedMetrizableDifferenceπ₂W485]
              using H.hclosedπ₂))
        WalkingParallelPair.one)

/-- Third selected component leg equation from colimit-point uniqueness. -/
theorem selectedComponentπ₃Leg_eq_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      (selectedComponentπ₃PointIso_of_componentwiseProjection_w489 H).hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₃W485 S) := by
  simpa [selectedComponentπ₃PointIso_of_componentwiseProjection_w489,
    selectedForgottenComponentπ₃CokernelCoforkW485, forgottenExplicitCokernelCoforkW485] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (selectedComponentπ₃_isColimit_of_projection_w489 H.hπ₃)
        (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
          (selectedMetrizableDifferenceπ₃W485 S) (by
            simpa [selectedMetrizableDifferenceπ₃W481, selectedMetrizableDifferenceπ₃W485]
              using H.hclosedπ₃))
        WalkingParallelPair.one)

/-- W481 componentwise closed-range projection data supply W487 quotient-identification inputs. -/
def closedRangeQuotientIdentificationInputs_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    SelectedComponentClosedRangeQuotientIdentificationInputsW487 S cs where
  pointIsoπ₁ := selectedComponentπ₁PointIso_of_componentwiseProjection_w489 H
  pointIsoπ₂ := selectedComponentπ₂PointIso_of_componentwiseProjection_w489 H
  pointIsoπ₃ := selectedComponentπ₃PointIso_of_componentwiseProjection_w489 H
  legπ₁ := selectedComponentπ₁Leg_eq_of_componentwiseProjection_w489 H
  legπ₂ := selectedComponentπ₂Leg_eq_of_componentwiseProjection_w489 H
  legπ₃ := selectedComponentπ₃Leg_eq_of_componentwiseProjection_w489 H
  closedRangeπ₁ := by
    simpa [selectedMetrizableDifferenceπ₁W481, selectedMetrizableDifferenceπ₁W485]
      using H.hclosedπ₁
  closedRangeπ₂ := by
    simpa [selectedMetrizableDifferenceπ₂W481, selectedMetrizableDifferenceπ₂W485]
      using H.hclosedπ₂
  closedRangeπ₃ := by
    simpa [selectedMetrizableDifferenceπ₃W481, selectedMetrizableDifferenceπ₃W485]
      using H.hclosedπ₃

/-- A W481 componentwise projection provider gives the W487 closed-range quotient provider. -/
def closedRangeQuotientIdentificationProvider_of_componentwiseProjection_w489
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    ClosedRangeQuotientIdentificationProjectionProviderW487 :=
  fun S cs hcs =>
    closedRangeQuotientIdentificationInputs_of_componentwiseProjection_w489
      (hcomponentwise S cs hcs)

section Checks

#check selectedComponentπ₁_isColimit_of_projection_w489
#check selectedComponentπ₂_isColimit_of_projection_w489
#check selectedComponentπ₃_isColimit_of_projection_w489
#check closedRangeQuotientIdentificationInputs_of_componentwiseProjection_w489
#check closedRangeQuotientIdentificationProvider_of_componentwiseProjection_w489

end Checks

end WppOpClosedRangeQuotientIdentificationProviderCurrentHeadV370SupportW489

end LeanLCAExactChallenge
