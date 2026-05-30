import LeanLCAExactChallenge.Derived.WppOpExactAcyclicProjectionFields
import LeanLCAExactChallenge.LCA.ForgottenCokernel

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open MetrizableLCA

namespace WppOpW485ClosedRangeProjectionTransportParentW487

open WppOpQuotientIdentificationProjectionProviderV370SupportW485

#check IsColimit.equivOfNatIsoOfIso
#check IsColimit.ofIsoColimit
#check forgottenCokernelCoforkMappedCoconeIso
#check forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosed_range
#check WppOpQuotientIdentificationProjectionProviderV370SupportW485.forgottenExplicitCokernelCoforkW485

/-- Transport the W433-shaped mapped cokernel colimit back to the typed AddCommGrp cofork. -/
def forgottenCokernelCoforkIsColimit_of_closedRange_w487
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (forgottenCokernelCofork f) :=
  (IsColimit.equivOfNatIsoOfIso
    (forgottenCokernelParallelPairIso f)
    (forgottenCokernelCofork f)
    (forgottenMappedExplicitCokernelCocone f)
    (forgottenCokernelCoforkMappedCoconeIso f)).symm
      (forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosed_range f hclosed)

/-- Closed range also gives the W485 duplicate explicit AddCommGrp cokernel cofork. -/
def forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (forgottenExplicitCokernelCoforkW485 f) := by
  simpa [
    forgottenExplicitCokernelCoforkW485,
    forgottenCokernelπW485,
    forgottenCokernelπ_conditionW485,
    underlyingForgetfulFunctorW485,
    forgottenCokernelCofork,
    forgottenCokernelπ,
    forgottenCokernelπ_condition] using
    (forgottenCokernelCoforkIsColimit_of_closedRange_w487 f hclosed)

#check forgottenCokernelCoforkIsColimit_of_closedRange_w487
#check forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487

end WppOpW485ClosedRangeProjectionTransportParentW487

end LeanLCAExactChallenge
