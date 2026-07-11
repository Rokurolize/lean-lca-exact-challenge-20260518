import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientFoundation

/-!
# Evaluation of the corrected Drinfeld quotient differential

The quotient internal differential is defined by a coproduct descent.  This file exposes the
corresponding elementwise computation on a chosen homogeneous word summand.  It is the reduction
step needed to compute the differential of the formal contracting generator.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

/-- Evaluating the quotient internal differential on an included homogeneous word element is
the signed sum of the internal differentials of that word. -/
theorem quotientInternalDifferential_inclusion_apply
    (X Y : ComplexCategory) (n : ℤ)
    (s : GradedSummandIndex X Y n) (x : largeSummandModule s) :
    (quotientInternalDifferential X Y n).hom
        ((CategoryTheory.Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s).hom x) =
      (internalDifferentialFromSummand s.2).hom x := by
  have h := quotientInternalDifferential_inclusion X Y n s
  exact congrArg (fun f ↦ f.hom x) h

/-- The internal differential of the formal contracting generator reduces to the internal
differential of its one-letter summand. -/
theorem quotientInternalDifferential_contractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (quotientInternalDifferential A.obj A.obj (-1)).hom
        (quotientContractingElement A) =
      (internalDifferentialFromSummand
        (singletonContractingDegreeProfile A)).hom
          (ULift.up (singletonContractingElement A)) := by
  exact quotientInternalDifferential_inclusion_apply A.obj A.obj (-1)
    ⟨singleton A.obj A.obj A, singletonContractingDegreeProfile A⟩
    (ULift.up (singletonContractingElement A))

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
