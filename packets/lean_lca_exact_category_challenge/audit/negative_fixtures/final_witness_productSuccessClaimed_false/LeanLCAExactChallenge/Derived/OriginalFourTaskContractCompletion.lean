namespace LeanLCAExactChallenge
namespace Dbounded

structure OriginalFourTaskContractCompletion where
  productSuccessClaimed : Bool

def originalFourTaskContractCompletion : OriginalFourTaskContractCompletion where
  productSuccessClaimed := false

theorem originalFourTaskContractCompletion_productSuccessClaimed :
    originalFourTaskContractCompletion.productSuccessClaimed = false :=
  rfl

end Dbounded
end LeanLCAExactChallenge
