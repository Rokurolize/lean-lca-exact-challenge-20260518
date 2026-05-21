import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W431: checked boundary from W426 certificate-only W399 inputs to the current
WPP-op exact/frontier theorem surface.

The copied W426/W423/W420/W418 support files are standalone scripts under
`audit/blockers`, not importable Lake modules.  This file therefore states the
small promotion interface needed by the integrated library and proves the
current W318 exact/frontier consumer from that interface.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpExactFrontierFromCertificatesV370SupportW431


/--
The importable W426 package expected after promoting the standalone audit
support files into real modules.  The `certificateOnlyW399Inputs` field is the
W426 theorem result, abstracted here because the copied W426 script is not an
importable dependency in this worktree.
-/
structure PromotedW426CertificateOnlyW399Package : Type 1 where
  certificateOnlyW399Inputs : Prop
  supportDeclarationNames : List String
  remainingPromotionInputs : List String

/--
The exact API bridge still missing from the project surface: promoted W426
certificate-only W399 inputs must supply the left topological W318 frontier.
-/
structure W426CertificateOnlyW399ToLeftFrontier
    (pkg : PromotedW426CertificateOnlyW399Package) : Type 1 where
  to_left_frontier :
    pkg.certificateOnlyW399Inputs →
      WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage

/--
Once W426's certificate-only W399 input package is promoted and connected to
the W318 left-frontier input, the current AddCommGrp exactness frontier proves
the WPP-op exact-acyclic colimit closure.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates
    (pkg : PromotedW426CertificateOnlyW399Package)
    (bridge : W426CertificateOnlyW399ToLeftFrontier pkg)
    (hcert : pkg.certificateOnlyW399Inputs)
    (halg : WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpKernelExact_wppOp_colimit_boundary_for_metrizable) :
    WppOpExactAcyclicFrontierConsolidatedW318.exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  WppOpExactAcyclicFrontierConsolidatedW318.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrp
    (bridge.to_left_frontier hcert) halg

/--
Strict algebraic variant matching the current frontier theorem that retains the
right-surjectivity fields from strict components.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates_strict
    (pkg : PromotedW426CertificateOnlyW399Package)
    (bridge : W426CertificateOnlyW399ToLeftFrontier pkg)
    (hcert : pkg.certificateOnlyW399Inputs)
    (halg : WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable) :
    WppOpExactAcyclicFrontierConsolidatedW318.exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  WppOpExactAcyclicFrontierConsolidatedW318.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrpStrict
    (bridge.to_left_frontier hcert) halg

/--
Snake-cokernel variant matching the most narrowed current exact/frontier
surface in WppOpExactAcyclicFrontierConsolidatedW318.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates_snake
    (pkg : PromotedW426CertificateOnlyW399Package)
    (bridge : W426CertificateOnlyW399ToLeftFrontier pkg)
    (hcert : pkg.certificateOnlyW399Inputs)
    (hsnake : WppOpExactAcyclicFrontierConsolidatedW318.addCommGrpStrictSnakeCokernel_wppOp_colimit_boundary_for_metrizable) :
    WppOpExactAcyclicFrontierConsolidatedW318.exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  WppOpExactAcyclicFrontierConsolidatedW318.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_snakeCokernel
    (bridge.to_left_frontier hcert) hsnake

def w431SupportDeclarationNames : List String :=
  ["PromotedW426CertificateOnlyW399Package",
    "W426CertificateOnlyW399ToLeftFrontier",
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates",
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates_strict",
    "exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates_snake"]

theorem w431SupportDeclarationNames_count :
    w431SupportDeclarationNames.length = 5 := rfl

def remainingInputsW431 : List String :=
  ["promote W426/W423/W420/W418 standalone audit scripts to importable Lean modules",
    "add the project API proving W426 certificate-only W399 inputs imply WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage",
    "supply the remaining W318 algebraic AddCommGrp or SnakeInput frontier"]

theorem remainingInputsW431_count :
    remainingInputsW431.length = 3 := rfl

structure WppOpExactFrontierFromCertificatesV370StateW431 : Type where
  seed : String
  declarations : List String
  remainingInputs : List String
  wppOpExactFrontierFromCertificatesResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpExactFrontierFromCertificatesV370StateW431 :
    WppOpExactFrontierFromCertificatesV370StateW431 where
  seed := "vFkYWtkBRia3SAdp5DZyxJzg"
  declarations := w431SupportDeclarationNames
  remainingInputs := remainingInputsW431
  wppOpExactFrontierFromCertificatesResult :=
    "checked boundary consumer for promoted W426 certificate-only W399 inputs"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpExactFrontierFromCertificatesV370StateW431_productSuccess :
    currentWppOpExactFrontierFromCertificatesV370StateW431.productSuccessClaimed = false := rfl

section Checks

#check PromotedW426CertificateOnlyW399Package
#check W426CertificateOnlyW399ToLeftFrontier
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates_strict
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426_certificates_snake
#check remainingInputsW431
#check currentWppOpExactFrontierFromCertificatesV370StateW431
#check currentWppOpExactFrontierFromCertificatesV370StateW431_productSuccess

end Checks

end WppOpExactFrontierFromCertificatesV370SupportW431

end LeanLCAExactChallenge
