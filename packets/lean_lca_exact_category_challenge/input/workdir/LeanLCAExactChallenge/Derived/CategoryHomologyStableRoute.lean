import LeanLCAExactChallenge.Derived.LeftRightComparisonRoute

/-!
W766 routes category-level MetrizableLCA homology into the Dbounded W669
kernel/cokernel-conditioned stable-certificate path.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory

namespace Dbounded

/--
W766: `CategoryWithHomology MetrizableLCA` supplies homology for every
MetrizableLCA cochain complex and degree.
-/
theorem cochainHasHomology_of_categoryWithHomologyW766
    [CategoryWithHomology MetrizableLCA.{0}] :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i := by
  intro K i
  infer_instance

/--
W766 replaces W669's raw global cochain-homology function with a category-level
homology premise in the kernel/cokernel-conditioned left-calculus route.
-/
noncomputable def metrizableLeftCalculusFieldsOfKernelCokernelCategoryHomology_w766
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (I : MetrizableExactAtKernelCokernelConditionedTopologyInputs)
    (R : BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}) :
    Dbounded.MetrizableLeftCalculusSemanticFields :=
  Dbounded.metrizableLeftCalculusFieldsOfKernelCokernelConditionedTopology_w669
    cochainHasHomology_of_categoryWithHomologyW766 I R

/--
W766 kernel/cokernel-conditioned category-homology route: W669 plus WPP
transfer supplies ordinary stable semantics.
-/
noncomputable def
    metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyWppTransfer_w766
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (I : MetrizableExactAtKernelCokernelConditionedTopologyInputs)
    (R : BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0})
    (inputs :
      Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
        (metrizableLeftCalculusFieldsOfKernelCokernelCategoryHomology_w766 I R)) :
    Dbounded.MetrizableOrdinaryStableSemanticInput := by
  exact
    Dbounded.metrizableOrdinaryStableSemanticInputOfKernelCokernelConditionedWppTransfer_w669
      cochainHasHomology_of_categoryWithHomologyW766 I R inputs

/-- W766 category-homology WPP-transfer route produces a ready stable certificate. -/
theorem stableCertificateOfKernelCokernelCategoryHomologyWppTransfer_w766_ready
    [CategoryWithHomology MetrizableLCA.{0}]
    [(exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (I : MetrizableExactAtKernelCokernelConditionedTopologyInputs)
    (R : BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0})
    (inputs :
      Dbounded.MetrizableWalkingParallelPairTransferStableSemanticInputs
        (metrizableLeftCalculusFieldsOfKernelCokernelCategoryHomology_w766 I R)) :
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyWppTransfer_w766
        I R inputs)).ready := by
  exact
    Dbounded.stableCertificateOfKernelCokernelConditionedWppTransfer_w669_ready
      cochainHasHomology_of_categoryWithHomologyW766 I R inputs

/-- W766 input names after replacing raw cochain homology by category homology. -/
def metrizableKernelCokernelCategoryHomologyWppTransferStableInputNamesW766 :
    List String :=
  ["CategoryWithHomology MetrizableLCA",
    "MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "bounded homotopy localized right adjoint plus unit membership",
    "MetrizableWalkingParallelPairTransferStableSemanticInputs"]

theorem metrizableKernelCokernelCategoryHomologyWppTransferStableInputNamesW766_count :
    metrizableKernelCokernelCategoryHomologyWppTransferStableInputNamesW766.length =
      5 :=
  rfl

/-- W766 route names for the category-homology kernel/cokernel path. -/
def metrizableKernelCokernelCategoryHomologyWppTransferStableRouteNamesW766 :
    List String :=
  ["cochainHasHomology_of_categoryWithHomologyW766",
    "metrizableLeftCalculusFieldsOfKernelCokernelCategoryHomology_w766",
    "metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyWppTransfer_w766",
    "stableCertificateOfKernelCokernelCategoryHomologyWppTransfer_w766_ready"]

theorem metrizableKernelCokernelCategoryHomologyWppTransferStableRouteNamesW766_count :
    metrizableKernelCokernelCategoryHomologyWppTransferStableRouteNamesW766.length =
      4 :=
  rfl

/-- Current checked W766 state for the category-homology stable route. -/
structure MetrizableKernelCokernelCategoryHomologyWppTransferStableRouteStateW766 :
    Type where
  seed : String
  declarations : List String
  homologyProjectionResult : String
  stableInputResult : String
  certificateResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W766 state. -/
def currentMetrizableKernelCokernelCategoryHomologyWppTransferStableRouteSupportStateW766 :
    MetrizableKernelCokernelCategoryHomologyWppTransferStableRouteStateW766
    where
  seed := "w766-category-homology-kernel-cokernel-wpp-transfer-stable"
  declarations :=
    ["cochainHasHomology_of_categoryWithHomologyW766",
      "metrizableLeftCalculusFieldsOfKernelCokernelCategoryHomology_w766",
      "metrizableOrdinaryStableSemanticInputOfKernelCokernelCategoryHomologyWppTransfer_w766",
      "stableCertificateOfKernelCokernelCategoryHomologyWppTransfer_w766_ready",
      "metrizableKernelCokernelCategoryHomologyWppTransferStableInputNamesW766",
      "metrizableKernelCokernelCategoryHomologyWppTransferStableInputNamesW766_count",
      "metrizableKernelCokernelCategoryHomologyWppTransferStableRouteNamesW766",
      "metrizableKernelCokernelCategoryHomologyWppTransferStableRouteNamesW766_count"]
  homologyProjectionResult :=
    "proved: CategoryWithHomology MetrizableLCA supplies HasHomology for every MetrizableLCA cochain complex and degree"
  stableInputResult :=
    "proved: W669 kernel/cokernel-conditioned calculus plus WPP transfer can use category homology instead of a raw cochain-homology function"
  certificateResult :=
    "proved: the W766 category-homology WPP-transfer route produces a ready stable certificate"
  replacedInputs :=
    ["raw function: for every MetrizableLCA cochain complex and degree, HasHomology"]
  remainingInputs :=
    ["construct CategoryWithHomology MetrizableLCA",
      "construct MetrizableExactAtKernelCokernelConditionedTopologyInputs",
      "prove exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
      "construct bounded homotopy localized right adjoint plus unit membership",
      "construct concrete WPP transfer stable semantic inputs"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentMetrizableKernelCokernelCategoryHomologyWppTransferStableRouteStateW766 :
    MetrizableKernelCokernelCategoryHomologyWppTransferStableRouteStateW766 :=
  currentMetrizableKernelCokernelCategoryHomologyWppTransferStableRouteSupportStateW766

theorem
    currentMetrizableKernelCokernelCategoryHomologyWppTransferStableRouteStateW766_productSuccess :
    currentMetrizableKernelCokernelCategoryHomologyWppTransferStableRouteStateW766.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
