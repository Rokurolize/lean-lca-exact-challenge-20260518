import LeanLCAExactChallenge.Derived.EndpointTopologyFromClosednessBranch
import LeanLCAExactChallenge.Derived.ComparisonBijectivityLeftCalculusRoute

/-!
W857 routes W519 closedness-derived forgetful homology preservation through the
kernel/cokernel-conditioned endpoint topology surface used by W831.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/--
W857 endpoint facts for the W668 kernel/cokernel-conditioned topology route.
The W856/W519 branch supplies forgetful homology preservation separately.
-/
structure MetrizableWppEndpointKernelCokernelFactsProviderW857 :
    Type 2 where
  kernelOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → IsLimit (KernelFork.ofι (K.sc i).f (K.sc i).zero)
  cokernelOfExactAt :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ),
      K.ExactAt i → IsColimit (CokernelCofork.ofπ (K.sc i).g (K.sc i).zero)

/--
W857 builds the W668 endpoint topology input from W519 closedness plus the two
kernel/cokernel ExactAt facts.
-/
def kernelCokernelConditionedTopologyInputsOfClosednessBranchW857
    (closednessData :
      MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725)
    (facts : MetrizableWppEndpointKernelCokernelFactsProviderW857) :
    MetrizableExactAtKernelCokernelConditionedTopologyInputs where
  forgetPreservesHomology :=
    endpointForgetPreservesHomologyOfClosednessBranchW856 closednessData
  kernel_of_exactAt := facts.kernelOfExactAt
  cokernel_of_exactAt := facts.cokernelOfExactAt

/--
W857 direct-left-calculus data: W831's comparison route plus W519 closedness
and ExactAt kernel/cokernel endpoint facts.
-/
structure
    MetrizableComparisonBijectivityEndpointKernelCokernelLeftCalculusDataW857 :
    Type 2 where
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  closednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  endpointKernelCokernelFacts :
    MetrizableWppEndpointKernelCokernelFactsProviderW857
  localizedRightAdjoint :
    BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA.{0}

/-- W857 supplies W831's three-field data package from the W519/kernels route. -/
noncomputable def comparisonBijectivityLeftCalculusDataOfEndpointKernelCokernelW857
    (data :
      MetrizableComparisonBijectivityEndpointKernelCokernelLeftCalculusDataW857) :
    MetrizableDirectBoundedLeftCalculusDataWithoutComparisonW831 where
  exactClosed2 := data.exactClosed2
  kernelCokernelTopologyData :=
    kernelCokernelConditionedTopologyInputsOfClosednessBranchW857
      data.closednessData data.endpointKernelCokernelFacts
  localizedRightAdjoint := data.localizedRightAdjoint

/--
W857 proves direct bounded left calculus from W519 closedness, ExactAt
kernel/cokernel facts, the exact-closedness input, and the localized right
adjoint input.
-/
theorem directBoundedLeftCalculusOfEndpointKernelCokernelW857
    (data :
      MetrizableComparisonBijectivityEndpointKernelCokernelLeftCalculusDataW857) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  Dbounded.directBoundedLeftCalculusOfComparisonBijectivityW831
    (Dbounded.comparisonBijectivityLeftCalculusDataOfEndpointKernelCokernelW857
      data)

/-- W857 stable route through W831 after replacing endpoint topology by kernel/cokernel facts. -/
noncomputable def boundedDerivedInfinityCategoryOfEndpointKernelCokernelW857
    (data :
      MetrizableComparisonBijectivityEndpointKernelCokernelLeftCalculusDataW857)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        Dbounded.directBoundedLeftCalculusOfComparisonBijectivityW831
          (Dbounded.comparisonBijectivityLeftCalculusDataOfEndpointKernelCokernelW857
            data)
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      Pretriangulated (Dbounded MetrizableLCA.{0}))
    (triangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        Dbounded.directBoundedLeftCalculusOfComparisonBijectivityW831
          (Dbounded.comparisonBijectivityLeftCalculusDataOfEndpointKernelCokernelW857
            data)
      letI : Preadditive (Dbounded MetrizableLCA.{0}) :=
        Dbounded.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : HasZeroObject (Dbounded MetrizableLCA.{0}) :=
        Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions MetrizableLCA.{0}
      letI : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive := by
        intro n
        exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
          MetrizableLCA.{0} n
      letI : Pretriangulated (Dbounded MetrizableLCA.{0}) := pretriangulated
      IsTriangulated (Dbounded MetrizableLCA.{0})) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfComparisonBijectivityLeftCalculusW831
    (Dbounded.comparisonBijectivityLeftCalculusDataOfEndpointKernelCokernelW857
      data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W857 endpoint kernel/cokernel facts still required after W519 supplies homology preservation. -/
def endpointKernelCokernelFactInputNamesW857 : List String :=
  ["ExactAt supplies the incoming endpoint kernel fork",
    "ExactAt supplies the outgoing endpoint cokernel cofork"]

theorem endpointKernelCokernelFactInputNamesW857_count :
    endpointKernelCokernelFactInputNamesW857.length = 2 :=
  rfl

/-- W857 direct-left-calculus inputs after expanding the W831 topology field. -/
def endpointKernelCokernelLeftCalculusInputNamesW857 : List String :=
  ["exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "endpoint kernel/cokernel ExactAt facts",
    "bounded homotopy localized right adjoint plus unit membership"]

theorem endpointKernelCokernelLeftCalculusInputNamesW857_count :
    endpointKernelCokernelLeftCalculusInputNamesW857.length = 4 :=
  rfl

/-- W857 expanded stable-route requirements. -/
def endpointKernelCokernelStableRouteExpandedInputNamesW857 : List String :=
  endpointKernelCokernelLeftCalculusInputNamesW857 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

theorem endpointKernelCokernelStableRouteExpandedInputNamesW857_count :
    endpointKernelCokernelStableRouteExpandedInputNamesW857.length = 8 :=
  rfl

/-- Current checked W857 state for the endpoint kernel/cokernel closedness branch route. -/
structure MetrizableEndpointKernelCokernelFromClosednessBranchStateW857 :
    Type where
  seed : String
  declarations : List String
  forgetPreservesHomologyResult : String
  topologyInputResult : String
  leftCalculusResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current W857 nonterminal state. -/
def currentMetrizableEndpointKernelCokernelFromClosednessBranchStateW857 :
    MetrizableEndpointKernelCokernelFromClosednessBranchStateW857
    where
  seed :=
    "w857-endpoint-kernel-cokernel-from-mapped-cokernel-closedness"
  declarations :=
    ["MetrizableWppEndpointKernelCokernelFactsProviderW857",
      "kernelCokernelConditionedTopologyInputsOfClosednessBranchW857",
      "MetrizableComparisonBijectivityEndpointKernelCokernelLeftCalculusDataW857",
      "comparisonBijectivityLeftCalculusDataOfEndpointKernelCokernelW857",
      "directBoundedLeftCalculusOfEndpointKernelCokernelW857",
      "boundedDerivedInfinityCategoryOfEndpointKernelCokernelW857",
      "endpointKernelCokernelFactInputNamesW857",
      "endpointKernelCokernelFactInputNamesW857_count",
      "endpointKernelCokernelLeftCalculusInputNamesW857",
      "endpointKernelCokernelLeftCalculusInputNamesW857_count",
      "endpointKernelCokernelStableRouteExpandedInputNamesW857",
      "endpointKernelCokernelStableRouteExpandedInputNamesW857_count"]
  forgetPreservesHomologyResult :=
    "proved: W519 closed-map or closed-embedding mapped-cokernel data supply \
      forgetful homology preservation through the W856 closedness branch"
  topologyInputResult :=
    "proved: W519 closedness plus two endpoint ExactAt kernel/cokernel facts \
      construct the W668 kernel/cokernel-conditioned topology input"
  leftCalculusResult :=
    "proved: W831 comparison bijectivity consumes the W857 topology input to \
      produce direct bounded left calculus"
  stablePackageResult :=
    "proved: the W831 stable package can be invoked through the W857 data surface"
  replacedInputs :=
    ["W856 direct endpoint closed-embedding facts",
      "W856 direct endpoint open-map facts",
      "W856 endpoint ExactAt-to-epi facts"]
  remainingInputs :=
    endpointKernelCokernelStableRouteExpandedInputNamesW857
  productSuccessClaimed := false

theorem currentW857EndpointKernelCokernelFromClosednessBranch_productSuccess :
    currentMetrizableEndpointKernelCokernelFromClosednessBranchStateW857.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
