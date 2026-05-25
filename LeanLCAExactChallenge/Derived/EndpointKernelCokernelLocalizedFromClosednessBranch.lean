import LeanLCAExactChallenge.Derived.EndpointKernelCokernelFromClosednessBranch
import LeanLCAExactChallenge.Derived.KernelCokernelProductRoute

/-!
W858 replaces W857's raw localized-right-adjoint input by the existing W721
localized-right-adjoint data provider.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace Dbounded

/--
W858 direct-left-calculus data: W857 endpoint kernel/cokernel data with the
localized-right-adjoint field expressed as the W721 provider.
-/
structure
    MetrizableEndpointKernelCokernelLocalizedRightAdjointDataW858 :
    Type 2 where
  exactClosed2 :
    (exactAcyclicHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂
  closednessData :
    MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725
  endpointKernelCokernelFacts :
    MetrizableWppEndpointKernelCokernelFactsProviderW857
  localizedRightAdjointData :
    MetrizableWppLocalizedRightAdjointDataProviderW721

/-- W858 converts W721 localized-right-adjoint data into W857's data surface. -/
noncomputable def endpointKernelCokernelLeftCalculusDataOfLocalizedRightAdjointW858
    (data :
      MetrizableEndpointKernelCokernelLocalizedRightAdjointDataW858) :
    MetrizableComparisonBijectivityEndpointKernelCokernelLeftCalculusDataW857 where
  exactClosed2 := data.exactClosed2
  closednessData := data.closednessData
  endpointKernelCokernelFacts := data.endpointKernelCokernelFacts
  localizedRightAdjoint :=
    boundedHomotopyLocalizedRightAdjointInput_of_localizedRightAdjointDataW767
      data.localizedRightAdjointData

/-- W858 direct bounded left calculus with localized-right-adjoint data in W721 form. -/
theorem directBoundedLeftCalculusOfEndpointKernelCokernelLocalizedRightAdjointW858
    (data :
      MetrizableEndpointKernelCokernelLocalizedRightAdjointDataW858) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  Dbounded.directBoundedLeftCalculusOfEndpointKernelCokernelW857
    (Dbounded.endpointKernelCokernelLeftCalculusDataOfLocalizedRightAdjointW858
      data)

/-- W858 stable route with W721 localized-right-adjoint data. -/
noncomputable def
    boundedDerivedInfinityCategoryOfEndpointKernelCokernelLocalizedRightAdjointW858
    (data :
      MetrizableEndpointKernelCokernelLocalizedRightAdjointDataW858)
    (finiteLimits : HasFiniteLimits (Dbounded MetrizableLCA.{0}))
    (finiteColimits : HasFiniteColimits (Dbounded MetrizableLCA.{0}))
    (pretriangulated :
      letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
        Dbounded.directBoundedLeftCalculusOfComparisonBijectivityW831
          (Dbounded.comparisonBijectivityLeftCalculusDataOfEndpointKernelCokernelW857
            (Dbounded.endpointKernelCokernelLeftCalculusDataOfLocalizedRightAdjointW858
              data))
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
            (Dbounded.endpointKernelCokernelLeftCalculusDataOfLocalizedRightAdjointW858
              data))
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
  Dbounded.boundedDerivedInfinityCategoryOfEndpointKernelCokernelW857
    (Dbounded.endpointKernelCokernelLeftCalculusDataOfLocalizedRightAdjointW858
      data)
    finiteLimits finiteColimits pretriangulated triangulated

/-- W858 direct-left-calculus inputs after replacing the raw localized adjoint by W721 data. -/
def endpointKernelCokernelLocalizedLeftCalculusInputNamesW858 :
    List String :=
  ["exactAcyclicHomotopyIsoClosure MetrizableLCA is triangulated closed",
    "matched selected-difference component and W519 mapped-cokernel closedness branch provider",
    "endpoint kernel/cokernel ExactAt facts",
    "W721 bounded homotopy localized-right-adjoint data provider"]

theorem endpointKernelCokernelLocalizedLeftCalculusInputNamesW858_count :
    endpointKernelCokernelLocalizedLeftCalculusInputNamesW858.length = 4 :=
  rfl

/-- W858 expanded stable-route requirements. -/
def endpointKernelCokernelLocalizedStableRouteExpandedInputNamesW858 :
    List String :=
  endpointKernelCokernelLocalizedLeftCalculusInputNamesW858 ++
    ["HasFiniteLimits (Dbounded MetrizableLCA)",
      "HasFiniteColimits (Dbounded MetrizableLCA)",
      "Pretriangulated (Dbounded MetrizableLCA)",
      "IsTriangulated (Dbounded MetrizableLCA)"]

theorem endpointKernelCokernelLocalizedStableRouteExpandedInputNamesW858_count :
    endpointKernelCokernelLocalizedStableRouteExpandedInputNamesW858.length = 8 :=
  rfl

/-- Current checked W858 state for the W721-localized W857 route. -/
structure MetrizableEndpointKernelCokernelLocalizedRouteStateW858 :
    Type where
  seed : String
  declarations : List String
  localizedRightAdjointResult : String
  leftCalculusResult : String
  stablePackageResult : String
  replacedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current W858 nonterminal state. -/
def currentMetrizableEndpointKernelCokernelLocalizedRouteStateW858 :
    MetrizableEndpointKernelCokernelLocalizedRouteStateW858
    where
  seed :=
    "w858-endpoint-kernel-cokernel-w721-localized-right-adjoint"
  declarations :=
    ["MetrizableEndpointKernelCokernelLocalizedRightAdjointDataW858",
      "endpointKernelCokernelLeftCalculusDataOfLocalizedRightAdjointW858",
      "directBoundedLeftCalculusOfEndpointKernelCokernelLocalizedRightAdjointW858",
      "boundedDerivedInfinityCategoryOfEndpointKernelCokernelLocalizedRightAdjointW858",
      "endpointKernelCokernelLocalizedLeftCalculusInputNamesW858",
      "endpointKernelCokernelLocalizedLeftCalculusInputNamesW858_count",
      "endpointKernelCokernelLocalizedStableRouteExpandedInputNamesW858",
      "endpointKernelCokernelLocalizedStableRouteExpandedInputNamesW858_count"]
  localizedRightAdjointResult :=
    "proved: the W767 projection converts W721 localized-right-adjoint data \
      into the raw W857 BoundedHomotopyLocalizedRightAdjointInput"
  leftCalculusResult :=
    "proved: W858 data supply the W857 endpoint kernel/cokernel direct \
      bounded left-calculus route"
  stablePackageResult :=
    "proved: the W857 stable package can be invoked through the W858 data surface"
  replacedInputs :=
    ["raw BoundedHomotopyLocalizedRightAdjointInput MetrizableLCA"]
  remainingInputs :=
    endpointKernelCokernelLocalizedStableRouteExpandedInputNamesW858
  productSuccessClaimed := false

theorem currentW858EndpointKernelCokernelLocalizedRoute_productSuccess :
    currentMetrizableEndpointKernelCokernelLocalizedRouteStateW858.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
