import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainClosed2Route

/-!
W849 routes W735 exact-input endpoint data through the W665/W666
forgetful-homological-kernel construction.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace Dbounded

/--
W849 closed-map route: W735 endpoint strict-topology data and the W736
comparison-isomorphism input supply exact-acyclic homotopy-object Closed₂.
-/
theorem closed2OfClosedMapExactInputsW849
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableExactAcyclicHomotopyObjectClosed2W848 :=
  metrizableExactAcyclicHomotopyObjectClosed2_of_forgetfulHomologicalKernelW665
    (metrizableExactAcyclicHomotopyObjectForgetfulHomologicalKernelPayload_of_endpointW666
      (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
      (metrizableExactAtEndpointStrictTopologyInputs_of_endpointStrictTopologyDataW720
        exactInputs.endpointStrictTopologyData))

/--
W849 closed-embedding route: W735 endpoint strict-topology data and the W736
comparison-isomorphism input supply exact-acyclic homotopy-object Closed₂.
-/
theorem closed2OfClosedEmbeddingExactInputsW849
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableExactAcyclicHomotopyObjectClosed2W848 :=
  metrizableExactAcyclicHomotopyObjectClosed2_of_forgetfulHomologicalKernelW665
    (metrizableExactAcyclicHomotopyObjectForgetfulHomologicalKernelPayload_of_endpointW666
      (cochainHasHomology_of_leftRightComparisonIsoW768 comparisonIso)
      (metrizableExactAtEndpointStrictTopologyInputs_of_endpointStrictTopologyDataW720
        exactInputs.endpointStrictTopologyData))

/--
W849 closed-map route: W735 exact inputs plus the W736 comparison-isomorphism
input construct the W847 selected-cochain strictification payload.
-/
theorem selectedCochainStrictificationOfClosedMapExactInputsW849
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :=
  selectedCochainStrictificationOfClosedMapExactInputsClosed2W848
    comparisonIso
    exactInputs
    (closed2OfClosedMapExactInputsW849 comparisonIso exactInputs)

/--
W849 closed-embedding route: W735 exact inputs plus the W736 comparison-
isomorphism input construct the W847 selected-cochain strictification payload.
-/
theorem selectedCochainStrictificationOfClosedEmbeddingExactInputsW849
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :=
  selectedCochainStrictificationOfClosedEmbeddingExactInputsClosed2W848
    comparisonIso
    exactInputs
    (closed2OfClosedEmbeddingExactInputsW849 comparisonIso exactInputs)

def selectedCochainExactInputsRouteInputNamesW849 : List String :=
  ["universal IsIso for every MetrizableLCA left-right homology comparison",
    "one W735 closed-map or closed-embedding exact-input branch"]

theorem selectedCochainExactInputsRouteInputNamesW849_count :
    selectedCochainExactInputsRouteInputNamesW849.length = 2 :=
  rfl

structure MetrizableSelectedCochainExactInputsRouteStateW849 :
    Type where
  seed : String
  declarations : List String
  closed2Result : String
  selectedPayloadResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSelectedCochainExactInputsRouteStateW849 :
    MetrizableSelectedCochainExactInputsRouteStateW849
    where
  seed := "w849-exact-inputs-selected-cochain-route"
  declarations :=
    ["Dbounded.closed2OfClosedMapExactInputsW849",
      "Dbounded.closed2OfClosedEmbeddingExactInputsW849",
      "Dbounded.selectedCochainStrictificationOfClosedMapExactInputsW849",
      "Dbounded.selectedCochainStrictificationOfClosedEmbeddingExactInputsW849",
      "Dbounded.selectedCochainExactInputsRouteInputNamesW849",
      "Dbounded.selectedCochainExactInputsRouteInputNamesW849_count"]
  closed2Result :=
    "proved: W735 endpoint strict-topology data plus W736 comparison-isomorphism\
      data supply exact-acyclic homotopy-object Closed₂ through W665/W666"
  selectedPayloadResult :=
    "proved: the W848 selected-cochain route consumes that Closed₂ witness and\
      W812 homotopy-equivalence invariance for both exact-input branches"
  remainingInputs :=
    ["construct the universal left-right comparison isomorphism for arbitrary\
        MetrizableLCA short complexes",
      "construct concrete values for one W735 exact-input branch",
      "construct the final original four-task witness and review packet"]
  productSuccessClaimed := false

theorem currentW849SelectedCochainExactInputsRoute_productSuccess :
    currentMetrizableSelectedCochainExactInputsRouteStateW849.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
