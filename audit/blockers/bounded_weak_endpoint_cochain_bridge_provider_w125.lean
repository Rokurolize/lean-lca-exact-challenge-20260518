import LeanLCAExactChallenge.Derived.ContractibleTail

/-!
Bounded weak-endpoint cochain bridge provider.

The weak endpoint payload is available from distinguished triangles, but it only gives
homotopy-category endpoint isomorphisms. This audit records the equivalent provider
interfaces that would bridge that weak payload into the selected/cochain payloads already
exported by `Derived.Bounded`.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- Provider shape that upgrades the weak endpoint payload to selected cochain data. -/
abbrev boundedWeakEndpointToSelectedCochainStrictification
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  homotopyEndpointPayloadWithoutSelectedCochainIso C →
    boundedTrianglehIso13SelectedCochainStrictification C

omit [QuillenExactCategory C] in
/-- Provider shape that upgrades the weak endpoint payload to compact cochain-isomorphism data. -/
abbrev boundedWeakEndpointToCochainIsoPayload
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  homotopyEndpointPayloadWithoutSelectedCochainIso C →
    boundedTrianglehIso13CochainIsoPayload C

omit [QuillenExactCategory C] in
/-- Provider shape for the current expanded cochain-data strictification frontier. -/
abbrev boundedWeakEndpointToCochainDataProvider
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  homotopyEndpointPayloadWithoutSelectedCochainIso C →
    boundedTrianglehIso13CochainDataStrictification C

omit [QuillenExactCategory C] in
/-- Selected cochain providers give the expanded cochain-data provider through the existing
realization equivalence. -/
theorem boundedWeakEndpointToCochainDataProvider_of_selected
    [HasZeroObject C] [HasBinaryBiproducts C]
    (provider : boundedWeakEndpointToSelectedCochainStrictification C) :
    boundedWeakEndpointToCochainDataProvider C := by
  intro weak
  exact boundedTrianglehIso13CochainDataStrictification_of_realization C
    (boundedHomotopyObjectTrianglehIso13Realization_of_selected_cochain C
      (provider weak))

omit [QuillenExactCategory C] in
/-- Expanded cochain-data providers give selected cochain providers through the promoted
compact cochain-isomorphism API. -/
theorem boundedWeakEndpointToSelected_of_cochainDataProvider
    [HasZeroObject C] [HasBinaryBiproducts C]
    (provider : boundedWeakEndpointToCochainDataProvider C) :
    boundedWeakEndpointToSelectedCochainStrictification C := by
  intro weak
  exact boundedTrianglehIso13SelectedCochainStrictification_of_cochain_iso_payload C
    (boundedTrianglehIso13CochainIsoPayload_of_cochain_data C (provider weak))

omit [QuillenExactCategory C] in
/-- The selected-provider and expanded cochain-data-provider formulations are equivalent. -/
theorem boundedWeakEndpointToSelected_iff_cochainDataProvider
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedWeakEndpointToSelectedCochainStrictification C ↔
      boundedWeakEndpointToCochainDataProvider C := by
  constructor
  · exact boundedWeakEndpointToCochainDataProvider_of_selected C
  · exact boundedWeakEndpointToSelected_of_cochainDataProvider C

omit [QuillenExactCategory C] in
/-- Compact cochain-isomorphism providers give the expanded cochain-data provider. -/
theorem boundedWeakEndpointToCochainDataProvider_of_cochainIso
    [HasZeroObject C] [HasBinaryBiproducts C]
    (provider : boundedWeakEndpointToCochainIsoPayload C) :
    boundedWeakEndpointToCochainDataProvider C := by
  intro weak
  exact boundedTrianglehIso13CochainDataStrictification_of_cochain_iso_payload C
    (provider weak)

omit [QuillenExactCategory C] in
/-- Expanded cochain-data providers give compact cochain-isomorphism providers. -/
theorem boundedWeakEndpointToCochainIso_of_cochainDataProvider
    [HasZeroObject C] [HasBinaryBiproducts C]
    (provider : boundedWeakEndpointToCochainDataProvider C) :
    boundedWeakEndpointToCochainIsoPayload C := by
  intro weak
  exact boundedTrianglehIso13CochainIsoPayload_of_cochain_data C (provider weak)

omit [QuillenExactCategory C] in
/-- The compact and expanded provider formulations are equivalent. -/
theorem boundedWeakEndpointToCochainIso_iff_cochainDataProvider
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedWeakEndpointToCochainIsoPayload C ↔
      boundedWeakEndpointToCochainDataProvider C := by
  constructor
  · exact boundedWeakEndpointToCochainDataProvider_of_cochainIso C
  · exact boundedWeakEndpointToCochainIso_of_cochainDataProvider C

/-- The provider cannot be supplied by the unconditional homotopy-equivalence
strictification bridge; the concrete alternating tail refutes that bridge. -/
theorem reject_unconditional_endpointHomotopyEquiv_provider_w125
    [HasZeroObject AlternatingTailExtendTransport.IntModuleCat]
    [HasBinaryBiproducts AlternatingTailExtendTransport.IntModuleCat] :
    ¬ endpointHomotopyEquivToSelectedCochainIsoStrictification
        AlternatingTailExtendTransport.IntModuleCat :=
  AlternatingTailExtendTransport.not_endpointHomotopyEquivToSelectedCochainIsoStrictification_intModuleCat

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check homotopyEndpointPayloadWithoutSelectedCochainIso
#check boundedTrianglehIso13SelectedCochainStrictification
#check boundedTrianglehIso13CochainIsoPayload
#check boundedTrianglehIso13CochainDataStrictification
#check boundedWeakEndpointToSelectedCochainStrictification
#check boundedWeakEndpointToCochainIsoPayload
#check boundedWeakEndpointToCochainDataProvider
#check boundedWeakEndpointToSelected_iff_cochainDataProvider
#check boundedWeakEndpointToCochainIso_iff_cochainDataProvider
#check reject_unconditional_endpointHomotopyEquiv_provider_w125

end Checks

end LeanLCAExactChallenge
