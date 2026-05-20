import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.ContractibleTail

/-!
Distinguished endpoint provider frontier.

The unconditional provider from homotopy-category endpoint isomorphisms to cochain-complex
isomorphisms is refuted by the alternating-tail counterexample. This audit records the
correct narrower provider shape: it asks directly, for each distinguished mapping-cone
presentation with bounded endpoint homotopy objects, for cochain-level endpoint
isomorphisms. The shape is exactly equivalent to the existing bounded strict-realization
frontier, so it is a name for the remaining positive theorem rather than a shortcut.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- The narrow endpoint provider still allowed by the counterexample: for each actual
distinguished triangle with bounded endpoint homotopy objects, produce selected
cochain-level endpoint isomorphisms for one mapping-cone presentation. -/
abbrev distinguishedEndpointSelectedCochainIsoProvider
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  boundedTrianglehIso13CochainIsoPayload C

omit [QuillenExactCategory C] in
/-- The distinguished endpoint provider gives bounded strict realization through the
existing selected/cochain payload consumer. -/
theorem boundedRealization_of_distinguishedEndpointSelectedCochainIsoProvider
    [HasZeroObject C] [HasBinaryBiproducts C]
    (provider : distinguishedEndpointSelectedCochainIsoProvider C) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_iso_payload C provider

omit [QuillenExactCategory C] in
/-- Bounded strict realization supplies the same distinguished endpoint provider by
choosing the selected source and cone as their own bounded representatives. -/
theorem distinguishedEndpointSelectedCochainIsoProvider_of_boundedRealization
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize : boundedHomotopyObjectTrianglehIso13Realization C) :
    distinguishedEndpointSelectedCochainIsoProvider C :=
  boundedTrianglehIso13CochainIsoPayload_of_realization C realize

omit [QuillenExactCategory C] in
/-- The narrow distinguished-endpoint provider is not weaker than the remaining bounded
frontier; it is an equivalent formulation of bounded strict realization. -/
theorem distinguishedEndpointSelectedCochainIsoProvider_iff_boundedRealization
    [HasZeroObject C] [HasBinaryBiproducts C] :
    distinguishedEndpointSelectedCochainIsoProvider C ↔
      boundedHomotopyObjectTrianglehIso13Realization C := by
  constructor
  · exact boundedRealization_of_distinguishedEndpointSelectedCochainIsoProvider C
  · exact distinguishedEndpointSelectedCochainIsoProvider_of_boundedRealization C

/-- The disallowed broad provider remains refuted over `IntModuleCat`; the new provider
above is intentionally narrower and does not claim to strictify arbitrary homotopy
equivalences or arbitrary weak endpoint payloads. -/
theorem reject_broad_endpoint_strictification_provider
    [HasZeroObject AlternatingTailExtendTransport.IntModuleCat]
    [HasBinaryBiproducts AlternatingTailExtendTransport.IntModuleCat] :
    ¬ endpointHomotopyEquivToSelectedCochainIsoStrictification
        AlternatingTailExtendTransport.IntModuleCat :=
  AlternatingTailExtendTransport.not_endpointHomotopyEquivToSelectedCochainIsoStrictification_intModuleCat

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check distinguishedEndpointSelectedCochainIsoProvider
#check boundedRealization_of_distinguishedEndpointSelectedCochainIsoProvider
#check distinguishedEndpointSelectedCochainIsoProvider_of_boundedRealization
#check distinguishedEndpointSelectedCochainIsoProvider_iff_boundedRealization
#check reject_broad_endpoint_strictification_provider

end Checks

end LeanLCAExactChallenge
