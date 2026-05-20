import LeanLCAExactChallenge.Derived.Bounded

/-!
Selected cochain restricted-isomorphism payload guard.

The production declarations now live in `LeanLCAExactChallenge.Derived.Bounded`.
This audit file keeps the w114 declaration names as thin aliases so old review
commands continue to check the same route.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
abbrev boundedTrianglehIso13RestrictedEndpointCochainIsoPayload
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  boundedTrianglehIso13CochainIsoPayload C

omit [QuillenExactCategory C] in
abbrev boundedTrianglehIso13CochainDataStrictification_w114
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  boundedTrianglehIso13CochainDataStrictification C

omit [QuillenExactCategory C] in
theorem boundedHomotopyObjectTrianglehIso13Realization_of_restricted_endpoint_cochain_isos
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_iso_payload C strictify

omit [QuillenExactCategory C] in
theorem boundedTrianglehIso13CochainDataStrictification_of_restricted_endpoint_cochain_isos_w114
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C) :
    boundedTrianglehIso13CochainDataStrictification_w114 C :=
  boundedTrianglehIso13CochainDataStrictification_of_cochain_iso_payload C strictify

omit [QuillenExactCategory C] in
theorem boundedTrianglehIso13RestrictedEndpointCochainIsoPayload_of_cochain_data_w114
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13CochainDataStrictification_w114 C) :
    boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C :=
  boundedTrianglehIso13CochainIsoPayload_of_cochain_data C strictify

omit [QuillenExactCategory C] in
theorem boundedTrianglehIso13RestrictedEndpointCochainIsoPayload_iff_cochain_data_w114
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C ↔
      boundedTrianglehIso13CochainDataStrictification_w114 C :=
  boundedTrianglehIso13CochainIsoPayload_iff_cochain_data C

#check BoundedTrianglehIso13SelectedCochainPayload
#check boundedTrianglehIso13SelectedCochainStrictification
#check boundedTrianglehIso13RestrictedEndpointCochainIsoPayload
#check boundedTrianglehIso13CochainDataStrictification_w114
#check boundedHomotopyObjectTrianglehIso13Realization_of_restricted_endpoint_cochain_isos
#check boundedTrianglehIso13RestrictedEndpointCochainIsoPayload_iff_cochain_data_w114

end LeanLCAExactChallenge
