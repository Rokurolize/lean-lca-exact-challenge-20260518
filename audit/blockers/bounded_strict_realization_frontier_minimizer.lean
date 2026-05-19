import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.ContractibleTail

/-!
Bounded strict-realization frontier minimizer.

The product API supplies `homotopyEndpointPayloadWithoutSelectedCochainIso`: for a
distinguished triangle with bounded first and third homotopy objects, mathlib gives a
mapping-cone presentation whose selected source and cone are only isomorphic to bounded
representatives in the homotopy category.

This audit isolates the remaining positive theorem as an upgrade from that weak endpoint
payload to the cochain-level strictification payload consumed by the bounded route. It also
records the negative boundary: arbitrary `HomotopyEquiv` transport of strict boundedness is
not an acceptable replacement theorem.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- Minimal remaining theorem shape for bounded strict realization.

This is intentionally stronger than the weak endpoint payload and weaker than product
success: it asks only for the cochain-level isomorphism data needed to reuse the existing
`boundedTrianglehIso13CochainDataStrictification` consumer. -/
abbrev boundedWeakEndpointPayloadToCochainDataStrictification
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  homotopyEndpointPayloadWithoutSelectedCochainIso C →
    boundedTrianglehIso13CochainDataStrictification C

omit [QuillenExactCategory C] in
/-- The frontier theorem converts the existing weak endpoint payload into the named
bounded strict-realization input. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_weakEndpoint_frontier
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedWeakEndpointPayloadToCochainDataStrictification C) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_cochain_data C
    (strictify (homotopyEndpointPayloadWithoutSelectedCochainIso_of_distinguished C))

omit [QuillenExactCategory C] in
/-- Bounded strict realization is enough to fill the weak-endpoint upgrade shape, because
the cochain-data payload is equivalent to bounded strict realization and the weak endpoint
argument can be ignored. This shows the minimizer is not weaker than the remaining bounded
positive theorem. -/
theorem boundedWeakEndpointPayloadToCochainDataStrictification_of_realization
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize : boundedHomotopyObjectTrianglehIso13Realization C) :
    boundedWeakEndpointPayloadToCochainDataStrictification C := fun _weak =>
  boundedTrianglehIso13CochainDataStrictification_of_realization C realize

omit [QuillenExactCategory C] in
/-- Since the weak endpoint payload is already available from distinguished triangles,
the minimizer is equivalent to the bounded strict-realization input itself. -/
theorem boundedWeakEndpointPayloadToCochainDataStrictification_iff_realization
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedWeakEndpointPayloadToCochainDataStrictification C ↔
      boundedHomotopyObjectTrianglehIso13Realization C := by
  constructor
  · exact boundedHomotopyObjectTrianglehIso13Realization_of_weakEndpoint_frontier C
  · exact boundedWeakEndpointPayloadToCochainDataStrictification_of_realization C

omit [QuillenExactCategory C] in
/-- Once the frontier theorem is supplied, bounded homotopy objects satisfy the middle-term
distinguished-triangle closure already implemented in `Derived.Bounded`. -/
theorem boundedHomotopyObject_isTriangulatedClosed2_of_weakEndpoint_frontier
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedWeakEndpointPayloadToCochainDataStrictification C) :
    (boundedHomotopyObject C).IsTriangulatedClosed₂ :=
  boundedHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization C
    (boundedHomotopyObjectTrianglehIso13Realization_of_weakEndpoint_frontier C strictify)

omit [QuillenExactCategory C] in
/-- The same frontier theorem gives the ordinary pretriangulated bounded homotopy category
through the existing product API. -/
noncomputable abbrev boundedHomotopyCategory_pretriangulated_of_weakEndpoint_frontier
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedWeakEndpointPayloadToCochainDataStrictification C) :
    Pretriangulated (BoundedHomotopyCategory C) :=
  boundedHomotopyCategory_pretriangulated_of_triangleh_iso13_realization C
    (boundedHomotopyObjectTrianglehIso13Realization_of_weakEndpoint_frontier C strictify)

omit [QuillenExactCategory C] in
/-- The same frontier theorem gives the ordinary triangulated bounded homotopy category
through the existing product API. -/
noncomputable abbrev boundedHomotopyCategory_isTriangulated_of_weakEndpoint_frontier
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedWeakEndpointPayloadToCochainDataStrictification C) :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_weakEndpoint_frontier C strictify
    IsTriangulated (BoundedHomotopyCategory C) := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_weakEndpoint_frontier C strictify
  exact boundedHomotopyCategory_isTriangulated_of_triangleh_iso13_realization C
    (boundedHomotopyObjectTrianglehIso13Realization_of_weakEndpoint_frontier C strictify)

/-- If the exact-acyclic strict-realization input is also supplied, the bounded frontier
theorem plugs into the paired `Closed₂` consequence already available in product code. -/
theorem exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_exactRealize_and_weakEndpoint_frontier
    [HasZeroObject C] [HasBinaryBiproducts C]
    (exactRealize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C)
    (strictify : boundedWeakEndpointPayloadToCochainDataStrictification C) :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ ∧
      (boundedHomotopyObject C).IsTriangulatedClosed₂ :=
  exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_triangleh_iso13_realizations
    C exactRealize
    (boundedHomotopyObjectTrianglehIso13Realization_of_weakEndpoint_frontier C strictify)

omit [QuillenExactCategory C] in
/-- A bare homotopy equivalence cannot be used to transport strict boundedness. The concrete
right-unbounded contractible alternating tail refutes that route. -/
theorem reject_boundedCochainComplex_transport_along_arbitrary_homotopyEquiv :
    ¬ StrictBoundednessTransportOfHomotopyEquiv
        AlternatingTailExtendTransport.IntModuleCat :=
  AlternatingTailExtendTransport.not_strictBoundednessTransport_intAlternatingTailGE 0

section Checks

variable [HasZeroObject C] [HasBinaryBiproducts C]

#check homotopyEndpointPayloadWithoutSelectedCochainIso
#check homotopyEndpointPayloadWithoutSelectedCochainIso_of_distinguished
#check boundedTrianglehIso13CochainDataStrictification
#check boundedWeakEndpointPayloadToCochainDataStrictification
#check boundedHomotopyObjectTrianglehIso13Realization_of_weakEndpoint_frontier
#check boundedWeakEndpointPayloadToCochainDataStrictification_of_realization
#check boundedWeakEndpointPayloadToCochainDataStrictification_iff_realization
#check boundedHomotopyObject_isTriangulatedClosed2_of_weakEndpoint_frontier
#check boundedHomotopyCategory_pretriangulated_of_weakEndpoint_frontier
#check boundedHomotopyCategory_isTriangulated_of_weakEndpoint_frontier
#check exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_exactRealize_and_weakEndpoint_frontier
#check reject_boundedCochainComplex_transport_along_arbitrary_homotopyEquiv

end Checks

end LeanLCAExactChallenge
