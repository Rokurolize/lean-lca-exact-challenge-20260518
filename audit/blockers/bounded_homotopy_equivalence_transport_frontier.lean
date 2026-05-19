import LeanLCAExactChallenge.Derived.Bounded

/-!
Bounded homotopy-equivalence transport frontier.

This probe follows the selected-cochain obstruction, but tests the weaker alternative
route: transport `boundedCochainComplex` directly along homotopy equivalences instead of
first producing strict cochain-complex isomorphisms. The local API exposes homotopy
equivalences from homotopy-category isomorphisms, while strict boundedness is an
objectwise cochain-complex property. The bridge below is therefore kept as an explicit
extra theorem shape rather than used as an available fact.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

#check HomotopyEquiv
#check HomotopyCategory.homotopyEquivOfIso
#check HomotopyCategory.isoOfHomotopyEquiv
#check boundedCochainComplex
#check boundedHomotopyObjectTrianglehIso13Realization
#check boundedHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization
#check exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_triangleh_iso13_realizations

omit [QuillenExactCategory C] in
/-- Weak endpoint data available after passing bounded endpoints through the homotopy
category: strict bounded representatives are merely homotopy equivalent to the selected
source and selected cone. -/
abbrev boundedHomotopyEndpointEquivPayload
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    ∃ (Ksrc Kcone K L : CochainComplex C ℤ) (f : K ⟶ L)
      (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
      (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃)
      (_ηK : HomotopyEquiv Ksrc K)
      (_ηCone : HomotopyEquiv Kcone (CochainComplex.mappingCone f)),
        (CochainComplex.mappingCone.triangleh f).mor₃ ≫
            (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
          e₃.hom ≫ T.mor₃ ∧
        boundedCochainComplex C Ksrc ∧
        boundedCochainComplex C Kcone

omit [QuillenExactCategory C] in
/-- The exact extra theorem needed by the direct homotopy-equivalence transport route.

This is intentionally stronger than anything currently exposed by the local APIs:
`boundedCochainComplex` is strict objectwise boundedness of a selected complex, while a
`HomotopyEquiv` permits contractible tails and only gives an isomorphism in the homotopy
category. -/
abbrev boundedCochainComplex_transportOfHomotopyEquiv : Prop :=
  ∀ {K L : CochainComplex C ℤ},
    boundedCochainComplex C K →
    HomotopyEquiv K L →
    boundedCochainComplex C L

omit [QuillenExactCategory C] in
/-- Endpoint homotopy-equivalence data would be enough for the existing bounded
strict-realization consumer if strict boundedness transported along those homotopy
equivalences. -/
theorem boundedRealization_of_endpointHomotopyEquivPayload_and_transport
    [HasZeroObject C] [HasBinaryBiproducts C]
    (weak : boundedHomotopyEndpointEquivPayload C)
    (transport : boundedCochainComplex_transportOfHomotopyEquiv C) :
    boundedHomotopyObjectTrianglehIso13Realization C := by
  intro T hT h₁ h₃
  rcases weak hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, ηK, ηCone, comm, hKsrc, hKcone⟩
  exact ⟨K, L, f, e₁, e₃, comm,
    transport hKsrc ηK,
    transport hKcone ηCone⟩

/-- The direct transport route connects to the same paired `Closed₂` consumer as the
selected cochain-isomorphism route, but only after the explicit homotopy-equivalence
boundedness transport theorem is supplied. -/
theorem closed2_pair_of_endpointHomotopyEquivPayload_and_transport
    [HasZeroObject C] [HasBinaryBiproducts C]
    (exactRealize : exactAcyclicHomotopyIsoClosureTrianglehIso13Realization C)
    (weak : boundedHomotopyEndpointEquivPayload C)
    (transport : boundedCochainComplex_transportOfHomotopyEquiv C) :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ ∧
      (boundedHomotopyObject C).IsTriangulatedClosed₂ :=
  exactAcyclicIsoClosure_and_boundedHomotopyObject_closed2_of_triangleh_iso13_realizations
    C exactRealize
    (boundedRealization_of_endpointHomotopyEquivPayload_and_transport C weak transport)

#check boundedHomotopyEndpointEquivPayload
#check boundedCochainComplex_transportOfHomotopyEquiv
#check boundedRealization_of_endpointHomotopyEquivPayload_and_transport
#check closed2_pair_of_endpointHomotopyEquivPayload_and_transport

end LeanLCAExactChallenge
