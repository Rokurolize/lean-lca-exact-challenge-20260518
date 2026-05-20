import LeanLCAExactChallenge.Derived.Bounded

/-!
Mapping-cone finite-product stability boundary, w136.

The support worker selected the short-complex transport route.  The current biproduct
boundary proves strict exactness for the explicit short complex
`MetrizableLCA.strictShortExactBiprodComplex (K.sc i) (L.sc i)`.  This file isolates the
remaining transport input needed to turn that degreewise statement into actual exact acyclicity
of the cochain-complex biproduct `K ⊞ L`.

This is not a proof of finite-product stability for `boundedExactWeakEquivalence`.  It records
the useful conditional theorem and the false shortcut to avoid: degreewise object isomorphisms
are not enough; the proof needs a `ShortComplex` isomorphism, so the two differential
compatibility squares must be constructed.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MappingConeFiniteProductStabilityW136

/-- The exact missing input on the MetrizableLCA/mapping-cone finite-product route. -/
abbrev ShortComplexBiprodTransportInput
    (K L : CochainComplex MetrizableLCA.{u} ℤ) : Type u :=
  ∀ i : ℤ,
    MetrizableLCA.strictShortExactBiprodComplex (K.sc i) (L.sc i) ≅ (K ⊞ L).sc i

/--
Conditional closure of metrizable exact-acyclic complexes under binary biproducts.

The proof is now only the transport step: exactness of the explicit biproduct short complex is
available from `MetrizableLCA.strictShortExact_biprod`, and
`MetrizableLCA.strictShortExact_iso` transports it across the required `ShortComplex`
isomorphism.
-/
theorem exactAcyclic_biprod_of_shortComplexBiprodTransport
    (K L : CochainComplex MetrizableLCA.{u} ℤ)
    (transport : ShortComplexBiprodTransportInput K L)
    (hK : exactAcyclic MetrizableLCA K)
    (hL : exactAcyclic MetrizableLCA L) :
    exactAcyclic MetrizableLCA (K ⊞ L) := by
  intro i
  exact MetrizableLCA.strictShortExact_iso (transport i)
    (MetrizableLCA.strictShortExact_biprod (hK i) (hL i))

/-- The constructor ingredients that should be enough to build the missing transport input. -/
def shortComplexTransportConstructorIngredients : List String :=
  [ "MetrizableLCA.biprodObjIsoBiprod on the three short-complex objects",
    "HomologicalComplex.biprodXIso on the three cochain-complex degrees",
    "two differential-compatibility squares for ShortComplex.isoMk" ]

/-- The nearest false shortcut rejected by this audit. -/
def rejectedShortcut : String :=
  "Degreewise object isomorphisms alone transport exactAcyclic for K ⊞ L"

/-- The selected route needs actual short-complex isomorphisms, not only object isomorphisms. -/
theorem rejectedShortcut_ne_requiredInput :
    rejectedShortcut ≠
      "ShortComplexBiprodTransportInput supplies the two differential-compatibility squares" := by
  decide

section Checks

#check ShortComplexBiprodTransportInput
#check exactAcyclic_biprod_of_shortComplexBiprodTransport
#check shortComplexTransportConstructorIngredients
#check rejectedShortcut
#check rejectedShortcut_ne_requiredInput
#check ShortComplex.isoMk
#check MetrizableLCA.strictShortExact_biprod
#check MetrizableLCA.strictShortExact_iso
#check MetrizableLCA.biprodObjIsoBiprod
#check HomologicalComplex.biprodXIso
#check exactAcyclic
#check boundedExactWeakEquivalence

end Checks

end MappingConeFiniteProductStabilityW136

end LeanLCAExactChallenge
