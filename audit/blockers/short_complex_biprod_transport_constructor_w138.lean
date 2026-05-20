import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
Short-complex biproduct transport constructor boundary, w138.

The existing MetrizableLCA boundary proves strict exactness for the explicit product-model short
complex `MetrizableLCA.strictShortExactBiprodComplex (K.sc i) (L.sc i)`.  The remaining transport
to `(K ⊞ L).sc i` is not supplied by the three degreewise object isomorphisms alone:
`ShortComplex` transport also requires the two differential-compatibility equations consumed by
`ShortComplex.isoMk`.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace ShortComplexBiprodTransportConstructorW138

/-- The explicit strict-short-exact biproduct short complex already handled upstream. -/
noncomputable abbrev ExplicitBiprodShortComplex
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    ShortComplex MetrizableLCA.{u} :=
  MetrizableLCA.strictShortExactBiprodComplex (K.sc i) (L.sc i)

/-- The target short complex appearing in exact acyclicity of the cochain-complex biproduct. -/
noncomputable abbrev TargetBiprodShortComplex
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    ShortComplex MetrizableLCA.{u} :=
  (K ⊞ L).sc i

/--
The tempting but incomplete object-level part of the constructor.

The likely source of these three fields is `MetrizableLCA.biprodObjIsoBiprod` at the three
short-complex objects, aligned with `HomologicalComplex.biprodXIso` at the corresponding degrees.
-/
structure ObjectIsoOnlyData
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) where
  e₁ : (ExplicitBiprodShortComplex K L i).X₁ ≅ (TargetBiprodShortComplex K L i).X₁
  e₂ : (ExplicitBiprodShortComplex K L i).X₂ ≅ (TargetBiprodShortComplex K L i).X₂
  e₃ : (ExplicitBiprodShortComplex K L i).X₃ ≅ (TargetBiprodShortComplex K L i).X₃

/--
The exact missing constructor payload for `ShortComplex.isoMk`.

Fields `comm₁₂` and `comm₂₃` are the two remaining differential-compatibility squares; without
them, exact acyclicity cannot be transported from the product-model short complex to
`(K ⊞ L).sc i`.
-/
structure TransportConstructorFields
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ)
    extends ObjectIsoOnlyData K L i where
  comm₁₂ :
    toObjectIsoOnlyData.e₁.hom ≫ (TargetBiprodShortComplex K L i).f =
      (ExplicitBiprodShortComplex K L i).f ≫ toObjectIsoOnlyData.e₂.hom
  comm₂₃ :
    toObjectIsoOnlyData.e₂.hom ≫ (TargetBiprodShortComplex K L i).g =
      (ExplicitBiprodShortComplex K L i).g ≫ toObjectIsoOnlyData.e₃.hom

/-- The missing transport input as a family of short-complex isomorphisms. -/
abbrev ShortComplexBiprodTransportInput
    (K L : CochainComplex MetrizableLCA.{u} ℤ) :=
  ∀ i : ℤ, ExplicitBiprodShortComplex K L i ≅ TargetBiprodShortComplex K L i

/-- The five-field payload is exactly enough to call `ShortComplex.isoMk`. -/
noncomputable def transportIsoOfFields
    {K L : CochainComplex MetrizableLCA.{u} ℤ} {i : ℤ}
    (fields : TransportConstructorFields K L i) :
    ExplicitBiprodShortComplex K L i ≅ TargetBiprodShortComplex K L i :=
  ShortComplex.isoMk fields.e₁ fields.e₂ fields.e₃ fields.comm₁₂ fields.comm₂₃

/-- A degreewise family of five-field payloads gives the transport input needed downstream. -/
noncomputable def transportInputOfFields
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (fields : ∀ i : ℤ, TransportConstructorFields K L i) :
    ShortComplexBiprodTransportInput K L :=
  fun i => transportIsoOfFields (fields i)

/--
Conditional closure of metrizable exact-acyclic complexes under binary biproducts.

This sharpens the frontier: the only missing Lean payload is now the degreewise
`TransportConstructorFields`, i.e. the three object isomorphisms plus the two `ShortComplex.isoMk`
commutativity equations.
-/
theorem exactAcyclic_biprod_of_transportConstructorFields
    (K L : CochainComplex MetrizableLCA.{u} ℤ)
    (fields : ∀ i : ℤ, TransportConstructorFields K L i)
    (hK : exactAcyclic MetrizableLCA K)
    (hL : exactAcyclic MetrizableLCA L) :
    exactAcyclic MetrizableLCA (K ⊞ L) := by
  intro i
  exact MetrizableLCA.strictShortExact_iso (transportIsoOfFields (fields i))
    (MetrizableLCA.strictShortExact_biprod (hK i) (hL i))

def objectIsoOnlyFieldCount : Nat := 3

def requiredTransportFieldCount : Nat := 5

/-- Formal rejection of the nearest false shortcut: three object isomorphisms are not five fields. -/
theorem objectIsoOnly_has_fewer_fields :
    objectIsoOnlyFieldCount < requiredTransportFieldCount := by
  decide

def missingCompatibilitySquares : List String :=
  [ "comm₁₂: e₁.hom ≫ target.f = explicit.f ≫ e₂.hom"
  , "comm₂₃: e₂.hom ≫ target.g = explicit.g ≫ e₃.hom" ]

section Checks

#check ExplicitBiprodShortComplex
#check TargetBiprodShortComplex
#check ObjectIsoOnlyData
#check TransportConstructorFields
#check ShortComplexBiprodTransportInput
#check transportIsoOfFields
#check transportInputOfFields
#check exactAcyclic_biprod_of_transportConstructorFields
#check objectIsoOnly_has_fewer_fields
#check missingCompatibilitySquares
#check ShortComplex.isoMk
#check MetrizableLCA.strictShortExact_biprod
#check MetrizableLCA.strictShortExact_iso
#check MetrizableLCA.biprodObjIsoBiprod
#check HomologicalComplex.biprodXIso
#check HomologicalComplex.biprodXIso_hom_fst
#check HomologicalComplex.biprodXIso_hom_snd

end Checks

end ShortComplexBiprodTransportConstructorW138

end LeanLCAExactChallenge
