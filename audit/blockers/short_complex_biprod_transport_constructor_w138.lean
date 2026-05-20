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
The three object isomorphisms are available: compose the explicit MetrizableLCA biproduct model
with `HomologicalComplex.biprodXIso` in the three degrees of the short complex.
-/
noncomputable def objectIsoDataOfBiprodXIso
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    ObjectIsoOnlyData K L i where
  e₁ :=
    MetrizableLCA.biprodObjIsoBiprod _ _ ≪≫
      (HomologicalComplex.biprodXIso K L ((ComplexShape.up ℤ).prev i)).symm
  e₂ :=
    MetrizableLCA.biprodObjIsoBiprod _ _ ≪≫
      (HomologicalComplex.biprodXIso K L i).symm
  e₃ :=
    MetrizableLCA.biprodObjIsoBiprod _ _ ≪≫
      (HomologicalComplex.biprodXIso K L ((ComplexShape.up ℤ).next i)).symm

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

/--
After the object isomorphisms above, only the two `ShortComplex.isoMk` compatibility squares
remain.
-/
structure TransportCompatibilitySquares
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) where
  comm₁₂ :
    (objectIsoDataOfBiprodXIso K L i).e₁.hom ≫ (TargetBiprodShortComplex K L i).f =
      (ExplicitBiprodShortComplex K L i).f ≫ (objectIsoDataOfBiprodXIso K L i).e₂.hom
  comm₂₃ :
    (objectIsoDataOfBiprodXIso K L i).e₂.hom ≫ (TargetBiprodShortComplex K L i).g =
      (ExplicitBiprodShortComplex K L i).g ≫ (objectIsoDataOfBiprodXIso K L i).e₃.hom

/-- The two remaining compatibility squares supply the full `ShortComplex.isoMk` payload. -/
noncomputable def transportConstructorFieldsOfCompatibilitySquares
    {K L : CochainComplex MetrizableLCA.{u} ℤ} {i : ℤ}
    (squares : TransportCompatibilitySquares K L i) :
    TransportConstructorFields K L i where
  toObjectIsoOnlyData := objectIsoDataOfBiprodXIso K L i
  comm₁₂ := squares.comm₁₂
  comm₂₃ := squares.comm₂₃

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

/--
Conditional closure after discharging the three object isomorphisms.

The only remaining payload is the two compatibility equations for each degree.
-/
theorem exactAcyclic_biprod_of_transportCompatibilitySquares
    (K L : CochainComplex MetrizableLCA.{u} ℤ)
    (squares : ∀ i : ℤ, TransportCompatibilitySquares K L i)
    (hK : exactAcyclic MetrizableLCA K)
    (hL : exactAcyclic MetrizableLCA L) :
    exactAcyclic MetrizableLCA (K ⊞ L) := by
  exact exactAcyclic_biprod_of_transportConstructorFields K L
    (fun i => transportConstructorFieldsOfCompatibilitySquares (squares i)) hK hL

def objectIsoOnlyFieldCount : Nat := 3

def requiredTransportFieldCount : Nat := 5

def remainingCompatibilityFieldCount : Nat := 2

/-- Formal rejection of the nearest false shortcut: three object isomorphisms are not five fields. -/
theorem objectIsoOnly_has_fewer_fields :
    objectIsoOnlyFieldCount < requiredTransportFieldCount := by
  decide

theorem remainingCompatibilityFields_count :
    remainingCompatibilityFieldCount + objectIsoOnlyFieldCount = requiredTransportFieldCount := by
  decide

def missingCompatibilitySquares : List String :=
  [ "comm₁₂: e₁.hom ≫ target.f = explicit.f ≫ e₂.hom"
  , "comm₂₃: e₂.hom ≫ target.g = explicit.g ≫ e₃.hom" ]

section Checks

#check ExplicitBiprodShortComplex
#check TargetBiprodShortComplex
#check ObjectIsoOnlyData
#check objectIsoDataOfBiprodXIso
#check TransportConstructorFields
#check TransportCompatibilitySquares
#check transportConstructorFieldsOfCompatibilitySquares
#check ShortComplexBiprodTransportInput
#check transportIsoOfFields
#check transportInputOfFields
#check exactAcyclic_biprod_of_transportConstructorFields
#check exactAcyclic_biprod_of_transportCompatibilitySquares
#check objectIsoOnly_has_fewer_fields
#check remainingCompatibilityFields_count
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
