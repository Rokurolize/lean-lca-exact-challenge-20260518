import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W444: ordinary/canonical colimit-map equality frontier after W441.

W441 left `ordinaryEqualsCanonicalColimitMap` as a named proposition.  This
support file tightens that boundary to a checked categorical reduction: after
the W387/W390 point identifications, the conjugated W426 ordinary descended map
is the canonical `IsColimit.map` as soon as its legs satisfy the usual W318
compatibility equations.  The remaining missing input is therefore not another
abstract equality, but the per-object leg calculation for the conjugated W426
map.

No product-completion claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpW426W318OrdinaryEqualsCanonicalV370SupportW444

/-- W318's per-object compatibility equation for a map between colimit points. -/
abbrev W318ColimitMapLegCompatibilityW444
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/-- The canonical `IsColimit.map` is the unique map with W318's leg equation. -/
theorem isColimit_map_eq_of_compat_w444
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y} (φ : cx.pt ⟶ cy.pt)
    (hcx : IsColimit cx)
    (hcompat : W318ColimitMapLegCompatibilityW444 X Y α cx cy φ) :
    IsColimit.map hcx cy α = φ :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans (hcompat j).symm

/--
W426 ordinary descended map data after W387/W390 point identifications.

The `conjugatedLegCompatibility` field is the exact remaining calculation:
show that the ordinary descended map, conjugated across the source and target
point identifications, has the same legs as the canonical W318 colimit map.
-/
structure W426OrdinaryEqualsCanonicalInputsW444
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  ordinarySource : MetrizableLCA.{0}
  ordinaryTarget : MetrizableLCA.{0}
  ordinaryDescended : ordinarySource ⟶ ordinaryTarget
  sourcePointIdentification : ordinarySource ≅ cx.pt
  targetPointIdentification : ordinaryTarget ≅ cy.pt
  ordinaryDescendedMapName : String
  sourcePointIdentificationName : String
  targetPointIdentificationName : String
  canonicalWppOpColimitMapName : String
  conjugatedLegCompatibility :
    W318ColimitMapLegCompatibilityW444 X Y α cx cy
      (sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom)

/-- The W426 ordinary map transported to the W318 colimit points. -/
def W426OrdinaryEqualsCanonicalInputsW444.conjugatedOrdinaryDescended
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426OrdinaryEqualsCanonicalInputsW444 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  inputs.sourcePointIdentification.inv ≫
    inputs.ordinaryDescended ≫ inputs.targetPointIdentification.hom

/--
The checked ordinary/canonical equality reduction.

Once W426 supplies the `conjugatedLegCompatibility` field, its transported
ordinary descended map is definitionally the same target as W318's canonical
colimit-point map and propositionally equal to `IsColimit.map`.
-/
theorem ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_legs_w444
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx)
    (inputs : W426OrdinaryEqualsCanonicalInputsW444 X Y α cx cy) :
    IsColimit.map hcx cy α = inputs.conjugatedOrdinaryDescended :=
  isColimit_map_eq_of_compat_w444 α inputs.conjugatedOrdinaryDescended hcx
    inputs.conjugatedLegCompatibility

/-- W441's `heq` input immediately yields W318's per-object leg compatibility. -/
theorem w318_legCompatibility_of_ordinaryEqualsCanonicalColimitMap_w444
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcx : IsColimit cx)
    (heq : IsColimit.map hcx cy α = φ) :
    W318ColimitMapLegCompatibilityW444 X Y α cx cy φ := by
  intro j
  simpa [heq] using IsColimit.ι_map hcx cy α j

/-- Applying the W444 reduction gives the concrete W318 leg equation directly. -/
theorem w318_legCompatibility_of_w426_w387_w390_legs_w444
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx)
    (inputs : W426OrdinaryEqualsCanonicalInputsW444 X Y α cx cy) :
    W318ColimitMapLegCompatibilityW444 X Y α cx cy
      inputs.conjugatedOrdinaryDescended :=
  w318_legCompatibility_of_ordinaryEqualsCanonicalColimitMap_w444 hcx
    (ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_legs_w444 hcx inputs)

/-- Names of the checked W444 declarations. -/
def w444CheckedDeclarationNames : List String :=
  ["W318ColimitMapLegCompatibilityW444",
    "isColimit_map_eq_of_compat_w444",
    "W426OrdinaryEqualsCanonicalInputsW444",
    "W426OrdinaryEqualsCanonicalInputsW444.conjugatedOrdinaryDescended",
    "ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_legs_w444",
    "w318_legCompatibility_of_ordinaryEqualsCanonicalColimitMap_w444",
    "w318_legCompatibility_of_w426_w387_w390_legs_w444"]

theorem w444CheckedDeclarationNames_count :
    w444CheckedDeclarationNames.length = 7 := rfl

/-- Concrete declarations whose promoted versions should fill the W444 input package. -/
def w444NamedSourceDeclarations : List String :=
  ["WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMapW418",
    "WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMap_quotient_compatW418",
    "WppOpW399InputsFromReverseMembershipAndCertificatesV370SupportW423.ordinaryDescendedOfOrdinaryMapW417_eq_W418",
    "WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387.transportedQuotientSourcePointIsoW387",
    "WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387.transportedQuotientTargetPointIsoW387",
    "WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390.transportedDescendedByPointIsoConjugacyW390",
    "IsColimit.map"]

theorem w444NamedSourceDeclarations_count :
    w444NamedSourceDeclarations.length = 7 := rfl

/-- The remaining input after W444's categorical uniqueness reduction. -/
def remainingOrdinaryEqualsCanonicalInputsW444 : List String :=
  ["promote W426's ordinaryDescendedOfOrdinaryMapW418 and quotient-compat theorem into an importable module",
    "promote W387's source and target point isomorphisms into the same namespace as the ordinary descended map",
    "instantiate W390's conjugated ordinary descended map using those point identifications",
    "prove the per-object leg equations for the conjugated W426 map: cx.ι.app j ≫ conjugatedOrdinaryDescended = α.app j ≫ cy.ι.app j",
    "then apply ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_legs_w444 to obtain W441's equality input"]

theorem remainingOrdinaryEqualsCanonicalInputsW444_count :
    remainingOrdinaryEqualsCanonicalInputsW444.length = 5 := rfl

/-- Machine-readable state for the W444 support file. -/
structure WppOpW426W318OrdinaryEqualsCanonicalV370StateW444 : Type where
  seed : String
  declarations : List String
  namedSourceDeclarations : List String
  remainingInputs : List String
  ordinaryEqualsCanonicalResult : String
  exactEqualityProved : Bool
  productSuccessClaimed : Bool

def currentWppOpW426W318OrdinaryEqualsCanonicalV370StateW444 :
    WppOpW426W318OrdinaryEqualsCanonicalV370StateW444 where
  seed := "1277d619d86b1fb32572f0a543a3c1e0"
  declarations := w444CheckedDeclarationNames
  namedSourceDeclarations := w444NamedSourceDeclarations
  remainingInputs := remainingOrdinaryEqualsCanonicalInputsW444
  ordinaryEqualsCanonicalResult :=
    "partial: checked reduction proves W426's W387/W390-conjugated ordinary descended map equals the canonical IsColimit.map from its per-object leg equations; the remaining input is the promoted leg calculation for the concrete W426 map"
  exactEqualityProved := false
  productSuccessClaimed := false

theorem currentWppOpW426W318OrdinaryEqualsCanonicalV370StateW444_productSuccess :
    currentWppOpW426W318OrdinaryEqualsCanonicalV370StateW444.productSuccessClaimed = false := rfl

section Checks

#check W318ColimitMapLegCompatibilityW444
#check isColimit_map_eq_of_compat_w444
#check W426OrdinaryEqualsCanonicalInputsW444
#check W426OrdinaryEqualsCanonicalInputsW444.conjugatedOrdinaryDescended
#check ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_legs_w444
#check w318_legCompatibility_of_ordinaryEqualsCanonicalColimitMap_w444
#check w318_legCompatibility_of_w426_w387_w390_legs_w444
#check w444CheckedDeclarationNames
#check w444NamedSourceDeclarations
#check remainingOrdinaryEqualsCanonicalInputsW444
#check currentWppOpW426W318OrdinaryEqualsCanonicalV370StateW444
#check currentWppOpW426W318OrdinaryEqualsCanonicalV370StateW444_productSuccess

end Checks

end WppOpW426W318OrdinaryEqualsCanonicalV370SupportW444

end LeanLCAExactChallenge
