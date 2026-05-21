import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W447: W426/W387/W390 conjugated leg inputs for W444.

This standalone support file packages the W426 ordinary descended map, the W387
source/target point identifications, and the W390 conjugated-map theorem into
the colimit-map input shape consumed by W444.  The remaining mathematical input
is narrowed to one named W390-style theorem proving the per-object legs of the
conjugated ordinary descended map.

No product-completion claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpW426W387W390ConjugatedLegInputsV370SupportW447

/-- W318/W444 per-object leg compatibility for a map between colimit points. -/
abbrev W318ConjugatedLegCompatibilityW447
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/-- The W390 theorem, named and typed as the one remaining W444 leg input. -/
structure W390NamedConjugatedLegTheoremW447
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} (φ : cx.pt ⟶ cy.pt) : Type 1 where
  theoremName : String
  legCompatibility : W318ConjugatedLegCompatibilityW447 X Y α cx cy φ

/--
Exact W444-shaped input package after W426, W387, and W390 are aligned.

The morphism is W426's ordinary descended map transported across the W387 point
identifications.  The `conjugatedLegTheorem` field is the smallest remaining
mathematical input for W444.
-/
structure W426OrdinaryEqualsCanonicalInputsW444ShapeW447
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  ordinarySource : MetrizableLCA.{0}
  ordinaryTarget : MetrizableLCA.{0}
  ordinaryDescended : ordinarySource ⟶ ordinaryTarget
  sourcePointIdentification : ordinarySource ≅ cx.pt
  targetPointIdentification : ordinaryTarget ≅ cy.pt
  w426OrdinaryDescendedName : String
  w426QuotientCompatibilityName : String
  w387SourcePointIdentificationName : String
  w387TargetPointIdentificationName : String
  w390ConjugatedMapName : String
  canonicalWppOpColimitMapName : String
  conjugatedLegTheorem :
    @W390NamedConjugatedLegTheoremW447 X Y α cx cy
      (sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom)

/-- The W426 ordinary descended map transported to W444's colimit points. -/
def W426OrdinaryEqualsCanonicalInputsW444ShapeW447.conjugatedOrdinaryDescended
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426OrdinaryEqualsCanonicalInputsW444ShapeW447 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  inputs.sourcePointIdentification.inv ≫
    inputs.ordinaryDescended ≫ inputs.targetPointIdentification.hom

/-- Projection of the named W390 theorem into W444's exact leg field. -/
theorem conjugatedLegCompatibility_of_namedW390Theorem_w447
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426OrdinaryEqualsCanonicalInputsW444ShapeW447 X Y α cx cy) :
    W318ConjugatedLegCompatibilityW447 X Y α cx cy
      inputs.conjugatedOrdinaryDescended :=
  inputs.conjugatedLegTheorem.legCompatibility

/-- The canonical `IsColimit.map` is determined by the W318/W444 leg equation. -/
theorem isColimit_map_eq_of_conjugatedLegCompatibility_w447
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} (α : X ⟶ Y)
    {cx : Cocone X} {cy : Cocone Y} (φ : cx.pt ⟶ cy.pt)
    (hcx : IsColimit cx)
    (hcompat : W318ConjugatedLegCompatibilityW447 X Y α cx cy φ) :
    IsColimit.map hcx cy α = φ :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans (hcompat j).symm

/--
W447's checked reduction for W444: after the named W390 leg theorem is supplied,
the W426/W387/W390-conjugated ordinary descended map is W444's canonical map.
-/
theorem ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_namedLegTheorem_w447
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx)
    (inputs : W426OrdinaryEqualsCanonicalInputsW444ShapeW447 X Y α cx cy) :
    IsColimit.map hcx cy α = inputs.conjugatedOrdinaryDescended :=
  isColimit_map_eq_of_conjugatedLegCompatibility_w447 α
    inputs.conjugatedOrdinaryDescended hcx
    (conjugatedLegCompatibility_of_namedW390Theorem_w447 inputs)

/-- The same package directly exposes the W318/W444 leg equation. -/
theorem w318_conjugatedLegCompatibility_of_w426_w387_w390_namedLegTheorem_w447
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426OrdinaryEqualsCanonicalInputsW444ShapeW447 X Y α cx cy) :
    W318ConjugatedLegCompatibilityW447 X Y α cx cy
      inputs.conjugatedOrdinaryDescended :=
  conjugatedLegCompatibility_of_namedW390Theorem_w447 inputs

/-- Checked declarations exported by W447. -/
def w447CheckedDeclarationNames : List String :=
  ["W318ConjugatedLegCompatibilityW447",
    "W390NamedConjugatedLegTheoremW447",
    "W426OrdinaryEqualsCanonicalInputsW444ShapeW447",
    "W426OrdinaryEqualsCanonicalInputsW444ShapeW447.conjugatedOrdinaryDescended",
    "conjugatedLegCompatibility_of_namedW390Theorem_w447",
    "isColimit_map_eq_of_conjugatedLegCompatibility_w447",
    "ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_namedLegTheorem_w447",
    "w318_conjugatedLegCompatibility_of_w426_w387_w390_namedLegTheorem_w447"]

theorem w447CheckedDeclarationNames_count :
    w447CheckedDeclarationNames.length = 8 := rfl

/-- Concrete upstream declaration names this package expects from W426/W387/W390. -/
def w447NamedSourceDeclarations : List String :=
  ["WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMapW418",
    "WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMap_quotient_compatW418",
    "WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387.transportedQuotientSourcePointIsoW387",
    "WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387.transportedQuotientTargetPointIsoW387",
    "WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390.transportedDescendedByPointIsoConjugacyW390",
    "WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390.transportedDescendedByPointIsoConjugacyW390_pointwise"]

theorem w447NamedSourceDeclarations_count :
    w447NamedSourceDeclarations.length = 6 := rfl

/-- Remaining port inputs after W447's packaging reduction. -/
def remainingConjugatedLegInputsW447 : List String :=
  ["promote the W426 ordinary descended map and quotient-compatibility theorem into an importable module",
    "promote W387's source and target point isomorphisms into the same importable namespace",
    "promote W390's conjugated descended map and pointwise theorem against those point isomorphisms",
    "prove the concrete per-object W318/W444 leg theorem for the W390-conjugated W426 map"]

theorem remainingConjugatedLegInputsW447_count :
    remainingConjugatedLegInputsW447.length = 4 := rfl

/-- Machine-readable state for the W447 support file. -/
structure WppOpW426W387W390ConjugatedLegInputsV370StateW447 : Type where
  seed : String
  declarations : List String
  namedSourceDeclarations : List String
  remainingInputs : List String
  conjugatedLegInputsResult : String
  exactEqualityProved : Bool
  productSuccessClaimed : Bool

def currentWppOpW426W387W390ConjugatedLegInputsV370StateW447 :
    WppOpW426W387W390ConjugatedLegInputsV370StateW447 where
  seed := "Jjlm6E3vEqbT3TlxnQVg0xcu"
  declarations := w447CheckedDeclarationNames
  namedSourceDeclarations := w447NamedSourceDeclarations
  remainingInputs := remainingConjugatedLegInputsW447
  conjugatedLegInputsResult :=
    "partial: checked W444-shaped package reduces the W426/W387/W390 ordinary/canonical equality to one named W390-style per-object leg theorem for the concrete conjugated descended map"
  exactEqualityProved := false
  productSuccessClaimed := false

theorem currentWppOpW426W387W390ConjugatedLegInputsV370StateW447_productSuccess :
    currentWppOpW426W387W390ConjugatedLegInputsV370StateW447.productSuccessClaimed = false := rfl

section Checks

#check W318ConjugatedLegCompatibilityW447
#check W390NamedConjugatedLegTheoremW447
#check W426OrdinaryEqualsCanonicalInputsW444ShapeW447
#check W426OrdinaryEqualsCanonicalInputsW444ShapeW447.conjugatedOrdinaryDescended
#check conjugatedLegCompatibility_of_namedW390Theorem_w447
#check isColimit_map_eq_of_conjugatedLegCompatibility_w447
#check ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_namedLegTheorem_w447
#check w318_conjugatedLegCompatibility_of_w426_w387_w390_namedLegTheorem_w447
#check w447CheckedDeclarationNames
#check w447NamedSourceDeclarations
#check remainingConjugatedLegInputsW447
#check currentWppOpW426W387W390ConjugatedLegInputsV370StateW447
#check currentWppOpW426W387W390ConjugatedLegInputsV370StateW447_productSuccess

end Checks

end WppOpW426W387W390ConjugatedLegInputsV370SupportW447

end LeanLCAExactChallenge
