import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W451: concrete W426/W387/W390 leg-theorem adapter for W447/W444.

The copied W387/W390/W447 audit files are standalone files under `audit/`, not
Lake-importable modules.  This file therefore rebuilds the narrow checked shape
needed by W447: the concrete transported descended map is the point-isomorphism
conjugate of an ordinary descended map, and the remaining W447 input is exactly
the categorical per-object leg equation for that concrete map.

No product-completion claim is made.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace WppOpW426W387W390ConcreteLegTheoremV370SupportW451

/-- W447/W318 per-object compatibility for a map between WPP-op colimit points. -/
abbrev W318ConjugatedLegCompatibilityW451
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/-- W447's named W390-style theorem shape, rebuilt because W447 is not importable. -/
structure W390NamedConjugatedLegTheoremW451
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} (φ : cx.pt ⟶ cy.pt) : Type 1 where
  theoremName : String
  legCompatibility : W318ConjugatedLegCompatibilityW451 X Y α cx cy φ

/--
The concrete W390 transported descended map: conjugate an ordinary descended
map across W387's source and target point identifications.
-/
def transportedDescendedByPointIsoConjugacyW451
    {ordinarySource ordinaryTarget colimitSource colimitTarget : MetrizableLCA.{0}}
    (sourcePointIdentification : ordinarySource ≅ colimitSource)
    (targetPointIdentification : ordinaryTarget ≅ colimitTarget)
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) :
    colimitSource ⟶ colimitTarget :=
  sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom

/-- The concrete W390 map satisfies the copied W390 pointwise conjugacy by reduction. -/
theorem transportedDescendedByPointIsoConjugacyW451_pointwise
    {ordinarySource ordinaryTarget colimitSource colimitTarget : MetrizableLCA.{0}}
    (sourcePointIdentification : ordinarySource ≅ colimitSource)
    (targetPointIdentification : ordinaryTarget ≅ colimitTarget)
    (ordinaryDescended : ordinarySource ⟶ ordinaryTarget) :
    ∀ x : colimitSource,
      transportedDescendedByPointIsoConjugacyW451
          sourcePointIdentification targetPointIdentification ordinaryDescended x =
        targetPointIdentification.hom
          (ordinaryDescended (sourcePointIdentification.inv x)) := by
  intro x
  rfl

/--
Concrete W426/W387/W390 input package for W447.

The first fields are the actual ordinary map and point identifications.  The
`concreteLegCompatibility` field is the exact remaining theorem: W390's
pointwise conjugacy gives the transported map, but W447/W444 also needs the
categorical W318 leg equation for the W426 natural transformation.
-/
structure W426W387W390ConcreteLegInputsW451
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
  w390PointwiseConjugacyName : String
  w447TargetTheoremName : String
  concreteLegCompatibility :
    W318ConjugatedLegCompatibilityW451 X Y α cx cy
      (transportedDescendedByPointIsoConjugacyW451
        sourcePointIdentification targetPointIdentification ordinaryDescended)

/-- The concrete W390-conjugated W426 ordinary descended map on colimit points. -/
def W426W387W390ConcreteLegInputsW451.concreteConjugatedDescended
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteLegInputsW451 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  transportedDescendedByPointIsoConjugacyW451
    inputs.sourcePointIdentification inputs.targetPointIdentification inputs.ordinaryDescended

/-- W390's pointwise conjugacy specialized to the concrete input package. -/
theorem concreteConjugatedDescended_pointwise_w451
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteLegInputsW451 X Y α cx cy) :
    ∀ x : cx.pt,
      inputs.concreteConjugatedDescended x =
        inputs.targetPointIdentification.hom
          (inputs.ordinaryDescended (inputs.sourcePointIdentification.inv x)) :=
  transportedDescendedByPointIsoConjugacyW451_pointwise
    inputs.sourcePointIdentification inputs.targetPointIdentification inputs.ordinaryDescended

/-- Adapter from the concrete W451 input package to W447's named-theorem shape. -/
def namedConjugatedLegTheorem_of_concreteInputs_w451
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteLegInputsW451 X Y α cx cy) :
    @W390NamedConjugatedLegTheoremW451 X Y α cx cy
      inputs.concreteConjugatedDescended where
  theoremName := inputs.w447TargetTheoremName
  legCompatibility := inputs.concreteLegCompatibility

/-- Projection of the concrete package into W318/W447 leg compatibility. -/
theorem w318_conjugatedLegCompatibility_of_concreteInputs_w451
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W426W387W390ConcreteLegInputsW451 X Y α cx cy) :
    W318ConjugatedLegCompatibilityW451 X Y α cx cy
      inputs.concreteConjugatedDescended :=
  inputs.concreteLegCompatibility

/-- The W444 ordinary/canonical colimit-map equality follows from the concrete leg theorem. -/
theorem ordinaryEqualsCanonicalColimitMap_of_concreteLegTheorem_w451
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (hcx : IsColimit cx)
    (inputs : W426W387W390ConcreteLegInputsW451 X Y α cx cy) :
    IsColimit.map hcx cy α = inputs.concreteConjugatedDescended :=
  hcx.hom_ext fun j =>
    (IsColimit.ι_map hcx cy α j).trans
      ((w318_conjugatedLegCompatibility_of_concreteInputs_w451 inputs j).symm)

/-- Exact copied declarations checked or mirrored by W451. -/
def w451CheckedDeclarationNames : List String :=
  ["W318ConjugatedLegCompatibilityW451",
    "W390NamedConjugatedLegTheoremW451",
    "transportedDescendedByPointIsoConjugacyW451",
    "transportedDescendedByPointIsoConjugacyW451_pointwise",
    "W426W387W390ConcreteLegInputsW451",
    "W426W387W390ConcreteLegInputsW451.concreteConjugatedDescended",
    "concreteConjugatedDescended_pointwise_w451",
    "namedConjugatedLegTheorem_of_concreteInputs_w451",
    "w318_conjugatedLegCompatibility_of_concreteInputs_w451",
    "ordinaryEqualsCanonicalColimitMap_of_concreteLegTheorem_w451"]

theorem w451CheckedDeclarationNames_count :
    w451CheckedDeclarationNames.length = 10 := rfl

/-- Source declarations W451 was asked to connect; these remain exact names for porting. -/
def w451CopiedInputDeclarationNames : List String :=
  ["WppOpW426W387W390ConjugatedLegInputsV370SupportW447.W318ConjugatedLegCompatibilityW447",
    "WppOpW426W387W390ConjugatedLegInputsV370SupportW447.W390NamedConjugatedLegTheoremW447",
    "WppOpW426W387W390ConjugatedLegInputsV370SupportW447.W426OrdinaryEqualsCanonicalInputsW444ShapeW447",
    "WppOpW426W387W390ConjugatedLegInputsV370SupportW447.ordinaryEqualsCanonicalColimitMap_of_w426_w387_w390_namedLegTheorem_w447",
    "WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387.transportedQuotientSourcePointIsoW387",
    "WppOpLeftLcaTransportedQuotientPointIsoV370SupportW387.transportedQuotientTargetPointIsoW387",
    "WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390.transportedDescendedByPointIsoConjugacyW390",
    "WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390.transportedDescendedByPointIsoConjugacyW390_pointwise",
    "WppOpLeftLcaTransportedDescendedConjugacyV370SupportW390.transportedDescendedByPointIsoConjugacyW390_to_pointIsoConjugacyPackageW384"]

theorem w451CopiedInputDeclarationNames_count :
    w451CopiedInputDeclarationNames.length = 9 := rfl

/-- Remaining fields after W451's concrete adapter. -/
def remainingConcreteLegInputsW451 : List String :=
  ["make the W387, W390, W447, and W444 audit support files Lake-importable, or move these declarations under LeanLCAExactChallenge",
    "instantiate W426W387W390ConcreteLegInputsW451 with W426's ordinaryDescendedOfOrdinaryMapW418 and quotient-compatibility theorem",
    "prove concreteLegCompatibility: cx.ι.app j ≫ transportedDescendedByPointIsoConjugacyW390 = α.app j ≫ cy.ι.app j for every WalkingParallelPairᵒᵖ object"]

theorem remainingConcreteLegInputsW451_count :
    remainingConcreteLegInputsW451.length = 3 := rfl

/-- Machine-readable state for the W451 support file. -/
structure WppOpW426W387W390ConcreteLegTheoremV370StateW451 : Type where
  seed : String
  declarations : List String
  copiedInputDeclarations : List String
  remainingInputs : List String
  concreteLegResult : String
  ordinaryEqualsCanonicalResult : String
  productSuccessClaimed : Bool

def currentWppOpW426W387W390ConcreteLegTheoremV370StateW451 :
    WppOpW426W387W390ConcreteLegTheoremV370StateW451 where
  seed := "4c69bf57d04de1f548c28f7286cdb864"
  declarations := w451CheckedDeclarationNames
  copiedInputDeclarations := w451CopiedInputDeclarationNames
  remainingInputs := remainingConcreteLegInputsW451
  concreteLegResult :=
    "partial: checked the concrete W390 point-isomorphism-conjugated map and a W447/W444 adapter; the exact remaining theorem is the categorical W318 leg compatibility for the W426 map"
  ordinaryEqualsCanonicalResult :=
    "partial: checked that the W444 equality follows once the concrete W318 leg compatibility field is supplied"
  productSuccessClaimed := false

theorem currentWppOpW426W387W390ConcreteLegTheoremV370StateW451_productSuccess :
    currentWppOpW426W387W390ConcreteLegTheoremV370StateW451.productSuccessClaimed = false := rfl

section Checks

#check W318ConjugatedLegCompatibilityW451
#check W390NamedConjugatedLegTheoremW451
#check transportedDescendedByPointIsoConjugacyW451
#check transportedDescendedByPointIsoConjugacyW451_pointwise
#check W426W387W390ConcreteLegInputsW451
#check W426W387W390ConcreteLegInputsW451.concreteConjugatedDescended
#check concreteConjugatedDescended_pointwise_w451
#check namedConjugatedLegTheorem_of_concreteInputs_w451
#check w318_conjugatedLegCompatibility_of_concreteInputs_w451
#check ordinaryEqualsCanonicalColimitMap_of_concreteLegTheorem_w451
#check w451CheckedDeclarationNames
#check w451CopiedInputDeclarationNames
#check remainingConcreteLegInputsW451
#check currentWppOpW426W387W390ConcreteLegTheoremV370StateW451
#check currentWppOpW426W387W390ConcreteLegTheoremV370StateW451_productSuccess

end Checks

end WppOpW426W387W390ConcreteLegTheoremV370SupportW451

end LeanLCAExactChallenge
