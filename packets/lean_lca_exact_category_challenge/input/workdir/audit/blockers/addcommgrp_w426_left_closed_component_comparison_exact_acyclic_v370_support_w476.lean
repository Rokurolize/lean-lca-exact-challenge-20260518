import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Topology.Defs.Induced


/-!
W441: ordinary descended map promotion surface for W426/W318 alignment.

W426 has checked standalone declarations for the ordinary descended quotient
map and its W399 quotient-compatibility field. W439 then records the W318
leg-compatibility bridge, but its W426 side is still mostly declaration names.

This file promotes that side one step further: the package below contains the
actual ordinary descended morphism, its quotient compatibility equation, and
the injective/inducing/closed-image facts that must be transported across the
ordinary/canonical colimit-map equality. The final equality is still exposed as
the exact missing input because the W426 standalone file and W318 canonical map
do not yet live in one importable module.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpW426W318LegCompatibilityAlignmentV370SupportW439

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagramW441 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomainW441 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW441 X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomainW441 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagramW441 X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeftW441 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW441 X ⟶ wppOpCodomainW441 X :=
  (wppOpOrdinaryDiagramW441 X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRightW441 (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomainW441 X ⟶ wppOpCodomainW441 X :=
  (wppOpOrdinaryDiagramW441 X).map WalkingParallelPairHom.right

/-- Ordinary quotient point used by the W426 descended quotient map. -/
abbrev wppOpOrdinaryQuotientPointW441
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomainW441 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW441 X - wppOpRightW441 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W318's per-object colimit-map compatibility equation. -/
abbrev W318ColimitMapLegCompatibilityW441
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  ∀ j : WalkingParallelPairᵒᵖ, cx.ι.app j ≫ φ = α.app j ≫ cy.ι.app j

/--
Concrete W426 ordinary descended quotient-map package.

The first field is the actual morphism, not only a declaration name. The
remaining fields are the W399 quotient-compatibility equation and the topology
facts that W318 ultimately needs after identifying this ordinary map with the
canonical colimit map.
-/
structure W426OrdinaryDescendedMapPackage
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y) : Type 1 where
  ordinaryDescended :
    wppOpOrdinaryQuotientPointW441 X ⟶ wppOpOrdinaryQuotientPointW441 Y
  quotient_compat :
    MetrizableLCA.quotientMap (wppOpCodomainW441 X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeftW441 X - wppOpRightW441 X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomainW441 Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeftW441 Y - wppOpRightW441 Y))
          (AddSubgroup.isClosed_topologicalClosure _)
  descended_injective :
    Function.Injective (ordinaryDescended :
      wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y)
  descended_inducing :
    IsInducing (ordinaryDescended :
      wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y)
  descended_range_closed :
    IsClosed (Set.range (ordinaryDescended :
      wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y))

/-- Projection of the promoted ordinary map's three topology facts. -/
theorem w426_ordinaryDescendedMap_topologyFacts
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y}
    (pkg : W426OrdinaryDescendedMapPackage ordinaryMap) :
    Function.Injective (pkg.ordinaryDescended :
        wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y) ∧
      IsInducing (pkg.ordinaryDescended :
        wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y) ∧
      IsClosed (Set.range (pkg.ordinaryDescended :
        wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y)) :=
  ⟨pkg.descended_injective, pkg.descended_inducing, pkg.descended_range_closed⟩

/--
Typed promotion from the W426 ordinary map package to one W318 colimit-map
instance.

The ordinary/canonical equality is still a named proposition because the W318
canonical map is not yet importable with W426's ordinary quotient map.
-/
structure W426OrdinaryMapPromotionToW318Fields
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y)
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Type 1 where
  ordinaryPackage : W426OrdinaryDescendedMapPackage ordinaryMap
  ordinaryDescendedMapName : String
  quotientCompatibilityName : String
  sourcePointIdentificationName : String
  targetPointIdentificationName : String
  canonicalWppOpColimitMapName : String
  ordinaryEqualsCanonicalColimitMap : Prop
  ordinaryEqualsCanonicalColimitMapName : String
  ordinaryEqualsCanonicalImpliesLegCompatibility :
    ordinaryEqualsCanonicalColimitMap →
      W318ColimitMapLegCompatibilityW441 X Y α cx cy φ
  ordinaryTopologyTransportsToColimitMap :
    ordinaryEqualsCanonicalColimitMap →
      Function.Injective (φ : cx.pt → cy.pt) ∧
        IsInducing (φ : cx.pt → cy.pt) ∧
        IsClosed (Set.range (φ : cx.pt → cy.pt))

/-- The exact equality frontier supplies W318's leg compatibility. -/
theorem w318_legCompatibility_of_w426_ordinaryMapPromotion
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y}
    {α : X ⟶ Y} {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (fields : W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ)
    (heq : fields.ordinaryEqualsCanonicalColimitMap) :
    W318ColimitMapLegCompatibilityW441 X Y α cx cy φ :=
  fields.ordinaryEqualsCanonicalImpliesLegCompatibility heq

/-- The same equality frontier transports W426's ordinary topology facts to W318's colimit map. -/
theorem w318_colimitMap_topologyFacts_of_w426_ordinaryMapPromotion
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y}
    {α : X ⟶ Y} {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (fields : W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ)
    (heq : fields.ordinaryEqualsCanonicalColimitMap) :
    Function.Injective (φ : cx.pt → cy.pt) ∧
      IsInducing (φ : cx.pt → cy.pt) ∧
      IsClosed (Set.range (φ : cx.pt → cy.pt)) :=
  fields.ordinaryTopologyTransportsToColimitMap heq

/--
Checked W318 left-frontier consumer from the promoted W426 ordinary map
package. This is the importable declaration W318 can use once the caller
constructs the promoted fields for each compatible colimit map.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryMapPromotion
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  let ordinaryMap := hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat
  let fields := hfields X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat
  exact fields.ordinaryTopologyTransportsToColimitMap
    (heq X Y α cx cy φ hcx hcy hclosed hcompat)

/-- Closed-embedding preservation consumer obtained from the W441 W318 left-frontier declaration. -/
theorem wppOp_colimit_preserves_leftClosedEmbedding_of_w426_ordinaryMapPromotion
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_colimit_preserves_leftClosedEmbedding :=
  WppOpExactAcyclicFrontierConsolidatedW318.wppOp_colimit_preserves_leftClosedEmbedding_of_injective_inducing_closedImage
    (wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryMapPromotion
      hfields hordinaryMap heq)

def w441CheckedDeclarationNames : List String :=
  ["wppOpOrdinaryDiagramW441",
    "wppOpOrdinaryQuotientPointW441",
    "W318ColimitMapLegCompatibilityW441",
    "W426OrdinaryDescendedMapPackage",
    "w426_ordinaryDescendedMap_topologyFacts",
    "W426OrdinaryMapPromotionToW318Fields",
    "w318_legCompatibility_of_w426_ordinaryMapPromotion",
    "w318_colimitMap_topologyFacts_of_w426_ordinaryMapPromotion",
    "wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryMapPromotion",
    "wppOp_colimit_preserves_leftClosedEmbedding_of_w426_ordinaryMapPromotion"]

theorem w441CheckedDeclarationNames_count :
    w441CheckedDeclarationNames.length = 10 := rfl

def w441ConcreteW426DeclarationNames : List String :=
  ["WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMapW418",
    "WppOpW399InputsFromReverseMembershipAndQuotientV370SupportW418.ordinaryDescendedOfOrdinaryMap_quotient_compatW418",
    "WppOpW399InputsFromReverseMembershipAndCertificatesV370SupportW423.ordinaryDescendedOfOrdinaryMapW417_eq_W418",
    "WppOpW399InputsFromCertificatesOnlyV370SupportW426.relationPullbackDescendedFieldsInputsW399_of_certificateRelationFieldsW395",
    "WppOpW399InputsFromCertificatesOnlyV370SupportW426.relationPullbackDescendedFieldsInputsW399_of_w380_w389_w386"]

theorem w441ConcreteW426DeclarationNames_count :
    w441ConcreteW426DeclarationNames.length = 5 := rfl

def missingInputsW441 : List String :=
  ["promote W426's ordinaryDescendedOfOrdinaryMapW418 and quotient compatibility theorem from standalone audit code to an importable module",
    "construct the W318 canonical WPP-op colimit-point map in the same namespace as W426's ordinary quotient map",
    "prove ordinaryEqualsCanonicalColimitMap after the W387/W390 source and target point identifications",
    "transport W426's ordinary descended injective/inducing/closed-image facts across that equality to the W318 colimit map"]

theorem missingInputsW441_count :
    missingInputsW441.length = 4 := rfl

def nextTheoremToPortW441 : String :=
  "ordinaryEqualsCanonicalColimitMap: identify W426's ordinaryDescendedOfOrdinaryMapW418, after W387/W390 point identifications, with W318's canonical compatible colimit-point map"

structure WppOpW426OrdinaryMapPromotionV370StateW441 : Type where
  seed : String
  declarations : List String
  concreteW426Declarations : List String
  missingInputs : List String
  nextTheoremToPort : String
  promotionResult : String
  exactOrdinaryEqualsCanonicalProved : Bool
  productSuccessClaimed : Bool

def currentWppOpW426OrdinaryMapPromotionV370StateW441 :
    WppOpW426OrdinaryMapPromotionV370StateW441 where
  seed := "0debc472baab29b6547903f8443717e4"
  declarations := w441CheckedDeclarationNames
  concreteW426Declarations := w441ConcreteW426DeclarationNames
  missingInputs := missingInputsW441
  nextTheoremToPort := nextTheoremToPortW441
  promotionResult :=
    "partial: checked package now carries the actual ordinary descended morphism, quotient compatibility, and topology facts; the ordinary/canonical equality remains the missing importable bridge"
  exactOrdinaryEqualsCanonicalProved := false
  productSuccessClaimed := false

theorem currentWppOpW426OrdinaryMapPromotionV370StateW441_productSuccess :
    currentWppOpW426OrdinaryMapPromotionV370StateW441.productSuccessClaimed = false := rfl

section Checks

#check W426OrdinaryDescendedMapPackage
#check w426_ordinaryDescendedMap_topologyFacts
#check W426OrdinaryMapPromotionToW318Fields
#check w318_legCompatibility_of_w426_ordinaryMapPromotion
#check w318_colimitMap_topologyFacts_of_w426_ordinaryMapPromotion
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryMapPromotion
#check wppOp_colimit_preserves_leftClosedEmbedding_of_w426_ordinaryMapPromotion
#check w441CheckedDeclarationNames
#check w441ConcreteW426DeclarationNames
#check missingInputsW441
#check nextTheoremToPortW441
#check currentWppOpW426OrdinaryMapPromotionV370StateW441
#check currentWppOpW426OrdinaryMapPromotionV370StateW441_productSuccess

end Checks

end WppOpW426W318LegCompatibilityAlignmentV370SupportW439

end LeanLCAExactChallenge



/-!
W463: selected component quotient-identification bridge.

Seed: `c33f238ef7fc4cbb2ff6d34e`.

This standalone support file reduces W460's remaining selected component
cofork `IsColimit` inputs to explicit quotient-identification data: an
AddCommGrp point isomorphism from the selected component target to the forgotten
explicit LCA cokernel quotient, a proof that the selected component leg becomes
the explicit quotient projection under that isomorphism, and the explicit
quotient cofork `IsColimit` proof.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA

/-- Worker seed recorded before edits, used only to diversify proof search. -/
def supportSeed : String := "c33f238ef7fc4cbb2ff6d34e"

/-- Local name for the short-complex functor forgetting topology. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The underlying functor used by the one-component wrappers. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The selected left arrow before forgetting topology. -/
def selectedMetrizableLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- The selected right arrow before forgetting topology. -/
def selectedMetrizableRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- The selected short-complex difference map whose components are normalized below. -/
def selectedMetrizableDifference
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  selectedMetrizableLeft S - selectedMetrizableRight S

/-- First component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₁
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₁ ⟶ (S.obj ordinaryTargetIndex).X₁ :=
  (selectedMetrizableDifference S).τ₁

/-- Second component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₂
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₂ ⟶ (S.obj ordinaryTargetIndex).X₂ :=
  (selectedMetrizableDifference S).τ₂

/-- Third component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₃
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₃ ⟶ (S.obj ordinaryTargetIndex).X₃ :=
  (selectedMetrizableDifference S).τ₃

/-- The selected leg before forgetting topology. -/
def selectedMetrizableTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    S.obj ordinaryTargetIndex ⟶ cs.pt :=
  cs.ι.app ordinaryTargetIndex

/-- Cocone naturality says the selected target leg coequalizes the two WPP arrows. -/
theorem selectedMetrizableTargetCoconeLeg_parallel_pair
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableLeft S ≫ selectedMetrizableTargetCoconeLeg S cs =
      selectedMetrizableRight S ≫ selectedMetrizableTargetCoconeLeg S cs :=
  (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).trans
    (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)).symm

/-- The selected target leg as a cofork in short complexes of metrizable LCA groups. -/
def selectedMetrizableTargetCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cofork (selectedMetrizableLeft S) (selectedMetrizableRight S) :=
  Cofork.ofπ (selectedMetrizableTargetCoconeLeg S cs)
    (selectedMetrizableTargetCoconeLeg_parallel_pair S cs)

/-- The selected metrizable target leg is a cokernel cofork for `(left - right)`. -/
def selectedMetrizableTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedMetrizableDifference S) :=
  Preadditive.cokernelCoforkOfCofork (selectedMetrizableTargetCofork S cs)

/-- The short-complex forgetful functor preserves zero morphisms, componentwise. -/
instance forgottenShortComplexFunctor_preservesZeroMorphisms :
    forgottenShortComplexFunctor.PreservesZeroMorphisms where
  map_zero S T := by
    ext x <;> rfl

/-- The short-complex forgetful functor is additive, componentwise. -/
instance forgottenShortComplexFunctor_additive :
    forgottenShortComplexFunctor.Additive where
  map_add {S T} {f g} := by
    ext x <;> rfl

/-- The selected component difference kills the first component target leg. -/
theorem selectedMetrizableDifferenceπ₁_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₁ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₁ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₁ h

/-- The selected component difference kills the second component target leg. -/
theorem selectedMetrizableDifferenceπ₂_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₂ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₂ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₂ h

/-- The selected component difference kills the third component target leg. -/
theorem selectedMetrizableDifferenceπ₃_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₃ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₃ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₃ h

/-- The first selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₁CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₁_comp_target S cs]
      rfl)

/-- The second selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₂CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₂_comp_target S cs]
      rfl)

/-- The third selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₃CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₃_comp_target S cs]
      rfl)

/-- The mapped selected short-complex cofork after forgetting topology. -/
abbrev selectedForgottenShortComplexCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) :=
  (selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor

/-- W433's explicit local cokernel cofork before forgetting topology. -/
def explicitMetrizableCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

/-- W433's mapped concrete cokernel cocone. -/
def mappedExplicitCokernelCocone {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Cocone (parallelPair f 0 ⋙ underlyingForgetfulFunctor) :=
  underlyingForgetfulFunctor.mapCocone (explicitMetrizableCokernelCofork f)

/-- The forgotten explicit cokernel projection, as in W440. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.obj Y ⟶ underlyingForgetfulFunctor.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

/-- W440's projection is the forgotten image of the LCA cokernel projection. -/
theorem forgottenCokernelπ_eq_map_cokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    forgottenCokernelπ f = underlyingForgetfulFunctor.map (cokernelπ f) := by
  ext y
  rfl

/-- The forgotten explicit cokernel projection kills the forgotten source map. -/
theorem forgottenCokernelπ_condition {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.map f ≫ forgottenCokernelπ f = 0 := by
  ext x
  change ((f x : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f x

/-- W440's explicit AddCommGrp cokernel cofork. -/
def forgottenExplicitCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork (underlyingForgetfulFunctor.map f) :=
  CokernelCofork.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)

/-- Transport data identifying the selected component cofork with the explicit quotient cofork. -/
structure SelectedComponentQuotientIdentificationInputsW463
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  pointIsoπ₁ :
    underlyingForgetfulFunctor.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₁ S))
  pointIsoπ₂ :
    underlyingForgetfulFunctor.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₂ S))
  pointIsoπ₃ :
    underlyingForgetfulFunctor.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₃ S))
  legπ₁ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      pointIsoπ₁.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₁ S)
  legπ₂ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      pointIsoπ₂.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₂ S)
  legπ₃ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      pointIsoπ₃.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₃ S)
  explicitπ₁CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S))
  explicitπ₂CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S))
  explicitπ₃CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S))

/-- The selected first-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₁CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₁CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S) :=
  Cocone.ext h.pointIsoπ₁ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S) ≫ q) h.legπ₁
      simpa [Category.assoc, selectedForgottenComponentπ₁CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₁CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₁)

/-- The selected second-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₂CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₂CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S) :=
  Cocone.ext h.pointIsoπ₂ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S) ≫ q) h.legπ₂
      simpa [Category.assoc, selectedForgottenComponentπ₂CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₂CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₂)

/-- The selected third-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₃CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₃CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S) :=
  Cocone.ext h.pointIsoπ₃ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S) ≫ q) h.legπ₃
      simpa [Category.assoc, selectedForgottenComponentπ₃CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₃CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₃)

/-- Quotient-identification data transports the explicit first-component cokernel proof. -/
def selectedComponentπ₁_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₁CokernelIsColimit
    (selectedComponentπ₁CoforkIso_of_quotientIdentification h).symm

/-- Quotient-identification data transports the explicit second-component cokernel proof. -/
def selectedComponentπ₂_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₂CokernelIsColimit
    (selectedComponentπ₂CoforkIso_of_quotientIdentification h).symm

/-- Quotient-identification data transports the explicit third-component cokernel proof. -/
def selectedComponentπ₃_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₃CokernelIsColimit
    (selectedComponentπ₃CoforkIso_of_quotientIdentification h).symm

/-- The projected `π₁` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₁DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₁]) (by rfl)

/-- The projected `π₂` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₂DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₂]) (by rfl)

/-- The projected `π₃` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₃DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₃]) (by rfl)

/-- The first selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₁CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₁DiagramIso S).inv).obj
        (selectedForgottenComponentπ₁CokernelCofork S cs) ≅
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The second selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₂CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₂DiagramIso S).inv).obj
        (selectedForgottenComponentπ₂CokernelCofork S cs) ≅
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The third selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₃CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₃DiagramIso S).inv).obj
        (selectedForgottenComponentπ₃CokernelCofork S cs) ≅
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- Transport a selected first-component `IsColimit` proof to the projected cofork. -/
def projectionπ₁_isColimit_of_selectedComponentπ₁
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₁DiagramIso S)
    (selectedForgottenComponentπ₁CokernelCofork S cs)
    _
    (selectedProjectionπ₁CoforkIso S cs)) h

/-- Transport a selected second-component `IsColimit` proof to the projected cofork. -/
def projectionπ₂_isColimit_of_selectedComponentπ₂
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₂DiagramIso S)
    (selectedForgottenComponentπ₂CokernelCofork S cs)
    _
    (selectedProjectionπ₂CoforkIso S cs)) h

/-- Transport a selected third-component `IsColimit` proof to the projected cofork. -/
def projectionπ₃_isColimit_of_selectedComponentπ₃
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₃DiagramIso S)
    (selectedForgottenComponentπ₃CokernelCofork S cs)
    _
    (selectedProjectionπ₃CoforkIso S cs)) h

/-- W457's selected projection colimit input shape. -/
def SelectedProjectionComponentIsColimitInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 :=
  IsColimit
    ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs)) ×
  IsColimit
    ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs)) ×
  IsColimit
    ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs))

/-- Component `IsColimit` proofs for the selected coforks supply W457's projected fields. -/
def selectedProjectionComponentIsColimitInputs_of_selectedComponentCoforks
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₁ : IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs))
    (hπ₂ : IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs))
    (hπ₃ : IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  ⟨projectionπ₁_isColimit_of_selectedComponentπ₁ hπ₁,
    projectionπ₂_isColimit_of_selectedComponentπ₂ hπ₂,
    projectionπ₃_isColimit_of_selectedComponentπ₃ hπ₃⟩

/-- Quotient-identification inputs provide all projected component `IsColimit` fields. -/
def selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  selectedProjectionComponentIsColimitInputs_of_selectedComponentCoforks
    (selectedComponentπ₁_isColimit_of_quotientIdentification_w463 h)
    (selectedComponentπ₂_isColimit_of_quotientIdentification_w463 h)
    (selectedComponentπ₃_isColimit_of_quotientIdentification_w463 h)

/-- Machine-readable W463 support state. -/
structure AddCommGrpSelectedComponentQuotientIdentificationV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  quotientIdentificationResult : String
  selectedComponentIsColimitResult : String
  projectionFieldsResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState :
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "SelectedComponentQuotientIdentificationInputsW463",
      "selectedComponentπ₁_isColimit_of_quotientIdentification_w463",
      "selectedComponentπ₂_isColimit_of_quotientIdentification_w463",
      "selectedComponentπ₃_isColimit_of_quotientIdentification_w463",
      "selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463"]
  quotientIdentificationResult := "proved"
  selectedComponentIsColimitResult := "proved"
  projectionFieldsResult := "proved"
  remainingInputs :=
    ["At the call site, supply the three AddCommGrp point isomorphisms from `cs.pt.Xᵢ` to the forgotten explicit cokernel quotients.",
      "At the call site, prove the three selected component legs compose with those isomorphisms to the forgotten explicit quotient projections.",
      "At the call site, supply the three explicit quotient `IsColimit` proofs, for example from the closed-range quotient support."]
  productSuccessClaimed := false

theorem currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState_productSuccess :
    currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check SelectedComponentQuotientIdentificationInputsW463
#check selectedComponentπ₁_isColimit_of_quotientIdentification_w463
#check selectedComponentπ₂_isColimit_of_quotientIdentification_w463
#check selectedComponentπ₃_isColimit_of_quotientIdentification_w463
#check selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463
#check currentAddCommGrpSelectedComponentQuotientIdentificationV370SupportState_productSuccess

end Checks

end AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463

end LeanLCAExactChallenge


/-!
W464: projection fields plus AddCommGrp row fields boundary.

Seed: `ee3109d3f37256d88905bcbb`.

This file composes W457's projection-field input surface with W459's canonical
selected-difference kernel row, giving a small wrapper from projection component
fields plus AddCommGrp row fields to strict SnakeInput cokernel data.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed recorded for the worker result contract. -/
def supportSeed : String :=
  "ee3109d3f37256d88905bcbb"

/-- Local name for the short-complex functor forgetting topology. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The selected left arrow before forgetting topology. -/
def selectedMetrizableLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- The selected right arrow before forgetting topology. -/
def selectedMetrizableRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- The selected leg before forgetting topology. -/
def selectedMetrizableTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    S.obj ordinaryTargetIndex ⟶ cs.pt :=
  cs.ι.app ordinaryTargetIndex

/-- Cocone naturality says the selected target leg coequalizes the two WPP arrows. -/
theorem selectedMetrizableTargetCoconeLeg_parallel_pair
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableLeft S ≫ selectedMetrizableTargetCoconeLeg S cs =
      selectedMetrizableRight S ≫ selectedMetrizableTargetCoconeLeg S cs :=
  (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).trans
    (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)).symm

/-- The selected target leg as a cofork in short complexes of metrizable LCA groups. -/
def selectedMetrizableTargetCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cofork (selectedMetrizableLeft S) (selectedMetrizableRight S) :=
  Cofork.ofπ (selectedMetrizableTargetCoconeLeg S cs)
    (selectedMetrizableTargetCoconeLeg_parallel_pair S cs)

/-- The selected metrizable target leg is a cokernel cofork for `(left - right)`. -/
def selectedMetrizableTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedMetrizableLeft S - selectedMetrizableRight S) :=
  Preadditive.cokernelCoforkOfCofork (selectedMetrizableTargetCofork S cs)

/-- The forgotten ordinary-left arrow of the WPP-op short-complex diagram. -/
def selectedForgottenLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableLeft S)

/-- The forgotten ordinary-right arrow of the WPP-op short-complex diagram. -/
def selectedForgottenRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableRight S)

/-- The selected forgotten-target cocone leg. -/
def selectedForgottenTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs)

/-- The selected forgotten leg is an explicit cokernel cofork. -/
def selectedForgottenTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedForgottenLeft S - selectedForgottenRight S) :=
  CokernelCofork.ofπ (selectedForgottenTargetCoconeLeg S cs) (by
    rw [Preadditive.sub_comp, sub_eq_zero]
    change
      forgottenShortComplexFunctor.map (selectedMetrizableLeft S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs) =
        forgottenShortComplexFunctor.map (selectedMetrizableRight S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs)
    rw [← forgottenShortComplexFunctor.map_comp, ← forgottenShortComplexFunctor.map_comp,
      selectedMetrizableTargetCoconeLeg_parallel_pair S cs])

/-- The short-complex forgetful functor preserves zero morphisms, componentwise. -/
instance forgottenShortComplexFunctor_preservesZeroMorphisms :
    forgottenShortComplexFunctor.PreservesZeroMorphisms where
  map_zero S T := by
    ext x <;> rfl

/-- The short-complex forgetful functor is additive, componentwise. -/
instance forgottenShortComplexFunctor_additive :
    forgottenShortComplexFunctor.Additive where
  map_add {S T} {f g} := by
    ext x <;> rfl

/-- The mapped selected cofork and selected forgotten cofork differ only by precomposition. -/
def precomposeSelectedForgottenCokernelCoforkIsoMap
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    let p : parallelPair
        (forgottenShortComplexFunctor.map
          (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
        parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
      parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
    ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) ≅
      (selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor := by
  dsimp
  refine Cofork.ext (Iso.refl _) ?_
  simp only [Iso.refl_hom]
  rfl

/-- Projection-field input surface for the selected mapped short-complex cofork. -/
def SelectedProjectionComponentIsColimitInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 :=
  IsColimit
    ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) ×
  IsColimit
    ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) ×
  IsColimit
    ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))

/-- Componentwise cokernel-colimit data for the selected mapped cofork. -/
structure SelectedMappedCokernelComponentwiseInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))

/-- Projection fields are exactly the three fields of the componentwise input package. -/
def selectedMappedCokernelComponentwiseInputsOfProjectionFields
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedProjectionComponentIsColimitInputs S cs) :
    SelectedMappedCokernelComponentwiseInputs S cs where
  hπ₁ := H.1
  hπ₂ := H.2.1
  hπ₃ := H.2.2

/-- Componentwise projection inputs assemble into the mapped short-complex cofork. -/
def selectedMappedCokernelColimitOfComponentwise
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    IsColimit
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
  ShortComplex.isColimitOfIsColimitπ
    ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)
    H.hπ₁ H.hπ₂ H.hπ₃

/-- W452 bridge: componentwise selected mapped cokernel inputs imply the forgotten cofork. -/
def selectedForgottenTargetCokernelColimitOfComponentwise
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  let p : parallelPair
      (forgottenShortComplexFunctor.map
        (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
      parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
    parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
  let hMap :
      IsColimit
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
    selectedMappedCokernelColimitOfComponentwise H
  let hPre :
      IsColimit
        ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) :=
    IsColimit.ofIsoColimit hMap
      (precomposeSelectedForgottenCokernelCoforkIsoMap S cs).symm
  exact (IsColimit.precomposeHomEquiv p (selectedForgottenTargetCokernelCofork S cs)) hPre

/-- A strict short exact row supplies W318's three AddCommGrp row inputs. -/
def addCommGrpStrictInputsOfStrictShortExact
    {S : ShortComplex MetrizableLCA.{0}}
    (hS : MetrizableLCA.strictShortExact S) :
    AddCommGrpLeftInjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
      AddCommGrpKernelExact (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpRightSurjective (S.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  ⟨hS.closed_inclusion.injective, hS.algebraic_exact, hS.surjective⟩

/-- A strict WPP-op family supplies W318's row-input family. -/
def addCommGrpStrictInputsFamilyOfStrictShortExact
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hS : ∀ j, MetrizableLCA.strictShortExact (S.obj j)) :
    ∀ j,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  fun j => addCommGrpStrictInputsOfStrictShortExact (hS j)

/-- Selected WPP-op source/target adapter for the difference-cokernel route. -/
def selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    {L₃ : ShortComplex AddCommGrpCat.{0}}
    (q :
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
        L₃)
    (w : (selectedForgottenLeft S - selectedForgottenRight S) ≫ q = 0 := by cat_disch)
    (L₀ : ShortComplex AddCommGrpCat.{0})
    (i :
      L₀ ⟶
        (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (wi : i ≫ (selectedForgottenLeft S - selectedForgottenRight S) = 0 := by cat_disch)
    (h₀ : IsLimit (KernelFork.ofι i wi))
    (h₃ : IsColimit (CokernelCofork.ofπ q w)) :
    ParallelPairDifferenceStrictCokernelData
      ((S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      ((S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
      L₃ where
  u := selectedForgottenLeft S
  v := selectedForgottenRight S
  q := q
  w := w
  L₀ := L₀
  i := i
  wi := wi
  h₀ := h₀
  h₃ := h₃
  L₁_kernelExact := (hRows ordinarySourceIndex).2.1
  L₁_rightSurjective := (hRows ordinarySourceIndex).2.2
  L₂_kernelExact := (hRows ordinaryTargetIndex).2.1
  L₂_leftInjective := (hRows ordinaryTargetIndex).1

/-- The selected target cofork supplies the strict SnakeInput cokernel data. -/
def strictSnakeCokernelData_of_componentwiseSelectedCokernel
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedMappedCokernelComponentwiseInputs S cs)
    (L₀ : ShortComplex AddCommGrpCat.{0})
    (i : L₀ ⟶ (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}))
    (wi : i ≫ (selectedForgottenLeft S - selectedForgottenRight S) = 0 := by cat_disch)
    (h₀ : IsLimit (KernelFork.ofι i wi)) :
  AddCommGrpStrictSnakeCokernelData
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_parallelPairDifferenceStrictCokernelData
    (selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows
      hRows (selectedForgottenTargetCoconeLeg S cs)
      (selectedForgottenTargetCokernelCofork S cs).condition L₀ i wi h₀
      (selectedForgottenTargetCokernelColimitOfComponentwise H))
    (Iso.refl _)

/-- The canonical kernel row for the selected forgotten difference map. -/
abbrev selectedDifferenceKernelRow
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    ShortComplex AddCommGrpCat.{0} :=
  kernel (selectedForgottenLeft S - selectedForgottenRight S)

/-- The kernel inclusion for the selected forgotten difference map. -/
abbrev selectedDifferenceKernelι
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    selectedDifferenceKernelRow S ⟶
      (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  kernel.ι (selectedForgottenLeft S - selectedForgottenRight S)

/-- The canonical kernel inclusion kills the selected forgotten difference map. -/
theorem selectedDifferenceKernelι_condition
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    selectedDifferenceKernelι S ≫
        (selectedForgottenLeft S - selectedForgottenRight S) =
      0 :=
  kernel.condition (selectedForgottenLeft S - selectedForgottenRight S)

/-- The canonical selected difference kernel fork is limiting. -/
def selectedDifferenceKernelIsLimit
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    IsLimit
      (KernelFork.ofι (selectedDifferenceKernelι S)
        (selectedDifferenceKernelι_condition S)) :=
  kernelIsKernel (selectedForgottenLeft S - selectedForgottenRight S)

/--
The W456 strict SnakeInput cokernel data with the remaining kernel-row input
filled by the categorical kernel of the selected forgotten difference map.
-/
def strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    AddCommGrpStrictSnakeCokernelData
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_componentwiseSelectedCokernel hRows H
    (selectedDifferenceKernelRow S) (selectedDifferenceKernelι S)
    (selectedDifferenceKernelι_condition S) (selectedDifferenceKernelIsLimit S)

/--
Projection component fields plus strict source rows give strict SnakeInput
cokernel data for the forgotten selected target short complex.
-/
def strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedProjectionComponentIsColimitInputs S cs) :
    AddCommGrpStrictSnakeCokernelData
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow hRows
    (selectedMappedCokernelComponentwiseInputsOfProjectionFields H)

/-- W318 consumer: the projection-field wrapper also supplies AddCommGrp kernel exactness. -/
theorem addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hRows : ∀ j : WalkingParallelPairᵒᵖ,
      AddCommGrpLeftInjective
          ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
        AddCommGrpKernelExact ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) ∧
          AddCommGrpRightSurjective
            ((S.obj j).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})))
    (H : SelectedProjectionComponentIsColimitInputs S cs) :
    AddCommGrpKernelExact
      (cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})) :=
  addCommGrpKernelExact_of_strictSnakeCokernelData _
    (strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows hRows H)

/-- Projection component fields supply W318's AddCommGrp row-field boundary. -/
theorem addCommGrpStrictKernelExactBoundary_of_projectionComponentFields
    (hproj : ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S), IsColimit cs → SelectedProjectionComponentIsColimitInputs S cs) :
    addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable := by
  intro S cs hcs hRows
  exact addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows hRows
    (hproj S cs hcs)

/-- Projection component fields plus the left strictness boundary imply exact acyclicity. -/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hproj : ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
      (cs : Cocone S), IsColimit cs → SelectedProjectionComponentIsColimitInputs S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_addCommGrpStrict
    hclosed (addCommGrpStrictKernelExactBoundary_of_projectionComponentFields hproj)

/-- W464 checked support state. -/
structure AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  projectionToComponentwiseResult : String
  strictSnakeResult : String
  kernelRowResult : String
  kernelExactResult : String
  boundaryResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W464. -/
def currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState :
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "SelectedProjectionComponentIsColimitInputs",
      "SelectedMappedCokernelComponentwiseInputs",
      "selectedMappedCokernelComponentwiseInputsOfProjectionFields",
      "selectedMappedCokernelColimitOfComponentwise",
      "selectedForgottenTargetCokernelColimitOfComponentwise",
      "addCommGrpStrictInputsOfStrictShortExact",
      "addCommGrpStrictInputsFamilyOfStrictShortExact",
      "selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows",
      "strictSnakeCokernelData_of_componentwiseSelectedCokernel",
      "selectedDifferenceKernelRow",
      "selectedDifferenceKernelι",
      "selectedDifferenceKernelι_condition",
      "selectedDifferenceKernelIsLimit",
      "strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow",
      "strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows",
      "addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows",
      "addCommGrpStrictKernelExactBoundary_of_projectionComponentFields",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields"]
  projectionToComponentwiseResult := "proved"
  strictSnakeResult := "proved"
  kernelRowResult := "proved"
  kernelExactResult := "proved"
  boundaryResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState_productSuccess :
    currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check SelectedProjectionComponentIsColimitInputs
#check SelectedMappedCokernelComponentwiseInputs
#check selectedMappedCokernelComponentwiseInputsOfProjectionFields
#check selectedMappedCokernelColimitOfComponentwise
#check selectedForgottenTargetCokernelColimitOfComponentwise
#check addCommGrpStrictInputsOfStrictShortExact
#check addCommGrpStrictInputsFamilyOfStrictShortExact
#check selectedWppOpParallelPairDifferenceStrictCokernelData_of_addCommGrpRows
#check strictSnakeCokernelData_of_componentwiseSelectedCokernel
#check selectedDifferenceKernelRow
#check selectedDifferenceKernelι
#check selectedDifferenceKernelι_condition
#check selectedDifferenceKernelIsLimit
#check strictSnakeCokernelData_of_componentwiseSelectedCokernel_kernelRow
#check strictSnakeCokernelData_of_projectionComponentFields_addCommGrpRows
#check addCommGrpKernelExact_of_projectionComponentFields_addCommGrpRows
#check addCommGrpStrictKernelExactBoundary_of_projectionComponentFields
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
#check currentAddCommGrpRowFieldsProjectionKernelBoundaryV370SupportState_productSuccess

end Checks

end AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464

end LeanLCAExactChallenge

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-!
W467: quotient-identification to exact-acyclic boundary.

Seed: `fba669c7dd85612f026c92ca`.

This final support layer composes W463 quotient-identification data with the
W464 projection-field consumer. The seed is recorded only for worker diversity;
it is not mathematical evidence.
-/

/-- Worker seed recorded before W467 edits. -/
def supportSeed : String :=
  "fba669c7dd85612f026c92ca"

/--
W463 quotient-identification inputs produce W464's selected projection
component `IsColimit` fields.
-/
def selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedComponentQuotientIdentificationInputsW463 S cs) :
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.SelectedProjectionComponentIsColimitInputs S cs := by
  simpa [AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.SelectedProjectionComponentIsColimitInputs,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableTargetCokernelCofork,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableTargetCofork,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableTargetCoconeLeg,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableLeft,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedMetrizableRight,
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.forgottenShortComplexFunctor,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedProjectionComponentIsColimitInputs,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedForgottenShortComplexCokernelCofork,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableTargetCokernelCofork,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableTargetCofork,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableTargetCoconeLeg,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableDifference,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableLeft,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedMetrizableRight,
    AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.forgottenShortComplexFunctor] using
    (AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463 h)

/--
Quotient-identification inputs supply the AddCommGrp strict kernel exactness
boundary by way of W464's projection-field wrapper.
-/
theorem addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467
    (hquot :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedComponentQuotientIdentificationInputsW463 S cs) :
    addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable :=
  AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.addCommGrpStrictKernelExactBoundary_of_projectionComponentFields
    (fun S cs hcs =>
      selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
        (hquot S cs hcs))

/--
Left closed-embedding input plus quotient-identification inputs imply the
walking-parallel-pair-op exact-acyclic colimit closure.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hquot :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463.SelectedComponentQuotientIdentificationInputsW463 S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
    hclosed
    (fun S cs hcs =>
      selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
        (hquot S cs hcs))

/-- Machine-readable W467 support state. -/
structure AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  projectionFieldsResult : String
  kernelExactBoundaryResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W467. -/
def currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState :
    AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467",
      "addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467"]
  projectionFieldsResult := "proved"
  kernelExactBoundaryResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs :=
    ["At each colimit call site, provide W463 quotient-identification inputs: three point isomorphisms, three leg/projection identifications, and three explicit quotient `IsColimit` proofs.",
      "Provide the W318/W464 left closed-embedding input `wppOp_lca_colimitMap_injective_inducing_closedImage` for the exact-acyclic closure theorem."]
  productSuccessClaimed := false

theorem currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState_productSuccess :
    currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
#check addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467
#check currentAddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportState_productSuccess

end Checks

end AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467

end LeanLCAExactChallenge

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA
open AddCommGrpSelectedComponentQuotientIdentificationV370SupportW463

/-- Worker seed recorded before W469 edits, used only to diversify proof search. -/
def supportSeedW469 : String := "609fc474ca14ac1abbf4d0a557af4907"

/--
Inputs for deriving W463's selected component quotient-identification package
from colimit comparison: selected component cofork colimits plus explicit
quotient cofork colimits, but no pre-supplied point isomorphisms or leg
equations.
-/
structure SelectedComponentColimitComparisonInputsW469
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  selectedπ₁CokernelIsColimit :
    IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs)
  selectedπ₂CokernelIsColimit :
    IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs)
  selectedπ₃CokernelIsColimit :
    IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)
  explicitπ₁CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S))
  explicitπ₂CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S))
  explicitπ₃CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S))

/-- The first selected component point isomorphism from colimit uniqueness. -/
def selectedComponentπ₁PointIso_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₁ S)) :=
  h.selectedπ₁CokernelIsColimit.coconePointUniqueUpToIso h.explicitπ₁CokernelIsColimit

/-- The second selected component point isomorphism from colimit uniqueness. -/
def selectedComponentπ₂PointIso_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₂ S)) :=
  h.selectedπ₂CokernelIsColimit.coconePointUniqueUpToIso h.explicitπ₂CokernelIsColimit

/-- The third selected component point isomorphism from colimit uniqueness. -/
def selectedComponentπ₃PointIso_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₃ S)) :=
  h.selectedπ₃CokernelIsColimit.coconePointUniqueUpToIso h.explicitπ₃CokernelIsColimit

/-- The first selected component leg equation follows from colimit-point uniqueness. -/
theorem selectedComponentπ₁Leg_eq_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      (selectedComponentπ₁PointIso_of_colimitComparison_w469 h).hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₁ S) := by
  simpa [selectedComponentπ₁PointIso_of_colimitComparison_w469,
    selectedForgottenComponentπ₁CokernelCofork, forgottenExplicitCokernelCofork] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom h.selectedπ₁CokernelIsColimit
        h.explicitπ₁CokernelIsColimit WalkingParallelPair.one)

/-- The second selected component leg equation follows from colimit-point uniqueness. -/
theorem selectedComponentπ₂Leg_eq_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      (selectedComponentπ₂PointIso_of_colimitComparison_w469 h).hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₂ S) := by
  simpa [selectedComponentπ₂PointIso_of_colimitComparison_w469,
    selectedForgottenComponentπ₂CokernelCofork, forgottenExplicitCokernelCofork] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom h.selectedπ₂CokernelIsColimit
        h.explicitπ₂CokernelIsColimit WalkingParallelPair.one)

/-- The third selected component leg equation follows from colimit-point uniqueness. -/
theorem selectedComponentπ₃Leg_eq_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      (selectedComponentπ₃PointIso_of_colimitComparison_w469 h).hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₃ S) := by
  simpa [selectedComponentπ₃PointIso_of_colimitComparison_w469,
    selectedForgottenComponentπ₃CokernelCofork, forgottenExplicitCokernelCofork] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom h.selectedπ₃CokernelIsColimit
        h.explicitπ₃CokernelIsColimit WalkingParallelPair.one)

/--
Component cofork colimit comparison supplies W463's point isomorphisms, leg
equations, and explicit quotient cofork colimit proofs.
-/
def selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentColimitComparisonInputsW469 S cs) :
    SelectedComponentQuotientIdentificationInputsW463 S cs where
  pointIsoπ₁ := selectedComponentπ₁PointIso_of_colimitComparison_w469 h
  pointIsoπ₂ := selectedComponentπ₂PointIso_of_colimitComparison_w469 h
  pointIsoπ₃ := selectedComponentπ₃PointIso_of_colimitComparison_w469 h
  legπ₁ := selectedComponentπ₁Leg_eq_of_colimitComparison_w469 h
  legπ₂ := selectedComponentπ₂Leg_eq_of_colimitComparison_w469 h
  legπ₃ := selectedComponentπ₃Leg_eq_of_colimitComparison_w469 h
  explicitπ₁CokernelIsColimit := h.explicitπ₁CokernelIsColimit
  explicitπ₂CokernelIsColimit := h.explicitπ₂CokernelIsColimit
  explicitπ₃CokernelIsColimit := h.explicitπ₃CokernelIsColimit

section Checks

#check supportSeedW469
#check SelectedComponentColimitComparisonInputsW469
#check selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469

end Checks

end AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469

namespace AddCommGrpComponentColimitComparisonExactAcyclicV370SupportW471

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Worker seed recorded before W471 edits; it is only for diversity. -/
def supportSeed : String := "9vgu7mkck7c2xiib5av7oyoq"

/--
W469 component-colimit comparison inputs produce W464's selected projection
component `IsColimit` fields, through W467's quotient-identification consumer.
-/
def selectedProjectionComponentIsColimitInputs_of_componentColimitComparison_w471
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469.SelectedComponentColimitComparisonInputsW469 S cs) :
    AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.SelectedProjectionComponentIsColimitInputs S cs :=
  AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467.selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w467
    (AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469.selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469 h)

/--
Component-colimit comparison inputs supply the AddCommGrp strict kernel
exactness boundary by deriving W467 quotient-identification inputs at each
selected colimit call site.
-/
theorem addCommGrpStrictKernelExactBoundary_of_componentColimitComparison_w471
    (hcomp :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469.SelectedComponentColimitComparisonInputsW469 S cs) :
    addCommGrpStrictKernelExact_wppOp_colimit_boundary_for_metrizable :=
  AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467.addCommGrpStrictKernelExactBoundary_of_quotientIdentifications_w467
    (fun S cs hcs =>
      AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469.selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469
        (hcomp S cs hcs))

/--
The W464/W318 left closed-embedding input plus component-colimit comparison
inputs imply exact acyclicity for walking-parallel-pair-op colimits.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_componentColimitComparison_w471
    (hclosed : wppOp_lca_colimitMap_injective_inducing_closedImage)
    (hcomp :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469.SelectedComponentColimitComparisonInputsW469 S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  AddCommGrpQuotientIdentificationExactAcyclicBoundaryV370SupportW467.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_quotientIdentifications_w467
    hclosed
    (fun S cs hcs =>
      AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469.selectedComponentQuotientIdentificationInputs_of_colimitComparison_w469
        (hcomp S cs hcs))

/-- Machine-readable W471 support state. -/
structure AddCommGrpComponentColimitComparisonExactAcyclicV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  projectionFieldsResult : String
  kernelExactBoundaryResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W471. -/
def currentAddCommGrpComponentColimitComparisonExactAcyclicV370SupportState :
    AddCommGrpComponentColimitComparisonExactAcyclicV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "selectedProjectionComponentIsColimitInputs_of_componentColimitComparison_w471",
      "addCommGrpStrictKernelExactBoundary_of_componentColimitComparison_w471",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_componentColimitComparison_w471"]
  projectionFieldsResult := "proved"
  kernelExactBoundaryResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs :=
    ["At each colimit call site, provide selected component cofork `IsColimit` proofs.",
      "At each colimit call site, provide explicit quotient cofork `IsColimit` proofs.",
      "Provide the W464/W318 left closed-embedding input `wppOp_lca_colimitMap_injective_inducing_closedImage` for the exact-acyclic closure theorem."]
  productSuccessClaimed := false

theorem currentAddCommGrpComponentColimitComparisonExactAcyclicV370SupportState_productSuccess :
    currentAddCommGrpComponentColimitComparisonExactAcyclicV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check selectedProjectionComponentIsColimitInputs_of_componentColimitComparison_w471
#check addCommGrpStrictKernelExactBoundary_of_componentColimitComparison_w471
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_componentColimitComparison_w471
#check currentAddCommGrpComponentColimitComparisonExactAcyclicV370SupportState_productSuccess

end Checks

end AddCommGrpComponentColimitComparisonExactAcyclicV370SupportW471

end LeanLCAExactChallenge

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology
open WppOpExactAcyclicFrontierConsolidatedW318

namespace AddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportW476

open WppOpW426W318LegCompatibilityAlignmentV370SupportW439

/-!
W476: W426 ordinary-map-promotion left-closedness plus component-colimit
comparison exact-acyclic wrapper.

Seed: `d88ae68b833f9b96d46dfd4a3e56b2e7`.
-/

/-- Worker seed recorded before edits; it is only for diversity. -/
def supportSeedW476 : String := "d88ae68b833f9b96d46dfd4a3e56b2e7"

/--
W441's W426 ordinary-map-promotion package supplies the W318 left closed-map
input expected by downstream exact-acyclic closure wrappers.
-/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w476
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap) :
    wppOp_lca_colimitMap_injective_inducing_closedImage :=
  wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryMapPromotion
    hfields hordinaryMap heq

/--
Component-colimit comparison exact acyclicity from W426 promotion data.

The caller provides W441's ordinary-map-promotion inputs and W471's component
comparison inputs, rather than a preassembled left closed-map theorem.
-/
theorem exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_componentColimitComparison_w476
    (hfields :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
        (ordinaryMap : (wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y))
        (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ)
    (hordinaryMap :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
          IsColimit cx →
            IsColimit cy →
              (∀ j : WalkingParallelPairᵒᵖ,
                IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
                W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                  ((wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y)))
    (heq :
      ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
        (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
        (hcx : IsColimit cx) (hcy : IsColimit cy)
        (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
          IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
        (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ),
          (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
            α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap)
    (hcomp :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          AddCommGrpComponentColimitComparisonQuotientIdentificationV370SupportW469.SelectedComponentColimitComparisonInputsW469 S cs) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  AddCommGrpComponentColimitComparisonExactAcyclicV370SupportW471.exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_componentColimitComparison_w471
    (wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w476
      hfields hordinaryMap heq)
    hcomp

/-- Machine-readable W476 support state. -/
structure AddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  leftClosedWrapperResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W476. -/
def currentAddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportState :
    AddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportState where
  seed := supportSeedW476
  checkedDeclarations :=
    ["supportSeedW476",
      "wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w476",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_componentColimitComparison_w476"]
  leftClosedWrapperResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs :=
    ["W441 ordinary-map-promotion fields at each compatible colimit-map call site.",
      "The W441 ordinary/canonical colimit-map equality field at each call site.",
      "W471 component-colimit comparison inputs at each selected short-complex colimit call site."]
  productSuccessClaimed := false

theorem currentAddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportState_productSuccess :
    currentAddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW476
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w476
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_componentColimitComparison_w476
#check currentAddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportState_productSuccess

end Checks

end AddCommGrpW426LeftClosedComponentComparisonExactAcyclicV370SupportW476

end LeanLCAExactChallenge
