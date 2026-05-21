import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact


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

/-- The exact equality input supplies W318's leg compatibility. -/
theorem w318_legCompatibility_of_w426_ordinaryMapPromotion
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y}
    {α : X ⟶ Y} {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (fields : W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ)
    (heq : fields.ordinaryEqualsCanonicalColimitMap) :
    W318ColimitMapLegCompatibilityW441 X Y α cx cy φ :=
  fields.ordinaryEqualsCanonicalImpliesLegCompatibility heq

/-- The same equality input transports W426's ordinary topology facts to W318's colimit map. -/
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
Checked W318 left-side consumer from the promoted W426 ordinary map
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

/-- Closed-embedding preservation consumer obtained from the W441 W318 left-side declaration. -/
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

/-!
W475: W426 ordinary-map promotion plus projection fields exact-acyclic wrapper.

Seed: `ea02b48d336b61e595a82ddf`.
-/

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475

open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed recorded for the worker result contract. -/
def supportSeedW475 : String :=
  "ea02b48d336b61e595a82ddf"

/-- W441 provider for the W426 ordinary-map promotion fields. -/
abbrev W426PromotionFieldsProviderW475 : Type 1 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (ordinaryMap : (wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y))
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ

/-- W441 provider for the ordinary descended map associated to the WPP-op map. -/
abbrev W426OrdinaryMapProviderW475 : Type 1 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              ((wppOpOrdinaryDiagramW441 X) ⟶ (wppOpOrdinaryDiagramW441 Y))

/-- W441 equality input identifying the ordinary descended map with W318's colimit map. -/
abbrev W426OrdinaryEqualsCanonicalProviderW475
    (hfields : W426PromotionFieldsProviderW475)
    (hordinaryMap : W426OrdinaryMapProviderW475) : Prop :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
    (hcx : IsColimit cx) (hcy : IsColimit cy)
    (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
      IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
    (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ),
      (hfields X Y (hordinaryMap X Y α cx cy φ hcx hcy hclosed hcompat)
        α cx cy φ hcx hcy hclosed hcompat).ordinaryEqualsCanonicalColimitMap

/-- W464 projection-field provider for selected component cokernel colimits. -/
abbrev ProjectionFieldsProviderW475 : Type 1 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs → SelectedProjectionComponentIsColimitInputs S cs

/-- W441's W426 promotion discharges W318's left closed-image input. -/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w475
    (hfields : W426PromotionFieldsProviderW475)
    (hordinaryMap : W426OrdinaryMapProviderW475)
    (heq : W426OrdinaryEqualsCanonicalProviderW475 hfields hordinaryMap) :
    WppOpExactAcyclicFrontierConsolidatedW318.wppOp_lca_colimitMap_injective_inducing_closedImage :=
  wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426_ordinaryMapPromotion
    hfields hordinaryMap heq

/--
W475 composition theorem: W441 supplies the left closed-image input, and W464's
projection fields supply the AddCommGrp row boundary consumed by W318.
-/
theorem
    exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_projectionFields_w475
    (hfields : W426PromotionFieldsProviderW475)
    (hordinaryMap : W426OrdinaryMapProviderW475)
    (heq : W426OrdinaryEqualsCanonicalProviderW475 hfields hordinaryMap)
    (hproj : ProjectionFieldsProviderW475) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
    (wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w475
      hfields hordinaryMap heq)
    hproj

/-- W475 checked support state. -/
structure W426LeftClosedProjectionFieldsExactAcyclicV370SupportStateW475 : Type where
  seed : String
  declarations : List String
  composedLeftClosedImageInput : String
  composedExactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W475. -/
def currentW426LeftClosedProjectionFieldsExactAcyclicV370SupportStateW475 :
    W426LeftClosedProjectionFieldsExactAcyclicV370SupportStateW475 where
  seed := supportSeedW475
  declarations :=
    ["W426PromotionFieldsProviderW475",
      "W426OrdinaryMapProviderW475",
      "W426OrdinaryEqualsCanonicalProviderW475",
      "ProjectionFieldsProviderW475",
      "wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w475",
      "exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_" ++
        "and_projectionFields_w475"]
  composedLeftClosedImageInput := "proved"
  composedExactAcyclicResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentW426LeftClosedProjectionFieldsExactAcyclicV370SupportStateW475_productSuccess :
    currentW426LeftClosedProjectionFieldsExactAcyclicV370SupportStateW475.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW475
#check W426PromotionFieldsProviderW475
#check W426OrdinaryMapProviderW475
#check W426OrdinaryEqualsCanonicalProviderW475
#check ProjectionFieldsProviderW475
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_w426Promotion_w475
#check exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_projectionFields_w475
#check currentW426LeftClosedProjectionFieldsExactAcyclicV370SupportStateW475_productSuccess

end Checks

end AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475

/-
W477: W426 ordinary-map promotion plus componentwise closed-range projection
inputs.

Seed: `c477c0de20260521`.
-/

namespace AddCommGrpW426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportW477

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed recorded for the worker result contract. -/
def supportSeedW477 : String :=
  "c477c0de20260521"

/-- First component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₁W477
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₁ ⟶ (S.obj ordinaryTargetIndex).X₁ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₁

/-- Second component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₂W477
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₂ ⟶ (S.obj ordinaryTargetIndex).X₂ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₂

/-- Third component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₃W477
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₃ ⟶ (S.obj ordinaryTargetIndex).X₃ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₃

/--
Componentwise closed-range surface plus the projection colimit fields consumed
by W475. The closed-range fields record the stronger intended input surface;
the projection fields remain explicit because the closed-range-to-projection
bridge is not part of this wrapper.
-/
structure SelectedComponentwiseClosedRangeProjectionInputsW477
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hclosedπ₁ : IsClosed (Set.range (selectedMetrizableDifferenceπ₁W477 S :
    (S.obj ordinarySourceIndex).X₁ → (S.obj ordinaryTargetIndex).X₁))
  hclosedπ₂ : IsClosed (Set.range (selectedMetrizableDifferenceπ₂W477 S :
    (S.obj ordinarySourceIndex).X₂ → (S.obj ordinaryTargetIndex).X₂))
  hclosedπ₃ : IsClosed (Set.range (selectedMetrizableDifferenceπ₃W477 S :
    (S.obj ordinarySourceIndex).X₃ → (S.obj ordinaryTargetIndex).X₃))
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

/-- Provider for componentwise closed-range projection inputs. -/
abbrev ComponentwiseClosedRangeProjectionProviderW477 : Type 1 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs → SelectedComponentwiseClosedRangeProjectionInputsW477 S cs

/-- Forget the closed-range fields and keep exactly the projection fields W475 consumes. -/
def projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w477
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW477) :
    ProjectionFieldsProviderW475 :=
  fun S cs hcs =>
    let H := hcomponentwise S cs hcs
    (H.hπ₁, H.hπ₂, H.hπ₃)

/--
W477 composition theorem: W426 ordinary-map promotion supplies W318's left
closed-image input, and the componentwise closed-range projection provider
supplies W475's projection fields.
-/
theorem
    exactAcyclic_of_w426Promotion_and_componentwiseClosedRangeProjection_w477
    (hfields : W426PromotionFieldsProviderW475)
    (hordinaryMap : W426OrdinaryMapProviderW475)
    (heq : W426OrdinaryEqualsCanonicalProviderW475 hfields hordinaryMap)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW477) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_projectionFields_w475
    hfields hordinaryMap heq
    (projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w477 hcomponentwise)

/-- W477 checked support state. -/
structure W426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportStateW477 :
    Type where
  seed : String
  declarations : List String
  componentwiseProjectionProviderResult : String
  composedExactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W477. -/
def currentW426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportStateW477 :
    W426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportStateW477 where
  seed := supportSeedW477
  declarations :=
    ["SelectedComponentwiseClosedRangeProjectionInputsW477",
      "ComponentwiseClosedRangeProjectionProviderW477",
      "projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w477",
      "exactAcyclic_of_w426Promotion_and_componentwiseClosedRangeProjection_w477"]
  componentwiseProjectionProviderResult := "proved"
  composedExactAcyclicResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

/-- Short alias used by checks to avoid long projection lines. -/
def currentStateW477 :
    W426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportStateW477 :=
  currentW426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportStateW477

theorem
    currentW426LeftClosedComponentwiseClosedRangeProjectionStateW477_productSuccess :
    currentStateW477.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW477
#check selectedMetrizableDifferenceπ₁W477
#check selectedMetrizableDifferenceπ₂W477
#check selectedMetrizableDifferenceπ₃W477
#check SelectedComponentwiseClosedRangeProjectionInputsW477
#check ComponentwiseClosedRangeProjectionProviderW477
#check projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w477
#check exactAcyclic_of_w426Promotion_and_componentwiseClosedRangeProjection_w477
#check currentW426LeftClosedComponentwiseClosedRangeProjectionStateW477_productSuccess

end Checks

end AddCommGrpW426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportW477

/-
W478: W461-style target-leg data as an importable W441/W475 promotion provider.

Seed: `478c0de-current-head`.
-/

namespace WppOpW461ToW441PromotionProviderV370SupportW478

open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpExactAcyclicFrontierConsolidatedW318
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439

/-- Reproducible seed recorded for this importable provider. -/
def supportSeedW478 : String :=
  "478c0de-current-head"

/-- Ordinary quotient map used by the W426 quotient-compatibility equation. -/
abbrev wppOpOrdinaryQuotientMapW478
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpCodomainW441 X ⟶ wppOpOrdinaryQuotientPointW441 X :=
  MetrizableLCA.quotientMap (wppOpCodomainW441 X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeftW441 X - wppOpRightW441 X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndexW478 : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- W461-style target-leg point-identification input shape. -/
structure W461TargetLegPointIdentificationInputsW478
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y
  ordinaryDescended :
    wppOpOrdinaryQuotientPointW441 X ⟶ wppOpOrdinaryQuotientPointW441 Y
  sourcePointIdentification : wppOpOrdinaryQuotientPointW441 X ≅ cx.pt
  targetPointIdentification : wppOpOrdinaryQuotientPointW441 Y ≅ cy.pt
  quotient_compat :
    wppOpOrdinaryQuotientMapW478 X ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫ wppOpOrdinaryQuotientMapW478 Y
  sourcePointIdentification_target_leg :
    cx.ι.app ordinaryTargetIndexW478 ≫ sourcePointIdentification.inv =
      wppOpOrdinaryQuotientMapW478 X
  targetPointIdentification_target_leg :
    α.app ordinaryTargetIndexW478 ≫ cy.ι.app ordinaryTargetIndexW478 =
      ordinaryMap.app WalkingParallelPair.one ≫
        wppOpOrdinaryQuotientMapW478 Y ≫ targetPointIdentification.hom

/-- Conjugate an ordinary descended map across point identifications. -/
def concreteConjugatedDescendedW478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W461TargetLegPointIdentificationInputsW478 X Y α cx cy) :
    cx.pt ⟶ cy.pt :=
  inputs.sourcePointIdentification.inv ≫
    inputs.ordinaryDescended ≫ inputs.targetPointIdentification.hom

/-- The ordinary-target component equation of W318's leg compatibility. -/
abbrev ordinaryTargetComponentEquationW478
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinaryTargetIndexW478 ≫ φ =
    α.app ordinaryTargetIndexW478 ≫ cy.ι.app ordinaryTargetIndexW478

/-- W426 quotient compatibility plus point-identification legs gives the target component. -/
theorem target_component_of_quotient_compat_and_point_identifications_w478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W461TargetLegPointIdentificationInputsW478 X Y α cx cy) :
    ordinaryTargetComponentEquationW478 X Y α cx cy
      (concreteConjugatedDescendedW478 inputs) := by
  have hcalc :
      ((cx.ι.app ordinaryTargetIndexW478 ≫ inputs.sourcePointIdentification.inv) ≫
          inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
        α.app ordinaryTargetIndexW478 ≫ cy.ι.app ordinaryTargetIndexW478 := by
    have hsource :
        ((cx.ι.app ordinaryTargetIndexW478 ≫ inputs.sourcePointIdentification.inv) ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (wppOpOrdinaryQuotientMapW478 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom :=
      congrArg
        (fun f => (f ≫ inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom)
        inputs.sourcePointIdentification_target_leg
    have hquotient :
        (wppOpOrdinaryQuotientMapW478 X ≫
            inputs.ordinaryDescended) ≫ inputs.targetPointIdentification.hom =
          (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW478 Y) ≫
              inputs.targetPointIdentification.hom :=
      congrArg (fun f => f ≫ inputs.targetPointIdentification.hom) inputs.quotient_compat
    have htarget :
        (inputs.ordinaryMap.app WalkingParallelPair.one ≫
            wppOpOrdinaryQuotientMapW478 Y) ≫
              inputs.targetPointIdentification.hom =
          α.app ordinaryTargetIndexW478 ≫ cy.ι.app ordinaryTargetIndexW478 := by
      simpa only [Category.assoc] using inputs.targetPointIdentification_target_leg.symm
    exact hsource.trans (hquotient.trans htarget)
  simpa only [concreteConjugatedDescendedW478, Category.assoc] using hcalc

/-- W461-style input package for W441 promotion fields. -/
structure W461ToW441PromotionInputsW478
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  pointIdentificationInputs :
    W461TargetLegPointIdentificationInputsW478 X Y α cx cy
  targetComponentImpliesW318 :
    ordinaryTargetComponentEquationW478 X Y α cx cy
        (concreteConjugatedDescendedW478 pointIdentificationInputs) →
      W318ColimitMapLegCompatibilityW441 X Y α cx cy
        (concreteConjugatedDescendedW478 pointIdentificationInputs)
  ordinaryPackage :
    W426OrdinaryDescendedMapPackage pointIdentificationInputs.ordinaryMap
  ordinaryDescended_eq :
    ordinaryPackage.ordinaryDescended =
      pointIdentificationInputs.ordinaryDescended

/-- The conjugated descended map is a closed embedding. -/
theorem concreteConjugatedDescended_closedEmbedding_of_w461_to_w441_w478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (inputs : W461ToW441PromotionInputsW478 X Y α cx cy) :
    IsClosedEmbedding (concreteConjugatedDescendedW478
      inputs.pointIdentificationInputs : cx.pt → cy.pt) := by
  let p := inputs.pointIdentificationInputs
  have hordinary :
      IsClosedEmbedding (p.ordinaryDescended :
        wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y) := by
    have hclosed :
        IsClosedEmbedding (inputs.ordinaryPackage.ordinaryDescended :
          wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y) :=
      closedEmbedding_of_injective_inducing_closedImage
        (inputs.ordinaryPackage.ordinaryDescended :
          wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y)
        inputs.ordinaryPackage.descended_injective
        inputs.ordinaryPackage.descended_inducing
        inputs.ordinaryPackage.descended_range_closed
    simpa [inputs.ordinaryDescended_eq] using hclosed
  let sourceHomeomorph : cx.pt ≃ₜ+ wppOpOrdinaryQuotientPointW441 X :=
    MetrizableLCA.isoToContinuousAddEquiv p.sourcePointIdentification.symm
  let targetHomeomorph : wppOpOrdinaryQuotientPointW441 Y ≃ₜ+ cy.pt :=
    MetrizableLCA.isoToContinuousAddEquiv p.targetPointIdentification
  have hcomp :
      IsClosedEmbedding
        (fun x : cx.pt => targetHomeomorph (p.ordinaryDescended (sourceHomeomorph x))) :=
    targetHomeomorph.toHomeomorph.isClosedEmbedding.comp
      (hordinary.comp sourceHomeomorph.toHomeomorph.isClosedEmbedding)
  have hfun :
      (fun x : cx.pt => targetHomeomorph (p.ordinaryDescended (sourceHomeomorph x))) =
        (concreteConjugatedDescendedW478 p : cx.pt → cy.pt) := by
    funext x
    rfl
  simpa [hfun] using hcomp

/-- The W461-shaped concrete map and any W318-compatible map out of `cx` are equal. -/
theorem eq_concreteConjugatedDescended_of_w461_compat_w478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcx : IsColimit cx)
    (inputs : W461ToW441PromotionInputsW478 X Y α cx cy)
    (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ) :
    φ = concreteConjugatedDescendedW478 inputs.pointIdentificationInputs := by
  apply hcx.hom_ext
  intro j
  have hconcrete :
      cx.ι.app j ≫ concreteConjugatedDescendedW478 inputs.pointIdentificationInputs =
        α.app j ≫ cy.ι.app j :=
    inputs.targetComponentImpliesW318
      (target_component_of_quotient_compat_and_point_identifications_w478
        inputs.pointIdentificationInputs) j
  exact (hcompat j).trans hconcrete.symm

/-- W461-style data supplies W441 promotion fields. -/
def w441PromotionFields_of_w461_to_w441_w478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcx : IsColimit cx)
    (inputs : W461ToW441PromotionInputsW478 X Y α cx cy)
    (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ) :
    W426OrdinaryMapPromotionToW318Fields
      inputs.pointIdentificationInputs.ordinaryMap α cx cy φ where
  ordinaryPackage := inputs.ordinaryPackage
  ordinaryDescendedMapName := "W478 ordinaryDescended"
  quotientCompatibilityName := "W478 quotient_compat"
  sourcePointIdentificationName := "W478 sourcePointIdentification"
  targetPointIdentificationName := "W478 targetPointIdentification"
  canonicalWppOpColimitMapName := "IsColimit.map"
  ordinaryEqualsCanonicalColimitMap := True
  ordinaryEqualsCanonicalColimitMapName := "W478 supplied leg compatibility"
  ordinaryEqualsCanonicalImpliesLegCompatibility := by
    intro _heq
    exact hcompat
  ordinaryTopologyTransportsToColimitMap := by
    intro _heq
    have hclosedConcrete :=
      concreteConjugatedDescended_closedEmbedding_of_w461_to_w441_w478 inputs
    have hφ :
        IsClosedEmbedding (φ : cx.pt → cy.pt) := by
      have hEq := eq_concreteConjugatedDescended_of_w461_compat_w478 hcx inputs hcompat
      simpa [hEq] using hclosedConcrete
    exact ⟨hφ.injective, hφ.isInducing, hφ.isClosed_range⟩

/-- W461-style data supplies W441 promotion fields for a specified ordinary map. -/
def w441PromotionFields_of_w461_to_w441_for_ordinaryMap_w478
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (hcx : IsColimit cx)
    (ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y)
    (inputs : W461ToW441PromotionInputsW478 X Y α cx cy)
    (ordinaryPackage : W426OrdinaryDescendedMapPackage ordinaryMap)
    (ordinaryDescended_eq :
      ordinaryPackage.ordinaryDescended =
        inputs.pointIdentificationInputs.ordinaryDescended)
    (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ) :
    W426OrdinaryMapPromotionToW318Fields ordinaryMap α cx cy φ where
  ordinaryPackage := ordinaryPackage
  ordinaryDescendedMapName := "W478 ordinaryDescended"
  quotientCompatibilityName := "W478 quotient_compat"
  sourcePointIdentificationName := "W478 sourcePointIdentification"
  targetPointIdentificationName := "W478 targetPointIdentification"
  canonicalWppOpColimitMapName := "IsColimit.map"
  ordinaryEqualsCanonicalColimitMap := True
  ordinaryEqualsCanonicalColimitMapName := "W478 supplied leg compatibility"
  ordinaryEqualsCanonicalImpliesLegCompatibility := by
    intro _heq
    exact hcompat
  ordinaryTopologyTransportsToColimitMap := by
    intro _heq
    let p := inputs.pointIdentificationInputs
    have hordinary :
        IsClosedEmbedding (p.ordinaryDescended :
          wppOpOrdinaryQuotientPointW441 X → wppOpOrdinaryQuotientPointW441 Y) := by
      have hclosed :
          IsClosedEmbedding (ordinaryPackage.ordinaryDescended :
            wppOpOrdinaryQuotientPointW441 X →
              wppOpOrdinaryQuotientPointW441 Y) :=
        closedEmbedding_of_injective_inducing_closedImage
          (ordinaryPackage.ordinaryDescended :
            wppOpOrdinaryQuotientPointW441 X →
              wppOpOrdinaryQuotientPointW441 Y)
          ordinaryPackage.descended_injective
          ordinaryPackage.descended_inducing
          ordinaryPackage.descended_range_closed
      simpa [ordinaryDescended_eq] using hclosed
    let sourceHomeomorph : cx.pt ≃ₜ+ wppOpOrdinaryQuotientPointW441 X :=
      MetrizableLCA.isoToContinuousAddEquiv p.sourcePointIdentification.symm
    let targetHomeomorph : wppOpOrdinaryQuotientPointW441 Y ≃ₜ+ cy.pt :=
      MetrizableLCA.isoToContinuousAddEquiv p.targetPointIdentification
    have hcomp :
        IsClosedEmbedding
          (fun x : cx.pt => targetHomeomorph (p.ordinaryDescended (sourceHomeomorph x))) :=
      targetHomeomorph.toHomeomorph.isClosedEmbedding.comp
        (hordinary.comp sourceHomeomorph.toHomeomorph.isClosedEmbedding)
    have hfun :
        (fun x : cx.pt => targetHomeomorph (p.ordinaryDescended (sourceHomeomorph x))) =
          (concreteConjugatedDescendedW478 p : cx.pt → cy.pt) := by
      funext x
      rfl
    have hclosedConcrete :
        IsClosedEmbedding (concreteConjugatedDescendedW478 p : cx.pt → cy.pt) := by
      simpa [hfun] using hcomp
    have hφ :
        IsClosedEmbedding (φ : cx.pt → cy.pt) := by
      have hEq := eq_concreteConjugatedDescended_of_w461_compat_w478 hcx inputs hcompat
      simpa [hEq] using hclosedConcrete
    exact ⟨hφ.injective, hφ.isInducing, hφ.isClosed_range⟩

/-- Provider for W461-style input packages at every W475 call site. -/
structure W461PromotionInputProviderW478 : Type 1 where
  ordinaryMapProvider : W426OrdinaryMapProviderW475
  inputs :
    ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
      (_ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y)
      (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
        IsColimit cx →
          IsColimit cy →
            (∀ j : WalkingParallelPairᵒᵖ,
              IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
              W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
                W461ToW441PromotionInputsW478 X Y α cx cy
  ordinaryPackage :
    ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
      (ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y)
      (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
      (_hcx : IsColimit cx) (_hcy : IsColimit cy)
      (_hclosed : ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
      (_hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ),
        W426OrdinaryDescendedMapPackage ordinaryMap
  ordinaryDescended_eq :
    ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
      (ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y)
      (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt)
      (hcx : IsColimit cx) (hcy : IsColimit cy)
      (hclosed : ∀ j : WalkingParallelPairᵒᵖ,
        IsClosedEmbedding (α.app j : X.obj j → Y.obj j))
      (hcompat : W318ColimitMapLegCompatibilityW441 X Y α cx cy φ),
        (ordinaryPackage X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat).ordinaryDescended =
          W461TargetLegPointIdentificationInputsW478.ordinaryDescended
            ((inputs X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat).pointIdentificationInputs)

/-- W478 input packages provide W475 promotion fields. -/
def w426PromotionFieldsProvider_of_w461Inputs_w478
    (hinputs : W461PromotionInputProviderW478) :
    W426PromotionFieldsProviderW475 :=
  fun X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat => by
    let input := hinputs.inputs X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat
    exact w441PromotionFields_of_w461_to_w441_for_ordinaryMap_w478 hcx ordinaryMap
      input
      (hinputs.ordinaryPackage X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat)
      (hinputs.ordinaryDescended_eq X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat)
      hcompat

/-- W478 input packages provide W475 ordinary maps. -/
def w426OrdinaryMapProvider_of_w461Inputs_w478
    (hinputs : W461PromotionInputProviderW478) :
    W426OrdinaryMapProviderW475 :=
  hinputs.ordinaryMapProvider

/-- W478 input packages provide W475 ordinary/canonical equality witnesses. -/
theorem w426OrdinaryEqualsCanonicalProvider_of_w461Inputs_w478
    (hinputs : W461PromotionInputProviderW478) :
    W426OrdinaryEqualsCanonicalProviderW475
      (w426PromotionFieldsProvider_of_w461Inputs_w478 hinputs)
      (w426OrdinaryMapProvider_of_w461Inputs_w478 hinputs) := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  trivial

/-- W478 input packages and W475 projection fields imply exact-acyclic WPP-op colimit closure. -/
theorem exactAcyclic_of_w461PromotionInputs_and_projectionFields_w478
    (hinputs : W461PromotionInputProviderW478)
    (hproj : ProjectionFieldsProviderW475) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_projectionFields_w475
    (w426PromotionFieldsProvider_of_w461Inputs_w478 hinputs)
    (w426OrdinaryMapProvider_of_w461Inputs_w478 hinputs)
    (w426OrdinaryEqualsCanonicalProvider_of_w461Inputs_w478 hinputs)
    hproj

/-- W478 checked support state. -/
structure W461ToW441PromotionProviderV370SupportStateW478 : Type where
  seed : String
  declarations : List String
  promotionProviderResult : String
  exactAcyclicWrapperResult : String
  productSuccessClaimed : Bool

/-- Current checked support state for W478. -/
def currentW461ToW441PromotionProviderV370SupportStateW478 :
    W461ToW441PromotionProviderV370SupportStateW478 where
  seed := supportSeedW478
  declarations :=
    ["W461TargetLegPointIdentificationInputsW478",
      "W461ToW441PromotionInputsW478",
      "w441PromotionFields_of_w461_to_w441_w478",
      "w426PromotionFieldsProvider_of_w461Inputs_w478",
      "exactAcyclic_of_w461PromotionInputs_and_projectionFields_w478"]
  promotionProviderResult := "proved"
  exactAcyclicWrapperResult := "proved"
  productSuccessClaimed := false

theorem currentW461ToW441PromotionProviderStateW478_productSuccess :
    currentW461ToW441PromotionProviderV370SupportStateW478.productSuccessClaimed = false :=
  rfl

section Checks

#check W461TargetLegPointIdentificationInputsW478
#check W461ToW441PromotionInputsW478
#check w441PromotionFields_of_w461_to_w441_w478
#check w426PromotionFieldsProvider_of_w461Inputs_w478
#check w426OrdinaryMapProvider_of_w461Inputs_w478
#check w426OrdinaryEqualsCanonicalProvider_of_w461Inputs_w478
#check exactAcyclic_of_w461PromotionInputs_and_projectionFields_w478
#check currentW461ToW441PromotionProviderStateW478_productSuccess

end Checks

end WppOpW461ToW441PromotionProviderV370SupportW478

namespace WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480

open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible seed for the W480 importable adapter. -/
def supportSeedW480 : String :=
  "w480-current-head-importable-adapter"

/--
W461-shaped inputs whose ordinary descended package is already stated for the
ordinary map currently requested by W475.
-/
structure W461ToW475PromotionInputsAtOrdinaryMapW480
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y)
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  inputs : W461ToW441PromotionInputsW478 X Y α cx cy
  ordinaryPackage : W426OrdinaryDescendedMapPackage ordinaryMap
  ordinaryDescended_eq :
    ordinaryPackage.ordinaryDescended =
      W461TargetLegPointIdentificationInputsW478.ordinaryDescended
        inputs.pointIdentificationInputs

/-- Promotion-field provider surface matching each W475 ordinary-map argument. -/
abbrev W461ToW475PromotionInputsProviderW480 : Type 1 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (ordinaryMap : wppOpOrdinaryDiagramW441 X ⟶ wppOpOrdinaryDiagramW441 Y)
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              W461ToW475PromotionInputsAtOrdinaryMapW480 ordinaryMap α cx cy

/-- Ordinary-map provider surface used to choose W475's ordinary map. -/
abbrev W461ToW475OrdinaryMapProviderW480 : Type 1 :=
  W426OrdinaryMapProviderW475

/-- W480 split providers assemble the W478 provider contract. -/
def w461PromotionInputProvider_of_w480
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480) :
    W461PromotionInputProviderW478 where
  ordinaryMapProvider := hordinaryMap
  inputs := fun X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat =>
    (hinputs X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat).inputs
  ordinaryPackage := fun X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat =>
    (hinputs X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat).ordinaryPackage
  ordinaryDescended_eq := fun X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat =>
    (hinputs X Y ordinaryMap α cx cy φ hcx hcy hclosed hcompat).ordinaryDescended_eq

/-- W480 split providers supply W475 promotion fields through the importable W478 adapter. -/
def w426PromotionFieldsProvider_of_w480
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480) :
    W426PromotionFieldsProviderW475 :=
  w426PromotionFieldsProvider_of_w461Inputs_w478
    (w461PromotionInputProvider_of_w480 hinputs hordinaryMap)

/-- W480 split providers supply W475 ordinary maps. -/
def w426OrdinaryMapProvider_of_w480
    (_hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480) :
    W426OrdinaryMapProviderW475 :=
  hordinaryMap

/-- W480 split providers supply W475's ordinary/canonical equality provider. -/
theorem w426OrdinaryEqualsCanonicalProvider_of_w480
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480) :
    W426OrdinaryEqualsCanonicalProviderW475
      (w426PromotionFieldsProvider_of_w480 hinputs hordinaryMap)
      (w426OrdinaryMapProvider_of_w480 hinputs hordinaryMap) :=
  w426OrdinaryEqualsCanonicalProvider_of_w461Inputs_w478
    (w461PromotionInputProvider_of_w480 hinputs hordinaryMap)

/-- W480 composition into W475's projection-field exact-acyclic endpoint. -/
theorem exactAcyclic_of_w461_bridge_to_w475_projection_w480
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    (hproj : ProjectionFieldsProviderW475) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461PromotionInputs_and_projectionFields_w478
    (w461PromotionInputProvider_of_w480 hinputs hordinaryMap) hproj

/-- W480 checked support state. -/
structure W461BridgeToW475ProjectionExactAcyclicV370SupportStateW480 : Type where
  seed : String
  declarations : List String
  exactAcyclicWrapperResult : String
  productSuccessClaimed : Bool

/-- Current checked support state for W480. -/
def currentW461BridgeToW475ProjectionExactAcyclicV370SupportStateW480 :
    W461BridgeToW475ProjectionExactAcyclicV370SupportStateW480 where
  seed := supportSeedW480
  declarations :=
    ["W461ToW475PromotionInputsAtOrdinaryMapW480",
      "W461ToW475PromotionInputsProviderW480",
      "W461ToW475OrdinaryMapProviderW480",
      "w461PromotionInputProvider_of_w480",
      "w426PromotionFieldsProvider_of_w480",
      "w426OrdinaryMapProvider_of_w480",
      "w426OrdinaryEqualsCanonicalProvider_of_w480",
      "exactAcyclic_of_w461_bridge_to_w475_projection_w480"]
  exactAcyclicWrapperResult := "proved"
  productSuccessClaimed := false

theorem currentW461BridgeToW475ProjectionExactAcyclicStateW480_productSuccess :
    currentW461BridgeToW475ProjectionExactAcyclicV370SupportStateW480.productSuccessClaimed =
      false :=
  rfl

section Checks

#check W461ToW475PromotionInputsAtOrdinaryMapW480
#check W461ToW475PromotionInputsProviderW480
#check W461ToW475OrdinaryMapProviderW480
#check w461PromotionInputProvider_of_w480
#check w426PromotionFieldsProvider_of_w480
#check w426OrdinaryMapProvider_of_w480
#check w426OrdinaryEqualsCanonicalProvider_of_w480
#check exactAcyclic_of_w461_bridge_to_w475_projection_w480
#check currentW461BridgeToW475ProjectionExactAcyclicStateW480_productSuccess

end Checks

end WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480

namespace WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed recorded for the worker result contract. -/
def supportSeedW481 : String :=
  "fa8174f2e9"

/-- First component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₁W481
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₁ ⟶ (S.obj ordinaryTargetIndex).X₁ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₁

/-- Second component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₂W481
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₂ ⟶ (S.obj ordinaryTargetIndex).X₂ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₂

/-- Third component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₃W481
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₃ ⟶ (S.obj ordinaryTargetIndex).X₃ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₃

/--
Componentwise closed-range surface plus the projection colimit fields consumed
by W475. The closed-range fields record the stronger intended input surface;
the projection fields remain explicit because the closed-range-to-projection
bridge is not part of this wrapper.
-/
structure SelectedComponentwiseClosedRangeProjectionInputsW481
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hclosedπ₁ : IsClosed (Set.range (selectedMetrizableDifferenceπ₁W481 S :
    (S.obj ordinarySourceIndex).X₁ → (S.obj ordinaryTargetIndex).X₁))
  hclosedπ₂ : IsClosed (Set.range (selectedMetrizableDifferenceπ₂W481 S :
    (S.obj ordinarySourceIndex).X₂ → (S.obj ordinaryTargetIndex).X₂))
  hclosedπ₃ : IsClosed (Set.range (selectedMetrizableDifferenceπ₃W481 S :
    (S.obj ordinarySourceIndex).X₃ → (S.obj ordinaryTargetIndex).X₃))
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

/-- Provider for componentwise closed-range projection inputs. -/
abbrev ComponentwiseClosedRangeProjectionProviderW481 : Type 1 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs → SelectedComponentwiseClosedRangeProjectionInputsW481 S cs

/-- Forget the closed-range fields and keep exactly the projection fields W475 consumes. -/
def projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w481
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    ProjectionFieldsProviderW475 :=
  fun S cs hcs =>
    let H := hcomponentwise S cs hcs
    (H.hπ₁, H.hπ₂, H.hπ₃)

/--
W481 composition theorem: W461 promotion inputs supply W480's W475 bridge, and
the componentwise closed-range projection provider supplies W475's projection
fields.
-/
theorem exactAcyclic_of_w461_to_w441_and_componentwiseClosedRangeProjection_w481
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461_bridge_to_w475_projection_w480
    hinputs hordinaryMap
    (projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w481
      hcomponentwise)

/-- W481 checked support state. -/
structure W461BridgeComponentwiseClosedRangeProjectionV370SupportStateW481 : Type where
  seed : String
  declarations : List String
  componentwiseProjectionProviderResult : String
  composedExactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W481. -/
def currentW461BridgeComponentwiseClosedRangeProjectionV370SupportStateW481 :
    W461BridgeComponentwiseClosedRangeProjectionV370SupportStateW481 where
  seed := supportSeedW481
  declarations :=
    ["SelectedComponentwiseClosedRangeProjectionInputsW481",
      "ComponentwiseClosedRangeProjectionProviderW481",
      "projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w481",
      "exactAcyclic_of_w461_to_w441_and_componentwiseClosedRangeProjection_w481"]
  componentwiseProjectionProviderResult := "proved"
  composedExactAcyclicResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentW461BridgeComponentwiseClosedRangeProjectionV370SupportStateW481_productSuccess :
    currentW461BridgeComponentwiseClosedRangeProjectionV370SupportStateW481.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW481
#check selectedMetrizableDifferenceπ₁W481
#check selectedMetrizableDifferenceπ₂W481
#check selectedMetrizableDifferenceπ₃W481
#check SelectedComponentwiseClosedRangeProjectionInputsW481
#check ComponentwiseClosedRangeProjectionProviderW481
#check projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w481
#check exactAcyclic_of_w461_to_w441_and_componentwiseClosedRangeProjection_w481
#check currentW461BridgeComponentwiseClosedRangeProjectionV370SupportStateW481_productSuccess

end Checks

end WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481

namespace WppOpW477ToW481ComponentwiseProjectionAdapterV370SupportW482

open AddCommGrpW426LeftClosedComponentwiseClosedRangeProjectionExactAcyclicV370SupportW477
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W477-to-W481 adapter. -/
def supportSeedW482 : String :=
  "482c0de-current-head"

/-- W477 and W481 use the same first selected difference component. -/
theorem selectedMetrizableDifferenceπ₁_w477_eq_w481
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    selectedMetrizableDifferenceπ₁W477 S =
      selectedMetrizableDifferenceπ₁W481 S :=
  rfl

/-- W477 and W481 use the same second selected difference component. -/
theorem selectedMetrizableDifferenceπ₂_w477_eq_w481
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    selectedMetrizableDifferenceπ₂W477 S =
      selectedMetrizableDifferenceπ₂W481 S :=
  rfl

/-- W477 and W481 use the same third selected difference component. -/
theorem selectedMetrizableDifferenceπ₃_w477_eq_w481
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    selectedMetrizableDifferenceπ₃W477 S =
      selectedMetrizableDifferenceπ₃W481 S :=
  rfl

/-- Convert W477 componentwise projection inputs into the W481 input surface. -/
def componentwiseClosedRangeProjectionInputsW481_of_w477
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW477 S cs) :
    SelectedComponentwiseClosedRangeProjectionInputsW481 S cs where
  hclosedπ₁ := by
    simpa [selectedMetrizableDifferenceπ₁W481, selectedMetrizableDifferenceπ₁W477]
      using H.hclosedπ₁
  hclosedπ₂ := by
    simpa [selectedMetrizableDifferenceπ₂W481, selectedMetrizableDifferenceπ₂W477]
      using H.hclosedπ₂
  hclosedπ₃ := by
    simpa [selectedMetrizableDifferenceπ₃W481, selectedMetrizableDifferenceπ₃W477]
      using H.hclosedπ₃
  hπ₁ := H.hπ₁
  hπ₂ := H.hπ₂
  hπ₃ := H.hπ₃

/-- Convert a W477 provider into the W481 provider surface. -/
def componentwiseClosedRangeProjectionProviderW481_of_w477
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW477) :
    ComponentwiseClosedRangeProjectionProviderW481 :=
  fun S cs hcs =>
    componentwiseClosedRangeProjectionInputsW481_of_w477 (hcomponentwise S cs hcs)

/--
W482 composition theorem: the already importable W477 componentwise provider can
feed W481, which then feeds W480's W461-to-W475 bridge.
-/
theorem exactAcyclic_of_w461_bridge_and_w477_componentwiseProjection_w482
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW477) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461_to_w441_and_componentwiseClosedRangeProjection_w481
    hinputs hordinaryMap
    (componentwiseClosedRangeProjectionProviderW481_of_w477 hcomponentwise)

/-- W482 checked support state. -/
structure W477ToW481ComponentwiseProjectionAdapterV370SupportStateW482 : Type where
  seed : String
  declarations : List String
  adapterResult : String
  composedExactAcyclicResult : String
  productSuccessClaimed : Bool

/-- Current checked support state for W482. -/
def currentW477ToW481ComponentwiseProjectionAdapterV370SupportStateW482 :
    W477ToW481ComponentwiseProjectionAdapterV370SupportStateW482 where
  seed := supportSeedW482
  declarations :=
    ["componentwiseClosedRangeProjectionInputsW481_of_w477",
      "componentwiseClosedRangeProjectionProviderW481_of_w477",
      "exactAcyclic_of_w461_bridge_and_w477_componentwiseProjection_w482"]
  adapterResult := "proved"
  composedExactAcyclicResult := "proved"
  productSuccessClaimed := false

theorem currentW477ToW481ComponentwiseProjectionAdapterStateW482_productSuccess :
    currentW477ToW481ComponentwiseProjectionAdapterV370SupportStateW482.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW482
#check selectedMetrizableDifferenceπ₁_w477_eq_w481
#check selectedMetrizableDifferenceπ₂_w477_eq_w481
#check selectedMetrizableDifferenceπ₃_w477_eq_w481
#check componentwiseClosedRangeProjectionInputsW481_of_w477
#check componentwiseClosedRangeProjectionProviderW481_of_w477
#check exactAcyclic_of_w461_bridge_and_w477_componentwiseProjection_w482
#check currentW477ToW481ComponentwiseProjectionAdapterStateW482_productSuccess

end Checks

end WppOpW477ToW481ComponentwiseProjectionAdapterV370SupportW482

namespace WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483

open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the parent W483 importable adapter. -/
def supportSeedW483 : String :=
  "w483-parent-single-w461-provider"

/--
Single selected W461 input provider for each W318 call site. This package avoids
requiring a separate W475 ordinary-map provider when the selected W461 data can
directly identify the W318 colimit map.
-/
abbrev SelectedW461PromotionInputsProviderW483 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0})
    (α : X ⟶ Y) (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              W461ToW441PromotionInputsW478 X Y α cx cy

/-- A single selected W461 provider proves W318's left closed-image input directly. -/
theorem wppOp_lca_colimitMap_injective_inducing_closedImage_of_selectedW461Provider_w483
    (hinputs : SelectedW461PromotionInputsProviderW483) :
    wppOp_lca_colimitMap_injective_inducing_closedImage := by
  intro X Y α cx cy φ hcx hcy hclosed hcompat
  let data := hinputs X Y α cx cy φ hcx hcy hclosed hcompat
  have hclosedConcrete :=
    concreteConjugatedDescended_closedEmbedding_of_w461_to_w441_w478 data
  have hφ : IsClosedEmbedding (φ : cx.pt → cy.pt) := by
    have hEq := eq_concreteConjugatedDescended_of_w461_compat_w478 hcx data hcompat
    simpa [hEq] using hclosedConcrete
  exact ⟨hφ.injective, hφ.isInducing, hφ.isClosed_range⟩

/-- W483 composition into the W475 projection-field exact-acyclic endpoint. -/
theorem exactAcyclic_of_selectedW461Provider_and_projectionFields_w483
    (hinputs : SelectedW461PromotionInputsProviderW483)
    (hproj : ProjectionFieldsProviderW475) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_left_and_projectionComponentFields
    (wppOp_lca_colimitMap_injective_inducing_closedImage_of_selectedW461Provider_w483
      hinputs)
    hproj

/-- W483 support theorem using one selected W461 provider and W481 projection inputs. -/
theorem exactAcyclic_of_selectedW461Provider_and_componentwiseClosedRangeProjection_w483
    (hinputs : SelectedW461PromotionInputsProviderW483)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_projectionFields_w483
    hinputs
    (projectionFieldsProvider_of_componentwiseClosedRangeProjectionInputs_w481
      hcomponentwise)

/-- W483 checked support state. -/
structure SingleW461ProviderComponentwiseProjectionV370SupportStateW483 : Type where
  seed : String
  declarations : List String
  leftClosedInputResult : String
  projectionFieldsCompositionResult : String
  componentwiseProjectionResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W483. -/
def currentSingleW461ProviderComponentwiseProjectionV370SupportStateW483 :
    SingleW461ProviderComponentwiseProjectionV370SupportStateW483 where
  seed := supportSeedW483
  declarations :=
    ["SelectedW461PromotionInputsProviderW483",
      "wppOp_lca_colimitMap_injective_inducing_closedImage_of_selectedW461Provider_w483",
      "exactAcyclic_of_selectedW461Provider_and_projectionFields_w483",
      "exactAcyclic_of_selectedW461Provider_and_componentwiseClosedRangeProjection_w483"]
  leftClosedInputResult := "proved"
  projectionFieldsCompositionResult := "proved"
  componentwiseProjectionResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentSingleW461ProviderComponentwiseProjectionStateW483_productSuccess :
    currentSingleW461ProviderComponentwiseProjectionV370SupportStateW483.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW483
#check SelectedW461PromotionInputsProviderW483
#check wppOp_lca_colimitMap_injective_inducing_closedImage_of_selectedW461Provider_w483
#check exactAcyclic_of_selectedW461Provider_and_projectionFields_w483
#check exactAcyclic_of_selectedW461Provider_and_componentwiseClosedRangeProjection_w483
#check currentSingleW461ProviderComponentwiseProjectionStateW483_productSuccess

end Checks

end WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483

end LeanLCAExactChallenge
