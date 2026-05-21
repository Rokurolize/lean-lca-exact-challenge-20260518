import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.ForgottenCokernel
import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Finite
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
  ["W418 ordinaryDescendedOfOrdinaryMap",
    "W418 ordinaryDescended quotient compatibility",
    "W423 ordinaryDescended W417/W418 equality",
    "W426 certificate relation fields to W399",
    "W426 W380/W389/W386 fields to W399"]

theorem w441ConcreteW426DeclarationNames_count :
    w441ConcreteW426DeclarationNames.length = 5 := rfl

def missingInputsW441 : List String :=
  ["promote W426 ordinary descended map and quotient compatibility",
    "construct W318 canonical WPP-op colimit-point map",
    "prove ordinaryEqualsCanonicalColimitMap after W387/W390 identifications",
    "transport W426 topology facts across that equality"]

theorem missingInputsW441_count :
    missingInputsW441.length = 4 := rfl

def nextTheoremToPortW441 : String :=
  "ordinaryEqualsCanonicalColimitMap for W426/W318 after W387/W390 identifications"

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
    "partial: package carries descended map, compatibility, and topology facts"
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

namespace WppOpW478ProviderToSelectedW461ProviderCurrentHeadV370SupportW486

open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible seed for the W486 W478-to-W483 provider adapter. -/
def supportSeedW486 : String :=
  "u8ruwzvh"

/-- Adapter from W478's bundled provider surface to W483's selected W461 provider surface. -/
def selectedW461Provider_of_w461PromotionInputProvider_w486
    (hinputs : W461PromotionInputProviderW478) :
    SelectedW461PromotionInputsProviderW483 :=
  fun X Y α cx cy φ hcx hcy hclosed hcompat =>
    hinputs.inputs X Y
      (hinputs.ordinaryMapProvider X Y α cx cy φ hcx hcy hclosed hcompat)
      α cx cy φ hcx hcy hclosed hcompat

/-- W478 input packages prove W318's left closed-image input through W483. -/
theorem leftClosedImage_of_w461PromotionInputProvider_w486
    (hinputs : W461PromotionInputProviderW478) :
    wppOp_lca_colimitMap_injective_inducing_closedImage :=
  wppOp_lca_colimitMap_injective_inducing_closedImage_of_selectedW461Provider_w483
    (selectedW461Provider_of_w461PromotionInputProvider_w486 hinputs)

/-- W478 input packages compose with any W475 projection-field provider through W483. -/
theorem exactAcyclic_of_w461PromotionInputProvider_and_projectionFields_w486
    (hinputs : W461PromotionInputProviderW478)
    (hproj : ProjectionFieldsProviderW475) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_projectionFields_w483
    (selectedW461Provider_of_w461PromotionInputProvider_w486 hinputs)
    hproj

/-- W486 checked support state. -/
structure W478ProviderToSelectedW461ProviderCurrentHeadV370SupportStateW486 : Type where
  seed : String
  declarations : List String
  adapterResult : String
  leftClosedImageResult : String
  exactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W486. -/
def currentW478ProviderToSelectedW461ProviderCurrentHeadV370SupportStateW486 :
    W478ProviderToSelectedW461ProviderCurrentHeadV370SupportStateW486 where
  seed := supportSeedW486
  declarations :=
    ["selectedW461Provider_of_w461PromotionInputProvider_w486",
      "leftClosedImage_of_w461PromotionInputProvider_w486",
      "exactAcyclic_of_w461PromotionInputProvider_and_projectionFields_w486"]
  adapterResult := "proved"
  leftClosedImageResult := "proved"
  exactAcyclicResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentW478ProviderToSelectedW461ProviderCurrentHeadStateW486_productSuccess :
    currentW478ProviderToSelectedW461ProviderCurrentHeadV370SupportStateW486.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW486
#check selectedW461Provider_of_w461PromotionInputProvider_w486
#check leftClosedImage_of_w461PromotionInputProvider_w486
#check exactAcyclic_of_w461PromotionInputProvider_and_projectionFields_w486
#check currentW478ProviderToSelectedW461ProviderCurrentHeadStateW486_productSuccess

end Checks

end WppOpW478ProviderToSelectedW461ProviderCurrentHeadV370SupportW486

namespace WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484

open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the parent W484 closed-range-only boundary. -/
def supportSeedW484 : String :=
  "w484-parent-closed-range-only-componentwise"

/-- Short local name for W484's ordinary source index. -/
abbrev ordinarySourceIndexW484 : WalkingParallelPairᵒᵖ :=
  AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.ordinarySourceIndex

/-- Short local name for W484's ordinary target index. -/
abbrev ordinaryTargetIndexW484 : WalkingParallelPairᵒᵖ :=
  AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.ordinaryTargetIndex

/-- Short local alias for the selected target cokernel cofork used in W484 fields. -/
abbrev selectedTargetCokernelCoforkW484
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :=
  selectedMetrizableTargetCokernelCofork S cs

/--
Closed-range-only component input surface. These are the intended topological
inputs, without hiding selected component projection `IsColimit` fields.
-/
structure SelectedComponentwiseClosedRangeOnlyInputsW484
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hclosedπ₁ : IsClosed (Set.range (selectedMetrizableDifferenceπ₁W481 S :
    (S.obj ordinarySourceIndexW484).X₁ → (S.obj ordinaryTargetIndexW484).X₁))
  hclosedπ₂ : IsClosed (Set.range (selectedMetrizableDifferenceπ₂W481 S :
    (S.obj ordinarySourceIndexW484).X₂ → (S.obj ordinaryTargetIndexW484).X₂))
  hclosedπ₃ : IsClosed (Set.range (selectedMetrizableDifferenceπ₃W481 S :
    (S.obj ordinarySourceIndexW484).X₃ → (S.obj ordinaryTargetIndexW484).X₃))

/-- Provider for the closed-range-only component input surface. -/
abbrev ComponentwiseClosedRangeOnlyProviderW484 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs → SelectedComponentwiseClosedRangeOnlyInputsW484 S cs

/--
The exact extra componentwise bridge still needed beyond closed range alone:
each selected projected component cofork must be an `IsColimit`.
-/
structure SelectedComponentwiseProjectionBridgeInputsW484
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedTargetCokernelCoforkW484 S cs).map forgottenShortComplexFunctor))
  hπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedTargetCokernelCoforkW484 S cs).map forgottenShortComplexFunctor))
  hπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedTargetCokernelCoforkW484 S cs).map forgottenShortComplexFunctor))

/--
Provider for the missing closed-range-to-selected-projection bridge. W484 keeps
this separate so the closed-range-only provider does not smuggle in W481's
projection fields.
-/
abbrev ComponentwiseClosedRangeOnlyProjectionBridgeW484 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs →
      SelectedComponentwiseClosedRangeOnlyInputsW484 S cs →
        SelectedComponentwiseProjectionBridgeInputsW484 S cs

/-- Closed-range-only inputs plus the isolated bridge recover W481's surface. -/
def selectedComponentwiseClosedRangeProjectionInputs_of_closedRangeOnly_w484
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hclosed : SelectedComponentwiseClosedRangeOnlyInputsW484 S cs)
    (hbridge : SelectedComponentwiseProjectionBridgeInputsW484 S cs) :
    SelectedComponentwiseClosedRangeProjectionInputsW481 S cs where
  hclosedπ₁ := hclosed.hclosedπ₁
  hclosedπ₂ := hclosed.hclosedπ₂
  hclosedπ₃ := hclosed.hclosedπ₃
  hπ₁ := hbridge.hπ₁
  hπ₂ := hbridge.hπ₂
  hπ₃ := hbridge.hπ₃

/--
Provider-level adapter from closed-range-only inputs to W481's projection
surface, parameterized by the exact missing bridge.
-/
def componentwiseProjectionProvider_of_closedRangeOnly_w484
    (hclosedOnly : ComponentwiseClosedRangeOnlyProviderW484)
    (hbridge : ComponentwiseClosedRangeOnlyProjectionBridgeW484) :
    ComponentwiseClosedRangeProjectionProviderW481 := by
  intro S cs hcs
  let hclosed := hclosedOnly S cs hcs
  exact selectedComponentwiseClosedRangeProjectionInputs_of_closedRangeOnly_w484 hclosed
    (hbridge S cs hcs hclosed)

/--
W484 composition theorem: once the isolated component projection bridge is
provided, the closed-range-only surface composes through W483.
-/
theorem exactAcyclic_of_selectedW461Provider_and_closedRangeOnlyComponentwiseProjection_w484
    (hinputs : SelectedW461PromotionInputsProviderW483)
    (hclosedOnly : ComponentwiseClosedRangeOnlyProviderW484)
    (hbridge : ComponentwiseClosedRangeOnlyProjectionBridgeW484) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_componentwiseClosedRangeProjection_w483
    hinputs
    (componentwiseProjectionProvider_of_closedRangeOnly_w484 hclosedOnly hbridge)

/-- Machine-readable blocked support state for W484. -/
structure ClosedRangeOnlyComponentwiseProjectionV370SupportStateW484 : Type where
  seed : String
  declarations : List String
  closedRangeOnlyProviderResult : String
  adapterResult : String
  composedExactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state: W484 is blocked exactly at the bridge fields. -/
def currentClosedRangeOnlyComponentwiseProjectionV370SupportStateW484 :
    ClosedRangeOnlyComponentwiseProjectionV370SupportStateW484 where
  seed := supportSeedW484
  declarations :=
    ["SelectedComponentwiseClosedRangeOnlyInputsW484",
      "ComponentwiseClosedRangeOnlyProviderW484",
      "SelectedComponentwiseProjectionBridgeInputsW484",
      "ComponentwiseClosedRangeOnlyProjectionBridgeW484",
      "selectedComponentwiseClosedRangeProjectionInputs_of_closedRangeOnly_w484",
      "componentwiseProjectionProvider_of_closedRangeOnly_w484",
      "exactAcyclic_of_selectedW461Provider_and_closedRangeOnlyComponentwiseProjection_w484"]
  closedRangeOnlyProviderResult := "proved"
  adapterResult := "blocked-with-explicit-bridge"
  composedExactAcyclicResult := "proved-assuming-bridge"
  remainingInputs :=
    ["prove projected selected target cokernel cofork IsColimit fields",
      "identify selected component legs with explicit LCA cokernel projections"]
  productSuccessClaimed := false

theorem currentClosedRangeOnlyComponentwiseProjectionStateW484_productSuccess :
    currentClosedRangeOnlyComponentwiseProjectionV370SupportStateW484.productSuccessClaimed =
      false :=
  rfl

theorem currentClosedRangeOnlyComponentwiseProjectionStateW484_remainingInputs_count :
    currentClosedRangeOnlyComponentwiseProjectionV370SupportStateW484.remainingInputs.length =
      2 :=
  rfl

section Checks

#check supportSeedW484
#check SelectedComponentwiseClosedRangeOnlyInputsW484
#check ComponentwiseClosedRangeOnlyProviderW484
#check SelectedComponentwiseProjectionBridgeInputsW484
#check ComponentwiseClosedRangeOnlyProjectionBridgeW484
#check selectedComponentwiseClosedRangeProjectionInputs_of_closedRangeOnly_w484
#check componentwiseProjectionProvider_of_closedRangeOnly_w484
#check exactAcyclic_of_selectedW461Provider_and_closedRangeOnlyComponentwiseProjection_w484
#check currentClosedRangeOnlyComponentwiseProjectionStateW484_productSuccess
#check currentClosedRangeOnlyComponentwiseProjectionStateW484_remainingInputs_count

end Checks

end WppOpClosedRangeOnlyComponentwiseProjectionV370SupportW484

namespace WppOpQuotientIdentificationProjectionProviderV370SupportW485

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA

/-- Reproducible seed for the W485 quotient-identification projection provider. -/
def supportSeedW485 : String :=
  "w485-quotient-identification-provider"

/-- The underlying forgetful functor used by the component quotient wrappers. -/
abbrev underlyingForgetfulFunctorW485 : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- First component of the selected short-complex difference map. -/
abbrev selectedMetrizableDifferenceπ₁W485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₁ ⟶ (S.obj ordinaryTargetIndex).X₁ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₁

/-- Second component of the selected short-complex difference map. -/
abbrev selectedMetrizableDifferenceπ₂W485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₂ ⟶ (S.obj ordinaryTargetIndex).X₂ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₂

/-- Third component of the selected short-complex difference map. -/
abbrev selectedMetrizableDifferenceπ₃W485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₃ ⟶ (S.obj ordinaryTargetIndex).X₃ :=
  (selectedMetrizableLeft S - selectedMetrizableRight S).τ₃

/-- The selected component difference kills the first component target leg. -/
theorem selectedMetrizableDifferenceπ₁_comp_target_w485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₁W485 S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₁ = 0 := by
  have h :
      (selectedMetrizableLeft S - selectedMetrizableRight S) ≫
          selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₁ h

/-- The selected component difference kills the second component target leg. -/
theorem selectedMetrizableDifferenceπ₂_comp_target_w485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₂W485 S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₂ = 0 := by
  have h :
      (selectedMetrizableLeft S - selectedMetrizableRight S) ≫
          selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₂ h

/-- The selected component difference kills the third component target leg. -/
theorem selectedMetrizableDifferenceπ₃_comp_target_w485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₃W485 S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₃ = 0 := by
  have h :
      (selectedMetrizableLeft S - selectedMetrizableRight S) ≫
          selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₃ h

/-- The first selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₁CokernelCoforkW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₁W485 S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₁) (by
      rw [← underlyingForgetfulFunctorW485.map_comp,
        selectedMetrizableDifferenceπ₁_comp_target_w485 S cs]
      rfl)

/-- The second selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₂CokernelCoforkW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₂W485 S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₂) (by
      rw [← underlyingForgetfulFunctorW485.map_comp,
        selectedMetrizableDifferenceπ₂_comp_target_w485 S cs]
      rfl)

/-- The third selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₃CokernelCoforkW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₃W485 S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₃) (by
      rw [← underlyingForgetfulFunctorW485.map_comp,
        selectedMetrizableDifferenceπ₃_comp_target_w485 S cs]
      rfl)

/-- The forgotten explicit cokernel projection, phrased as an AddCommGrp morphism. -/
abbrev forgottenCokernelπW485 {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctorW485.obj Y ⟶ underlyingForgetfulFunctorW485.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

/-- The forgotten explicit cokernel projection kills the forgotten source map. -/
theorem forgottenCokernelπ_conditionW485 {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctorW485.map f ≫ forgottenCokernelπW485 f = 0 := by
  ext x
  change ((f x : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f x

/-- The forgotten explicit AddCommGrp cokernel cofork. -/
def forgottenExplicitCokernelCoforkW485 {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork (underlyingForgetfulFunctorW485.map f) :=
  CokernelCofork.ofπ (forgottenCokernelπW485 f) (forgottenCokernelπ_conditionW485 f)

/-- Transport the W433-shaped mapped cokernel colimit back to the typed AddCommGrp cofork. -/
def forgottenCokernelCoforkIsColimit_of_closedRange_w487
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (MetrizableLCA.forgottenCokernelCofork f) :=
  (IsColimit.equivOfNatIsoOfIso
    (MetrizableLCA.forgottenCokernelParallelPairIso f)
    (MetrizableLCA.forgottenCokernelCofork f)
    (MetrizableLCA.forgottenMappedExplicitCokernelCocone f)
    (MetrizableLCA.forgottenCokernelCoforkMappedCoconeIso f)).symm
      (MetrizableLCA.forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosed_range
        f hclosed)

/-- Closed range gives the W485 duplicate explicit AddCommGrp cokernel cofork. -/
def forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (forgottenExplicitCokernelCoforkW485 f) := by
  simpa [
    forgottenExplicitCokernelCoforkW485,
    forgottenCokernelπW485,
    forgottenCokernelπ_conditionW485,
    underlyingForgetfulFunctorW485,
    MetrizableLCA.forgottenCokernelCofork,
    MetrizableLCA.forgottenCokernelπ,
    MetrizableLCA.forgottenCokernelπ_condition] using
    (forgottenCokernelCoforkIsColimit_of_closedRange_w487 f hclosed)

/-- Transport data identifying the selected component coforks with explicit quotient coforks. -/
structure SelectedComponentQuotientIdentificationInputsW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  pointIsoπ₁ :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₁W485 S))
  pointIsoπ₂ :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₂W485 S))
  pointIsoπ₃ :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₃W485 S))
  legπ₁ :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      pointIsoπ₁.hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₁W485 S)
  legπ₂ :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      pointIsoπ₂.hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₂W485 S)
  legπ₃ :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      pointIsoπ₃.hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₃W485 S)
  explicitπ₁CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCoforkW485 (selectedMetrizableDifferenceπ₁W485 S))
  explicitπ₂CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCoforkW485 (selectedMetrizableDifferenceπ₂W485 S))
  explicitπ₃CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCoforkW485 (selectedMetrizableDifferenceπ₃W485 S))

/-- Closed-range quotient-identification data; the explicit cokernel colimits are derived. -/
structure SelectedComponentClosedRangeQuotientIdentificationInputsW487
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  pointIsoπ₁ :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₁W485 S))
  pointIsoπ₂ :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₂W485 S))
  pointIsoπ₃ :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₃W485 S))
  legπ₁ :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      pointIsoπ₁.hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₁W485 S)
  legπ₂ :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      pointIsoπ₂.hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₂W485 S)
  legπ₃ :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      pointIsoπ₃.hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₃W485 S)
  closedRangeπ₁ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₁W485 S :
        (S.obj ordinarySourceIndex).X₁ → (S.obj ordinaryTargetIndex).X₁))
  closedRangeπ₂ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₂W485 S :
        (S.obj ordinarySourceIndex).X₂ → (S.obj ordinaryTargetIndex).X₂))
  closedRangeπ₃ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₃W485 S :
        (S.obj ordinarySourceIndex).X₃ → (S.obj ordinaryTargetIndex).X₃))

/-- Closed-range quotient-identification inputs derive the W485 explicit-colimit package. -/
def quotientIdentificationInputs_of_closedRange_w487
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentClosedRangeQuotientIdentificationInputsW487 S cs) :
    SelectedComponentQuotientIdentificationInputsW485 S cs where
  pointIsoπ₁ := h.pointIsoπ₁
  pointIsoπ₂ := h.pointIsoπ₂
  pointIsoπ₃ := h.pointIsoπ₃
  legπ₁ := h.legπ₁
  legπ₂ := h.legπ₂
  legπ₃ := h.legπ₃
  explicitπ₁CokernelIsColimit :=
    forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₁W485 S) h.closedRangeπ₁
  explicitπ₂CokernelIsColimit :=
    forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₂W485 S) h.closedRangeπ₂
  explicitπ₃CokernelIsColimit :=
    forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₃W485 S) h.closedRangeπ₃

/-- Provider for selected component quotient-identification inputs. -/
abbrev QuotientIdentificationProjectionProviderW485 : Type 1 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs → SelectedComponentQuotientIdentificationInputsW485 S cs

/-- Provider for closed-range selected component quotient-identification inputs. -/
abbrev ClosedRangeQuotientIdentificationProjectionProviderW487 : Type 1 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs →
      SelectedComponentClosedRangeQuotientIdentificationInputsW487 S cs

/-- Closed-range quotient-identification provider adapted to W485's projection-field surface. -/
def quotientIdentificationProvider_of_closedRange_w487
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    QuotientIdentificationProjectionProviderW485 :=
  fun S cs hcs => quotientIdentificationInputs_of_closedRange_w487 (hclosed S cs hcs)

/-- The selected first-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₁CoforkIso_of_quotientIdentification_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW485 S cs) :
    selectedForgottenComponentπ₁CokernelCoforkW485 S cs ≅
      forgottenExplicitCokernelCoforkW485 (selectedMetrizableDifferenceπ₁W485 S) :=
  Cocone.ext h.pointIsoπ₁ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₁W485 S) ≫ q)
        h.legπ₁
      simpa [Category.assoc, selectedForgottenComponentπ₁CokernelCoforkW485,
        forgottenExplicitCokernelCoforkW485] using hzero
    · simpa [selectedForgottenComponentπ₁CokernelCoforkW485,
        forgottenExplicitCokernelCoforkW485] using h.legπ₁)

/-- The selected second-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₂CoforkIso_of_quotientIdentification_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW485 S cs) :
    selectedForgottenComponentπ₂CokernelCoforkW485 S cs ≅
      forgottenExplicitCokernelCoforkW485 (selectedMetrizableDifferenceπ₂W485 S) :=
  Cocone.ext h.pointIsoπ₂ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₂W485 S) ≫ q)
        h.legπ₂
      simpa [Category.assoc, selectedForgottenComponentπ₂CokernelCoforkW485,
        forgottenExplicitCokernelCoforkW485] using hzero
    · simpa [selectedForgottenComponentπ₂CokernelCoforkW485,
        forgottenExplicitCokernelCoforkW485] using h.legπ₂)

/-- The selected third-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₃CoforkIso_of_quotientIdentification_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW485 S cs) :
    selectedForgottenComponentπ₃CokernelCoforkW485 S cs ≅
      forgottenExplicitCokernelCoforkW485 (selectedMetrizableDifferenceπ₃W485 S) :=
  Cocone.ext h.pointIsoπ₃ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₃W485 S) ≫ q)
        h.legπ₃
      simpa [Category.assoc, selectedForgottenComponentπ₃CokernelCoforkW485,
        forgottenExplicitCokernelCoforkW485] using hzero
    · simpa [selectedForgottenComponentπ₃CokernelCoforkW485,
        forgottenExplicitCokernelCoforkW485] using h.legπ₃)

/-- Quotient-identification data transports the explicit first-component cokernel proof. -/
def selectedComponentπ₁_isColimit_of_quotientIdentification_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW485 S cs) :
    IsColimit (selectedForgottenComponentπ₁CokernelCoforkW485 S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₁CokernelIsColimit
    (selectedComponentπ₁CoforkIso_of_quotientIdentification_w485 h).symm

/-- Quotient-identification data transports the explicit second-component cokernel proof. -/
def selectedComponentπ₂_isColimit_of_quotientIdentification_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW485 S cs) :
    IsColimit (selectedForgottenComponentπ₂CokernelCoforkW485 S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₂CokernelIsColimit
    (selectedComponentπ₂CoforkIso_of_quotientIdentification_w485 h).symm

/-- Quotient-identification data transports the explicit third-component cokernel proof. -/
def selectedComponentπ₃_isColimit_of_quotientIdentification_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW485 S cs) :
    IsColimit (selectedForgottenComponentπ₃CokernelCoforkW485 S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₃CokernelIsColimit
    (selectedComponentπ₃CoforkIso_of_quotientIdentification_w485 h).symm

/-- The projected `π₁` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₁DiagramIsoW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₁W485 S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map
          (selectedMetrizableLeft S - selectedMetrizableRight S)) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by
    exact (congrArg ShortComplex.Hom.τ₁
      (forgottenShortComplexFunctor.map_sub
        (f := selectedMetrizableLeft S) (g := selectedMetrizableRight S))).symm)
    (by rfl)

/-- The projected `π₂` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₂DiagramIsoW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₂W485 S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map
          (selectedMetrizableLeft S - selectedMetrizableRight S)) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by
    exact (congrArg ShortComplex.Hom.τ₂
      (forgottenShortComplexFunctor.map_sub
        (f := selectedMetrizableLeft S) (g := selectedMetrizableRight S))).symm)
    (by rfl)

/-- The projected `π₃` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₃DiagramIsoW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctorW485.map (selectedMetrizableDifferenceπ₃W485 S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map
          (selectedMetrizableLeft S - selectedMetrizableRight S)) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by
    exact (congrArg ShortComplex.Hom.τ₃
      (forgottenShortComplexFunctor.map_sub
        (f := selectedMetrizableLeft S) (g := selectedMetrizableRight S))).symm)
    (by rfl)

/-- The first selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₁CoforkIsoW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₁DiagramIsoW485 S).inv).obj
        (selectedForgottenComponentπ₁CokernelCoforkW485 S cs) ≅
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The second selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₂CoforkIsoW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₂DiagramIsoW485 S).inv).obj
        (selectedForgottenComponentπ₂CokernelCoforkW485 S cs) ≅
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The third selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₃CoforkIsoW485
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₃DiagramIsoW485 S).inv).obj
        (selectedForgottenComponentπ₃CokernelCoforkW485 S cs) ≅
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- Transport a selected first-component `IsColimit` proof to the projected cofork. -/
def projectionπ₁_isColimit_of_selectedComponentπ₁_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₁CokernelCoforkW485 S cs)) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₁DiagramIsoW485 S)
    (selectedForgottenComponentπ₁CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₁CoforkIsoW485 S cs)) h

/-- Transport a selected second-component `IsColimit` proof to the projected cofork. -/
def projectionπ₂_isColimit_of_selectedComponentπ₂_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₂CokernelCoforkW485 S cs)) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₂DiagramIsoW485 S)
    (selectedForgottenComponentπ₂CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₂CoforkIsoW485 S cs)) h

/-- Transport a selected third-component `IsColimit` proof to the projected cofork. -/
def projectionπ₃_isColimit_of_selectedComponentπ₃_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₃CokernelCoforkW485 S cs)) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₃DiagramIsoW485 S)
    (selectedForgottenComponentπ₃CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₃CoforkIsoW485 S cs)) h

/-- Quotient-identification inputs provide all projected component `IsColimit` fields. -/
def selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w485
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW485 S cs) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  ⟨projectionπ₁_isColimit_of_selectedComponentπ₁_w485
      (selectedComponentπ₁_isColimit_of_quotientIdentification_w485 h),
    projectionπ₂_isColimit_of_selectedComponentπ₂_w485
      (selectedComponentπ₂_isColimit_of_quotientIdentification_w485 h),
    projectionπ₃_isColimit_of_selectedComponentπ₃_w485
      (selectedComponentπ₃_isColimit_of_quotientIdentification_w485 h)⟩

/-- A quotient-identification provider supplies W475 projection fields. -/
def projectionFieldsProvider_of_quotientIdentifications_w485
    (hquot : QuotientIdentificationProjectionProviderW485) :
    ProjectionFieldsProviderW475 :=
  fun S cs hcs =>
    selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w485
      (hquot S cs hcs)

/-- W483 composition using one selected W461 provider and W485 quotient-identification inputs. -/
theorem exactAcyclic_of_selectedW461Provider_and_quotientIdentificationProjection_w485
    (hinputs : SelectedW461PromotionInputsProviderW483)
    (hquot : QuotientIdentificationProjectionProviderW485) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_projectionFields_w483
    hinputs
    (projectionFieldsProvider_of_quotientIdentifications_w485 hquot)

/-- W487 composition using selected W461 inputs and closed-range quotient identifications. -/
theorem exactAcyclic_of_selectedW461Provider_and_closedRangeQuotientIdentification_w487
    (hinputs : SelectedW461PromotionInputsProviderW483)
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_quotientIdentificationProjection_w485
    hinputs
    (quotientIdentificationProvider_of_closedRange_w487 hclosed)

end WppOpQuotientIdentificationProjectionProviderV370SupportW485

namespace WppOpW478ProviderQuotientIdentificationProjectionV370SupportW487

open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpW478ProviderToSelectedW461ProviderCurrentHeadV370SupportW486
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible seed for the W487 W478-provider plus quotient-identification route. -/
def supportSeedW487 : String :=
  "w487-w478-quotient-identification"

/--
W487 combines W486 and W485: a W478 provider supplies the selected W461 input,
and quotient-identification data supply the W475 projection fields.
-/
theorem exactAcyclic_of_w461PromotionInputProvider_and_quotientIdentificationProjection_w487
    (hinputs : W461PromotionInputProviderW478)
    (hquot : QuotientIdentificationProjectionProviderW485) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461PromotionInputProvider_and_projectionFields_w486
    hinputs
    (projectionFieldsProvider_of_quotientIdentifications_w485 hquot)

/--
W487 closed-range route: closed-range quotient-identification data are adapted to
W485 before composing with the W478 provider.
-/
theorem exactAcyclic_of_w461PromotionInputProvider_and_closedRangeQuotientIdentification_w487
    (hinputs : W461PromotionInputProviderW478)
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461PromotionInputProvider_and_quotientIdentificationProjection_w487
    hinputs
    (quotientIdentificationProvider_of_closedRange_w487 hclosed)

/-- W487 checked support state. -/
structure W478ProviderQuotientIdentificationProjectionV370SupportStateW487 : Type where
  seed : String
  declarations : List String
  exactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked support state for W487. -/
def currentW478ProviderQuotientIdentificationProjectionV370SupportStateW487 :
    W478ProviderQuotientIdentificationProjectionV370SupportStateW487 where
  seed := supportSeedW487
  declarations :=
    ["exactAcyclic_of_w461PromotionInputProvider_and_quotientIdentificationProjection_w487",
      "exactAcyclic_of_w461PromotionInputProvider_and_closedRangeQuotientIdentification_w487"]
  exactAcyclicResult := "proved"
  remainingInputs :=
    ["construct concrete W461PromotionInputProviderW478",
      "construct concrete QuotientIdentificationProjectionProviderW485",
      "or construct the closed-range provider surface adapted to it"]
  productSuccessClaimed := false

theorem currentW478ProviderQuotientIdentificationProjectionStateW487_productSuccess :
    currentW478ProviderQuotientIdentificationProjectionV370SupportStateW487.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeedW487
#check exactAcyclic_of_w461PromotionInputProvider_and_quotientIdentificationProjection_w487
#check exactAcyclic_of_w461PromotionInputProvider_and_closedRangeQuotientIdentification_w487
#check currentW478ProviderQuotientIdentificationProjectionStateW487_productSuccess

end Checks

end WppOpW478ProviderQuotientIdentificationProjectionV370SupportW487

namespace WppOpComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportW489

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open WppOpW478ProviderQuotientIdentificationProjectionV370SupportW487
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA

def supportSeedW489 : String :=
  "w489-componentwise-to-closed-range-quotient"

def selectedComponentπ₁_isColimit_of_projection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₁ :
      IsColimit
        ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))) :
    IsColimit (selectedForgottenComponentπ₁CokernelCoforkW485 S cs) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₁DiagramIsoW485 S)
    (selectedForgottenComponentπ₁CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₁CoforkIsoW485 S cs)).symm hπ₁

def selectedComponentπ₂_isColimit_of_projection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₂ :
      IsColimit
        ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))) :
    IsColimit (selectedForgottenComponentπ₂CokernelCoforkW485 S cs) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₂DiagramIsoW485 S)
    (selectedForgottenComponentπ₂CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₂CoforkIsoW485 S cs)).symm hπ₂

def selectedComponentπ₃_isColimit_of_projection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₃ :
      IsColimit
        ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))) :
    IsColimit (selectedForgottenComponentπ₃CokernelCoforkW485 S cs) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₃DiagramIsoW485 S)
    (selectedForgottenComponentπ₃CokernelCoforkW485 S cs)
    _
    (selectedProjectionπ₃CoforkIsoW485 S cs)).symm hπ₃

def selectedComponentπ₁PointIso_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₁W485 S)) :=
  (selectedComponentπ₁_isColimit_of_projection_w489 H.hπ₁).coconePointUniqueUpToIso
    (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₁W485 S) (by
        simpa [selectedMetrizableDifferenceπ₁W481, selectedMetrizableDifferenceπ₁W485]
          using H.hclosedπ₁))

def selectedComponentπ₂PointIso_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₂W485 S)) :=
  (selectedComponentπ₂_isColimit_of_projection_w489 H.hπ₂).coconePointUniqueUpToIso
    (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₂W485 S) (by
        simpa [selectedMetrizableDifferenceπ₂W481, selectedMetrizableDifferenceπ₂W485]
          using H.hclosedπ₂))

def selectedComponentπ₃PointIso_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctorW485.obj (cokernelObj (selectedMetrizableDifferenceπ₃W485 S)) :=
  (selectedComponentπ₃_isColimit_of_projection_w489 H.hπ₃).coconePointUniqueUpToIso
    (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
      (selectedMetrizableDifferenceπ₃W485 S) (by
        simpa [selectedMetrizableDifferenceπ₃W481, selectedMetrizableDifferenceπ₃W485]
          using H.hclosedπ₃))

theorem selectedComponentπ₁Leg_eq_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      (selectedComponentπ₁PointIso_of_componentwiseProjection_w489 H).hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₁W485 S) := by
  simpa [selectedComponentπ₁PointIso_of_componentwiseProjection_w489,
    selectedForgottenComponentπ₁CokernelCoforkW485, forgottenExplicitCokernelCoforkW485] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (selectedComponentπ₁_isColimit_of_projection_w489 H.hπ₁)
        (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
          (selectedMetrizableDifferenceπ₁W485 S) (by
            simpa [selectedMetrizableDifferenceπ₁W481, selectedMetrizableDifferenceπ₁W485]
              using H.hclosedπ₁))
        WalkingParallelPair.one)

theorem selectedComponentπ₂Leg_eq_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      (selectedComponentπ₂PointIso_of_componentwiseProjection_w489 H).hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₂W485 S) := by
  simpa [selectedComponentπ₂PointIso_of_componentwiseProjection_w489,
    selectedForgottenComponentπ₂CokernelCoforkW485, forgottenExplicitCokernelCoforkW485] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (selectedComponentπ₂_isColimit_of_projection_w489 H.hπ₂)
        (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
          (selectedMetrizableDifferenceπ₂W485 S) (by
            simpa [selectedMetrizableDifferenceπ₂W481, selectedMetrizableDifferenceπ₂W485]
              using H.hclosedπ₂))
        WalkingParallelPair.one)

theorem selectedComponentπ₃Leg_eq_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    underlyingForgetfulFunctorW485.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      (selectedComponentπ₃PointIso_of_componentwiseProjection_w489 H).hom =
        forgottenCokernelπW485 (selectedMetrizableDifferenceπ₃W485 S) := by
  simpa [selectedComponentπ₃PointIso_of_componentwiseProjection_w489,
    selectedForgottenComponentπ₃CokernelCoforkW485, forgottenExplicitCokernelCoforkW485] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (selectedComponentπ₃_isColimit_of_projection_w489 H.hπ₃)
        (forgottenExplicitCokernelCoforkW485_isColimit_of_closedRange_w487
          (selectedMetrizableDifferenceπ₃W485 S) (by
            simpa [selectedMetrizableDifferenceπ₃W481, selectedMetrizableDifferenceπ₃W485]
              using H.hclosedπ₃))
        WalkingParallelPair.one)

def closedRangeQuotientIdentificationInputs_of_componentwiseProjection_w489
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputsW481 S cs) :
    SelectedComponentClosedRangeQuotientIdentificationInputsW487 S cs where
  pointIsoπ₁ := selectedComponentπ₁PointIso_of_componentwiseProjection_w489 H
  pointIsoπ₂ := selectedComponentπ₂PointIso_of_componentwiseProjection_w489 H
  pointIsoπ₃ := selectedComponentπ₃PointIso_of_componentwiseProjection_w489 H
  legπ₁ := selectedComponentπ₁Leg_eq_of_componentwiseProjection_w489 H
  legπ₂ := selectedComponentπ₂Leg_eq_of_componentwiseProjection_w489 H
  legπ₃ := selectedComponentπ₃Leg_eq_of_componentwiseProjection_w489 H
  closedRangeπ₁ := by
    simpa [selectedMetrizableDifferenceπ₁W481, selectedMetrizableDifferenceπ₁W485]
      using H.hclosedπ₁
  closedRangeπ₂ := by
    simpa [selectedMetrizableDifferenceπ₂W481, selectedMetrizableDifferenceπ₂W485]
      using H.hclosedπ₂
  closedRangeπ₃ := by
    simpa [selectedMetrizableDifferenceπ₃W481, selectedMetrizableDifferenceπ₃W485]
      using H.hclosedπ₃

def closedRangeQuotientIdentificationProvider_of_componentwiseProjection_w489
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    ClosedRangeQuotientIdentificationProjectionProviderW487 :=
  fun S cs hcs =>
    closedRangeQuotientIdentificationInputs_of_componentwiseProjection_w489
      (hcomponentwise S cs hcs)

theorem exactAcyclic_of_w461PromotionInputProvider_and_componentwiseProjection_w489
    (hinputs : W461PromotionInputProviderW478)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461PromotionInputProvider_and_closedRangeQuotientIdentification_w487
    hinputs
    (closedRangeQuotientIdentificationProvider_of_componentwiseProjection_w489 hcomponentwise)

structure ComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportStateW489 :
    Type where
  seed : String
  declarations : List String
  providerAdapterResult : String
  exactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportStateW489 :
    ComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportStateW489 where
  seed := supportSeedW489
  declarations :=
    ["selectedComponentπ₁_isColimit_of_projection_w489",
      "selectedComponentπ₂_isColimit_of_projection_w489",
      "selectedComponentπ₃_isColimit_of_projection_w489",
      "closedRangeQuotientIdentificationInputs_of_componentwiseProjection_w489",
      "closedRangeQuotientIdentificationProvider_of_componentwiseProjection_w489",
      "exactAcyclic_of_w461PromotionInputProvider_and_componentwiseProjection_w489"]
  providerAdapterResult := "proved"
  exactAcyclicResult := "proved"
  remainingInputs :=
    ["construct concrete W461PromotionInputProviderW478",
      "construct concrete ComponentwiseClosedRangeProjectionProviderW481"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW489State :
    ComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportStateW489 :=
  currentComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportStateW489

theorem currentComponentwiseProjectionToClosedRangeQuotientIdentificationStateW489_productSuccess :
    currentW489State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW489
#check selectedComponentπ₁_isColimit_of_projection_w489
#check selectedComponentπ₂_isColimit_of_projection_w489
#check selectedComponentπ₃_isColimit_of_projection_w489
#check closedRangeQuotientIdentificationInputs_of_componentwiseProjection_w489
#check closedRangeQuotientIdentificationProvider_of_componentwiseProjection_w489
#check exactAcyclic_of_w461PromotionInputProvider_and_componentwiseProjection_w489
#check currentComponentwiseProjectionToClosedRangeQuotientIdentificationStateW489_productSuccess

end Checks

end WppOpComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportW489

namespace WppOpW480SplitProvidersComponentwiseProjectionV370SupportW490

open WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480
open WppOpQuotientIdentificationProjectionProviderV370SupportW485
open WppOpW478ProviderQuotientIdentificationProjectionV370SupportW487
open WppOpComponentwiseProjectionToClosedRangeQuotientIdentificationV370SupportW489
open WppOpW461BridgeComponentwiseClosedRangeProjectionV370SupportW481
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible seed for the W490 W480-split-provider composition route. -/
def supportSeedW490 : String :=
  "w490-w480-split-provider-componentwise-projection"

/--
W490 composes the W480 split-provider adapter with the W487 closed-range
quotient-identification route.
-/
theorem exactAcyclic_of_w480_splitProviders_and_closedRangeQuotientIdentification_w490
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    (hclosed : ClosedRangeQuotientIdentificationProjectionProviderW487) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461PromotionInputProvider_and_closedRangeQuotientIdentification_w487
    (w461PromotionInputProvider_of_w480 hinputs hordinaryMap)
    hclosed

/--
W490 endpoint using W480 split providers and W489's componentwise closed-range
projection adapter.
-/
theorem exactAcyclic_of_w480_splitProviders_and_componentwiseProjection_w490
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    (hcomponentwise : ComponentwiseClosedRangeProjectionProviderW481) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w461PromotionInputProvider_and_componentwiseProjection_w489
    (w461PromotionInputProvider_of_w480 hinputs hordinaryMap)
    hcomponentwise

structure W480SplitProvidersComponentwiseProjectionV370SupportStateW490 : Type where
  seed : String
  declarations : List String
  exactAcyclicClosedRangeResult : String
  exactAcyclicComponentwiseResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentW480SplitProvidersComponentwiseProjectionV370SupportStateW490 :
    W480SplitProvidersComponentwiseProjectionV370SupportStateW490 where
  seed := supportSeedW490
  declarations :=
    ["exactAcyclic_of_w480_splitProviders_and_closedRangeQuotientIdentification_w490",
      "exactAcyclic_of_w480_splitProviders_and_componentwiseProjection_w490"]
  exactAcyclicClosedRangeResult := "proved"
  exactAcyclicComponentwiseResult := "proved"
  remainingInputs :=
    ["construct concrete W461ToW475PromotionInputsProviderW480",
      "construct concrete W461ToW475OrdinaryMapProviderW480",
      "construct concrete ComponentwiseClosedRangeProjectionProviderW481"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW490State :
    W480SplitProvidersComponentwiseProjectionV370SupportStateW490 :=
  currentW480SplitProvidersComponentwiseProjectionV370SupportStateW490

theorem currentW480SplitProvidersComponentwiseProjectionStateW490_productSuccess :
    currentW490State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW490
#check exactAcyclic_of_w480_splitProviders_and_closedRangeQuotientIdentification_w490
#check exactAcyclic_of_w480_splitProviders_and_componentwiseProjection_w490
#check currentW480SplitProvidersComponentwiseProjectionStateW490_productSuccess

end Checks

end WppOpW480SplitProvidersComponentwiseProjectionV370SupportW490

namespace WppOpProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportW491

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open AddCommGrpW426LeftClosedProjectionFieldsExactAcyclicV370SupportW475
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W491 projection-field narrowing. -/
def supportSeedW491 : String :=
  "w491-selected-cokernel-colimit-to-projection-fields"

/--
Transport a selected forgotten-target cokernel colimit proof across the
precomposition iso to the mapped short-complex cokernel cofork used by W475.
-/
def selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h :
      IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    IsColimit
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) := by
  let p : parallelPair
      (forgottenShortComplexFunctor.map
        (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
      parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
    parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
  let hPre :
      IsColimit
        ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) :=
    (IsColimit.precomposeHomEquiv p (selectedForgottenTargetCokernelCofork S cs)).symm h
  exact
    IsColimit.ofIsoColimit hPre
      (precomposeSelectedForgottenCokernelCoforkIsoMap S cs)

/--
One selected forgotten-target cokernel colimit proof supplies all three W475
projection fields by applying the short-complex projection functors.
-/
def selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h :
      IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  let hMapped :=
    selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491 h
  ⟨isColimitOfPreserves
      (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      hMapped,
    isColimitOfPreserves
      (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      hMapped,
    isColimitOfPreserves
      (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0})
      hMapped⟩

/-- Provider form of the W491 narrowing. -/
def projectionFieldsProvider_of_selectedCokernelColimitProvider_w491
    (hselected :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    ProjectionFieldsProviderW475 :=
  fun S cs hcs =>
    selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491
      (hselected S cs hcs)

/--
W491 composition endpoint: a selected cokernel-colimit provider can replace the
component projection-field provider in W475.
-/
theorem exactAcyclic_of_w426Promotion_and_selectedCokernelColimitProvider_w491
    (hfields : W426PromotionFieldsProviderW475)
    (hordinaryMap : W426OrdinaryMapProviderW475)
    (heq : W426OrdinaryEqualsCanonicalProviderW475 hfields hordinaryMap)
    (hselected :
      ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
        (cs : Cocone S), IsColimit cs →
          IsColimit (selectedForgottenTargetCokernelCofork S cs)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_walkingParallelPairOp_colimit_closure_of_w426Promotion_and_projectionFields_w475
    hfields hordinaryMap heq
    (projectionFieldsProvider_of_selectedCokernelColimitProvider_w491 hselected)

/-- Checked nonterminal state for W491. -/
structure ProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 :
    Type where
  seed : String
  declarations : List String
  projectionFieldNarrowingResult : String
  exactAcyclicWrapperResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W491 state. -/
def currentProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 :
    ProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 where
  seed := supportSeedW491
  declarations :=
    ["selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491",
      "selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491",
      "projectionFieldsProvider_of_selectedCokernelColimitProvider_w491",
      "exactAcyclic_of_w426Promotion_and_selectedCokernelColimitProvider_w491"]
  projectionFieldNarrowingResult := "proved"
  exactAcyclicWrapperResult := "proved"
  remainingInputs :=
    ["construct W426PromotionFieldsProviderW475",
      "construct W426OrdinaryMapProviderW475",
      "construct W426OrdinaryEqualsCanonicalProviderW475",
      "construct selected forgotten-target cokernel colimit provider, e.g. from W435 preservation"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW491State :
    ProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491 :=
  currentProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportStateW491

theorem currentProjectionFieldsFromSelectedCokernelColimitStateW491_productSuccess :
    currentW491State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW491
#check selectedMappedCokernelColimitOfSelectedForgottenTargetCokernel_w491
#check selectedProjectionComponentIsColimitInputs_of_selectedCokernelColimit_w491
#check projectionFieldsProvider_of_selectedCokernelColimitProvider_w491
#check exactAcyclic_of_w426Promotion_and_selectedCokernelColimitProvider_w491
#check currentProjectionFieldsFromSelectedCokernelColimitStateW491_productSuccess

end Checks

end WppOpProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportW491

namespace WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492

open WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480
open WppOpProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportW491
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W492 W480/W491 composition route. -/
def supportSeedW492 : String :=
  "w492-w480-split-provider-selected-cokernel-colimit"

/-- Provider for the selected forgotten-target cokernel colimit used by W491. -/
abbrev SelectedCokernelColimitProviderW492 :=
  ∀ (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S), IsColimit cs →
      IsColimit
        (AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464.selectedForgottenTargetCokernelCofork
          S cs)

/--
W492 endpoint: W480 split providers supply W475's W426 promotion data, while
W491 turns one selected forgotten-target cokernel colimit provider into the
projection fields consumed by W475.
-/
theorem exactAcyclic_of_w480_splitProviders_and_selectedCokernelColimit_w492
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w426Promotion_and_selectedCokernelColimitProvider_w491
    (w426PromotionFieldsProvider_of_w480 hinputs hordinaryMap)
    (w426OrdinaryMapProvider_of_w480 hinputs hordinaryMap)
    (w426OrdinaryEqualsCanonicalProvider_of_w480 hinputs hordinaryMap)
    (fun S cs hcs => hselected S cs hcs)

/-- Checked nonterminal state for W492. -/
structure W480SplitProvidersSelectedCokernelColimitV370SupportStateW492 : Type where
  seed : String
  declarations : List String
  exactAcyclicResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W492 state. -/
def currentW480SplitProvidersSelectedCokernelColimitV370SupportStateW492 :
    W480SplitProvidersSelectedCokernelColimitV370SupportStateW492 where
  seed := supportSeedW492
  declarations :=
    ["SelectedCokernelColimitProviderW492",
      "exactAcyclic_of_w480_splitProviders_and_selectedCokernelColimit_w492"]
  exactAcyclicResult := "proved"
  remainingInputs :=
    ["construct concrete W461ToW475PromotionInputsProviderW480",
      "construct concrete W461ToW475OrdinaryMapProviderW480",
      "construct concrete SelectedCokernelColimitProviderW492"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW492State :
    W480SplitProvidersSelectedCokernelColimitV370SupportStateW492 :=
  currentW480SplitProvidersSelectedCokernelColimitV370SupportStateW492

theorem currentW480SplitProvidersSelectedCokernelColimitStateW492_productSuccess :
    currentW492State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW492
#check SelectedCokernelColimitProviderW492
#check exactAcyclic_of_w480_splitProviders_and_selectedCokernelColimit_w492
#check currentW480SplitProvidersSelectedCokernelColimitStateW492_productSuccess

end Checks

end WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492

namespace WppOpSelectedCokernelColimitFromPreservationV370SupportW493

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492

/-- Reproducible support seed for the W493 selected-cokernel preservation route. -/
def supportSeedW493 : String :=
  "w493-selected-cokernel-colimit-from-shortcomplex-preservation"

/-- The ordinary forgotten diagram associated to the WPP-op short-complex diagram. -/
abbrev selectedForgottenTargetOrdinaryDiagramW493
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ ShortComplex AddCommGrpCat.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ S ⋙ forgottenShortComplexFunctor

/-- The selected forgotten target cofork before turning it into a cokernel cofork. -/
def selectedForgottenTargetCoforkW493
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cofork (selectedForgottenLeft S) (selectedForgottenRight S) :=
  Cofork.ofπ (selectedForgottenTargetCoconeLeg S cs) (by
    change
      forgottenShortComplexFunctor.map (selectedMetrizableLeft S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs) =
        forgottenShortComplexFunctor.map (selectedMetrizableRight S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs)
    rw [← forgottenShortComplexFunctor.map_comp, ← forgottenShortComplexFunctor.map_comp,
      selectedMetrizableTargetCoconeLeg_parallel_pair S cs])

/-- The forgotten cocone over the ordinary `WalkingParallelPair`. -/
def selectedForgottenTargetMappedCoconeW493
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (selectedForgottenTargetOrdinaryDiagramW493 S) where
  pt := cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})
  ι :=
    { app := fun j =>
        forgottenShortComplexFunctor.map
          (cs.ι.app (walkingParallelPairOpEquiv.functor.obj j))
      naturality := fun {j j'} f => by
        simpa only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
          Functor.const_obj_map, Category.comp_id] using
          congrArg forgottenShortComplexFunctor.map
            (cs.w (walkingParallelPairOpEquiv.functor.map f)) }

/-- The mapped ordinary cocone is the selected cofork after the parallel-pair iso. -/
def selectedForgottenTargetMappedCoconeIsoPrecomposeCoforkW493
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedForgottenTargetMappedCoconeW493 S cs ≅
      (Cocone.precompose
        (diagramIsoParallelPair (selectedForgottenTargetOrdinaryDiagramW493 S)).hom).obj
        (selectedForgottenTargetCoforkW493 S cs) :=
  Cocone.ext (Iso.refl _) (fun j => by
    cases j
    · simp only [Iso.refl_hom]
      change
        forgottenShortComplexFunctor.map
            (cs.ι.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero)) =
          forgottenShortComplexFunctor.map
              (S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)) ≫
            forgottenShortComplexFunctor.map
              (cs.ι.app (walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one))
      rw [← forgottenShortComplexFunctor.map_comp]
      exact congrArg forgottenShortComplexFunctor.map
        (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).symm
    · rfl)

/-- A colimit proof for the mapped ordinary cocone gives the selected cofork colimit. -/
def selectedForgottenTargetCoforkColimitOfMappedCoconeW493
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hMapped : IsColimit (selectedForgottenTargetMappedCoconeW493 S cs)) :
    IsColimit (selectedForgottenTargetCoforkW493 S cs) := by
  let hPre :
      IsColimit
        ((Cocone.precompose
          (diagramIsoParallelPair (selectedForgottenTargetOrdinaryDiagramW493 S)).hom).obj
          (selectedForgottenTargetCoforkW493 S cs)) :=
    IsColimit.ofIsoColimit hMapped
      (selectedForgottenTargetMappedCoconeIsoPrecomposeCoforkW493 S cs)
  exact
    (IsColimit.precomposeHomEquiv
      (diagramIsoParallelPair (selectedForgottenTargetOrdinaryDiagramW493 S))
      (selectedForgottenTargetCoforkW493 S cs)) hPre

/-- A mapped-cocone colimit proof gives the selected forgotten-target cokernel colimit. -/
def selectedForgottenTargetCokernelColimitOfMappedCoconeW493
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hMapped : IsColimit (selectedForgottenTargetMappedCoconeW493 S cs)) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) :=
  IsColimit.ofIsoColimit
    (Preadditive.isColimitCokernelCoforkOfCofork
      (selectedForgottenTargetCoforkColimitOfMappedCoconeW493 S cs hMapped))
    (Cofork.ext (Iso.refl _) (by
      simp [selectedForgottenTargetCokernelCofork, selectedForgottenTargetCoforkW493]))

/-- The mapped ordinary cocone is colimit if the short-complex forgetful functor preserves `S`. -/
def selectedForgottenTargetMappedCoconeIsColimitOfPreservesW493
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    [PreservesColimit S forgottenShortComplexFunctor]
    (hcs : IsColimit cs) :
    IsColimit (selectedForgottenTargetMappedCoconeW493 S cs) := by
  change
    IsColimit
      ((forgottenShortComplexFunctor.mapCocone cs).whisker
        walkingParallelPairOpEquiv.functor)
  exact
    (PreservesColimit.preserves (F := forgottenShortComplexFunctor) hcs).some.whiskerEquivalence
      walkingParallelPairOpEquiv

/--
W493 provider: shape-level preservation by the short-complex forgetful functor
supplies W492's selected forgotten-target cokernel colimit provider.
-/
def selectedCokernelColimitProvider_of_shortComplexPreservesWppOpColimits_w493
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor] :
    SelectedCokernelColimitProviderW492 :=
  fun S cs hcs =>
    selectedForgottenTargetCokernelColimitOfMappedCoconeW493 S cs
      (selectedForgottenTargetMappedCoconeIsColimitOfPreservesW493 S cs hcs)

/-- W493 checked nonterminal state. -/
structure SelectedCokernelColimitFromPreservationV370SupportStateW493 : Type where
  seed : String
  declarations : List String
  selectedProviderResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W493 state. -/
def currentSelectedCokernelColimitFromPreservationV370SupportStateW493 :
    SelectedCokernelColimitFromPreservationV370SupportStateW493 where
  seed := supportSeedW493
  declarations :=
    ["selectedForgottenTargetCokernelColimitOfMappedCoconeW493",
      "selectedForgottenTargetMappedCoconeIsColimitOfPreservesW493",
      "selectedCokernelColimitProvider_of_shortComplexPreservesWppOpColimits_w493"]
  selectedProviderResult := "proved"
  remainingInputs :=
    ["prove PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor",
      "construct concrete W480 promotion and ordinary-map providers"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW493State :
    SelectedCokernelColimitFromPreservationV370SupportStateW493 :=
  currentSelectedCokernelColimitFromPreservationV370SupportStateW493

theorem currentSelectedCokernelColimitFromPreservationStateW493_productSuccess :
    currentW493State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW493
#check selectedForgottenTargetCokernelColimitOfMappedCoconeW493
#check selectedForgottenTargetMappedCoconeIsColimitOfPreservesW493
#check selectedCokernelColimitProvider_of_shortComplexPreservesWppOpColimits_w493
#check currentSelectedCokernelColimitFromPreservationStateW493_productSuccess

end Checks

end WppOpSelectedCokernelColimitFromPreservationV370SupportW493

namespace WppOpW480SplitProvidersShortComplexPreservationV370SupportW494

open WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpSelectedCokernelColimitFromPreservationV370SupportW493
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W494 preservation endpoint. -/
def supportSeedW494 : String :=
  "w494-w480-split-providers-short-complex-preservation"

/--
W494 endpoint: W480 split providers plus WPP-op colimit preservation by the
short-complex forgetful functor imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_w480_splitProviders_and_shortComplexPreservesWppOpColimits_w494
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor] :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_w480_splitProviders_and_selectedCokernelColimit_w492
    hinputs hordinaryMap
    selectedCokernelColimitProvider_of_shortComplexPreservesWppOpColimits_w493

/-- W494 checked nonterminal state. -/
structure W480SplitProvidersShortComplexPreservationV370SupportStateW494 : Type where
  seed : String
  declarations : List String
  preservationEndpointResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W494 state. -/
def currentW480SplitProvidersShortComplexPreservationV370SupportStateW494 :
    W480SplitProvidersShortComplexPreservationV370SupportStateW494 where
  seed := supportSeedW494
  declarations :=
    ["exactAcyclic_of_w480_splitProviders_and_shortComplexPreservesWppOpColimits_w494"]
  preservationEndpointResult := "proved"
  remainingInputs :=
    ["construct concrete W461ToW475PromotionInputsProviderW480",
      "construct concrete W461ToW475OrdinaryMapProviderW480",
      "prove PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW494State :
    W480SplitProvidersShortComplexPreservationV370SupportStateW494 :=
  currentW480SplitProvidersShortComplexPreservationV370SupportStateW494

theorem currentW480SplitProvidersShortComplexPreservationStateW494_productSuccess :
    currentW494State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW494
#check exactAcyclic_of_w480_splitProviders_and_shortComplexPreservesWppOpColimits_w494
#check currentW480SplitProvidersShortComplexPreservationStateW494_productSuccess

end Checks

end WppOpW480SplitProvidersShortComplexPreservationV370SupportW494

namespace WppOpShortComplexPreservationFromUnderlyingV370SupportW495

open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464

/-- Reproducible support seed for the W495 preservation reduction. -/
def supportSeedW495 : String :=
  "w495-short-complex-preservation-from-underlying"

/-- Local name for the underlying forgetful functor. -/
abbrev underlyingForgetfulFunctorW495 : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/--
Generic bridge: colimit preservation by an underlying functor supplies colimit
preservation by the induced short-complex functor.
-/
@[reducible]
def mapShortComplexPreservesColimitsOfShapeOfUnderlyingW495
    {J C D : Type*} [Category J] [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    [PreservesColimitsOfShape J F] :
    PreservesColimitsOfShape J F.mapShortComplex where
  preservesColimit {K} :=
    preservesColimit_of_preserves_colimit_cocone
      (ShortComplex.isColimitColimitCocone K)
      (by
        refine ShortComplex.isColimitOfIsColimitπ _ ?_ ?_ ?_
        · change IsColimit (F.mapCocone (ShortComplex.π₁.mapCocone (ShortComplex.colimitCocone K)))
          exact isColimitOfPreserves F
            (isColimitOfPreserves (ShortComplex.π₁ : ShortComplex C ⥤ C)
              (ShortComplex.isColimitColimitCocone K))
        · change IsColimit (F.mapCocone (ShortComplex.π₂.mapCocone (ShortComplex.colimitCocone K)))
          exact isColimitOfPreserves F
            (isColimitOfPreserves (ShortComplex.π₂ : ShortComplex C ⥤ C)
              (ShortComplex.isColimitColimitCocone K))
        · change IsColimit (F.mapCocone (ShortComplex.π₃.mapCocone (ShortComplex.colimitCocone K)))
          exact isColimitOfPreserves F
            (isColimitOfPreserves (ShortComplex.π₃ : ShortComplex C ⥤ C)
              (ShortComplex.isColimitColimitCocone K)))

/--
Underlying WPP-op colimit preservation supplies W493's short-complex
preservation input.
-/
@[reducible]
def forgottenShortComplexPreservesWppOpColimitsOfUnderlyingW495
    [HasColimitsOfShape WalkingParallelPairᵒᵖ MetrizableLCA.{0}]
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctorW495] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
  mapShortComplexPreservesColimitsOfShapeOfUnderlyingW495
    (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0})

/-- Finite-colimit preservation implies the needed underlying WPP-op preservation. -/
theorem underlyingForgetfulPreservesWppOpColimitsOfShapeOfFiniteW495
    [PreservesFiniteColimits underlyingForgetfulFunctorW495] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctorW495 :=
  inferInstance

/-- Finite-colimit preservation supplies W493's short-complex preservation input. -/
@[reducible]
def forgottenShortComplexPreservesWppOpColimitsOfFiniteW495
    [PreservesFiniteColimits underlyingForgetfulFunctorW495] :
    PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor := by
  haveI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ underlyingForgetfulFunctorW495 :=
    underlyingForgetfulPreservesWppOpColimitsOfShapeOfFiniteW495
  exact forgottenShortComplexPreservesWppOpColimitsOfUnderlyingW495

/-- W495 checked nonterminal state. -/
structure ShortComplexPreservationFromUnderlyingV370SupportStateW495 : Type where
  seed : String
  declarations : List String
  preservationReductionResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W495 state. -/
def currentShortComplexPreservationFromUnderlyingV370SupportStateW495 :
    ShortComplexPreservationFromUnderlyingV370SupportStateW495 where
  seed := supportSeedW495
  declarations :=
    ["mapShortComplexPreservesColimitsOfShapeOfUnderlyingW495",
      "forgottenShortComplexPreservesWppOpColimitsOfUnderlyingW495",
      "underlyingForgetfulPreservesWppOpColimitsOfShapeOfFiniteW495",
      "forgottenShortComplexPreservesWppOpColimitsOfFiniteW495"]
  preservationReductionResult := "proved"
  remainingInputs :=
    ["prove PreservesFiniteColimits (forget₂ MetrizableLCA AddCommGrpCat)",
      "construct concrete W461ToW475PromotionInputsProviderW480",
      "construct concrete W461ToW475OrdinaryMapProviderW480"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW495State :
    ShortComplexPreservationFromUnderlyingV370SupportStateW495 :=
  currentShortComplexPreservationFromUnderlyingV370SupportStateW495

theorem currentShortComplexPreservationFromUnderlyingStateW495_productSuccess :
    currentW495State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW495
#check mapShortComplexPreservesColimitsOfShapeOfUnderlyingW495
#check forgottenShortComplexPreservesWppOpColimitsOfUnderlyingW495
#check underlyingForgetfulPreservesWppOpColimitsOfShapeOfFiniteW495
#check forgottenShortComplexPreservesWppOpColimitsOfFiniteW495
#check currentShortComplexPreservationFromUnderlyingStateW495_productSuccess

end Checks

end WppOpShortComplexPreservationFromUnderlyingV370SupportW495

namespace WppOpW480SplitProvidersFinitePreservationV370SupportW496

open WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480
open WppOpW480SplitProvidersShortComplexPreservationV370SupportW494
open WppOpShortComplexPreservationFromUnderlyingV370SupportW495
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W496 finite-preservation endpoint. -/
def supportSeedW496 : String :=
  "w496-w480-split-providers-finite-preservation"

/--
W496 endpoint: W480 split providers plus finite-colimit preservation by the
underlying forgetful functor imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_w480_splitProviders_and_underlyingPreservesFiniteColimits_w496
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    [PreservesFiniteColimits underlyingForgetfulFunctorW495] :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  haveI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
    forgottenShortComplexPreservesWppOpColimitsOfFiniteW495
  exact
    exactAcyclic_of_w480_splitProviders_and_shortComplexPreservesWppOpColimits_w494
      hinputs hordinaryMap

/-- W496 checked nonterminal state. -/
structure W480SplitProvidersFinitePreservationV370SupportStateW496 : Type where
  seed : String
  declarations : List String
  finitePreservationEndpointResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W496 state. -/
def currentW480SplitProvidersFinitePreservationV370SupportStateW496 :
    W480SplitProvidersFinitePreservationV370SupportStateW496 where
  seed := supportSeedW496
  declarations :=
    ["exactAcyclic_of_w480_splitProviders_and_underlyingPreservesFiniteColimits_w496"]
  finitePreservationEndpointResult := "proved"
  remainingInputs :=
    ["construct concrete W461ToW475PromotionInputsProviderW480",
      "construct concrete W461ToW475OrdinaryMapProviderW480",
      "prove PreservesFiniteColimits (forget₂ MetrizableLCA AddCommGrpCat)"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW496State :
    W480SplitProvidersFinitePreservationV370SupportStateW496 :=
  currentW480SplitProvidersFinitePreservationV370SupportStateW496

theorem currentW480SplitProvidersFinitePreservationStateW496_productSuccess :
    currentW496State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW496
#check exactAcyclic_of_w480_splitProviders_and_underlyingPreservesFiniteColimits_w496
#check currentW480SplitProvidersFinitePreservationStateW496_productSuccess

end Checks

end WppOpW480SplitProvidersFinitePreservationV370SupportW496

namespace WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497

open WppOpW461BridgeToW475ProjectionExactAcyclicV370SupportW480
open WppOpShortComplexPreservationFromUnderlyingV370SupportW495
open WppOpW480SplitProvidersFinitePreservationV370SupportW496
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W497 forgetful finite-preservation route. -/
def supportSeedW497 : String :=
  "w497-forgetful-finite-preservation-from-cokernels"

/-- The explicit local cokernel cofork before forgetting topology. -/
def explicitMetrizableCokernelCoforkW497 {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (MetrizableLCA.cokernelπ f) (MetrizableLCA.comp_cokernelπ f)

/-- The existing quotient/cokernel API proves the explicit cofork is colimiting. -/
def explicitMetrizableCokernelCoforkIsColimitW497
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    IsColimit (explicitMetrizableCokernelCoforkW497 f) :=
  MetrizableLCA.cokernelIsColimit f

/-- The mapped explicit cokernel cocone after forgetting topology. -/
def mappedExplicitCokernelCoconeW497 {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Cocone (parallelPair f 0 ⋙ underlyingForgetfulFunctorW495) :=
  underlyingForgetfulFunctorW495.mapCocone (explicitMetrizableCokernelCoforkW497 f)

/-- The mapped explicit cokernel leg at `one` is the forgotten quotient projection. -/
theorem mappedExplicitCokernelCocone_ι_oneW497
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelCoconeW497 f).ι.app WalkingParallelPair.one =
      underlyingForgetfulFunctorW495.map (MetrizableLCA.cokernelπ f) :=
  rfl

/-- Preservation of one cokernel follows from the mapped explicit cofork colimit proof. -/
@[reducible]
def preservesCokernelOfMappedExplicitCokernelCoconeIsColimitW497
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hMapped : IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctorW495 :=
  preservesColimit_of_preserves_colimit_cocone
    (explicitMetrizableCokernelCoforkIsColimitW497 f) hMapped

/-- If every mapped explicit cokernel cofork is colimiting, all cokernels are preserved. -/
@[reducible]
def preservesAllCokernelsOfMappedExplicitCokernelCoconesW497
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) underlyingForgetfulFunctorW495 :=
  fun f => preservesCokernelOfMappedExplicitCokernelCoconeIsColimitW497 f (hMapped f)

/--
The mapped explicit cokernel-cofork input supplies finite-colimit preservation by
the underlying forgetful functor.
-/
theorem underlyingForgetfulPreservesFiniteColimitsOfMappedExplicitCokernelCoforksW497
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    PreservesFiniteColimits underlyingForgetfulFunctorW495 := by
  haveI : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) underlyingForgetfulFunctorW495 :=
    preservesAllCokernelsOfMappedExplicitCokernelCoconesW497 hMapped
  exact CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels
    underlyingForgetfulFunctorW495

/--
W497 endpoint: W480 split providers plus mapped explicit cokernel cofork
colimit proofs imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_w480_splitProviders_and_mappedExplicitCokernelCoforks_w497
    (hinputs : W461ToW475PromotionInputsProviderW480)
    (hordinaryMap : W461ToW475OrdinaryMapProviderW480)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  haveI : PreservesFiniteColimits underlyingForgetfulFunctorW495 :=
    underlyingForgetfulPreservesFiniteColimitsOfMappedExplicitCokernelCoforksW497 hMapped
  exact
    exactAcyclic_of_w480_splitProviders_and_underlyingPreservesFiniteColimits_w496
      hinputs hordinaryMap

/-- W497 checked nonterminal state. -/
structure ForgetfulFinitePreservationFromCokernelsV370SupportStateW497 : Type where
  seed : String
  declarations : List String
  finitePreservationRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W497 state. -/
def currentForgetfulFinitePreservationFromCokernelsV370SupportStateW497 :
    ForgetfulFinitePreservationFromCokernelsV370SupportStateW497 where
  seed := supportSeedW497
  declarations :=
    ["explicitMetrizableCokernelCoforkW497",
      "mappedExplicitCokernelCoconeW497",
      "underlyingForgetfulPreservesFiniteColimitsOfMappedExplicitCokernelCoforksW497",
      "exactAcyclic_of_w480_splitProviders_and_mappedExplicitCokernelCoforks_w497"]
  finitePreservationRouteResult := "proved"
  remainingInputs :=
    ["construct concrete W461ToW475PromotionInputsProviderW480",
      "construct concrete W461ToW475OrdinaryMapProviderW480",
      "prove every mapped explicit MetrizableLCA cokernel cofork is colimiting in AddCommGrpCat"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW497State :
    ForgetfulFinitePreservationFromCokernelsV370SupportStateW497 :=
  currentForgetfulFinitePreservationFromCokernelsV370SupportStateW497

theorem currentForgetfulFinitePreservationFromCokernelsStateW497_productSuccess :
    currentW497State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW497
#check explicitMetrizableCokernelCoforkW497
#check explicitMetrizableCokernelCoforkIsColimitW497
#check mappedExplicitCokernelCoconeW497
#check mappedExplicitCokernelCocone_ι_oneW497
#check preservesCokernelOfMappedExplicitCokernelCoconeIsColimitW497
#check preservesAllCokernelsOfMappedExplicitCokernelCoconesW497
#check underlyingForgetfulPreservesFiniteColimitsOfMappedExplicitCokernelCoforksW497
#check exactAcyclic_of_w480_splitProviders_and_mappedExplicitCokernelCoforks_w497
#check currentForgetfulFinitePreservationFromCokernelsStateW497_productSuccess

end Checks

end WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497

namespace WppOpSelectedW461ProviderSelectedCokernelColimitV370SupportW498

open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open WppOpProjectionFieldsFromSelectedCokernelColimitCurrentHeadV370SupportW491
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W498 selected-provider/cokernel-colimit route. -/
def supportSeedW498 : String :=
  "w498-selected-w461-provider-selected-cokernel-colimit"

/--
W498 endpoint: the single selected W461 provider from W483 can use W491's selected
cokernel-colimit narrowing without the W480 split-provider surface.
-/
def exactAcyclic_of_selectedW461Provider_and_selectedCokernelColimit_w498
    (hinputs : SelectedW461PromotionInputsProviderW483)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_projectionFields_w483 hinputs
    (projectionFieldsProvider_of_selectedCokernelColimitProvider_w491 hselected)

/-- W498 checked nonterminal state. -/
structure SelectedW461ProviderSelectedCokernelColimitV370SupportStateW498 : Type where
  seed : String
  declarations : List String
  selectedProviderRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W498 state. -/
def currentSelectedW461ProviderSelectedCokernelColimitV370SupportStateW498 :
    SelectedW461ProviderSelectedCokernelColimitV370SupportStateW498 where
  seed := supportSeedW498
  declarations :=
    ["exactAcyclic_of_selectedW461Provider_and_selectedCokernelColimit_w498"]
  selectedProviderRouteResult := "proved"
  remainingInputs :=
    ["construct concrete SelectedW461PromotionInputsProviderW483",
      "construct concrete SelectedCokernelColimitProviderW492"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW498State :
    SelectedW461ProviderSelectedCokernelColimitV370SupportStateW498 :=
  currentSelectedW461ProviderSelectedCokernelColimitV370SupportStateW498

theorem currentSelectedW461ProviderSelectedCokernelColimitStateW498_productSuccess :
    currentW498State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW498
#check exactAcyclic_of_selectedW461Provider_and_selectedCokernelColimit_w498
#check currentSelectedW461ProviderSelectedCokernelColimitStateW498_productSuccess

end Checks

end WppOpSelectedW461ProviderSelectedCokernelColimitV370SupportW498

namespace WppOpSelectedW461ProviderPreservationRoutesV370SupportW499

open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open WppOpSelectedW461ProviderSelectedCokernelColimitV370SupportW498
open WppOpSelectedCokernelColimitFromPreservationV370SupportW493
open WppOpShortComplexPreservationFromUnderlyingV370SupportW495
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open AddCommGrpRowFieldsProjectionKernelBoundaryV370SupportW464
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for selected-provider preservation routes. -/
def supportSeedW499 : String :=
  "w499-selected-w461-provider-preservation-routes"

/--
W499 endpoint: a selected W461 provider plus WPP-op colimit preservation by the
short-complex forgetful functor imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_selectedW461Provider_and_shortComplexPreservesWppOpColimits_w499
    (hinputs : SelectedW461PromotionInputsProviderW483)
    [PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor] :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_selectedCokernelColimit_w498 hinputs
    selectedCokernelColimitProvider_of_shortComplexPreservesWppOpColimits_w493

/--
Finite-colimit preservation by the underlying forgetful functor supplies the W499
short-complex preservation endpoint.
-/
def exactAcyclic_of_selectedW461Provider_and_underlyingPreservesFiniteColimits_w499
    (hinputs : SelectedW461PromotionInputsProviderW483)
    [PreservesFiniteColimits underlyingForgetfulFunctorW495] :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  haveI : PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor :=
    forgottenShortComplexPreservesWppOpColimitsOfFiniteW495
  exact
    exactAcyclic_of_selectedW461Provider_and_shortComplexPreservesWppOpColimits_w499
      hinputs

/--
The W497 mapped-explicit-cokernel input also feeds the selected-provider route,
avoiding the W480 split-provider pair.
-/
def exactAcyclic_of_selectedW461Provider_and_mappedExplicitCokernelCoforks_w499
    (hinputs : SelectedW461PromotionInputsProviderW483)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure := by
  haveI : PreservesFiniteColimits underlyingForgetfulFunctorW495 :=
    underlyingForgetfulPreservesFiniteColimitsOfMappedExplicitCokernelCoforksW497 hMapped
  exact
    exactAcyclic_of_selectedW461Provider_and_underlyingPreservesFiniteColimits_w499
      hinputs

/-- W499 checked nonterminal state. -/
structure SelectedW461ProviderPreservationRoutesV370SupportStateW499 : Type where
  seed : String
  declarations : List String
  shortComplexPreservationRouteResult : String
  finitePreservationRouteResult : String
  mappedCokernelRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W499 state. -/
def currentSelectedW461ProviderPreservationRoutesV370SupportStateW499 :
    SelectedW461ProviderPreservationRoutesV370SupportStateW499 where
  seed := supportSeedW499
  declarations :=
    ["exactAcyclic_of_selectedW461Provider_and_shortComplexPreservesWppOpColimits_w499",
      "exactAcyclic_of_selectedW461Provider_and_underlyingPreservesFiniteColimits_w499",
      "exactAcyclic_of_selectedW461Provider_and_mappedExplicitCokernelCoforks_w499"]
  shortComplexPreservationRouteResult := "proved"
  finitePreservationRouteResult := "proved"
  mappedCokernelRouteResult := "proved"
  remainingInputs :=
    ["construct concrete SelectedW461PromotionInputsProviderW483",
      "prove PreservesColimitsOfShape WalkingParallelPairᵒᵖ forgottenShortComplexFunctor, " ++
        "or prove the underlying finite-colimit/mapped-cokernel input"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW499State :
    SelectedW461ProviderPreservationRoutesV370SupportStateW499 :=
  currentSelectedW461ProviderPreservationRoutesV370SupportStateW499

theorem currentSelectedW461ProviderPreservationRoutesStateW499_productSuccess :
    currentW499State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW499
#check exactAcyclic_of_selectedW461Provider_and_shortComplexPreservesWppOpColimits_w499
#check exactAcyclic_of_selectedW461Provider_and_underlyingPreservesFiniteColimits_w499
#check exactAcyclic_of_selectedW461Provider_and_mappedExplicitCokernelCoforks_w499
#check currentSelectedW461ProviderPreservationRoutesStateW499_productSuccess

end Checks

end WppOpSelectedW461ProviderPreservationRoutesV370SupportW499

namespace WppOpSelectedW461PointIdentificationRouteV370SupportW500

open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpSelectedW461ProviderSelectedCokernelColimitV370SupportW498
open WppOpSelectedW461ProviderPreservationRoutesV370SupportW499
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W500 selected point-identification route. -/
def supportSeedW500 : String :=
  "w500-selected-w461-point-identification-route"

/--
Concrete call-site fields sufficient to build W483's selected W461 provider.
This exposes the remaining W461 input surface as point identifications, one
ordinary descended package, and the target-component-to-W318 leg theorem.
-/
structure SelectedW461PointIdentificationCallSiteInputsW500
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

/-- Provider surface for W500's concrete point-identification call-site fields. -/
abbrev SelectedW461PointIdentificationProviderW500 : Type 1 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              SelectedW461PointIdentificationCallSiteInputsW500 X Y α cx cy

/-- W500 call-site fields build W478's selected promotion input package. -/
def selectedW461PromotionInputs_of_pointIdentification_w500
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (H : SelectedW461PointIdentificationCallSiteInputsW500 X Y α cx cy) :
    W461ToW441PromotionInputsW478 X Y α cx cy where
  pointIdentificationInputs := H.pointIdentificationInputs
  targetComponentImpliesW318 := H.targetComponentImpliesW318
  ordinaryPackage := H.ordinaryPackage
  ordinaryDescended_eq := H.ordinaryDescended_eq

/-- W500 point-identification providers feed W483's selected W461 provider surface. -/
def selectedW461Provider_of_pointIdentification_w500
    (hpoint : SelectedW461PointIdentificationProviderW500) :
    SelectedW461PromotionInputsProviderW483 :=
  fun X Y α cx cy φ hcx hcy hclosed hcompat =>
    selectedW461PromotionInputs_of_pointIdentification_w500
      (hpoint X Y α cx cy φ hcx hcy hclosed hcompat)

/--
W500 endpoint: point-identification call-site fields plus the selected cokernel
colimit provider imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_selectedW461PointIdentification_and_selectedCokernelColimit_w500
    (hpoint : SelectedW461PointIdentificationProviderW500)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_selectedCokernelColimit_w498
    (selectedW461Provider_of_pointIdentification_w500 hpoint) hselected

/--
W500 endpoint with W499's mapped-explicit-cokernel preservation input.
-/
def exactAcyclic_of_selectedW461PointIdentification_and_mappedExplicitCokernelCoforks_w500
    (hpoint : SelectedW461PointIdentificationProviderW500)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461Provider_and_mappedExplicitCokernelCoforks_w499
    (selectedW461Provider_of_pointIdentification_w500 hpoint) hMapped

/-- W500 checked nonterminal state. -/
structure SelectedW461PointIdentificationRouteV370SupportStateW500 : Type where
  seed : String
  declarations : List String
  providerAdapterResult : String
  selectedCokernelRouteResult : String
  mappedCokernelRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W500 state. -/
def currentSelectedW461PointIdentificationRouteV370SupportStateW500 :
    SelectedW461PointIdentificationRouteV370SupportStateW500 where
  seed := supportSeedW500
  declarations :=
    ["SelectedW461PointIdentificationCallSiteInputsW500",
      "SelectedW461PointIdentificationProviderW500",
      "selectedW461PromotionInputs_of_pointIdentification_w500",
      "selectedW461Provider_of_pointIdentification_w500",
      "exactAcyclic_of_selectedW461PointIdentification_and_selectedCokernelColimit_w500",
      "exactAcyclic_of_selectedW461PointIdentification_and_mappedExplicitCokernelCoforks_w500"]
  providerAdapterResult := "proved"
  selectedCokernelRouteResult := "proved"
  mappedCokernelRouteResult := "proved"
  remainingInputs :=
    ["construct concrete SelectedW461PointIdentificationProviderW500",
      "prove the selected cokernel-colimit or mapped-cokernel preservation input"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW500State :
    SelectedW461PointIdentificationRouteV370SupportStateW500 :=
  currentSelectedW461PointIdentificationRouteV370SupportStateW500

theorem currentSelectedW461PointIdentificationRouteStateW500_productSuccess :
    currentW500State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW500
#check SelectedW461PointIdentificationCallSiteInputsW500
#check SelectedW461PointIdentificationProviderW500
#check selectedW461PromotionInputs_of_pointIdentification_w500
#check selectedW461Provider_of_pointIdentification_w500
#check exactAcyclic_of_selectedW461PointIdentification_and_selectedCokernelColimit_w500
#check exactAcyclic_of_selectedW461PointIdentification_and_mappedExplicitCokernelCoforks_w500
#check currentSelectedW461PointIdentificationRouteStateW500_productSuccess

end Checks

end WppOpSelectedW461PointIdentificationRouteV370SupportW500

namespace WppOpSelectedW461ConcreteLegRouteV370SupportW501

open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpSelectedW461ProviderSelectedCokernelColimitV370SupportW498
open WppOpSelectedW461ProviderPreservationRoutesV370SupportW499
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open WppOpSelectedW461PointIdentificationRouteV370SupportW500
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W501 concrete-leg route. -/
def supportSeedW501 : String :=
  "w501-selected-w461-concrete-leg-route"

/--
Concrete point-identification fields plus the full W318 leg theorem for the
conjugated descended map.
-/
structure SelectedW461ConcreteLegCallSiteInputsW501
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) : Type 1 where
  pointIdentificationInputs :
    W461TargetLegPointIdentificationInputsW478 X Y α cx cy
  concreteLegCompatibility :
    W318ColimitMapLegCompatibilityW441 X Y α cx cy
      (concreteConjugatedDescendedW478 pointIdentificationInputs)
  ordinaryPackage :
    W426OrdinaryDescendedMapPackage pointIdentificationInputs.ordinaryMap
  ordinaryDescended_eq :
    ordinaryPackage.ordinaryDescended =
      pointIdentificationInputs.ordinaryDescended

/-- Provider surface for W501 concrete W318 leg-compatibility inputs. -/
abbrev SelectedW461ConcreteLegProviderW501 : Type 1 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              SelectedW461ConcreteLegCallSiteInputsW501 X Y α cx cy

/-- W501 concrete-leg fields build W500 point-identification call-site fields. -/
def selectedPointIdentificationInputs_of_concreteLeg_w501
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (H : SelectedW461ConcreteLegCallSiteInputsW501 X Y α cx cy) :
    SelectedW461PointIdentificationCallSiteInputsW500 X Y α cx cy where
  pointIdentificationInputs := H.pointIdentificationInputs
  targetComponentImpliesW318 := fun _htarget => H.concreteLegCompatibility
  ordinaryPackage := H.ordinaryPackage
  ordinaryDescended_eq := H.ordinaryDescended_eq

/-- W501 concrete-leg providers feed W500's selected point-identification route. -/
def selectedPointIdentificationProvider_of_concreteLeg_w501
    (hleg : SelectedW461ConcreteLegProviderW501) :
    SelectedW461PointIdentificationProviderW500 :=
  fun X Y α cx cy φ hcx hcy hclosed hcompat =>
    selectedPointIdentificationInputs_of_concreteLeg_w501
      (hleg X Y α cx cy φ hcx hcy hclosed hcompat)

/--
W501 endpoint: concrete point-identification leg compatibility plus the selected
cokernel-colimit provider imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_selectedW461ConcreteLeg_and_selectedCokernelColimit_w501
    (hleg : SelectedW461ConcreteLegProviderW501)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461PointIdentification_and_selectedCokernelColimit_w500
    (selectedPointIdentificationProvider_of_concreteLeg_w501 hleg) hselected

/--
W501 endpoint with W499's mapped-explicit-cokernel preservation input.
-/
def exactAcyclic_of_selectedW461ConcreteLeg_and_mappedExplicitCokernelCoforks_w501
    (hleg : SelectedW461ConcreteLegProviderW501)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461PointIdentification_and_mappedExplicitCokernelCoforks_w500
    (selectedPointIdentificationProvider_of_concreteLeg_w501 hleg) hMapped

/-- W501 checked nonterminal state. -/
structure SelectedW461ConcreteLegRouteV370SupportStateW501 : Type where
  seed : String
  declarations : List String
  pointIdentificationAdapterResult : String
  selectedCokernelRouteResult : String
  mappedCokernelRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W501 state. -/
def currentSelectedW461ConcreteLegRouteV370SupportStateW501 :
    SelectedW461ConcreteLegRouteV370SupportStateW501 where
  seed := supportSeedW501
  declarations :=
    ["SelectedW461ConcreteLegCallSiteInputsW501",
      "SelectedW461ConcreteLegProviderW501",
      "selectedPointIdentificationInputs_of_concreteLeg_w501",
      "selectedPointIdentificationProvider_of_concreteLeg_w501",
      "exactAcyclic_of_selectedW461ConcreteLeg_and_selectedCokernelColimit_w501",
      "exactAcyclic_of_selectedW461ConcreteLeg_and_mappedExplicitCokernelCoforks_w501"]
  pointIdentificationAdapterResult := "proved"
  selectedCokernelRouteResult := "proved"
  mappedCokernelRouteResult := "proved"
  remainingInputs :=
    ["construct concrete SelectedW461ConcreteLegProviderW501",
      "prove the selected cokernel-colimit or mapped-cokernel preservation input"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW501State :
    SelectedW461ConcreteLegRouteV370SupportStateW501 :=
  currentSelectedW461ConcreteLegRouteV370SupportStateW501

theorem currentSelectedW461ConcreteLegRouteStateW501_productSuccess :
    currentW501State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW501
#check SelectedW461ConcreteLegCallSiteInputsW501
#check SelectedW461ConcreteLegProviderW501
#check selectedPointIdentificationInputs_of_concreteLeg_w501
#check selectedPointIdentificationProvider_of_concreteLeg_w501
#check exactAcyclic_of_selectedW461ConcreteLeg_and_selectedCokernelColimit_w501
#check exactAcyclic_of_selectedW461ConcreteLeg_and_mappedExplicitCokernelCoforks_w501
#check currentSelectedW461ConcreteLegRouteStateW501_productSuccess

end Checks

end WppOpSelectedW461ConcreteLegRouteV370SupportW501

namespace WppOpSelectedW461W451StyleRouteV370SupportW502

open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpSingleW461ProviderComponentwiseProjectionV370SupportW483
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpSelectedW461ProviderSelectedCokernelColimitV370SupportW498
open WppOpSelectedW461ProviderPreservationRoutesV370SupportW499
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open WppOpSelectedW461PointIdentificationRouteV370SupportW500
open WppOpSelectedW461ConcreteLegRouteV370SupportW501
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W502 W451-style route. -/
def supportSeedW502 : String :=
  "w502-selected-w461-w451-style-route"

/--
Raw W451-style call-site fields for the selected W461 point-identification map.
These are the quotient-map compatibility, the two point identifications, and the
full W318 leg theorem for their conjugated descended map.
-/
structure SelectedW461W451StyleCallSiteInputsW502
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
  concreteLegCompatibility :
    W318ColimitMapLegCompatibilityW441 X Y α cx cy
      (sourcePointIdentification.inv ≫ ordinaryDescended ≫ targetPointIdentification.hom)
  ordinaryPackage : W426OrdinaryDescendedMapPackage ordinaryMap
  ordinaryDescended_eq :
    ordinaryPackage.ordinaryDescended = ordinaryDescended

/-- Build W478 point-identification inputs from W502's raw W451-style fields. -/
def pointIdentificationInputs_of_w451Style_w502
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (H : SelectedW461W451StyleCallSiteInputsW502 X Y α cx cy) :
    W461TargetLegPointIdentificationInputsW478 X Y α cx cy where
  ordinaryMap := H.ordinaryMap
  ordinaryDescended := H.ordinaryDescended
  sourcePointIdentification := H.sourcePointIdentification
  targetPointIdentification := H.targetPointIdentification
  quotient_compat := H.quotient_compat
  sourcePointIdentification_target_leg := H.sourcePointIdentification_target_leg
  targetPointIdentification_target_leg := H.targetPointIdentification_target_leg

/-- W502 raw fields build W501 concrete-leg call-site fields. -/
def selectedConcreteLegInputs_of_w451Style_w502
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (H : SelectedW461W451StyleCallSiteInputsW502 X Y α cx cy) :
    SelectedW461ConcreteLegCallSiteInputsW501 X Y α cx cy where
  pointIdentificationInputs := pointIdentificationInputs_of_w451Style_w502 H
  concreteLegCompatibility := by
    simpa [pointIdentificationInputs_of_w451Style_w502, concreteConjugatedDescendedW478]
      using H.concreteLegCompatibility
  ordinaryPackage := H.ordinaryPackage
  ordinaryDescended_eq := H.ordinaryDescended_eq

/-- Provider surface for W502 raw W451-style inputs. -/
abbrev SelectedW461W451StyleProviderW502 : Type 1 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              SelectedW461W451StyleCallSiteInputsW502 X Y α cx cy

/-- W502 W451-style providers feed W501's selected concrete-leg route. -/
def selectedConcreteLegProvider_of_w451Style_w502
    (hstyle : SelectedW461W451StyleProviderW502) :
    SelectedW461ConcreteLegProviderW501 :=
  fun X Y α cx cy φ hcx hcy hclosed hcompat =>
    selectedConcreteLegInputs_of_w451Style_w502
      (hstyle X Y α cx cy φ hcx hcy hclosed hcompat)

/--
W502 endpoint: W451-style raw fields plus the selected cokernel-colimit provider
imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_selectedW461W451Style_and_selectedCokernelColimit_w502
    (hstyle : SelectedW461W451StyleProviderW502)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461ConcreteLeg_and_selectedCokernelColimit_w501
    (selectedConcreteLegProvider_of_w451Style_w502 hstyle) hselected

/--
W502 endpoint with W499's mapped-explicit-cokernel preservation input.
-/
def exactAcyclic_of_selectedW461W451Style_and_mappedExplicitCokernelCoforks_w502
    (hstyle : SelectedW461W451StyleProviderW502)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461ConcreteLeg_and_mappedExplicitCokernelCoforks_w501
    (selectedConcreteLegProvider_of_w451Style_w502 hstyle) hMapped

/-- W502 checked nonterminal state. -/
structure SelectedW461W451StyleRouteV370SupportStateW502 : Type where
  seed : String
  declarations : List String
  concreteLegAdapterResult : String
  selectedCokernelRouteResult : String
  mappedCokernelRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W502 state. -/
def currentSelectedW461W451StyleRouteV370SupportStateW502 :
    SelectedW461W451StyleRouteV370SupportStateW502 where
  seed := supportSeedW502
  declarations :=
    ["SelectedW461W451StyleCallSiteInputsW502",
      "pointIdentificationInputs_of_w451Style_w502",
      "selectedConcreteLegInputs_of_w451Style_w502",
      "SelectedW461W451StyleProviderW502",
      "selectedConcreteLegProvider_of_w451Style_w502",
      "exactAcyclic_of_selectedW461W451Style_and_selectedCokernelColimit_w502",
      "exactAcyclic_of_selectedW461W451Style_and_mappedExplicitCokernelCoforks_w502"]
  concreteLegAdapterResult := "proved"
  selectedCokernelRouteResult := "proved"
  mappedCokernelRouteResult := "proved"
  remainingInputs :=
    ["construct concrete SelectedW461W451StyleProviderW502",
      "prove the selected cokernel-colimit or mapped-cokernel preservation input"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW502State :
    SelectedW461W451StyleRouteV370SupportStateW502 :=
  currentSelectedW461W451StyleRouteV370SupportStateW502

theorem currentSelectedW461W451StyleRouteStateW502_productSuccess :
    currentW502State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW502
#check SelectedW461W451StyleCallSiteInputsW502
#check pointIdentificationInputs_of_w451Style_w502
#check selectedConcreteLegInputs_of_w451Style_w502
#check SelectedW461W451StyleProviderW502
#check selectedConcreteLegProvider_of_w451Style_w502
#check exactAcyclic_of_selectedW461W451Style_and_selectedCokernelColimit_w502
#check exactAcyclic_of_selectedW461W451Style_and_mappedExplicitCokernelCoforks_w502
#check currentSelectedW461W451StyleRouteStateW502_productSuccess

end Checks

end WppOpSelectedW461W451StyleRouteV370SupportW502

namespace WppOpSelectedW461W451StyleClosureKernelRouteV370SupportW503

open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpShortComplexPreservationFromUnderlyingV370SupportW495
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open WppOpSelectedW461W451StyleRouteV370SupportW502
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W503 closure-kernel preservation route. -/
def supportSeedW503 : String :=
  "w503-selected-w461-w451-style-closure-kernel-route"

/-- Closure-kernel inputs for every mapped explicit LCA cokernel. -/
structure MappedExplicitCokernelClosureKernelProviderW503 : Type 1 where
  closureKernel : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
    MetrizableLCA.ClosureKernelInput f

/--
The existing forgotten-cokernel API supplies the W497 mapped explicit cokernel
colimit input from closure-kernel data.
-/
def mappedExplicitCokernelCoforks_of_closureKernelProvider_w503
    (hClosure : MappedExplicitCokernelClosureKernelProviderW503) :
    ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f) := by
  intro X Y f
  simpa [mappedExplicitCokernelCoconeW497, explicitMetrizableCokernelCoforkW497,
    underlyingForgetfulFunctorW495, MetrizableLCA.forgottenMappedExplicitCokernelCocone]
    using
      (MetrizableLCA.forgottenMappedExplicitCokernelCoconeIsColimit_of_closureKernelInput
        f (hClosure.closureKernel f))

/--
W503 endpoint: W502 raw selected-W461 fields plus closure-kernel data for every
mapped explicit cokernel imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_selectedW461W451Style_and_closureKernelProvider_w503
    (hstyle : SelectedW461W451StyleProviderW502)
    (hClosure : MappedExplicitCokernelClosureKernelProviderW503) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461W451Style_and_mappedExplicitCokernelCoforks_w502
    hstyle (mappedExplicitCokernelCoforks_of_closureKernelProvider_w503 hClosure)

/-- W503 checked nonterminal state. -/
structure SelectedW461W451StyleClosureKernelRouteV370SupportStateW503 : Type where
  seed : String
  declarations : List String
  closureKernelRouteResult : String
  exactAcyclicRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W503 state. -/
def currentSelectedW461W451StyleClosureKernelRouteV370SupportStateW503 :
    SelectedW461W451StyleClosureKernelRouteV370SupportStateW503 where
  seed := supportSeedW503
  declarations :=
    ["MappedExplicitCokernelClosureKernelProviderW503",
      "mappedExplicitCokernelCoforks_of_closureKernelProvider_w503",
      "exactAcyclic_of_selectedW461W451Style_and_closureKernelProvider_w503"]
  closureKernelRouteResult := "proved"
  exactAcyclicRouteResult := "proved"
  remainingInputs :=
    ["construct concrete SelectedW461W451StyleProviderW502",
      "construct concrete MappedExplicitCokernelClosureKernelProviderW503"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW503State :
    SelectedW461W451StyleClosureKernelRouteV370SupportStateW503 :=
  currentSelectedW461W451StyleClosureKernelRouteV370SupportStateW503

theorem currentSelectedW461W451StyleClosureKernelRouteStateW503_productSuccess :
    currentW503State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW503
#check MappedExplicitCokernelClosureKernelProviderW503
#check mappedExplicitCokernelCoforks_of_closureKernelProvider_w503
#check exactAcyclic_of_selectedW461W451Style_and_closureKernelProvider_w503
#check currentSelectedW461W451StyleClosureKernelRouteStateW503_productSuccess

end Checks

end WppOpSelectedW461W451StyleClosureKernelRouteV370SupportW503

namespace WppOpSelectedW461TargetLegRouteV370SupportW504

open WppOpW426W318LegCompatibilityAlignmentV370SupportW439
open WppOpW461ToW441PromotionProviderV370SupportW478
open WppOpW480SplitProvidersSelectedCokernelColimitV370SupportW492
open WppOpForgetfulFinitePreservationFromCokernelsV370SupportW497
open WppOpSelectedW461PointIdentificationRouteV370SupportW500
open WppOpSelectedW461W451StyleClosureKernelRouteV370SupportW503
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Reproducible support seed for the W504 target-leg route. -/
def supportSeedW504 : String :=
  "w504-selected-w461-target-leg-route"

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndexW504 : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The WPP-op image of the ordinary left arrow. -/
abbrev ordinaryLeftHomW504 : ordinarySourceIndexW504 ⟶ ordinaryTargetIndexW478 :=
  walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left

/-- The ordinary-source component equation for a map between WPP-op colimit points. -/
abbrev ordinarySourceComponentEquationW504
    (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt) : Prop :=
  cx.ι.app ordinarySourceIndexW504 ≫ φ =
    α.app ordinarySourceIndexW504 ≫ cy.ι.app ordinarySourceIndexW504

/--
The ordinary source equation follows from the ordinary target equation by
using cocone naturality and naturality of the WPP-op map.
-/
theorem source_component_of_target_component_w504
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquationW478 X Y α cx cy φ) :
    ordinarySourceComponentEquationW504 X Y α cx cy φ := by
  change cx.ι.app ordinarySourceIndexW504 ≫ φ =
    α.app ordinarySourceIndexW504 ≫ cy.ι.app ordinarySourceIndexW504
  have h0 :
      cx.ι.app ordinarySourceIndexW504 ≫ φ =
        (X.map ordinaryLeftHomW504 ≫ cx.ι.app ordinaryTargetIndexW478) ≫ φ :=
    congrArg (fun f => f ≫ φ) (cx.w ordinaryLeftHomW504).symm
  have h1 :
      (X.map ordinaryLeftHomW504 ≫ cx.ι.app ordinaryTargetIndexW478) ≫ φ =
        (X.map ordinaryLeftHomW504 ≫ α.app ordinaryTargetIndexW478) ≫
          cy.ι.app ordinaryTargetIndexW478 := by
    simpa only [Category.assoc] using
      congrArg (fun f => X.map ordinaryLeftHomW504 ≫ f) htarget
  have h2 :
      (X.map ordinaryLeftHomW504 ≫ α.app ordinaryTargetIndexW478) ≫
          cy.ι.app ordinaryTargetIndexW478 =
        (α.app ordinarySourceIndexW504 ≫ Y.map ordinaryLeftHomW504) ≫
          cy.ι.app ordinaryTargetIndexW478 :=
    congrArg (fun f => f ≫ cy.ι.app ordinaryTargetIndexW478)
      (α.naturality ordinaryLeftHomW504)
  have h3 :
      (α.app ordinarySourceIndexW504 ≫ Y.map ordinaryLeftHomW504) ≫
          cy.ι.app ordinaryTargetIndexW478 =
        α.app ordinarySourceIndexW504 ≫ cy.ι.app ordinarySourceIndexW504 := by
    simpa only [Category.assoc] using
      congrArg (fun f => α.app ordinarySourceIndexW504 ≫ f) (cy.w ordinaryLeftHomW504)
  exact h0.trans (h1.trans (h2.trans h3))

/-- A target-index component equation supplies the full W318 leg compatibility. -/
theorem w318ColimitMapLegCompatibility_of_target_component_w504
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y} {φ : cx.pt ⟶ cy.pt}
    (htarget : ordinaryTargetComponentEquationW478 X Y α cx cy φ) :
    W318ColimitMapLegCompatibilityW441 X Y α cx cy φ := by
  intro j
  cases j using Opposite.rec
  rename_i j
  cases j
  · simpa [ordinaryTargetIndexW478] using htarget
  · simpa [ordinarySourceIndexW504] using
      source_component_of_target_component_w504 htarget

/--
Raw target-leg call-site fields for the selected W461 map. W504 removes the
need to supply full concrete W318 leg compatibility as an input.
-/
structure SelectedW461TargetLegCallSiteInputsW504
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
  ordinaryPackage : W426OrdinaryDescendedMapPackage ordinaryMap
  ordinaryDescended_eq :
    ordinaryPackage.ordinaryDescended = ordinaryDescended

/-- Build W478 point-identification inputs from W504's target-leg fields. -/
def pointIdentificationInputs_of_targetLeg_w504
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (H : SelectedW461TargetLegCallSiteInputsW504 X Y α cx cy) :
    W461TargetLegPointIdentificationInputsW478 X Y α cx cy where
  ordinaryMap := H.ordinaryMap
  ordinaryDescended := H.ordinaryDescended
  sourcePointIdentification := H.sourcePointIdentification
  targetPointIdentification := H.targetPointIdentification
  quotient_compat := H.quotient_compat
  sourcePointIdentification_target_leg := H.sourcePointIdentification_target_leg
  targetPointIdentification_target_leg := H.targetPointIdentification_target_leg

/-- W504 target-leg fields build W500 point-identification call-site fields. -/
def selectedPointIdentificationInputs_of_targetLeg_w504
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}} {α : X ⟶ Y}
    {cx : Cocone X} {cy : Cocone Y}
    (H : SelectedW461TargetLegCallSiteInputsW504 X Y α cx cy) :
    SelectedW461PointIdentificationCallSiteInputsW500 X Y α cx cy where
  pointIdentificationInputs := pointIdentificationInputs_of_targetLeg_w504 H
  targetComponentImpliesW318 := fun htarget =>
    w318ColimitMapLegCompatibility_of_target_component_w504 htarget
  ordinaryPackage := H.ordinaryPackage
  ordinaryDescended_eq := H.ordinaryDescended_eq

/-- Provider surface for W504 target-leg inputs. -/
abbrev SelectedW461TargetLegProviderW504 : Type 1 :=
  ∀ (X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) (α : X ⟶ Y)
    (cx : Cocone X) (cy : Cocone Y) (φ : cx.pt ⟶ cy.pt),
      IsColimit cx →
        IsColimit cy →
          (∀ j : WalkingParallelPairᵒᵖ,
            IsClosedEmbedding (α.app j : X.obj j → Y.obj j)) →
            W318ColimitMapLegCompatibilityW441 X Y α cx cy φ →
              SelectedW461TargetLegCallSiteInputsW504 X Y α cx cy

/-- W504 target-leg providers feed W500's selected point-identification route. -/
def selectedPointIdentificationProvider_of_targetLeg_w504
    (htarget : SelectedW461TargetLegProviderW504) :
    SelectedW461PointIdentificationProviderW500 :=
  fun X Y α cx cy φ hcx hcy hclosed hcompat =>
    selectedPointIdentificationInputs_of_targetLeg_w504
      (htarget X Y α cx cy φ hcx hcy hclosed hcompat)

/--
W504 endpoint: target-leg fields plus the selected cokernel-colimit provider
imply the current WPP-op exact-acyclic closure.
-/
def exactAcyclic_of_selectedW461TargetLeg_and_selectedCokernelColimit_w504
    (htarget : SelectedW461TargetLegProviderW504)
    (hselected : SelectedCokernelColimitProviderW492) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461PointIdentification_and_selectedCokernelColimit_w500
    (selectedPointIdentificationProvider_of_targetLeg_w504 htarget) hselected

/-- W504 endpoint with W499's mapped-explicit-cokernel preservation input. -/
def exactAcyclic_of_selectedW461TargetLeg_and_mappedExplicitCokernelCoforks_w504
    (htarget : SelectedW461TargetLegProviderW504)
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit (mappedExplicitCokernelCoconeW497 f)) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461PointIdentification_and_mappedExplicitCokernelCoforks_w500
    (selectedPointIdentificationProvider_of_targetLeg_w504 htarget) hMapped

/-- W504 endpoint with W503's closure-kernel preservation input. -/
def exactAcyclic_of_selectedW461TargetLeg_and_closureKernelProvider_w504
    (htarget : SelectedW461TargetLegProviderW504)
    (hClosure : MappedExplicitCokernelClosureKernelProviderW503) :
    exactAcyclic_metrizableLCA_walkingParallelPairOp_colimit_closure :=
  exactAcyclic_of_selectedW461TargetLeg_and_mappedExplicitCokernelCoforks_w504
    htarget (mappedExplicitCokernelCoforks_of_closureKernelProvider_w503 hClosure)

/-- W504 checked nonterminal state. -/
structure SelectedW461TargetLegRouteV370SupportStateW504 : Type where
  seed : String
  declarations : List String
  targetToW318Result : String
  providerAdapterResult : String
  selectedCokernelRouteResult : String
  closureKernelRouteResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W504 state. -/
def currentSelectedW461TargetLegRouteV370SupportStateW504 :
    SelectedW461TargetLegRouteV370SupportStateW504 where
  seed := supportSeedW504
  declarations :=
    ["source_component_of_target_component_w504",
      "w318ColimitMapLegCompatibility_of_target_component_w504",
      "SelectedW461TargetLegCallSiteInputsW504",
      "pointIdentificationInputs_of_targetLeg_w504",
      "selectedPointIdentificationInputs_of_targetLeg_w504",
      "SelectedW461TargetLegProviderW504",
      "selectedPointIdentificationProvider_of_targetLeg_w504",
      "exactAcyclic_of_selectedW461TargetLeg_and_selectedCokernelColimit_w504",
      "exactAcyclic_of_selectedW461TargetLeg_and_mappedExplicitCokernelCoforks_w504",
      "exactAcyclic_of_selectedW461TargetLeg_and_closureKernelProvider_w504"]
  targetToW318Result := "proved"
  providerAdapterResult := "proved"
  selectedCokernelRouteResult := "proved"
  closureKernelRouteResult := "proved"
  remainingInputs :=
    ["construct concrete SelectedW461TargetLegProviderW504",
      "construct concrete MappedExplicitCokernelClosureKernelProviderW503 or selected cokernel-colimit provider"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentW504State :
    SelectedW461TargetLegRouteV370SupportStateW504 :=
  currentSelectedW461TargetLegRouteV370SupportStateW504

theorem currentSelectedW461TargetLegRouteStateW504_productSuccess :
    currentW504State.productSuccessClaimed = false :=
  rfl

section Checks

#check supportSeedW504
#check ordinarySourceIndexW504
#check ordinaryLeftHomW504
#check source_component_of_target_component_w504
#check w318ColimitMapLegCompatibility_of_target_component_w504
#check SelectedW461TargetLegCallSiteInputsW504
#check pointIdentificationInputs_of_targetLeg_w504
#check selectedPointIdentificationInputs_of_targetLeg_w504
#check SelectedW461TargetLegProviderW504
#check selectedPointIdentificationProvider_of_targetLeg_w504
#check exactAcyclic_of_selectedW461TargetLeg_and_selectedCokernelColimit_w504
#check exactAcyclic_of_selectedW461TargetLeg_and_mappedExplicitCokernelCoforks_w504
#check exactAcyclic_of_selectedW461TargetLeg_and_closureKernelProvider_w504
#check currentSelectedW461TargetLegRouteStateW504_productSuccess

end Checks

end WppOpSelectedW461TargetLegRouteV370SupportW504

end LeanLCAExactChallenge
