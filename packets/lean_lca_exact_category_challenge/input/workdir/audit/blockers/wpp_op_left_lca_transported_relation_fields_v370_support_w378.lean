import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated

/-!
W378: transported relation-fields support for the left-LCA W375 route.

The copied W375 audit file is not importable as a Lean module in this worktree,
so this standalone file keeps the adapter at the stable typed boundary: the
three topological relation-pullback fields required by W375's
`RelationPullbackDescendedFieldsInputsW354Shape`.

The result is intentionally a checked reduction rather than a product claim.
It names exactly the remaining fields and provides the consumer constructor
that downstream W375 can use once those fields are instantiated for the
transported concrete quotient cocones and ordinary descended quotient map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaTransportedRelationFieldsV370SupportW378

/--
W375's relation-pullback topological field shape.

This is the same three-field boundary used by W354/W375: injectivity, inducing
topology, and closed image for the descended quotient map between cocone points.
-/
structure RelationPullbackDescendedFieldsInputsW354Shape
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/--
Smallest remaining W378 input package.

For the concrete W375 instantiation, `source` and `target` are the transported
concrete quotient cocones and `descended` is the ordinary concrete descended
quotient map.  W352/W337/W340/W343 are expected to prove these three fields
from relation-pullback equality, quotient compatibility, and closed-map data.
-/
structure TransportedRelationPullbackTopologicalFieldsW378
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (source : Cocone X) (target : Cocone Y)
    (descended : source.pt ⟶ target.pt) : Prop where
  injective : Function.Injective (descended : source.pt → target.pt)
  inducing : IsInducing (descended : source.pt → target.pt)
  closed_range : IsClosed (Set.range (descended : source.pt → target.pt))

/-- Repackage the W378 topological field package into W375's W354-shaped input. -/
def transportedRelationPullbackFieldsW378
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : TransportedRelationPullbackTopologicalFieldsW378 source target descended) :
    RelationPullbackDescendedFieldsInputsW354Shape source target descended where
  injective := h.injective
  inducing := h.inducing
  closed_range := h.closed_range

/--
Consumer theorem for W375's `transportedConcreteQuotientW354Inputs_of_w357_ordinary_projection`.

After substituting W375's transported source/target cocones and descended map,
this theorem supplies exactly the relation-input argument expected by that
consumer.
-/
theorem transportedRelationPullbackFieldsW378_for_w375_consumer
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {source : Cocone X} {target : Cocone Y}
    {descended : source.pt ⟶ target.pt}
    (h : TransportedRelationPullbackTopologicalFieldsW378 source target descended) :
    RelationPullbackDescendedFieldsInputsW354Shape source target descended :=
  transportedRelationPullbackFieldsW378 h

/--
Explicit checklist of the ordinary relation-pullback inputs still needed to
instantiate the topological fields for W375's concrete quotient map.
-/
def remainingTransportedRelationFieldInputsW378 : List String :=
  ["ordinary component square equations for the WPP-op natural transformation",
    "relation-pullback equality, equivalently the reverse preimage condition",
    "quotient compatibility for the ordinary descended quotient map",
    "closed-map input for the ordinary descended quotient map",
    "identification of these ordinary W352 fields with the transported concrete quotient cocone points"]

theorem remainingTransportedRelationFieldInputsW378_count :
    remainingTransportedRelationFieldInputsW378.length = 5 := rfl

/-- Declaration names exported by this support file. -/
def w378SupportDeclarationNames : List String :=
  ["RelationPullbackDescendedFieldsInputsW354Shape",
    "TransportedRelationPullbackTopologicalFieldsW378",
    "transportedRelationPullbackFieldsW378",
    "transportedRelationPullbackFieldsW378_for_w375_consumer",
    "remainingTransportedRelationFieldInputsW378"]

theorem w378SupportDeclarationNames_count :
    w378SupportDeclarationNames.length = 5 := rfl

/-- Machine-readable state for this checked W378 support file. -/
structure WppOpLeftLcaTransportedRelationFieldsV370StateW378 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  transportedRelationFieldsResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaTransportedRelationFieldsV370StateW378 :
    WppOpLeftLcaTransportedRelationFieldsV370StateW378 where
  seed := "14961b85b7500e6355fb9aab3b7fba09"
  checkedFacts :=
    ["defined the W375/W354-shaped relation-pullback topological field boundary",
      "exposed the smallest W378 package naming the three transported fields",
      "provided a checked consumer theorem that repackages W378 fields into the W375 relation-input shape"]
  remainingInputs := remainingTransportedRelationFieldInputsW378
  transportedRelationFieldsResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaTransportedRelationFieldsV370StateW378_productSuccess :
    currentWppOpLeftLcaTransportedRelationFieldsV370StateW378.productSuccessClaimed = false := rfl

section Checks

#check RelationPullbackDescendedFieldsInputsW354Shape
#check TransportedRelationPullbackTopologicalFieldsW378
#check transportedRelationPullbackFieldsW378
#check transportedRelationPullbackFieldsW378_for_w375_consumer
#check remainingTransportedRelationFieldInputsW378
#check remainingTransportedRelationFieldInputsW378_count
#check currentWppOpLeftLcaTransportedRelationFieldsV370StateW378
#check currentWppOpLeftLcaTransportedRelationFieldsV370StateW378_productSuccess

end Checks

end WppOpLeftLcaTransportedRelationFieldsV370SupportW378

end LeanLCAExactChallenge
