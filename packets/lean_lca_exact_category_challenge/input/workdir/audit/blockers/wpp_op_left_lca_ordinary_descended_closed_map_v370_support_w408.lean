import LeanLCAExactChallenge.LCA.Quotient
import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.WppOpExactAcyclicFrontierConsolidated
import Mathlib.Topology.Maps.Basic

/-!
W408: closed-map support for the ordinary descended quotient map.

This standalone audit file keeps the W405 quotient-compatibility bridge local
and isolates the remaining topological input for `IsClosedMap` as closedness of
the target quotient preimage of images of closed source-quotient sets.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace WppOpLeftLcaOrdinaryDescendedClosedMapV370SupportW408

/-- Ordinary diagram associated to a `WalkingParallelPairᵒᵖ` diagram. -/
abbrev wppOpOrdinaryDiagram (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    WalkingParallelPair ⥤ MetrizableLCA.{0} :=
  walkingParallelPairOpEquiv.functor ⋙ X

/-- Domain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpDomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.zero

/-- Codomain object of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpCodomain (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  (wppOpOrdinaryDiagram X).obj WalkingParallelPair.one

/-- Left arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpLeft (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.left

/-- Right arrow of the ordinary parallel pair underlying a WPP-op diagram. -/
abbrev wppOpRight (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) :
    wppOpDomain X ⟶ wppOpCodomain X :=
  (wppOpOrdinaryDiagram X).map WalkingParallelPairHom.right

/-- The ordinary quotient point used by the concrete descended map. -/
abbrev wppOpOrdinaryQuotientPoint
    (X : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}) : MetrizableLCA.{0} :=
  MetrizableLCA.quotientObj (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)

/-- W405/W408 relation-pullback equality for cokernel-relation subgroups. -/
abbrev relationPreimagePullbackConditionW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  AddSubgroup.comap (ordinaryMap.app WalkingParallelPair.one).hom.toAddMonoidHom
      (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y)) =
    MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X)

/-- Naturality square for the ordinary left leg. -/
theorem ordinarySquareLeftW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpLeft X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpLeft Y := by
  simpa [wppOpLeft] using ordinaryMap.naturality WalkingParallelPairHom.left

/-- Naturality square for the ordinary right leg. -/
theorem ordinarySquareRightW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpRight X ≫ ordinaryMap.app WalkingParallelPair.one =
      ordinaryMap.app WalkingParallelPair.zero ≫ wppOpRight Y := by
  simpa [wppOpRight] using ordinaryMap.naturality WalkingParallelPairHom.right

/-- Source relation maps forward to the target relation under compatible squares. -/
theorem relationPreimageForwardOfSquaresW408
    {A B A' B' : MetrizableLCA.{0}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    ∀ b : B, b ∈ MetrizableLCA.cokernelSubgroup (f - g) →
      iB b ∈ MetrizableLCA.cokernelSubgroup (f' - g') := by
  intro b hb
  let targetPreimage : AddSubgroup B :=
    AddSubgroup.comap iB.hom.toAddMonoidHom (MetrizableLCA.cokernelSubgroup (f' - g'))
  have hrange_le :
      AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A) ≤
        targetPreimage := by
    intro x hx
    rcases hx with ⟨a, _ha, rfl⟩
    change iB ((f - g) a) ∈ MetrizableLCA.cokernelSubgroup (f' - g')
    have hleft : iB (f a) = f' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_left
    have hright : iB (g a) = g' (iA a) := by
      simpa using congrArg (fun q : A ⟶ B' => q a) hsquare_right
    have hval : iB ((f - g) a) = (f' - g') (iA a) := by
      calc
        iB ((f - g) a) = iB (f a - g a) := by rfl
        _ = iB (f a) - iB (g a) := by
          exact map_sub iB.hom.toAddMonoidHom (f a) (g a)
        _ = f' (iA a) - g' (iA a) := by rw [hleft, hright]
        _ = (f' - g') (iA a) := by rfl
    rw [hval]
    exact MetrizableLCA.map_mem_cokernelSubgroup (f' - g') (iA a)
  have htargetPreimage_closed : IsClosed (targetPreimage : Set B) := by
    change IsClosed
      ((fun b : B => iB b) ⁻¹' (MetrizableLCA.cokernelSubgroup (f' - g') : Set B'))
    exact (AddSubgroup.isClosed_topologicalClosure _).preimage iB.hom.continuous
  have hclosure_le : MetrizableLCA.cokernelSubgroup (f - g) ≤ targetPreimage :=
    AddSubgroup.topologicalClosure_minimal
      (AddSubgroup.map (f - g).hom.toAddMonoidHom (⊤ : AddSubgroup A))
      hrange_le htargetPreimage_closed
  exact hclosure_le hb

/-- Kernel condition needed to descend the ordinary component map through quotient objects. -/
theorem ordinaryDescendedTargetKernel_leW408
    {A B A' B' : MetrizableLCA.{0}} {f g : A ⟶ B} {f' g' : A' ⟶ B'}
    (iA : A ⟶ A') (iB : B ⟶ B')
    (hsquare_left : f ≫ iB = iA ≫ f')
    (hsquare_right : g ≫ iB = iA ≫ g') :
    MetrizableLCA.cokernelSubgroup (f - g) ≤
      (iB ≫ MetrizableLCA.quotientMap B'
        (MetrizableLCA.cokernelSubgroup (f' - g'))
        (AddSubgroup.isClosed_topologicalClosure _)).hom.toAddMonoidHom.ker := by
  intro b hb
  change ((iB b : B') : B' ⧸ MetrizableLCA.cokernelSubgroup (f' - g')) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact relationPreimageForwardOfSquaresW408 iA iB hsquare_left hsquare_right b hb

/-- The ordinary descended quotient map induced by the ordinary component map. -/
def ordinaryDescendedOfOrdinaryMapW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y :=
  MetrizableLCA.quotientLift (wppOpCodomain X)
    (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
    (AddSubgroup.isClosed_topologicalClosure _)
    (ordinaryMap.app WalkingParallelPair.one ≫
      MetrizableLCA.quotientMap (wppOpCodomain Y)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
        (AddSubgroup.isClosed_topologicalClosure _))
    (ordinaryDescendedTargetKernel_leW408
      (ordinaryMap.app WalkingParallelPair.zero)
      (ordinaryMap.app WalkingParallelPair.one)
      (ordinarySquareLeftW408 ordinaryMap)
      (ordinarySquareRightW408 ordinaryMap))

/-- W405-style quotient compatibility for the W408 local descended map. -/
theorem ordinaryDescendedOfOrdinaryMap_quotient_compatW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫
        ordinaryDescendedOfOrdinaryMapW408 ordinaryMap =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _) := by
  change
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫
        MetrizableLCA.quotientLift (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _)
          (ordinaryMap.app WalkingParallelPair.one ≫
            MetrizableLCA.quotientMap (wppOpCodomain Y)
              (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
              (AddSubgroup.isClosed_topologicalClosure _))
          (ordinaryDescendedTargetKernel_leW408
            (ordinaryMap.app WalkingParallelPair.zero)
            (ordinaryMap.app WalkingParallelPair.one)
            (ordinarySquareLeftW408 ordinaryMap)
            (ordinarySquareRightW408 ordinaryMap)) =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _)
  exact MetrizableLCA.quotientLift_quotientMap (wppOpCodomain X)
      (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
      (AddSubgroup.isClosed_topologicalClosure _)
      (ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _))
      (ordinaryDescendedTargetKernel_leW408
        (ordinaryMap.app WalkingParallelPair.zero)
        (ordinaryMap.app WalkingParallelPair.one)
        (ordinarySquareLeftW408 ordinaryMap)
        (ordinarySquareRightW408 ordinaryMap))

/--
Closed-image certificate reduced to representatives.  For every closed source
quotient set, pull it back to source representatives, map by the component, and
project to the target quotient.
-/
abbrev ordinaryDescendedRepresentativeImageClosedConditionW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop :=
  ∀ C : Set (wppOpOrdinaryQuotientPoint X), IsClosed C →
    IsClosed
      ((MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _) :
          wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y) ''
        (((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
          ((MetrizableLCA.quotientMap (wppOpCodomain X)
              (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
              (AddSubgroup.isClosed_topologicalClosure _) :
              wppOpCodomain X → wppOpOrdinaryQuotientPoint X) ⁻¹' C)))

/-- The representative-image certificate proves `IsClosedMap` for the ordinary descended map. -/
theorem ordinaryDescendedOfOrdinaryMap_isClosedMap_of_representative_image_closedW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (hclosed : ordinaryDescendedRepresentativeImageClosedConditionW408 ordinaryMap) :
    IsClosedMap (ordinaryDescendedOfOrdinaryMapW408 ordinaryMap :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) := by
  intro C hC
  have himage_eq :
      ((ordinaryDescendedOfOrdinaryMapW408 ordinaryMap :
          wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) '' C) =
        ((MetrizableLCA.quotientMap (wppOpCodomain Y)
            (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
            (AddSubgroup.isClosed_topologicalClosure _) :
            wppOpCodomain Y → wppOpOrdinaryQuotientPoint Y) ''
          (((ordinaryMap.app WalkingParallelPair.one) : wppOpCodomain X → wppOpCodomain Y) ''
            ((MetrizableLCA.quotientMap (wppOpCodomain X)
                (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
                (AddSubgroup.isClosed_topologicalClosure _) :
                wppOpCodomain X → wppOpOrdinaryQuotientPoint X) ⁻¹' C))) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hxC, rfl⟩
      rcases MetrizableLCA.quotientMap_surjective (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _) x with ⟨b, rfl⟩
      refine ⟨ordinaryMap.app WalkingParallelPair.one b, ?_, ?_⟩
      · exact ⟨b, hxC, rfl⟩
      · exact (congrArg
          (fun q : wppOpCodomain X ⟶ wppOpOrdinaryQuotientPoint Y => q b)
          (ordinaryDescendedOfOrdinaryMap_quotient_compatW408 ordinaryMap)).symm
    · intro hy
      rcases hy with ⟨b', hb', rfl⟩
      rcases hb' with ⟨b, hbC, rfl⟩
      refine ⟨MetrizableLCA.quotientMap (wppOpCodomain X)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
          (AddSubgroup.isClosed_topologicalClosure _) b, hbC, ?_⟩
      exact congrArg
        (fun q : wppOpCodomain X ⟶ wppOpOrdinaryQuotientPoint Y => q b)
        (ordinaryDescendedOfOrdinaryMap_quotient_compatW408 ordinaryMap)
  rw [himage_eq]
  exact hclosed C hC

/-- W408 closed-map certificate for the W405 descended quotient map. -/
structure OrdinaryDescendedClosedMapCertificateW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop where
  closed_image_preimage :
    ordinaryDescendedRepresentativeImageClosedConditionW408 ordinaryMap

/-- Extract the closed-map field from the W408 certificate. -/
theorem OrdinaryDescendedClosedMapCertificateW408.closedMap
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (h : OrdinaryDescendedClosedMapCertificateW408 ordinaryMap) :
    IsClosedMap (ordinaryDescendedOfOrdinaryMapW408 ordinaryMap :
      wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y) :=
  ordinaryDescendedOfOrdinaryMap_isClosedMap_of_representative_image_closedW408
    h.closed_image_preimage

/--
W405-after-quotient-compatibility package with the W408 closed-map condition
discharged.  Only the concrete relation-pullback equality remains external.
-/
structure OrdinaryDescendedConcreteInputsAfterClosedMapW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y) : Prop where
  relation_pullback : relationPreimagePullbackConditionW408 ordinaryMap

/-- W402-shaped ordinary concrete input package, specialized to the W408 map. -/
structure OrdinaryDescendedConcreteInputsW408
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    (ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y)
    (ordinaryDescended : wppOpOrdinaryQuotientPoint X ⟶ wppOpOrdinaryQuotientPoint Y) :
    Prop where
  relation_pullback : relationPreimagePullbackConditionW408 ordinaryMap
  quotient_compat :
    MetrizableLCA.quotientMap (wppOpCodomain X)
        (MetrizableLCA.cokernelSubgroup (wppOpLeft X - wppOpRight X))
        (AddSubgroup.isClosed_topologicalClosure _) ≫ ordinaryDescended =
      ordinaryMap.app WalkingParallelPair.one ≫
        MetrizableLCA.quotientMap (wppOpCodomain Y)
          (MetrizableLCA.cokernelSubgroup (wppOpLeft Y - wppOpRight Y))
          (AddSubgroup.isClosed_topologicalClosure _)
  descended_closedMap : IsClosedMap (ordinaryDescended :
    wppOpOrdinaryQuotientPoint X → wppOpOrdinaryQuotientPoint Y)

/--
Consumer combining W405 quotient compatibility and the W408 closed-map
certificate.  The returned package leaves only relation pullback as a concrete
input.
-/
def ordinaryConcreteInputsW408_of_closedMapCertificate
    {X Y : WalkingParallelPairᵒᵖ ⥤ MetrizableLCA.{0}}
    {ordinaryMap : wppOpOrdinaryDiagram X ⟶ wppOpOrdinaryDiagram Y}
    (hrel : OrdinaryDescendedConcreteInputsAfterClosedMapW408 ordinaryMap)
    (hclosed : OrdinaryDescendedClosedMapCertificateW408 ordinaryMap) :
    OrdinaryDescendedConcreteInputsW408 ordinaryMap
      (ordinaryDescendedOfOrdinaryMapW408 ordinaryMap) where
  relation_pullback := hrel.relation_pullback
  quotient_compat := ordinaryDescendedOfOrdinaryMap_quotient_compatW408 ordinaryMap
  descended_closedMap := hclosed.closedMap

/-- Remaining ordinary descended inputs after W408 isolates closed-map support. -/
def remainingOrdinaryDescendedInputsAfterClosedMapW408 : List String :=
  ["prove the concrete relation-pullback equality, equivalently reverse preimage or closed-range preimage equality",
    "prove the quotient-preimage closed-image certificate for the ordinary descended map"]

theorem remainingOrdinaryDescendedInputsAfterClosedMapW408_count :
    remainingOrdinaryDescendedInputsAfterClosedMapW408.length = 2 := rfl

/-- Declaration names exported by this W408 support layer. -/
def w408SupportDeclarationNames : List String :=
  ["ordinaryDescendedOfOrdinaryMapW408",
    "ordinaryDescendedOfOrdinaryMap_quotient_compatW408",
    "ordinaryDescendedRepresentativeImageClosedConditionW408",
    "ordinaryDescendedOfOrdinaryMap_isClosedMap_of_representative_image_closedW408",
    "OrdinaryDescendedClosedMapCertificateW408",
    "OrdinaryDescendedClosedMapCertificateW408.closedMap",
    "OrdinaryDescendedConcreteInputsAfterClosedMapW408",
    "OrdinaryDescendedConcreteInputsW408",
    "ordinaryConcreteInputsW408_of_closedMapCertificate",
    "remainingOrdinaryDescendedInputsAfterClosedMapW408"]

theorem w408SupportDeclarationNames_count :
    w408SupportDeclarationNames.length = 10 := rfl

structure WppOpLeftLcaOrdinaryDescendedClosedMapV370StateW408 : Type where
  seed : String
  checkedFacts : List String
  remainingInputs : List String
  ordinaryDescendedClosedMapResult : String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaOrdinaryDescendedClosedMapV370StateW408 :
    WppOpLeftLcaOrdinaryDescendedClosedMapV370StateW408 where
  seed := "uoDoQ77kYFgpJAvIMOUVbfIT"
  checkedFacts :=
    ["reconstructed the W405 ordinary descended quotient map in this standalone W408 file",
      "proved the W405-style quotient compatibility equation for the local descended map",
      "reduced IsClosedMap to closedness of representative images of closed source-quotient sets",
      "provided a consumer combining relation pullback, quotient compatibility, and the closed-map certificate"]
  remainingInputs := remainingOrdinaryDescendedInputsAfterClosedMapW408
  ordinaryDescendedClosedMapResult := "partial"
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaOrdinaryDescendedClosedMapV370StateW408_productSuccess :
    currentWppOpLeftLcaOrdinaryDescendedClosedMapV370StateW408.productSuccessClaimed = false := rfl

section Checks

#check relationPreimagePullbackConditionW408
#check ordinarySquareLeftW408
#check ordinarySquareRightW408
#check relationPreimageForwardOfSquaresW408
#check ordinaryDescendedTargetKernel_leW408
#check ordinaryDescendedOfOrdinaryMapW408
#check ordinaryDescendedOfOrdinaryMap_quotient_compatW408
#check ordinaryDescendedRepresentativeImageClosedConditionW408
#check ordinaryDescendedOfOrdinaryMap_isClosedMap_of_representative_image_closedW408
#check OrdinaryDescendedClosedMapCertificateW408
#check OrdinaryDescendedClosedMapCertificateW408.closedMap
#check OrdinaryDescendedConcreteInputsAfterClosedMapW408
#check OrdinaryDescendedConcreteInputsW408
#check ordinaryConcreteInputsW408_of_closedMapCertificate
#check remainingOrdinaryDescendedInputsAfterClosedMapW408
#check remainingOrdinaryDescendedInputsAfterClosedMapW408_count
#check w408SupportDeclarationNames
#check w408SupportDeclarationNames_count
#check currentWppOpLeftLcaOrdinaryDescendedClosedMapV370StateW408
#check currentWppOpLeftLcaOrdinaryDescendedClosedMapV370StateW408_productSuccess

end Checks

end WppOpLeftLcaOrdinaryDescendedClosedMapV370SupportW408

end LeanLCAExactChallenge
