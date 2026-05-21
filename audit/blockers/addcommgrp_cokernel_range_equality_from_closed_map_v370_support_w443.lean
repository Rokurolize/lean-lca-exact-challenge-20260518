import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Topology.Defs.Induced

/-!
W443: closed-range equality for the forgotten cokernel subgroup.

W440's AddCommGrp cokernel comparison needs the algebraic range subgroup of the
forgotten morphism to equal `MetrizableLCA.cokernelSubgroup f`.  The latter is
definitionally the topological closure of the same algebraic range.  This file
proves the equality from the practical closed-range hypothesis
`IsClosed (Set.range (f : X → Y))`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace AddCommGrpCokernelRangeEqualityFromClosedMapV370SupportW443

open LeanLCAExactChallenge.MetrizableLCA

/-- The forgetful functor used by W440. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The algebraic range subgroup of the forgotten source map. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup (underlyingForgetfulFunctor.obj Y) :=
  AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
    (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X))

/-- The same algebraic range subgroup, kept in the topological target object. -/
abbrev algebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup Y :=
  AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup X)

/-- The local algebraic range subgroup has carrier `Set.range f`. -/
theorem mem_algebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ algebraicRangeSubgroup f ↔ y ∈ Set.range (f : X → Y) := by
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- The forgotten algebraic range subgroup has the same carrier as the topological one. -/
theorem mem_forgottenAlgebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ forgottenAlgebraicRangeSubgroup f ↔ y ∈ algebraicRangeSubgroup f := by
  rw [mem_algebraicRangeSubgroup_iff]
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- Closedness of the underlying set range gives closedness of the algebraic range subgroup. -/
theorem isClosed_algebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsClosed (algebraicRangeSubgroup f : Set Y) := by
  rwa [Set.ext_iff.mpr (mem_algebraicRangeSubgroup_iff f)]

/-- In `Y`, a closed algebraic range is equal to the closed cokernel subgroup. -/
theorem algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    algebraicRangeSubgroup f = cokernelSubgroup f := by
  apply le_antisymm
  · exact range_le_cokernelSubgroup f
  · unfold cokernelSubgroup
    apply AddSubgroup.topologicalClosure_minimal
    · intro y hy
      exact hy
    · exact isClosed_algebraicRangeSubgroup_of_isClosed_range f hclosed

/--
Closed-range equality needed by W440: if the underlying image of `f` is closed,
then the forgotten algebraic range equals the closed subgroup used in the LCA
cokernel quotient.
-/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    forgottenAlgebraicRangeSubgroup f =
      (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) := by
  ext y
  constructor
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f :=
      (mem_forgottenAlgebraicRangeSubgroup_iff f y).mp hy
    rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed] at hyalg
    exact hyalg
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f := by
      rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed]
      exact hy
    exact (mem_forgottenAlgebraicRangeSubgroup_iff f y).mpr hyalg

/-- Reversed orientation, matching W438's local-subgroup closed-range variant. -/
theorem cokernelSubgroup_eq_forgottenAlgebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) =
      forgottenAlgebraicRangeSubgroup f :=
  (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed).symm

/-- A closed map has closed full image, so it supplies W440's range equality. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f =
      (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) := by
  refine forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f ?_
  simpa [Set.image_univ] using hclosedMap Set.univ isClosed_univ

/-- A closed embedding supplies the same equality through its closed range field. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f =
      (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) :=
  forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f
    hclosedEmbedding.isClosed_range

/-- Declaration-level summary for downstream review. -/
structure AddCommGrpCokernelRangeEqualityFromClosedMapV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  rangeEqualityResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpCokernelRangeEqualityFromClosedMapV370SupportState :
    AddCommGrpCokernelRangeEqualityFromClosedMapV370SupportState where
  seed := "b60e449adc67c816a62a12fc"
  checkedDeclarations :=
    ["underlyingForgetfulFunctor",
      "forgottenAlgebraicRangeSubgroup",
      "algebraicRangeSubgroup",
      "mem_algebraicRangeSubgroup_iff",
      "mem_forgottenAlgebraicRangeSubgroup_iff",
      "isClosed_algebraicRangeSubgroup_of_isClosed_range",
      "algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range",
      "cokernelSubgroup_eq_forgottenAlgebraicRangeSubgroup_of_isClosed_range",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding"]
  rangeEqualityResult := "proved"
  remainingInputs :=
    ["Supply `IsClosed (Set.range (f : X → Y))` from the local closed-map, closed-embedding, closed-range, or strict-exactness data at the W440 call site."]
  productSuccessClaimed := false

theorem currentAddCommGrpCokernelRangeEqualityFromClosedMapV370SupportState_productSuccess :
    currentAddCommGrpCokernelRangeEqualityFromClosedMapV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check underlyingForgetfulFunctor
#check forgottenAlgebraicRangeSubgroup
#check algebraicRangeSubgroup
#check mem_algebraicRangeSubgroup_iff
#check mem_forgottenAlgebraicRangeSubgroup_iff
#check isClosed_algebraicRangeSubgroup_of_isClosed_range
#check algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
#check cokernelSubgroup_eq_forgottenAlgebraicRangeSubgroup_of_isClosed_range
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding
#check currentAddCommGrpCokernelRangeEqualityFromClosedMapV370SupportState
#check currentAddCommGrpCokernelRangeEqualityFromClosedMapV370SupportState_productSuccess

end Checks

end AddCommGrpCokernelRangeEqualityFromClosedMapV370SupportW443

end LeanLCAExactChallenge
