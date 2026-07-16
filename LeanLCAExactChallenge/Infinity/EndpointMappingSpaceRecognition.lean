/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaces
import LeanLCAExactChallenge.Infinity.OrdinaryLocalizationBridge

/-! # Recognition infrastructure for endpoint mapping spaces -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory Opposite Simplicial

/-- Chosen object representatives and equivalence edges in the counit orientation. -/
structure EndpointFiberObjectChoice
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y) where
  preimage : Y.obj _⦋0⦌ → X.obj _⦋0⦌
  counitEdge : ∀ y : Y.obj _⦋0⦌,
    SSet.Edge (F.hom.app (op ⦋0⦌) (preimage y)) y
  counitEdge_isEquivalence : ∀ y : Y.obj _⦋0⦌,
    EdgeIsEquivalence (counitEdge y)

/-- Essential surjectivity supplies actual representative vertices and equivalence edges. -/
theorem endpointFiberEssentialSurjectivityChoices
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hess : (SSet.hoFunctor.map F.hom).toFunctor.EssSurj) :
    Nonempty (EndpointFiberObjectChoice F) := by
  letI := hess
  letI : SSet.Quasicategory Y.obj := Y.property
  have hchoice : ∀ y : Y.obj _⦋0⦌, ∃ x : X.obj _⦋0⦌,
      ∃ e : SSet.Edge (F.hom.app (op ⦋0⦌) x) y, EdgeIsEquivalence e := by
    intro y
    obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage
      (SSet.hoFunctor.map F.hom).toFunctor (homotopyObject y)
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    let s := homotopyCategory_homMk_surjective_of_quasicategory i.hom
    refine ⟨x, SSet.Edge.ofTruncated s.choose, ?_⟩
    change IsIso (SSet.Truncated.HomotopyCategory.homMk s.choose)
    rw [s.choose_spec]
    infer_instance
  exact ⟨⟨
    fun y ↦ (hchoice y).choose,
    fun y ↦ (hchoice y).choose_spec.choose,
    fun y ↦ (hchoice y).choose_spec.choose_spec
  ⟩⟩

end Infinity
end LeanLCAExactChallenge
