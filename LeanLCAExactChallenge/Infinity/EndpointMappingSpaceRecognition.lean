/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaces
import LeanLCAExactChallenge.Infinity.OrdinaryLocalizationBridge
import LeanLCAExactChallenge.Infinity.BicategoricalEquivalenceInternalHom

/-! # Recognition infrastructure for endpoint mapping spaces -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory CategoryTheory.MonoidalClosed Opposite Simplicial
open scoped Bicategory MonoidalCategory MonoidalClosed

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

/-- Local equivalence of every fixed-endpoint mapping-space map. -/
def EndpointFiberLocalEquivalenceInput
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hX : ∀ x y : X.obj _⦋0⦌, SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : ∀ x y : Y.obj _⦋0⦌, SSet.Quasicategory (endpointFiber Y.obj x y)) : Prop :=
  ∀ x y : X.obj _⦋0⦌,
    IsBicategoricalEquivalence
      (endpointFiberQCatMap F x y (hX x y)
        (hY (F.hom.app (op ⦋0⦌) x) (F.hom.app (op ⦋0⦌) y)))

/-- Coherent quasi-inverse data sufficient for a bicategorical adjoint equivalence. -/
structure EndpointFiberQuasiInverseData
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y) where
  inverse : Y ⟶ X
  unitEdge :
    SSet.Edge
      (SSet.unitHomEquiv ((ihom X.obj).obj X.obj)
        (MonoidalClosed.curry' ((𝟙 X : X ⟶ X).hom)))
      (SSet.unitHomEquiv ((ihom X.obj).obj X.obj)
        (MonoidalClosed.curry' (F ≫ inverse).hom))
  unitEdge_isEquivalence : EdgeIsEquivalence unitEdge
  counitEdge :
    SSet.Edge
      (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
        (MonoidalClosed.curry' (inverse ≫ F).hom))
      (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
        (MonoidalClosed.curry' ((𝟙 Y : Y ⟶ Y).hom)))
  counitEdge_isEquivalence : EdgeIsEquivalence counitEdge

/-- Coherently realizing object choices and local inverses produces quasi-inverse data. -/
def EndpointFiberCoherentQuasiInverseContract : Prop :=
  ∀ {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hX : ∀ x y : X.obj _⦋0⦌, SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : ∀ x y : Y.obj _⦋0⦌, SSet.Quasicategory (endpointFiber Y.obj x y))
    (_choices : EndpointFiberObjectChoice F),
    EndpointFiberLocalEquivalenceInput F hX hY →
      Nonempty (EndpointFiberQuasiInverseData F)

/-- Coherent endpoint-fiber quasi-inverses imply the endpoint recognition contract. -/
theorem endpointFiberRecognition_of_coherentQuasiInverse
    (hcoherent : EndpointFiberCoherentQuasiInverseContract.{u}) :
    EndpointFiberRecognitionContract.{u} := by
  intro X Y F hX hY hess hlocal
  obtain ⟨choices⟩ := endpointFiberEssentialSurjectivityChoices F hess
  obtain ⟨data⟩ := hcoherent F hX hY choices hlocal
  letI : Category (X ⟶ X) := SSet.QCat.bicategory.homCategory X X
  letI : Category (Y ⟶ Y) := SSet.QCat.bicategory.homCategory Y Y
  let unit : (𝟙 X) ≅ F ≫ data.inverse :=
    twoIsoOfInternalHomEquivalenceEdge data.unitEdge data.unitEdge_isEquivalence
  let counit : data.inverse ≫ F ≅ 𝟙 Y :=
    twoIsoOfInternalHomEquivalenceEdge data.counitEdge data.counitEdge_isEquivalence
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit unit counit, rfl⟩

end Infinity
end LeanLCAExactChallenge
