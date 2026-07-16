/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.Basic
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! # Endpoint-fiber mapping-space contracts -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open scoped MonoidalCategory MonoidalClosed
open Simplicial Opposite

abbrev endpointObject (Q : SSet.{u}) : SSet.{u} :=
  (ihom (Δ[0] : SSet.{u})).obj Q ⊗
    (ihom (Δ[0] : SSet.{u})).obj Q

def endpointEvaluation (Q : SSet.{u}) :
    (ihom (Δ[1] : SSet.{u})).obj Q ⟶ endpointObject Q :=
  CartesianMonoidalCategory.lift
    ((MonoidalClosed.pre (SSet.stdSimplex.δ (1 : Fin 2))).app Q)
    ((MonoidalClosed.pre (SSet.stdSimplex.δ (0 : Fin 2))).app Q)

def endpointVertex (Q : SSet.{u}) (x : Q _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ Q :=
  SSet.const x

def endpointPoint (Q : SSet.{u}) (x y : Q _⦋0⦌) :
    𝟙_ SSet.{u} ⟶ endpointObject Q :=
  CartesianMonoidalCategory.lift
    (MonoidalClosed.curry' (endpointVertex Q x))
    (MonoidalClosed.curry' (endpointVertex Q y))

def endpointObjectMap {X Y : SSet.{u}} (F : X ⟶ Y) :
    endpointObject X ⟶ endpointObject Y :=
  (ihom (Δ[0] : SSet.{u})).map F ⊗ₘ
    (ihom (Δ[0] : SSet.{u})).map F

@[reassoc]
lemma endpointEvaluation_naturality {X Y : SSet.{u}} (F : X ⟶ Y) :
    endpointEvaluation X ≫ endpointObjectMap F =
      (ihom (Δ[1] : SSet.{u})).map F ≫ endpointEvaluation Y := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [endpointEvaluation, endpointObjectMap, Category.assoc,
      CartesianMonoidalCategory.lift_fst_assoc,
      CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.lift_fst]
    exact MonoidalClosed.pre_comm_ihom_map _ _
  · simp only [endpointEvaluation, endpointObjectMap, Category.assoc,
      CartesianMonoidalCategory.lift_snd_assoc,
      CartesianMonoidalCategory.tensorHom_snd,
      CartesianMonoidalCategory.lift_snd]
    exact MonoidalClosed.pre_comm_ihom_map _ _

@[reassoc]
lemma endpointPoint_naturality {X Y : SSet.{u}} (F : X ⟶ Y)
    (x y : X _⦋0⦌) :
    endpointPoint X x y ≫ endpointObjectMap F =
      endpointPoint Y (F.app (op ⦋0⦌) x) (F.app (op ⦋0⦌) y) := by
  simp [endpointPoint, endpointObjectMap, endpointVertex,
    MonoidalClosed.curry'_ihom_map]

abbrev endpointFiber (Q : SSet.{u}) (x y : Q _⦋0⦌) : SSet.{u} :=
  pullback (endpointPoint Q x y) (endpointEvaluation Q)

noncomputable def endpointFiberMap {X Y : SSet.{u}} (F : X ⟶ Y)
    (x y : X _⦋0⦌) :
    endpointFiber X x y ⟶
      endpointFiber Y (F.app (op ⦋0⦌) x) (F.app (op ⦋0⦌) y) :=
  pullback.map
    (endpointPoint X x y)
    (endpointEvaluation X)
    (endpointPoint Y (F.app (op ⦋0⦌) x) (F.app (op ⦋0⦌) y))
    (endpointEvaluation Y)
    (𝟙 (𝟙_ SSet.{u}))
    ((ihom (Δ[1] : SSet.{u})).map F)
    (endpointObjectMap F)
    (by simpa using endpointPoint_naturality F x y)
    (endpointEvaluation_naturality F)

def endpointFiberQCat (Q : SSet.{u}) (x y : Q _⦋0⦌)
    (h : SSet.Quasicategory (endpointFiber Q x y)) :
    SSet.QCat.{u} :=
  ⟨endpointFiber Q x y, h⟩

def endpointFiberQCatMap {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (x y : X.obj _⦋0⦌)
    (hX : SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : SSet.Quasicategory
      (endpointFiber Y.obj
        (F.hom.app (op ⦋0⦌) x) (F.hom.app (op ⦋0⦌) y))) :
    endpointFiberQCat X.obj x y hX ⟶
      endpointFiberQCat Y.obj
        (F.hom.app (op ⦋0⦌) x) (F.hom.app (op ⦋0⦌) y) hY :=
  ObjectProperty.homMk (endpointFiberMap F.hom x y)

def EndpointFibersAreKanContract : Prop :=
  ∀ (Q : SSet.QCat.{u}) (x y : Q.obj _⦋0⦌),
    SSet.KanComplex (endpointFiber Q.obj x y)

def EndpointFiberRecognitionContract : Prop :=
  ∀ {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hX : ∀ x y : X.obj _⦋0⦌,
      SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : ∀ x y : Y.obj _⦋0⦌,
      SSet.Quasicategory (endpointFiber Y.obj x y)),
    (SSet.hoFunctor.map F.hom).toFunctor.EssSurj →
    (∀ x y : X.obj _⦋0⦌,
      IsBicategoricalEquivalence
        (endpointFiberQCatMap F x y (hX x y)
          (hY (F.hom.app (op ⦋0⦌) x)
            (F.hom.app (op ⦋0⦌) y)))) →
    IsBicategoricalEquivalence F

end Infinity
end LeanLCAExactChallenge
