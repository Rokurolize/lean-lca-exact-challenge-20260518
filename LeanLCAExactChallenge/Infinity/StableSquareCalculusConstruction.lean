/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.StableSquareCalculus

/-!
# Constructing stable square calculi from explicit corner extensions

This file exposes explicit corner-extension data for stable quasicategories.

The extension morphisms and their bicategorical adjunctions remain explicit.

DG nerve constructions can supply them from zero objects and mapping cones.

A shared square predicate recognizes both cartesian and cocartesian squares.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.MonoidalClosed
open Simplicial

universe u

/-- Explicit choices of the two corner-extension morphisms and their adjunctions. -/
structure StableCornerExtensionData (Q : SSet.QCat.{u}) where
  pullbackExtension :
    functorQCat PullbackCornerShape Q
        (canonicalFunctorQuasicategory PullbackCornerShape Q) ⟶
      functorQCat SquareShape Q (canonicalFunctorQuasicategory SquareShape Q)
  pullbackAdjunction :
    Bicategory.Adjunction
      (pullbackRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PullbackCornerShape Q))
      pullbackExtension
  pushoutExtension :
    functorQCat PushoutCornerShape Q
        (canonicalFunctorQuasicategory PushoutCornerShape Q) ⟶
      functorQCat SquareShape Q (canonicalFunctorQuasicategory SquareShape Q)
  pushoutAdjunction :
    Bicategory.Adjunction pushoutExtension
      (pushoutRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PushoutCornerShape Q))

/-- The chosen pullback extension proves existence of the required right adjoint. -/
@[reducible]
def StableCornerExtensionData.pullbackKanExtension {Q : SSet.QCat.{u}}
    (h : StableCornerExtensionData Q) :
    Bicategory.IsLeftAdjoint
      (pullbackRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PullbackCornerShape Q)) :=
  Bicategory.IsLeftAdjoint.mk h.pullbackAdjunction

/-- The chosen pushout extension proves existence of the required left adjoint. -/
@[reducible]
def StableCornerExtensionData.pushoutKanExtension {Q : SSet.QCat.{u}}
    (h : StableCornerExtensionData Q) :
    Bicategory.IsRightAdjoint
      (pushoutRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PushoutCornerShape Q)) :=
  Bicategory.IsRightAdjoint.mk h.pushoutAdjunction

/-- Extract selected corner extensions from adjoint-existence proofs. -/
def StableCornerExtensionData.ofAdjointExistence {Q : SSet.QCat.{u}}
    (pullbackKanExtension :
      Bicategory.IsLeftAdjoint
        (pullbackRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
          (canonicalFunctorQuasicategory PullbackCornerShape Q)))
    (pushoutKanExtension :
      Bicategory.IsRightAdjoint
        (pushoutRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
          (canonicalFunctorQuasicategory PushoutCornerShape Q))) :
    StableCornerExtensionData Q := by
  letI := pullbackKanExtension
  letI := pushoutKanExtension
  exact
    { pullbackExtension := Bicategory.rightAdjoint
        (pullbackRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
          (canonicalFunctorQuasicategory PullbackCornerShape Q))
      pullbackAdjunction := Bicategory.Adjunction.ofIsLeftAdjoint _
      pushoutExtension := Bicategory.leftAdjoint
        (pushoutRestriction Q (canonicalFunctorQuasicategory SquareShape Q)
          (canonicalFunctorQuasicategory PushoutCornerShape Q))
      pushoutAdjunction := Bicategory.Adjunction.ofIsRightAdjoint _ }

/-- A concrete square predicate recognizing both selected corner extensions. -/
structure StableSquareRecognition {Q : SSet.QCat.{u}}
    (extensions : StableCornerExtensionData Q) where
  recognized :
    (functorQCat SquareShape Q
      (canonicalFunctorQuasicategory SquareShape Q)).obj _⦋0⦌ → Prop
  pullback_iff :
    ∀ sq, IsPullbackSquare Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PullbackCornerShape Q)
        extensions.pullbackKanExtension sq ↔ recognized sq
  pushout_iff :
    ∀ sq, IsPushoutSquare Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PushoutCornerShape Q)
        extensions.pushoutKanExtension sq ↔ recognized sq

/-- Build recognition from a direct bicartesian comparison. -/
def StableSquareRecognition.ofBicartesian {Q : SSet.QCat.{u}}
    (extensions : StableCornerExtensionData Q)
    (bicartesian :
      ∀ sq : (functorQCat SquareShape Q
          (canonicalFunctorQuasicategory SquareShape Q)).obj _⦋0⦌,
        IsPullbackSquare Q (canonicalFunctorQuasicategory SquareShape Q)
            (canonicalFunctorQuasicategory PullbackCornerShape Q)
            extensions.pullbackKanExtension sq ↔
          IsPushoutSquare Q (canonicalFunctorQuasicategory SquareShape Q)
            (canonicalFunctorQuasicategory PushoutCornerShape Q)
            extensions.pushoutKanExtension sq) :
    StableSquareRecognition extensions where
  recognized sq :=
    IsPullbackSquare Q (canonicalFunctorQuasicategory SquareShape Q)
      (canonicalFunctorQuasicategory PullbackCornerShape Q)
      extensions.pullbackKanExtension sq
  pullback_iff _ := Iff.rfl
  pushout_iff sq := (bicartesian sq).symm

/-- A shared recognition predicate identifies the selected cartesian and cocartesian squares. -/
theorem StableSquareRecognition.bicartesian {Q : SSet.QCat.{u}}
    {extensions : StableCornerExtensionData Q}
    (h : StableSquareRecognition extensions)
    (sq : (functorQCat SquareShape Q
      (canonicalFunctorQuasicategory SquareShape Q)).obj _⦋0⦌) :
    IsPullbackSquare Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PullbackCornerShape Q)
        extensions.pullbackKanExtension sq ↔
      IsPushoutSquare Q (canonicalFunctorQuasicategory SquareShape Q)
        (canonicalFunctorQuasicategory PushoutCornerShape Q)
        extensions.pushoutKanExtension sq :=
  (h.pullback_iff sq).trans (h.pushout_iff sq).symm

/-- Package corner extensions and recognition as a stable square calculus. -/
def StableSquareCalculus.ofCornerExtensions {Q : SSet.QCat.{u}}
    (pointed : PointedStructure Q)
    (finiteBicomplete : HasFiniteInfinityBicompleteness Q)
    (extensions : StableCornerExtensionData Q)
    (recognition : StableSquareRecognition extensions) : StableSquareCalculus Q where
  pointed := pointed
  finiteBicomplete := finiteBicomplete
  pullbackKanExtension := extensions.pullbackKanExtension
  pushoutKanExtension := extensions.pushoutKanExtension
  bicartesian := recognition.bicartesian

/-- Expose the corner extensions and adjunctions in a stable square calculus. -/
def StableSquareCalculus.toCornerExtensionData {Q : SSet.QCat.{u}}
    (h : StableSquareCalculus Q) : StableCornerExtensionData Q :=
  StableCornerExtensionData.ofAdjointExistence h.pullbackKanExtension h.pushoutKanExtension

/-- Recover common square recognition from a stable square calculus. -/
def StableSquareCalculus.toSquareRecognition {Q : SSet.QCat.{u}}
    (h : StableSquareCalculus Q) : StableSquareRecognition h.toCornerExtensionData := by
  apply StableSquareRecognition.ofBicartesian
  intro sq
  have hp : h.toCornerExtensionData.pullbackKanExtension = h.pullbackKanExtension :=
    Subsingleton.elim _ _
  have hc : h.toCornerExtensionData.pushoutKanExtension = h.pushoutKanExtension :=
    Subsingleton.elim _ _
  rw [hp, hc]
  exact h.bicartesian sq

end Infinity
end LeanLCAExactChallenge
