/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.StableSquareCalculusConstruction
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Gluing functor quasicategories along finite simplicial cell attachments -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed

/-- Restriction of diagrams along an arbitrary map of simplicial-set shapes. -/
def functorQCatRestriction {K L : SSet.{u}} (f : K ⟶ L) (Q : SSet.QCat.{u}) :
    functorQCat L Q (canonicalFunctorQuasicategory L Q) ⟶
      functorQCat K Q (canonicalFunctorQuasicategory K Q) :=
  ObjectProperty.homMk ((MonoidalClosed.pre f).app Q.obj)

/-- Functor quasicategory for one of the four shapes in a cell attachment. -/
abbrev CellAttachmentFunctorQCat (K : SSet.{u}) (Q : SSet.QCat.{u}) : SSet.QCat.{u} :=
  functorQCat K Q (canonicalFunctorQuasicategory K Q)

/-- Previous skeleton in the attachment of the `d`-cells of a monomorphism. -/
abbrev CellAttachmentPreviousShape {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ) : SSet.{u} :=
  SSet.skeletonOfMono i d

/-- Next skeleton in the attachment of the `d`-cells of a monomorphism. -/
abbrev CellAttachmentNextShape {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ) : SSet.{u} :=
  SSet.skeletonOfMono i (d + 1)

/-- Coproduct of boundaries in the attachment of the `d`-cells. -/
abbrev CellAttachmentBoundaryShape {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ) : SSet.{u} :=
  SSet.relativeCellComplexOfMono.sigmaBoundary i d

/-- Coproduct of standard simplices in the attachment of the `d`-cells. -/
abbrev CellAttachmentCellShape {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ) : SSet.{u} :=
  SSet.relativeCellComplexOfMono.sigmaStdSimplex i d

/-- Restrict a diagram on the next skeleton to the previous skeleton. -/
def cellAttachmentToPrevious {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ)
    (Q : SSet.QCat.{u}) :
    CellAttachmentFunctorQCat (CellAttachmentNextShape i d) Q ⟶
      CellAttachmentFunctorQCat (CellAttachmentPreviousShape i d) Q :=
  functorQCatRestriction (SSet.relativeCellComplexOfMono.r i d) Q

/-- Restrict a diagram on the next skeleton to its newly attached cells. -/
def cellAttachmentToCells {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ)
    (Q : SSet.QCat.{u}) :
    CellAttachmentFunctorQCat (CellAttachmentNextShape i d) Q ⟶
      CellAttachmentFunctorQCat (CellAttachmentCellShape i d) Q :=
  functorQCatRestriction (SSet.relativeCellComplexOfMono.b i d) Q

/-- Restrict a previous-skeleton diagram to the attaching boundaries. -/
def cellAttachmentPreviousToBoundary {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ)
    (Q : SSet.QCat.{u}) :
    CellAttachmentFunctorQCat (CellAttachmentPreviousShape i d) Q ⟶
      CellAttachmentFunctorQCat (CellAttachmentBoundaryShape i d) Q :=
  functorQCatRestriction (SSet.relativeCellComplexOfMono.t i d) Q

/-- Restrict a cell diagram to its attaching boundaries. -/
def cellAttachmentCellsToBoundary {X Y : SSet.{u}} (i : X ⟶ Y) (d : ℕ)
    (Q : SSet.QCat.{u}) :
    CellAttachmentFunctorQCat (CellAttachmentCellShape i d) Q ⟶
      CellAttachmentFunctorQCat (CellAttachmentBoundaryShape i d) Q :=
  functorQCatRestriction (SSet.relativeCellComplexOfMono.l i d) Q

/-- Internal Hom turns a cell-attachment pushout into a pullback of functor quasicategories. -/
theorem cellAttachmentInternalHomIsPullback
    {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] (d : ℕ) (Q : SSet.QCat.{u}) :
    IsPullback
      (cellAttachmentToPrevious i d Q)
      (cellAttachmentToCells i d Q)
      (cellAttachmentPreviousToBoundary i d Q)
      (cellAttachmentCellsToBoundary i d Q) := by
  apply IsPullback.of_map_of_faithful (ObjectProperty.ι SSet.Quasicategory)
  exact ((MonoidalClosed.internalHom.flip.obj Q.obj).map_isPullback
    (SSet.relativeCellComplexOfMono.isPushout i d).op).flip

end Infinity
end LeanLCAExactChallenge
