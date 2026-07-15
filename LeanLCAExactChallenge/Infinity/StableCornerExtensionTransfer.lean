/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.StableEquivalenceTransferFull
import LeanLCAExactChallenge.Infinity.StableSquareCalculusConstruction

/-!
# Corner-extension transfer across bicategorical equivalences

This file packages the explicit corner-extension construction as a stable-structure transfer.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalClosed
open Simplicial
open scoped Bicategory MonoidalCategory

universe u

local instance qcatHomCategoryCornerTransfer (A B : SSet.QCat.{u}) : Category (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

local instance qcatPropertyCornerTransfer (Q : SSet.QCat.{u}) : SSet.Quasicategory Q.obj :=
  Q.property

noncomputable def StableCornerExtensionData.ofBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (pointed : PointedStructure X)
    (finiteBicomplete : HasFiniteInfinityBicompleteness X)
    (extensions : StableCornerExtensionData X)
    (recognition : StableSquareRecognition extensions)
    (e : Bicategory.Equivalence X Y) : StableCornerExtensionData Y :=
  (StableSquareCalculus.ofBicategoricalEquivalence
      (StableSquareCalculus.ofCornerExtensions pointed finiteBicomplete extensions recognition) e)
    |>.toCornerExtensionData

noncomputable def StableSquareRecognition.ofBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (pointed : PointedStructure X)
    (finiteBicomplete : HasFiniteInfinityBicompleteness X)
    (extensions : StableCornerExtensionData X)
    (recognition : StableSquareRecognition extensions)
    (e : Bicategory.Equivalence X Y) :
    StableSquareRecognition
      (StableCornerExtensionData.ofBicategoricalEquivalence
        pointed finiteBicomplete extensions recognition e) :=
  (StableSquareCalculus.ofBicategoricalEquivalence
      (StableSquareCalculus.ofCornerExtensions pointed finiteBicomplete extensions recognition) e)
    |>.toSquareRecognition

noncomputable def StableInfinityStructure.ofCornerExtensionsBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (pointed : PointedStructure X)
    (finiteBicomplete : HasFiniteInfinityBicompleteness X)
    (extensions : StableCornerExtensionData X)
    (recognition : StableSquareRecognition extensions)
    (e : Bicategory.Equivalence X Y) : StableInfinityStructure Y :=
  (StableSquareCalculus.ofBicategoricalEquivalence
      (StableSquareCalculus.ofCornerExtensions pointed finiteBicomplete extensions recognition) e)
    |>.toStableInfinityStructure

end LeanLCAExactChallenge.Infinity
