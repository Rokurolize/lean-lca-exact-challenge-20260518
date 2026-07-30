/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedCoefficientUniqueness
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEnrichedNaturalTransformationElements

/-! # The category of annihilating enriched functors

Morphisms are strict unit-graded enriched natural transformations whose components commute
with every chosen contracting element.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open scoped MonoidalCategory

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]

/-- A unit-graded enriched transformation that commutes with all selected contracting
elements. -/
structure AnnihilatingEnrichedFunctorNatTrans
    (E F : AnnihilatingEnrichedFunctorData D) where
  hom : QuotientDGUnitGradedNatTrans E.functor F.functor
  contraction_naturality : ∀ A : CorrectedAcyclicComplexCategory,
    quotientDGComposeElement
        (E.functor.obj (op A.obj))
        (E.functor.obj (op A.obj))
        (F.functor.obj (op A.obj))
        (-1) 0 (-1) (by omega)
        (E.contraction A)
        (quotientDGUnitGradedNatTransElement hom (op A.obj)) =
      quotientDGComposeElement
        (E.functor.obj (op A.obj))
        (F.functor.obj (op A.obj))
        (F.functor.obj (op A.obj))
        0 (-1) (-1) (by omega)
        (quotientDGUnitGradedNatTransElement hom (op A.obj))
        (F.contraction A)

@[ext]
theorem AnnihilatingEnrichedFunctorNatTrans.ext
    {E F : AnnihilatingEnrichedFunctorData D}
    {α β : AnnihilatingEnrichedFunctorNatTrans E F}
    (h : α.hom = β.hom) : α = β := by
  cases α
  cases β
  cases h
  rfl

/-- Transport an annihilating enriched transformation along equalities of its source and
target data. -/
noncomputable def annihilatingEnrichedFunctorNatTransTransport
    {E E' F F' : AnnihilatingEnrichedFunctorData D}
    (hE : E = E') (hF : F = F')
    (α : AnnihilatingEnrichedFunctorNatTrans E F) :
    AnnihilatingEnrichedFunctorNatTrans E' F' := by
  subst E'
  subst F'
  exact α

/-- Transport does not change the underlying component family, up to heterogeneous
equality. -/
theorem annihilatingEnrichedFunctorNatTransTransport_app_heq
    {E E' F F' : AnnihilatingEnrichedFunctorData D}
    (hE : E = E') (hF : F = F')
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    (X : OriginalCoefficientDGCategory) :
    HEq ((annihilatingEnrichedFunctorNatTransTransport hE hF α).hom.app X)
      (α.hom.app X) := by
  cases hE
  cases hF
  rfl

/-- The identity transformation preserves the selected contractions. -/
noncomputable def annihilatingEnrichedFunctorNatTransId
    (E : AnnihilatingEnrichedFunctorData D) :
    AnnihilatingEnrichedFunctorNatTrans E E where
  hom := quotientDGUnitGradedNatTransId E.functor
  contraction_naturality A := by
    rw [quotientDGUnitGradedNatTransId_element]
    exact (quotientDGComposeElement_identity_right
      (E.functor.obj (op A.obj)) (E.functor.obj (op A.obj)) (-1)
      (E.contraction A)).trans
        (quotientDGComposeElement_identity_left
          (E.functor.obj (op A.obj)) (E.functor.obj (op A.obj)) (-1)
          (E.contraction A)).symm

/-- Vertical composition preserves compatibility with all selected contractions. -/
noncomputable def annihilatingEnrichedFunctorNatTransComp
    {E F G : AnnihilatingEnrichedFunctorData D}
    (α : AnnihilatingEnrichedFunctorNatTrans E F)
    (β : AnnihilatingEnrichedFunctorNatTrans F G) :
    AnnihilatingEnrichedFunctorNatTrans E G where
  hom := quotientDGUnitGradedNatTransComp α.hom β.hom
  contraction_naturality A := by
    let X := E.functor.obj (op A.obj)
    let Y := F.functor.obj (op A.obj)
    let Z := G.functor.obj (op A.obj)
    let h := E.contraction A
    let a := quotientDGUnitGradedNatTransElement α.hom (op A.obj)
    let b := quotientDGUnitGradedNatTransElement β.hom (op A.obj)
    let k := F.contraction A
    let l := G.contraction A
    rw [quotientDGUnitGradedNatTransComp_element]
    have hassoc₁ := quotientDGComposeElement_assoc X X Y Z (-1) 0 0 h a b
    have hassoc₂ := quotientDGComposeElement_assoc X Y Y Z 0 (-1) 0 a k b
    have hassoc₃ := quotientDGComposeElement_assoc X Y Z Z 0 0 (-1) a b l
    have hα := α.contraction_naturality A
    have hβ := β.contraction_naturality A
    change quotientDGComposeElement X X Z (-1) 0 (-1) (by omega) h
        (quotientDGComposeElement X Y Z 0 0 0 rfl a b) =
      quotientDGComposeElement X Z Z 0 (-1) (-1) (by omega)
        (quotientDGComposeElement X Y Z 0 0 0 rfl a b) l
    calc
      _ = quotientDGComposeElement X Y Z (-1) 0 (-1) (by omega)
          (quotientDGComposeElement X X Y (-1) 0 (-1) (by omega) h a) b := by
        simpa [X, Y, Z, h, a, b] using hassoc₁.symm
      _ = quotientDGComposeElement X Y Z (-1) 0 (-1) (by omega)
          (quotientDGComposeElement X Y Y 0 (-1) (-1) (by omega) a k) b := by
        rw [hα]
      _ = quotientDGComposeElement X Y Z 0 (-1) (-1) (by omega) a
          (quotientDGComposeElement Y Y Z (-1) 0 (-1) (by omega) k b) := by
        simpa [X, Y, Z, a, k, b] using hassoc₂
      _ = quotientDGComposeElement X Y Z 0 (-1) (-1) (by omega) a
          (quotientDGComposeElement Y Z Z 0 (-1) (-1) (by omega) b l) := by
        rw [hβ]
      _ = quotientDGComposeElement X Z Z 0 (-1) (-1) (by omega)
          (quotientDGComposeElement X Y Z 0 0 0 rfl a b) l := by
        simpa [X, Y, Z, a, b, l] using hassoc₃.symm

/-- Restriction of a quotient-enriched transformation preserves the selected contractions. -/
noncomputable def quotientDGUnitGradedNatTransRestriction
    {G H : EnrichedFunctor QuotientDGCochain CorrectedQuotientDGCategory D}
    (α : QuotientDGUnitGradedNatTrans G H) :
    AnnihilatingEnrichedFunctorNatTrans
      (AnnihilatingEnrichedFunctorData.restriction G)
      (AnnihilatingEnrichedFunctorData.restriction H) where
  hom := quotientDGUnitGradedNatTransPrecomp
    originalToCorrectedQuotientDG α
  contraction_naturality A := by
    let K : CorrectedQuotientDGCategory := op A.obj
    let x : (K ⟶[QuotientDGCochain] K).X (-1) :=
      ULift.up (quotientContractingElement A)
    have h := quotientDGUnitGradedNatTrans_naturality_element
      α K K (-1) x
    change quotientDGComposeElement (G.obj K) (G.obj K) (H.obj K)
        (-1) 0 (-1) (by omega) ((G.map K K).f (-1) x)
        (quotientDGUnitGradedNatTransElement α K) =
      quotientDGComposeElement (G.obj K) (H.obj K) (H.obj K)
        0 (-1) (-1) (by omega)
        (quotientDGUnitGradedNatTransElement α K) ((H.map K K).f (-1) x)
    exact h

/-- The category whose objects are annihilating enriched-functor data. -/
def AnnihilatingEnrichedFunctorCategory
    (D : Type*) [EnrichedCategory QuotientDGCochain D] :=
  AnnihilatingEnrichedFunctorData D

noncomputable instance : Category (AnnihilatingEnrichedFunctorCategory D) where
  Hom E F := AnnihilatingEnrichedFunctorNatTrans E F
  id E := annihilatingEnrichedFunctorNatTransId E
  comp α β := annihilatingEnrichedFunctorNatTransComp α β
  id_comp α := by
    apply AnnihilatingEnrichedFunctorNatTrans.ext
    exact quotientDGUnitGradedNatTrans_id_comp α.hom
  comp_id α := by
    apply AnnihilatingEnrichedFunctorNatTrans.ext
    exact quotientDGUnitGradedNatTrans_comp_id α.hom
  assoc α β γ := by
    apply AnnihilatingEnrichedFunctorNatTrans.ext
    exact quotientDGUnitGradedNatTrans_assoc α.hom β.hom γ.hom

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
