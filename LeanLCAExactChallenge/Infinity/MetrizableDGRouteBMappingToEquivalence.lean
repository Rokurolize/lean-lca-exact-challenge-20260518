/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.BicategoricalEquivalenceInternalHom
import LeanLCAExactChallenge.Infinity.BicategoricalEquivalenceTwoOfThree
import LeanLCAExactChallenge.Infinity.MetrizableDGLocalizationComparison

/-! # Route B mapping localization to base-change equivalence -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory
open scoped Bicategory

local instance routeBQCatHomCategory (X Y : SSet.QCat.{u}) :
    Category (X ⟶ Y) :=
  SSet.QCat.bicategory.homCategory X Y

private theorem routeBHoFunctorInternalHomPrecompObj
    {X Y Q : SSet.QCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Q) :
    (SSet.hoFunctor.map (internalHomPrecomp f.hom Q.obj)).toFunctor.obj
        ((qcatHomToEnrichedHom Y Q).obj g) =
      (qcatHomToEnrichedHom X Q).obj (f ≫ g) := by
  rfl

private theorem routeBInternalHomPrecompReflectsBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (f : X ⟶ Y)
    (h : ∀ Q : SSet.QCat.{u},
      IsBicategoricalEquivalence
        (ObjectProperty.homMk (internalHomPrecomp f.hom Q.obj) :
          internalHomQCat Y.obj Q.obj
              (@quasicategory_ihom Y.obj Q.obj Q.property) ⟶
            internalHomQCat X.obj Q.obj
              (@quasicategory_ihom X.obj Q.obj Q.property))) :
    IsBicategoricalEquivalence f := by
  let HX := (SSet.hoFunctor.map (internalHomPrecomp f.hom X.obj)).toFunctor
  let HY := (SSet.hoFunctor.map (internalHomPrecomp f.hom Y.obj)).toFunctor
  haveI : HX.IsEquivalence := IsBicategoricalEquivalence.hoFunctor_isEquivalence (h X)
  haveI : HY.IsEquivalence := IsBicategoricalEquivalence.hoFunctor_isEquivalence (h Y)
  let EYX := qcatHomToEnrichedHom Y X
  let EXX := qcatHomToEnrichedHom X X
  let EYY := qcatHomToEnrichedHom Y Y
  let EXY := qcatHomToEnrichedHom X Y
  let v := HX.inv.obj (EXX.obj (𝟙 X))
  let g : Y ⟶ X := EYX.inv.obj v
  let unitBase : EXX.obj (f ≫ g) ≅ EXX.obj (𝟙 X) :=
    eqToIso (routeBHoFunctorInternalHomPrecompObj f g).symm ≪≫
      HX.mapIso (EYX.objObjPreimageIso v) ≪≫
        HX.objObjPreimageIso (EXX.obj (𝟙 X))
  let unit' : f ≫ g ≅ 𝟙 X := EXX.preimageIso unitBase
  let counitImage : f ≫ (g ≫ f) ≅ f ≫ 𝟙 Y :=
    ((α_ f g f).symm.trans (Bicategory.whiskerRightIso unit' f)).trans
      ((Bicategory.leftUnitor f).trans (Bicategory.rightUnitor f).symm)
  let counitBaseImage :
      HY.obj (EYY.obj (g ≫ f)) ≅ HY.obj (EYY.obj (𝟙 Y)) :=
    eqToIso (routeBHoFunctorInternalHomPrecompObj f (g ≫ f)) ≪≫
      EXY.mapIso counitImage ≪≫
        eqToIso (routeBHoFunctorInternalHomPrecompObj f (𝟙 Y)).symm
  let counitBase : EYY.obj (g ≫ f) ≅ EYY.obj (𝟙 Y) :=
    HY.preimageIso counitBaseImage
  let counit : g ≫ f ≅ 𝟙 Y := EYY.preimageIso counitBase
  exact ⟨Bicategory.Equivalence.mkOfAdjointifyCounit unit'.symm counit, rfl⟩

private theorem routeBMappingLocalizationTriangleUniqueness
    {A L D : SSet.QCat.{u}} (W : EdgeMarking A.obj)
    (ell : A ⟶ L) (d : A ⟶ D) (b : L ⟶ D)
    (htriangle : ell ≫ b = d)
    (hL : MappingQuasicategoryLocalizationProperty W ell)
    (hD : MappingQuasicategoryLocalizationProperty W d) :
    IsBicategoricalEquivalence b := by
  apply routeBInternalHomPrecompReflectsBicategoricalEquivalence b
  intro Q
  let l := (hL.universal Q).some
  let r := (hD.universal Q).some
  let pre :
      internalHomQCat D.obj Q.obj
          (@quasicategory_ihom D.obj Q.obj Q.property) ⟶
        internalHomQCat L.obj Q.obj
          (@quasicategory_ihom L.obj Q.obj Q.property) :=
    ObjectProperty.homMk (internalHomPrecomp b.hom Q.obj)
  let cL :
      internalHomQCat L.obj Q.obj l.sourceQuasicategory ⟶
        relativeInternalHomQCat W Q.obj l.targetQuasicategory :=
    ObjectProperty.homMk l.comparison
  let cD :
      internalHomQCat D.obj Q.obj r.sourceQuasicategory ⟶
        relativeInternalHomQCat W Q.obj r.targetQuasicategory :=
    ObjectProperty.homMk r.comparison
  have htriangleHom : ell.hom ≫ b.hom = d.hom :=
    congrArg (fun k ↦ k.hom) htriangle
  have hcomparison : pre ≫ cL = cD := by
    apply ObjectProperty.hom_ext SSet.Quasicategory
    change internalHomPrecomp b.hom Q.obj ≫ l.comparison = r.comparison
    apply (cancel_mono (relativeInternalHom W Q.obj).ι).1
    rw [Category.assoc, l.comparison_comp_inclusion,
      r.comparison_comp_inclusion, internalHomPrecomp_comp,
      htriangleHom]
  apply IsBicategoricalEquivalence.of_comp_right l.isEquivalence
  rw [hcomparison]
  exact r.isEquivalence

namespace MetrizableBoundedComplexes

/-- The direct-DG mapping localization property forces the exact base-change map to be a
bicategorical equivalence. -/
theorem routeBBaseChange_isBicategoricalEquivalence
    (h : MetrizableDirectDGMappingLocalizationProperty) :
    IsBicategoricalEquivalence
      metrizableOrdinaryToDirectDGBaseChangeQCatMap := by
  apply routeBMappingLocalizationTriangleUniqueness
    (relativeNerveEdgeMarking relativeCategory)
    metrizableEquivalenceForcingQCatMap
    metrizableComplexNerveToLocalizedDirectDGQCatMap
  · exact metrizableOrdinaryToDirectDGBaseChangeQCat_triangle
  · exact metrizableEquivalenceForcingMappingLocalizationProperty_direct
  · exact h

end MetrizableBoundedComplexes

end LeanLCAExactChallenge.Infinity

