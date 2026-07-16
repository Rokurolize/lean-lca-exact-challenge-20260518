/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.Basic

/-! # Two-out-of-three for bicategorical equivalences -/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open scoped Bicategory

private noncomputable def reverseBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y) :
    Bicategory.Equivalence Y X :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm

private noncomputable def bicategoricalEquivalenceOfIso
    {X Y : SSet.QCat.{u}} {f : X ⟶ Y} (e : Bicategory.Equivalence X Y)
    (i : e.hom ≅ f) : Bicategory.Equivalence X Y := by
  let unit : 𝟙 X ≅ f ≫ e.inv :=
    e.unit ≪≫ Bicategory.whiskerRightIso i e.inv
  let counit : e.inv ≫ f ≅ 𝟙 Y :=
    Bicategory.whiskerLeftIso e.inv i.symm ≪≫ e.counit
  exact Bicategory.Equivalence.mkOfAdjointifyCounit unit counit

/-- If `f` and `f ≫ g` are bicategorical equivalences, then so is `g`. -/
theorem IsBicategoricalEquivalence.of_comp_left
    {X Y Z : SSet.QCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsBicategoricalEquivalence f)
    (hfg : IsBicategoricalEquivalence (f ≫ g)) :
    IsBicategoricalEquivalence g := by
  obtain ⟨ef, rfl⟩ := hf
  obtain ⟨efg, hfg⟩ := hfg
  let e := bicategoricalEquivalenceComp (reverseBicategoricalEquivalence ef) efg
  let i : e.hom ≅ g :=
    Bicategory.whiskerLeftIso ef.inv (eqToIso hfg) ≪≫
      (α_ ef.inv ef.hom g).symm ≪≫
        Bicategory.whiskerRightIso ef.counit g ≪≫
          λ_ g
  exact ⟨bicategoricalEquivalenceOfIso e i, rfl⟩

/-- If `g` and `f ≫ g` are bicategorical equivalences, then so is `f`. -/
theorem IsBicategoricalEquivalence.of_comp_right
    {X Y Z : SSet.QCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hg : IsBicategoricalEquivalence g)
    (hfg : IsBicategoricalEquivalence (f ≫ g)) :
    IsBicategoricalEquivalence f := by
  obtain ⟨eg, rfl⟩ := hg
  obtain ⟨efg, hfg⟩ := hfg
  let e := bicategoricalEquivalenceComp efg (reverseBicategoricalEquivalence eg)
  let i : e.hom ≅ f :=
    Bicategory.whiskerRightIso (eqToIso hfg) eg.inv ≪≫
      α_ f eg.hom eg.inv ≪≫
        Bicategory.whiskerLeftIso f eg.unit.symm ≪≫
          ρ_ f
  exact ⟨bicategoricalEquivalenceOfIso e i, rfl⟩

end Infinity
end LeanLCAExactChallenge
