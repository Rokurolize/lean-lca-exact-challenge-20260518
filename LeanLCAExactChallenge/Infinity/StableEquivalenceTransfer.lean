/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.StableSquareCalculus
import LeanLCAExactChallenge.Infinity.BicategoricalEquivalenceInternalHom

/-!
# Stable-structure transfer across quasicategorical equivalences

This file transfers stable structure across quasicategorical equivalences.

It does not infer stability from the homotopy category.
-/

set_option autoImplicit false

noncomputable section

namespace CategoryTheory.Bicategory

open Category
open scoped Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]
variable {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

/-- Transport an adjunction across an invertible two-cell on its left adjoint. -/
def Adjunction.ofIsoLeft (adj : Adjunction f g) (i : f' ≅ f) : Adjunction f' g where
  unit := adj.unit ≫ (whiskerRightIso i g).inv
  counit := (whiskerLeftIso g i).hom ≫ adj.counit
  left_triangle := by
    dsimp only [leftZigzag, whiskerRightIso, whiskerLeftIso]
    calc
      _ = (λ_ f').hom ≫ i.hom ≫ (λ_ f).inv ≫
          leftZigzag adj.unit adj.counit ≫
          (ρ_ f).hom ≫ i.inv ≫ (ρ_ f').inv := by
            bicategory
            simp only [Iso.trans_refl, whiskerRightIso_hom, Iso.refl_hom,
              id_whiskerRight, Iso.refl_trans, BicategoricalCoherence.assoc_iso,
              BicategoricalCoherence.whiskerRight_iso,
              BicategoricalCoherence.refl_iso, Iso.trans_assoc, Iso.trans_hom,
              whiskerRight_comp, id_comp, Iso.inv_hom_id, whiskerLeftIso_hom,
              whiskerLeft_id, comp_id, Iso.symm_hom]
            rw [← leftUnitor_naturality_assoc i.hom, Iso.hom_inv_id_assoc]
            rw [← rightUnitor_naturality_assoc i.inv]
            simp only [Iso.hom_inv_id, Category.comp_id]
            rw [associator_naturality_left_assoc i.inv g f']
            rw [← whisker_exchange_assoc i.inv (g ◁ i.hom)]
            rw [← whisker_exchange i.inv adj.counit]
            rw [whisker_exchange_assoc adj.unit i.hom]
            rw [associator_naturality_right_assoc f g i.hom]
      _ = (λ_ f').hom ≫ i.hom ≫ (λ_ f).inv ≫
          ((λ_ f).hom ≫ (ρ_ f).inv) ≫
          (ρ_ f).hom ≫ i.inv ≫ (ρ_ f').inv := by
        rw [adj.left_triangle]
      _ = (λ_ f').hom ≫ (ρ_ f').inv := by simp
  right_triangle := by
    dsimp only [rightZigzag, whiskerRightIso, whiskerLeftIso]
    calc
      _ = rightZigzag adj.unit adj.counit := by
        bicategory
        simp
      _ = _ := adj.right_triangle

/-- Transport an adjunction across an invertible two-cell on its right adjoint. -/
def Adjunction.ofIsoRight (adj : Adjunction f g) (i : g' ≅ g) : Adjunction f g' where
  unit := adj.unit ≫ (whiskerLeftIso f i).inv
  counit := (whiskerRightIso i f).hom ≫ adj.counit
  left_triangle := by
    dsimp only [leftZigzag, whiskerRightIso, whiskerLeftIso]
    calc
      _ = leftZigzag adj.unit adj.counit := by
        bicategory
        simp
      _ = _ := adj.left_triangle
  right_triangle := by
    dsimp only [rightZigzag, whiskerRightIso, whiskerLeftIso]
    calc
      _ = (ρ_ g').hom ≫ i.hom ≫ (ρ_ g).inv ≫
          rightZigzag adj.unit adj.counit ≫
          (λ_ g).hom ≫ i.inv ≫ (λ_ g').inv := by
            bicategory
            simp only [whiskerLeftIso_hom, Iso.refl_hom, whiskerLeft_id,
              Iso.refl_trans, BicategoricalCoherence.assoc'_iso,
              BicategoricalCoherence.whiskerRight_iso,
              BicategoricalCoherence.refl_iso, Iso.trans_refl,
              Iso.trans_assoc, Iso.trans_hom, whiskerRightIso_hom,
              whiskerRight_comp, id_whiskerRight, id_comp, Iso.inv_hom_id,
              Iso.symm_hom, comp_id]
            rw [← rightUnitor_naturality_assoc i.hom, Iso.hom_inv_id_assoc]
            rw [← leftUnitor_naturality_assoc i.inv]
            simp only [Iso.hom_inv_id, Category.comp_id]
            rw [associator_inv_naturality_right_assoc g' f i.inv]
            rw [whisker_exchange_assoc (i.hom ▷ f) i.inv]
            rw [whisker_exchange adj.counit i.inv]
            rw [← whisker_exchange_assoc i.hom adj.unit]
            rw [associator_inv_naturality_left_assoc i.hom f g]
      _ = (ρ_ g').hom ≫ i.hom ≫ (ρ_ g).inv ≫
          ((ρ_ g).hom ≫ (λ_ g).inv) ≫
          (λ_ g).hom ≫ i.inv ≫ (λ_ g').inv := by
        rw [adj.right_triangle]
      _ = (ρ_ g').hom ≫ (λ_ g').inv := by simp

/-- Being a left adjoint is invariant under an invertible two-cell. -/
theorem isLeftAdjoint_of_iso (hf : IsLeftAdjoint f) (i : f' ≅ f) : IsLeftAdjoint f' := by
  letI : IsLeftAdjoint f := hf
  exact IsLeftAdjoint.mk ((Adjunction.ofIsLeftAdjoint f).ofIsoLeft i)

/-- Being a right adjoint is invariant under an invertible two-cell. -/
theorem isRightAdjoint_of_iso (hg : IsRightAdjoint g) (i : g' ≅ g) : IsRightAdjoint g' := by
  letI : IsRightAdjoint g := hg
  exact IsRightAdjoint.mk ((Adjunction.ofIsRightAdjoint g).ofIsoRight i)

/-- Conjugating a map through object equivalences gives an isomorphic map. -/
noncomputable def conjugateEquivalenceIso
    {a a' b b' : B} (ea : Equivalence a a') (eb : Equivalence b b')
    {f : a ⟶ b} {f' : a' ⟶ b'} (h : ea.hom ≫ f' = f ≫ eb.hom) :
    f' ≅ ea.inv ≫ f ≫ eb.hom :=
  (λ_ f').symm ≪≫
    whiskerRightIso ea.counit.symm f' ≪≫
      α_ ea.inv ea.hom f' ≪≫
        whiskerLeftIso ea.inv (eqToIso h)

end CategoryTheory.Bicategory

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open scoped Bicategory

local instance qcatHomCategoryTransfer (A B : SSet.QCat.{u}) : Category (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- The adjunction underlying a bicategorical adjoint equivalence. -/
def bicategoricalEquivalenceAdjunction {X Y : SSet.QCat.{u}}
    (e : Bicategory.Equivalence X Y) :
    Bicategory.Adjunction e.hom e.inv where
  unit := e.unit.hom
  counit := e.counit.hom
  left_triangle := e.left_triangle_hom
  right_triangle := e.right_triangle_hom

/-- Reverse a bicategorical adjoint equivalence, allowing the counit to be adjointified. -/
def reverseBicategoricalEquivalence {X Y : SSet.QCat.{u}}
    (e : Bicategory.Equivalence X Y) : Bicategory.Equivalence Y X :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm

/-- The adjunction in the reverse direction of a bicategorical equivalence. -/
def reverseBicategoricalEquivalenceAdjunction {X Y : SSet.QCat.{u}}
    (e : Bicategory.Equivalence X Y) :
    Bicategory.Adjunction e.inv e.hom :=
  bicategoricalEquivalenceAdjunction (reverseBicategoricalEquivalence e)

theorem bicategoricalEquivalence_hom_isLeftAdjoint {X Y : SSet.QCat.{u}}
    (e : Bicategory.Equivalence X Y) : Bicategory.IsLeftAdjoint e.hom :=
  Bicategory.IsLeftAdjoint.mk (bicategoricalEquivalenceAdjunction e)

theorem bicategoricalEquivalence_hom_isRightAdjoint {X Y : SSet.QCat.{u}}
    (e : Bicategory.Equivalence X Y) : Bicategory.IsRightAdjoint e.hom :=
  Bicategory.IsRightAdjoint.mk (reverseBicategoricalEquivalenceAdjunction e)

theorem bicategoricalEquivalence_inv_isLeftAdjoint {X Y : SSet.QCat.{u}}
    (e : Bicategory.Equivalence X Y) : Bicategory.IsLeftAdjoint e.inv :=
  Bicategory.IsLeftAdjoint.mk (reverseBicategoricalEquivalenceAdjunction e)

theorem bicategoricalEquivalence_inv_isRightAdjoint {X Y : SSet.QCat.{u}}
    (e : Bicategory.Equivalence X Y) : Bicategory.IsRightAdjoint e.inv :=
  Bicategory.IsRightAdjoint.mk (bicategoricalEquivalenceAdjunction e)

/-- A composite of left adjoints is a left adjoint. -/
theorem bicategoryIsLeftAdjoint_comp
    {X Y Z : SSet.QCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Bicategory.IsLeftAdjoint f) (hg : Bicategory.IsLeftAdjoint g) :
    Bicategory.IsLeftAdjoint (f ≫ g) := by
  letI : Bicategory.IsLeftAdjoint f := hf
  letI : Bicategory.IsLeftAdjoint g := hg
  exact Bicategory.IsLeftAdjoint.mk
    ((Bicategory.Adjunction.ofIsLeftAdjoint f).comp
      (Bicategory.Adjunction.ofIsLeftAdjoint g))

/-- A composite of right adjoints is a right adjoint. -/
theorem bicategoryIsRightAdjoint_comp
    {X Y Z : SSet.QCat.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Bicategory.IsRightAdjoint f) (hg : Bicategory.IsRightAdjoint g) :
    Bicategory.IsRightAdjoint (f ≫ g) := by
  letI : Bicategory.IsRightAdjoint f := hf
  letI : Bicategory.IsRightAdjoint g := hg
  exact Bicategory.IsRightAdjoint.mk
    ((Bicategory.Adjunction.ofIsRightAdjoint g).comp
      (Bicategory.Adjunction.ofIsRightAdjoint f))

/-- A commuting square of equivalences transfers a left-adjoint structure. -/
theorem isLeftAdjoint_conjugateEquivalence
    {a a' b b' : SSet.QCat.{u}} (ea : Bicategory.Equivalence a a')
    (eb : Bicategory.Equivalence b b') {f : a ⟶ b} {f' : a' ⟶ b'}
    (h : ea.hom ≫ f' = f ≫ eb.hom) (hf : Bicategory.IsLeftAdjoint f) :
    Bicategory.IsLeftAdjoint f' := by
  have hc : Bicategory.IsLeftAdjoint (ea.inv ≫ f ≫ eb.hom) :=
    bicategoryIsLeftAdjoint_comp (f := ea.inv) (g := f ≫ eb.hom)
      (bicategoricalEquivalence_inv_isLeftAdjoint ea)
      (bicategoryIsLeftAdjoint_comp hf
        (bicategoricalEquivalence_hom_isLeftAdjoint eb))
  exact Bicategory.isLeftAdjoint_of_iso hc
    (Bicategory.conjugateEquivalenceIso ea eb h)

/-- A commuting square of equivalences transfers a right-adjoint structure. -/
theorem isRightAdjoint_conjugateEquivalence
    {a a' b b' : SSet.QCat.{u}} (ea : Bicategory.Equivalence a a')
    (eb : Bicategory.Equivalence b b') {f : a ⟶ b} {f' : a' ⟶ b'}
    (h : ea.hom ≫ f' = f ≫ eb.hom) (hf : Bicategory.IsRightAdjoint f) :
    Bicategory.IsRightAdjoint f' := by
  have hc : Bicategory.IsRightAdjoint (ea.inv ≫ f ≫ eb.hom) :=
    bicategoryIsRightAdjoint_comp (f := ea.inv) (g := f ≫ eb.hom)
      (bicategoricalEquivalence_inv_isRightAdjoint ea)
      (bicategoryIsRightAdjoint_comp hf
        (bicategoricalEquivalence_hom_isRightAdjoint eb))
  exact Bicategory.isRightAdjoint_of_iso hc
    (Bicategory.conjugateEquivalenceIso ea eb h)

/-- Pullback-corner restriction commutes with postcomposition. -/
theorem pullbackRestriction_naturality
    {X Y : SSet.QCat.{u}} (f : X ⟶ Y) :
    (ObjectProperty.homMk ((ihom SquareShape).map f.hom) :
        functorQCat SquareShape X (canonicalFunctorQuasicategory SquareShape X) ⟶
          functorQCat SquareShape Y (canonicalFunctorQuasicategory SquareShape Y)) ≫
      pullbackRestriction Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PullbackCornerShape Y) =
    pullbackRestriction X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PullbackCornerShape X) ≫
      (ObjectProperty.homMk ((ihom PullbackCornerShape).map f.hom) :
        functorQCat PullbackCornerShape X
            (canonicalFunctorQuasicategory PullbackCornerShape X) ⟶
          functorQCat PullbackCornerShape Y
            (canonicalFunctorQuasicategory PullbackCornerShape Y)) := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  exact (MonoidalClosed.pre pullbackCornerInclusion).naturality f.hom

/-- Pushout-corner restriction commutes with postcomposition. -/
theorem pushoutRestriction_naturality
    {X Y : SSet.QCat.{u}} (f : X ⟶ Y) :
    (ObjectProperty.homMk ((ihom SquareShape).map f.hom) :
        functorQCat SquareShape X (canonicalFunctorQuasicategory SquareShape X) ⟶
          functorQCat SquareShape Y (canonicalFunctorQuasicategory SquareShape Y)) ≫
      pushoutRestriction Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PushoutCornerShape Y) =
    pushoutRestriction X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PushoutCornerShape X) ≫
      (ObjectProperty.homMk ((ihom PushoutCornerShape).map f.hom) :
        functorQCat PushoutCornerShape X
            (canonicalFunctorQuasicategory PushoutCornerShape X) ⟶
          functorQCat PushoutCornerShape Y
            (canonicalFunctorQuasicategory PushoutCornerShape Y)) := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  exact (MonoidalClosed.pre pushoutCornerInclusion).naturality f.hom

/-- Pullback-corner adjunctions transfer across bicategorical equivalences. -/
theorem pullbackRestriction_isLeftAdjoint_of_bicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y)
    (hX : Bicategory.IsLeftAdjoint
      (pullbackRestriction X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PullbackCornerShape X))) :
    Bicategory.IsLeftAdjoint
      (pullbackRestriction Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PullbackCornerShape Y)) := by
  exact isLeftAdjoint_conjugateEquivalence
    (internalHomPostcompBicategoricalEquivalence e SquareShape)
    (internalHomPostcompBicategoricalEquivalence e PullbackCornerShape)
    (pullbackRestriction_naturality e.hom) hX

/-- Pushout-corner adjunctions transfer across bicategorical equivalences. -/
theorem pushoutRestriction_isRightAdjoint_of_bicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y)
    (hX : Bicategory.IsRightAdjoint
      (pushoutRestriction X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PushoutCornerShape X))) :
    Bicategory.IsRightAdjoint
      (pushoutRestriction Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PushoutCornerShape Y)) := by
  exact isRightAdjoint_conjugateEquivalence
    (internalHomPostcompBicategoricalEquivalence e SquareShape)
    (internalHomPostcompBicategoricalEquivalence e PushoutCornerShape)
    (pushoutRestriction_naturality e.hom) hX

/-- A chosen zero object transfers along a bicategorical adjoint equivalence. -/
def PointedStructure.ofBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (p : PointedStructure X)
    (e : Bicategory.Equivalence X Y) : PointedStructure Y where
  zeroObject := p.zeroObject ≫ e.hom
  initialAdjunction := by
    have hterminal : e.inv ≫ toTerminalQCat X = toTerminalQCat Y := by
      apply ObjectProperty.hom_ext SSet.Quasicategory
      exact terminalIsTerminal.hom_ext _ _
    rw [← hterminal]
    exact p.initialAdjunction.comp (bicategoricalEquivalenceAdjunction e)
  terminalAdjunction := by
    have hterminal : e.inv ≫ toTerminalQCat X = toTerminalQCat Y := by
      apply ObjectProperty.hom_ext SSet.Quasicategory
      exact terminalIsTerminal.hom_ext _ _
    rw [← hterminal]
    exact (reverseBicategoricalEquivalenceAdjunction e).comp p.terminalAdjunction

/-- A chosen zero object transfers along a bicategorical equivalence map. -/
noncomputable def PointedStructure.ofIsBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (p : PointedStructure X) (f : X ⟶ Y)
    (hf : IsBicategoricalEquivalence f) : PointedStructure Y :=
  p.ofBicategoricalEquivalence hf.choose

/-- Constant diagrams commute with postcomposition. -/
theorem constantDiagram_naturality
    {X Y : SSet.QCat.{u}} (K : SSet.{u}) (f : X ⟶ Y)
    (hx : SSet.Quasicategory ((ihom K).obj X.obj))
    (hy : SSet.Quasicategory ((ihom K).obj Y.obj)) :
    f ≫ constantDiagram K Y hy =
      constantDiagram K X hx ≫
        (ObjectProperty.homMk ((ihom K).map f.hom) :
          functorQCat K X hx ⟶ functorQCat K Y hy) := by
  apply ObjectProperty.hom_ext SSet.Quasicategory
  change f.hom ≫ curry (CategoryTheory.CartesianMonoidalCategory.snd K Y.obj) =
    curry (CategoryTheory.CartesianMonoidalCategory.snd K X.obj) ≫ (ihom K).map f.hom
  rw [← MonoidalClosed.curry_natural_left]
  congr 1

/-- Transporting a constant diagram through an equivalence gives an isomorphic map. -/
noncomputable def constantDiagramEquivalenceIso
    {X Y : SSet.QCat.{u}} (K : SSet.{u}) (e : Bicategory.Equivalence X Y) :
    constantDiagram K Y (@quasicategory_ihom K Y.obj Y.property) ≅
      e.inv ≫ constantDiagram K X (@quasicategory_ihom K X.obj X.property) ≫
        (ObjectProperty.homMk ((ihom K).map e.hom.hom) :
          functorQCat K X (@quasicategory_ihom K X.obj X.property) ⟶
            functorQCat K Y (@quasicategory_ihom K Y.obj Y.property)) := by
  let cX := constantDiagram K X (@quasicategory_ihom K X.obj X.property)
  let cY := constantDiagram K Y (@quasicategory_ihom K Y.obj Y.property)
  let p : functorQCat K X (@quasicategory_ihom K X.obj X.property) ⟶
      functorQCat K Y (@quasicategory_ihom K Y.obj Y.property) :=
    ObjectProperty.homMk ((ihom K).map e.hom.hom)
  have hnat : e.hom ≫ cY = cX ≫ p := constantDiagram_naturality K e.hom _ _
  have hcomp : e.inv ≫ cX ≫ p = (e.inv ≫ e.hom) ≫ cY := by
    rw [← hnat]
    exact (Category.assoc _ _ _).symm
  exact (λ_ cY).symm ≪≫ Bicategory.whiskerRightIso e.counit.symm cY ≪≫
    eqToIso hcomp.symm

/-- Infinity-limits of one shape transfer across an equivalence. -/
theorem hasLimitsOfShape_of_bicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (K : SSet.{u}) (e : Bicategory.Equivalence X Y)
    (hX : HasLimitsOfShape K X (@quasicategory_ihom K X.obj X.property)) :
    HasLimitsOfShape K Y (@quasicategory_ihom K Y.obj Y.property) := by
  let cX := constantDiagram K X (@quasicategory_ihom K X.obj X.property)
  let p : functorQCat K X (@quasicategory_ihom K X.obj X.property) ⟶
      functorQCat K Y (@quasicategory_ihom K Y.obj Y.property) :=
    ObjectProperty.homMk ((ihom K).map e.hom.hom)
  have hp : Bicategory.IsLeftAdjoint p :=
    bicategoricalEquivalence_hom_isLeftAdjoint
      (internalHomPostcompBicategoricalEquivalence e K)
  have hc : Bicategory.IsLeftAdjoint (e.inv ≫ cX ≫ p) :=
    bicategoryIsLeftAdjoint_comp (f := e.inv ≫ cX) (g := p)
      (bicategoryIsLeftAdjoint_comp
        (bicategoricalEquivalence_inv_isLeftAdjoint e) hX) hp
  exact Bicategory.isLeftAdjoint_of_iso hc (constantDiagramEquivalenceIso K e)

/-- Infinity-colimits of one shape transfer across an equivalence. -/
theorem hasColimitsOfShape_of_bicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (K : SSet.{u}) (e : Bicategory.Equivalence X Y)
    (hX : HasColimitsOfShape K X (@quasicategory_ihom K X.obj X.property)) :
    HasColimitsOfShape K Y (@quasicategory_ihom K Y.obj Y.property) := by
  let cX := constantDiagram K X (@quasicategory_ihom K X.obj X.property)
  let p : functorQCat K X (@quasicategory_ihom K X.obj X.property) ⟶
      functorQCat K Y (@quasicategory_ihom K Y.obj Y.property) :=
    ObjectProperty.homMk ((ihom K).map e.hom.hom)
  have hp : Bicategory.IsRightAdjoint p :=
    bicategoricalEquivalence_hom_isRightAdjoint
      (internalHomPostcompBicategoricalEquivalence e K)
  have hc : Bicategory.IsRightAdjoint (e.inv ≫ cX ≫ p) :=
    bicategoryIsRightAdjoint_comp (f := e.inv ≫ cX) (g := p)
      (bicategoryIsRightAdjoint_comp
        (bicategoricalEquivalence_inv_isRightAdjoint e) hX) hp
  exact Bicategory.isRightAdjoint_of_iso hc (constantDiagramEquivalenceIso K e)

/-- Finite infinity-bicompleteness transfers across an equivalence. -/
theorem HasFiniteInfinityBicompleteness.ofBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (hX : HasFiniteInfinityBicompleteness X)
    (e : Bicategory.Equivalence X Y) : HasFiniteInfinityBicompleteness Y := by
  constructor
  · intro K hK
    obtain ⟨hx, hlim⟩ := hX.1 K hK
    cases Subsingleton.elim hx (@quasicategory_ihom K X.obj X.property)
    exact ⟨@quasicategory_ihom K Y.obj Y.property,
      hasLimitsOfShape_of_bicategoricalEquivalence K e hlim⟩
  · intro K hK
    obtain ⟨hx, hcolim⟩ := hX.2 K hK
    cases Subsingleton.elim hx (@quasicategory_ihom K X.obj X.property)
    exact ⟨@quasicategory_ihom K Y.obj Y.property,
      hasColimitsOfShape_of_bicategoricalEquivalence K e hcolim⟩

/-- Finite bicompleteness transfers along any equivalence map. -/
theorem HasFiniteInfinityBicompleteness.ofIsBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (hX : HasFiniteInfinityBicompleteness X)
    (f : X ⟶ Y) (hf : IsBicategoricalEquivalence f) :
    HasFiniteInfinityBicompleteness Y :=
  hX.ofBicategoricalEquivalence hf.choose

end LeanLCAExactChallenge.Infinity
