/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientOriginalCategory

/-! # The original DG category and its inclusion into the corrected quotient

This file proves the unit and associativity laws for the coefficient-changed original DG
category and packages the zero-word inclusions as an enriched functor into the corrected
Drinfeld quotient.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [-instance] ULift.semiring

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord

open CategoryTheory
open CategoryTheory.MonoidalCategory

@[reassoc]
private lemma ιTensorObj_tensorHom_original
    {K₁ K₂ L₁ L₂ : QuotientDGCochain} (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂)
    {p q n : ℤ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj K₁ K₂ p q n h ≫
        (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιTensorObj L₁ L₂ p q n h := by
  exact GradedObject.Monoidal.ι_tensorHom f.f g.f p q n h

theorem OriginalCoefficientDGIdentity_comp (K L : ComplexCategory) :
    (λ_ (OriginalCoefficientCochainComplex L K)).inv ≫
        OriginalCoefficientDGIdentity K ▷ OriginalCoefficientCochainComplex L K ≫
        OriginalCoefficientDGComposition L K K =
      𝟙 (OriginalCoefficientCochainComplex L K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change (((HomologicalComplex.leftUnitor'
      (OriginalCoefficientCochainComplex L K)).inv n ≫ _) ≫ _) = _
  rw [HomologicalComplex.leftUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (OriginalCoefficientDGIdentity K)
      (𝟙 (OriginalCoefficientCochainComplex L K))).f n
    rw [ιTensorObj_tensorHom_original]
  simp only [Category.assoc, HomologicalComplex.id_f]
  rw [OriginalCoefficientDGIdentity_f_zero]
  slice_lhs 4 5 =>
    rw [OriginalCoefficientDGComposition_f]
    apply HomologicalComplex.ι_mapBifunctorDesc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨⟨x⟩⟩
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  have hone : e.hom.hom (e.inv.hom (1 : QuotientCoefficientRing)) = 1 := by
    have h := ConcreteCategory.congr_hom e.inv_hom_id (1 : QuotientCoefficientRing)
    simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
  rw [hone]
  change (originalTensorMapChangeScalars
    (dgCochainCompTensorReversed L K K (zero_add n))).hom
      ((OriginalCoefficientDGIdentitySpan K).hom 1 ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up x)) = ULift.up (ULift.up x)
  rw [show (OriginalCoefficientDGIdentitySpan K).hom 1 =
      ULift.up (ULift.up (identityCochain K)) by
    exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _]
  rw [originalTensorMapChangeScalars_tmul]
  apply ULift.down_injective
  apply ULift.down_injective
  exact dgCochainCompTensorReversed_tmul L K K (zero_add n)
    (identityCochain K) x |>.trans
      (dgCochainCompTensorOfEq_tmul_identity_right L K n x)

theorem OriginalCoefficientDG_comp_identity (K L : ComplexCategory) :
    (ρ_ (OriginalCoefficientCochainComplex L K)).inv ≫
        OriginalCoefficientCochainComplex L K ◁ OriginalCoefficientDGIdentity L ≫
        OriginalCoefficientDGComposition L L K =
      𝟙 (OriginalCoefficientCochainComplex L K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  change (((HomologicalComplex.rightUnitor'
      (OriginalCoefficientCochainComplex L K)).inv n ≫ _) ≫ _) = _
  rw [HomologicalComplex.rightUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (𝟙 (OriginalCoefficientCochainComplex L K))
      (OriginalCoefficientDGIdentity L)).f n
    rw [ιTensorObj_tensorHom_original]
  simp only [Category.assoc, HomologicalComplex.id_f]
  rw [OriginalCoefficientDGIdentity_f_zero]
  slice_lhs 4 5 =>
    rw [OriginalCoefficientDGComposition_f]
    apply HomologicalComplex.ι_mapBifunctorDesc
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨⟨x⟩⟩
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply]
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))
  have hone : e.hom.hom (e.inv.hom (1 : QuotientCoefficientRing)) = 1 := by
    have h := ConcreteCategory.congr_hom e.inv_hom_id (1 : QuotientCoefficientRing)
    simpa only [ModuleCat.comp_apply, CategoryTheory.id_apply] using h
  rw [hone]
  change (originalTensorMapChangeScalars
    (dgCochainCompTensorReversed L L K (add_zero n))).hom
      (ULift.up (ULift.up x) ⊗ₜ[QuotientCoefficientRing]
        (OriginalCoefficientDGIdentitySpan L).hom 1) = ULift.up (ULift.up x)
  rw [show (OriginalCoefficientDGIdentitySpan L).hom 1 =
      ULift.up (ULift.up (identityCochain L)) by
    exact LinearMap.toSpanSingleton_apply_one QuotientCoefficientRing _ _]
  rw [originalTensorMapChangeScalars_tmul]
  apply ULift.down_injective
  apply ULift.down_injective
  exact dgCochainCompTensorReversed_tmul L L K (add_zero n)
    x (identityCochain L) |>.trans
      (dgCochainCompTensorOfEq_identity_left_tmul L K n x)

abbrev OriginalMappingCochain (K L : ComplexCategory) :=
  OriginalCoefficientCochainComplex K L

/-- One homogeneous component of original DG composition. -/
def originalDGCompositionComponent
    (K L M : ComplexCategory) {p q n : ℤ} (h : p + q = n) :
    (OriginalMappingCochain L M).X p ⊗ (OriginalMappingCochain K L).X q ⟶
      (OriginalMappingCochain K M).X n :=
  originalTensorMapChangeScalars (dgCochainCompTensorReversed K L M h)

@[reassoc]
lemma ιTensorObj_originalDGComposition
    (K L M : ComplexCategory) {p q n : ℤ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj
          (OriginalMappingCochain L M) (OriginalMappingCochain K L) p q n h ≫
        (OriginalCoefficientDGComposition K L M).f n =
      originalDGCompositionComponent K L M h := by
  unfold originalDGCompositionComponent
  rw [OriginalCoefficientDGComposition_f]
  apply HomologicalComplex.ι_mapBifunctorDesc

theorem originalDGCompositionComponent_assoc
    (W X Y Z : ComplexCategory) {p q r n : ℤ} (h : p + q + r = n) :
    (α_ ((OriginalMappingCochain X W).X p)
          ((OriginalMappingCochain Y X).X q)
          ((OriginalMappingCochain Z Y).X r)).inv ≫
        (originalDGCompositionComponent Y X W
              (show p + q = p + q by rfl) ⊗ₘ
            𝟙 ((OriginalMappingCochain Z Y).X r)) ≫
        originalDGCompositionComponent Z Y W
          (show (p + q) + r = n by exact h) =
      (𝟙 ((OriginalMappingCochain X W).X p) ⊗ₘ
          originalDGCompositionComponent Z Y X
            (show q + r = q + r by rfl)) ≫
        originalDGCompositionComponent Z X W
          (show p + (q + r) = n by omega) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold'
  intro a b c
  rcases a with ⟨a⟩
  rcases a with ⟨a⟩
  rcases b with ⟨b⟩
  rcases b with ⟨b⟩
  rcases c with ⟨c⟩
  rcases c with ⟨c⟩
  change
    originalDGCompositionComponent Z Y W
          (show (p + q) + r = n by exact h)
        (originalDGCompositionComponent Y X W
            (show p + q = p + q by rfl)
              (ULift.up (ULift.up a) ⊗ₜ[QuotientCoefficientRing]
                ULift.up (ULift.up b)) ⊗ₜ
            ULift.up (ULift.up c)) =
      originalDGCompositionComponent Z X W
          (show p + (q + r) = n by omega)
        (ULift.up (ULift.up a) ⊗ₜ
          originalDGCompositionComponent Z Y X
            (show q + r = q + r by rfl)
              (ULift.up (ULift.up b) ⊗ₜ[QuotientCoefficientRing]
                ULift.up (ULift.up c)))
  simp only [originalDGCompositionComponent]
  apply ULift.down_injective
  apply ULift.down_injective
  exact (CochainComplex.HomComplex.Cochain.comp_assoc c b a
    (by omega) (by omega) (by omega)).symm

set_option maxHeartbeats 2000000 in
-- The threefold tensor comparison expands the total-complex coproduct maps.
theorem OriginalCoefficientDGComposition_assoc
    (W X Y Z : ComplexCategory) :
    (α_ (OriginalMappingCochain X W)
          (OriginalMappingCochain Y X)
          (OriginalMappingCochain Z Y)).inv ≫
        OriginalCoefficientDGComposition Y X W ▷ OriginalMappingCochain Z Y ≫
        OriginalCoefficientDGComposition Z Y W =
      OriginalMappingCochain X W ◁ OriginalCoefficientDGComposition Z Y X ≫
        OriginalCoefficientDGComposition Z X W := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply GradedObject.Monoidal.tensorObj₃_ext
  intro p q r h
  simp only [HomologicalComplex.comp_f]
  have hassoc :
      (α_ (OriginalMappingCochain X W)
        (OriginalMappingCochain Y X)
        (OriginalMappingCochain Z Y)).inv.f n =
        (GradedObject.Monoidal.associator
          (OriginalMappingCochain X W).X
          (OriginalMappingCochain Y X).X
          (OriginalMappingCochain Z Y).X).inv n := rfl
  rw [hassoc]
  set_option backward.defeqAttrib.useBackward true in
    set_option backward.isDefEq.respectTransparency false in
      rw [GradedObject.Monoidal.ιTensorObj₃_associator_inv_assoc]
  rw [GradedObject.Monoidal.ιTensorObj₃'_eq
    (OriginalMappingCochain X W).X
    (OriginalMappingCochain Y X).X
    (OriginalMappingCochain Z Y).X p q r n h (p + q) rfl]
  rw [GradedObject.Monoidal.ιTensorObj₃_eq
    (OriginalMappingCochain X W).X
    (OriginalMappingCochain Y X).X
    (OriginalMappingCochain Z Y).X p q r n h (q + r) rfl]
  have hwr :
      (OriginalCoefficientDGComposition Y X W ▷ OriginalMappingCochain Z Y).f n =
        (HomologicalComplex.tensorHom (OriginalCoefficientDGComposition Y X W)
          (𝟙 (OriginalMappingCochain Z Y))).f n := rfl
  have hwl :
      (OriginalMappingCochain X W ◁ OriginalCoefficientDGComposition Z Y X).f n =
        (HomologicalComplex.tensorHom (𝟙 (OriginalMappingCochain X W))
          (OriginalCoefficientDGComposition Z Y X)).f n := rfl
  rw [hwr, hwl]
  have houterL :
      GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj
              (OriginalMappingCochain X W).X
              (OriginalMappingCochain Y X).X)
            (OriginalMappingCochain Z Y).X (p + q) r n h ≫
          (HomologicalComplex.tensorHom
            (OriginalCoefficientDGComposition Y X W)
            (𝟙 (OriginalMappingCochain Z Y))).f n =
        ((OriginalCoefficientDGComposition Y X W).f (p + q) ⊗ₘ
            𝟙 ((OriginalMappingCochain Z Y).X r)) ≫
          GradedObject.Monoidal.ιTensorObj
            (OriginalMappingCochain Y W).X
            (OriginalMappingCochain Z Y).X (p + q) r n h := by
    exact ιTensorObj_tensorHom_original
      (OriginalCoefficientDGComposition Y X W)
      (𝟙 (OriginalMappingCochain Z Y)) h
  have houterR :
      GradedObject.Monoidal.ιTensorObj
            (OriginalMappingCochain X W).X
            (GradedObject.Monoidal.tensorObj
              (OriginalMappingCochain Y X).X
              (OriginalMappingCochain Z Y).X)
            p (q + r) n (show p + (q + r) = n by omega) ≫
          (HomologicalComplex.tensorHom
            (𝟙 (OriginalMappingCochain X W))
            (OriginalCoefficientDGComposition Z Y X)).f n =
        (𝟙 ((OriginalMappingCochain X W).X p) ⊗ₘ
            (OriginalCoefficientDGComposition Z Y X).f (q + r)) ≫
          GradedObject.Monoidal.ιTensorObj
            (OriginalMappingCochain X W).X
            (OriginalMappingCochain Z X).X p (q + r) n
              (show p + (q + r) = n by omega) := by
    exact ιTensorObj_tensorHom_original
      (𝟙 (OriginalMappingCochain X W))
      (OriginalCoefficientDGComposition Z Y X)
      (show p + (q + r) = n by omega)
  simp only [Category.assoc]
  have hleftRaw := congrArg
    (fun t ↦
      (α_ ((OriginalMappingCochain X W).X p)
          ((OriginalMappingCochain Y X).X q)
          ((OriginalMappingCochain Z Y).X r)).inv ≫
        (GradedObject.Monoidal.ιTensorObj
            (OriginalMappingCochain X W).X
            (OriginalMappingCochain Y X).X p q (p + q) rfl ▷
          (OriginalMappingCochain Z Y).X r) ≫
        t ≫ (OriginalCoefficientDGComposition Z Y W).f n)
    houterL
  have hrightRaw := congrArg
    (fun t ↦
      ((OriginalMappingCochain X W).X p ◁
          GradedObject.Monoidal.ιTensorObj
            (OriginalMappingCochain Y X).X
            (OriginalMappingCochain Z Y).X q r (q + r) rfl) ≫
        t ≫ (OriginalCoefficientDGComposition Z X W).f n)
    houterR
  have hleft := hleftRaw
  have hright := hrightRaw
  simp only [Category.assoc] at hleft hright
  refine hleft.trans ?_
  refine Eq.trans ?_ hright.symm
  simp only [MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom]
  have hcompL₀ :=
    ιTensorObj_originalDGComposition
      Y X W (show p + q = p + q by rfl)
  have hcompL := congrArg
    (fun t ↦ t ▷ (OriginalMappingCochain Z Y).X r) hcompL₀
  simp only [MonoidalCategory.comp_whiskerRight] at hcompL
  have houterCompL :=
    ιTensorObj_originalDGComposition
      Z Y W (show (p + q) + r = n by exact h)
  have hcompR₀ :=
    ιTensorObj_originalDGComposition
      Z Y X (show q + r = q + r by rfl)
  have hcompR := congrArg
    (fun t ↦ (OriginalMappingCochain X W).X p ◁ t) hcompR₀
  simp only [MonoidalCategory.whiskerLeft_comp] at hcompR
  have houterCompR :=
    ιTensorObj_originalDGComposition
      Z X W (show p + (q + r) = n by omega)
  have hL₁Raw := congrArg
    (fun t ↦
      (α_ ((OriginalMappingCochain X W).X p)
          ((OriginalMappingCochain Y X).X q)
          ((OriginalMappingCochain Z Y).X r)).inv ≫
        t ≫
        GradedObject.Monoidal.ιTensorObj
          (OriginalMappingCochain Y W).X
          (OriginalMappingCochain Z Y).X (p + q) r n h ≫
        (OriginalCoefficientDGComposition Z Y W).f n)
    hcompL
  have hL₂Raw := congrArg
    (fun t ↦
      (α_ ((OriginalMappingCochain X W).X p)
          ((OriginalMappingCochain Y X).X q)
          ((OriginalMappingCochain Z Y).X r)).inv ≫
        (originalDGCompositionComponent Y X W
            (show p + q = p + q by rfl) ▷
          (OriginalMappingCochain Z Y).X r) ≫ t)
    houterCompL
  have hR₁Raw := congrArg
    (fun t ↦
      t ≫
        GradedObject.Monoidal.ιTensorObj
          (OriginalMappingCochain X W).X
          (OriginalMappingCochain Z X).X p (q + r) n
            (show p + (q + r) = n by omega) ≫
        (OriginalCoefficientDGComposition Z X W).f n)
    hcompR
  have hR₂Raw := congrArg
    (fun t ↦
      ((OriginalMappingCochain X W).X p ◁
          originalDGCompositionComponent Z Y X
            (show q + r = q + r by rfl)) ≫ t)
    houterCompR
  have hL₁ := hL₁Raw
  have hL₂ := hL₂Raw
  have hR₁ := hR₁Raw
  have hR₂ := hR₂Raw
  simp only [Category.assoc] at hL₁ hL₂ hR₁ hR₂
  have hleftComponents := hL₁.trans hL₂
  have hrightComponents := hR₁.trans hR₂
  have hmiddle := originalDGCompositionComponent_assoc W X Y Z h
  exact hleftComponents.trans (hmiddle.trans hrightComponents.symm)

theorem nil_append_nil (K L M : ComplexCategory) :
    (nil K L).append (nil L M) = nil K M := by
  simp only [append, nil, Nat.zero_add, DrinfeldWord.mk.injEq, heq_eq_eq]
  constructor
  · trivial
  · funext i
    exact Fin.elim0 i

theorem nilDegreeProfile_append_nilDegreeProfile
    (K L M : ComplexCategory) (q p : ℤ) :
    ((nilDegreeProfile K L q).append (nilDegreeProfile L M p)).castWord
        (nil_append_nil K L M) =
      nilDegreeProfile K M (q + p) :=
  degreeProfile_nil_eq_nilDegreeProfile K M (q + p) _

/-- The boundary list for two zero-word profiles contains only their merged factor. -/
def nilCompositionBoundaryListEq
    (K L M : ComplexCategory) (q p : ℤ) :
    compositionLeftPrefix (nilDegreeProfile K L q) ++
        compositionBoundaryModule (nilDegreeProfile K L q) (nilDegreeProfile L M p) ::
          compositionRightSuffix (nilDegreeProfile L M p) =
      [compositionBoundaryModule
        (nilDegreeProfile K L q) (nilDegreeProfile L M p)] := by
  simp

/-- Identify the composed zero-word summand with the canonical zero-word summand. -/
def nilCompositionSummandIso
    (K L M : ComplexCategory) (q p : ℤ) :
    summandModule ((nilDegreeProfile K L q).append (nilDegreeProfile L M p)) ≅
      summandModule (nilDegreeProfile K M (q + p)) :=
  eqToIso (congrArg tensorModuleList
      (finFamilyList_factorModule_append_boundary
        (nilDegreeProfile K L q) (nilDegreeProfile L M p))) ≪≫
    eqToIso (congrArg tensorModuleList
      (nilCompositionBoundaryListEq K L M q p)) ≪≫
    ρ_ (compositionBoundaryModule
      (nilDegreeProfile K L q) (nilDegreeProfile L M p)) ≪≫
    eqToIso (show
      compositionBoundaryModule (nilDegreeProfile K L q) (nilDegreeProfile L M p) =
        (dgHomZModuleCochainComplex K M).X (q + p) by rfl) ≪≫
    (nilSummandIsoOriginal K M (nilDegreeProfile K M (q + p))).symm

theorem nilCompositionGradedSummandIndexEq
    (K L M : ComplexCategory) (q p : ℤ) :
    (⟨(nil K L).append (nil L M),
        (nilDegreeProfile K L q).append (nilDegreeProfile L M p)⟩ :
      GradedSummandIndex K M (q + p)) =
    ⟨nil K M, nilDegreeProfile K M (q + p)⟩ := by
  apply Sigma.ext (nil_append_nil K L M)
  let raw := (nilDegreeProfile K L q).append (nilDegreeProfile L M p)
  have hp : raw.castWord (nil_append_nil K L M) =
      nilDegreeProfile K M (q + p) :=
    nilDegreeProfile_append_nilDegreeProfile K L M q p
  have hhp : raw.castWord (nil_append_nil K L M) ≍
      nilDegreeProfile K M (q + p) := heq_of_eq hp
  let hty := congrArg
    (fun w : DrinfeldWord K M ↦ DegreeProfile w (q + p))
    (nil_append_nil K L M)
  apply (cast_heq_iff_heq hty raw (nilDegreeProfile K M (q + p))).mp
  rw [DegreeProfile.cast_eq_castWord]
  exact hhp

theorem nilCompositionGradedSummandIndexCastEq
    (K L M : ComplexCategory) (q p : ℤ) :
    GradedSummandIndex.castTotal (Int.add_comm q p)
        (⟨(nil K L).append (nil L M),
          (nilDegreeProfile K L q).append (nilDegreeProfile L M p)⟩ :
          GradedSummandIndex K M (q + p)) =
      (⟨nil K M, nilDegreeProfile K M (p + q)⟩ :
        GradedSummandIndex K M (p + q)) := by
  rw [GradedSummandIndex.castTotal_sigma]
  apply Sigma.ext (nil_append_nil K L M)
  let raw := ((nilDegreeProfile K L q).append
    (nilDegreeProfile L M p)).castTotal (Int.add_comm q p)
  have hp : raw.castWord (nil_append_nil K L M) =
      nilDegreeProfile K M (p + q) :=
    degreeProfile_nil_eq_nilDegreeProfile K M (p + q) _
  have hhp : raw.castWord (nil_append_nil K L M) ≍
      nilDegreeProfile K M (p + q) := heq_of_eq hp
  let hty := congrArg
    (fun w : DrinfeldWord K M ↦ DegreeProfile w (p + q))
    (nil_append_nil K L M)
  apply (cast_heq_iff_heq hty raw (nilDegreeProfile K M (p + q))).mp
  rw [DegreeProfile.cast_eq_castWord]
  exact hhp

/-- The direct dependent transport from a composed zero-word summand to the canonical
zero-word summand in the reversed total degree. -/
def nilCompositionTransportIso
    (K L M : ComplexCategory) (q p : ℤ) :
    summandModule ((nilDegreeProfile K L q).append (nilDegreeProfile L M p)) ≅
      summandModule (nilDegreeProfile K M (p + q)) :=
  summandModuleTransportIso (nil_append_nil K L M) (Int.add_comm q p)
      ((nilDegreeProfile K L q).append (nilDegreeProfile L M p)) ≪≫
    eqToIso (congrArg summandModule
      (degreeProfile_nil_eq_nilDegreeProfile K M (p + q) _))

theorem largeSummandNilCompositionTransport
    (K L M : ComplexCategory) (q p : ℤ) :
    eqToHom (largeSummandModuleCastTotalEq (Int.add_comm q p)
          (⟨(nil K L).append (nil L M),
            (nilDegreeProfile K L q).append (nilDegreeProfile L M p)⟩ :
            GradedSummandIndex K M (q + p))) ≫
        eqToHom (congrArg largeSummandModule
          (nilCompositionGradedSummandIndexCastEq K L M q p)) =
      (ModuleCat.uliftFunctor.{1} ℤ).map
        (nilCompositionTransportIso K L M q p).hom := by
  simp only [nilCompositionTransportIso, summandModuleTransportIso,
    Iso.trans_hom, eqToIso.hom, eqToHom_map, eqToHom_trans]

theorem nilSummandIsoOriginal_inv_comp_lastFactorIso_hom
    (K L : ComplexCategory) (n : ℤ) :
    (nilSummandIsoOriginal K L (nilDegreeProfile K L n)).inv ≫
        (summandLastFactorIso (nilDegreeProfile K L n)).hom =
      (ρ_ (factorModule (nilDegreeProfile K L n) 0)).inv := by
  unfold nilSummandIsoOriginal summandLastFactorIso
  simp only [Iso.trans_inv, eqToIso.inv, eqToIso.hom, Category.assoc]
  congr 1

theorem nilSummandIsoOriginal_inv_comp_firstFactorIso_hom
    (K L : ComplexCategory) (n : ℤ) :
    (nilSummandIsoOriginal K L (nilDegreeProfile K L n)).inv ≫
        (summandFirstFactorIso (nilDegreeProfile K L n)).hom =
      (ρ_ (factorModule (nilDegreeProfile K L n) 0)).inv := by
  unfold nilSummandIsoOriginal summandFirstFactorIso
  simp only [Iso.trans_inv, eqToIso.inv, eqToIso.hom, Category.assoc]
  congr 1

theorem nilCompositionBoundaryModuleEq
    (K L M : ComplexCategory) (q p : ℤ) :
    compositionBoundaryModule (nilDegreeProfile K L q) (nilDegreeProfile L M p) =
      (dgHomZModuleCochainComplex K M).X (q + p) := by
  rfl

theorem nilCompositionBoundaryMap
    (K L M : ComplexCategory) (q p : ℤ) :
    compositionBoundaryMap (nilDegreeProfile K L q) (nilDegreeProfile L M p) ≫
        eqToHom (nilCompositionBoundaryModuleEq K L M q p) =
      dgCochainCompTensor K L M (show q + p = q + p by rfl) := by
  rfl

theorem nilCompositionSummandIso_from_boundary
    (K L M : ComplexCategory) (q p : ℤ) :
    eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_append_boundary
          (nilDegreeProfile K L q) (nilDegreeProfile L M p)).symm) ≫
      (nilCompositionSummandIso K L M q p).hom ≫
      (nilSummandIsoOriginal K M (nilDegreeProfile K M (q + p))).hom =
    (ρ_ (compositionBoundaryModule
      (nilDegreeProfile K L q) (nilDegreeProfile L M p))).hom ≫
      eqToHom (nilCompositionBoundaryModuleEq K L M q p) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x
  simp [nilCompositionSummandIso,
    nilSummandIsoOriginal, nilDegreeProfile, compositionLeftPrefix,
    compositionRightSuffix]

theorem eqToHom_tensorUnit_right
    {X Y : ModuleCat.{0} ℤ} (h : X = Y) :
    eqToHom (congrArg (fun Z : ModuleCat.{0} ℤ ↦
      Z ⊗ 𝟙_ (ModuleCat.{0} ℤ)) h) =
      eqToHom h ▷ 𝟙_ (ModuleCat.{0} ℤ) := by
  subst Y
  simp

set_option maxHeartbeats 1000000 in
-- Expanding the dependent word, degree, and tensor transports requires extra elaboration.
theorem nilCompositionTransportIso_to_boundary
    (K L M : ComplexCategory) (q p : ℤ) :
    (nilCompositionTransportIso K L M q p).hom ≫
        (nilSummandIsoOriginal K M (nilDegreeProfile K M (p + q))).hom =
      (nilCompositionSummandIso K L M q p).hom ≫
        (nilSummandIsoOriginal K M (nilDegreeProfile K M (q + p))).hom ≫
        eqToHom (congrArg
          (fun n ↦ (dgHomZModuleCochainComplex K M).X n)
          (Int.add_comm q p)) := by
  dsimp [nilCompositionTransportIso, summandModuleTransportIso,
    nilCompositionSummandIso, nilSummandIsoOriginal]
  simp only [Category.assoc, eqToHom_trans]
  simp only [Category.id_comp, Category.comp_id, Iso.inv_hom_id_assoc]
  let hbase : compositionBoundaryModule
      (nilDegreeProfile K L q) (nilDegreeProfile L M p) =
      factorModule (nilDegreeProfile K M (p + q)) 0 := by
    change (dgHomZModuleCochainComplex K M).X (q + p) =
      (dgHomZModuleCochainComplex K M).X (p + q)
    exact congrArg (fun n ↦ (dgHomZModuleCochainComplex K M).X n)
      (Int.add_comm q p)
  let f : compositionBoundaryModule
      (nilDegreeProfile K L q) (nilDegreeProfile L M p) ⟶
      factorModule (nilDegreeProfile K M (p + q)) 0 :=
    eqToHom hbase
  convert MonoidalCategory.rightUnitor_naturality f using 1
  · rfl
  · rw [← eqToHom_tensorUnit_right hbase]
  · simp only [f]
    congr 1

theorem tensorModuleList_single_merge
    {M N P : ModuleCat.{0} ℤ} (f : M ⊗ N ⟶ P) :
    ((ρ_ M).inv ⊗ₘ (ρ_ N).inv) ≫
        (tensorModuleListAppendIso [M] [N]).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq [] M N [])) ≫
        (adjacentMergeAfter [] (ys := []) f).tensorMap ≫
        (ρ_ P).hom =
      f := by
  dsimp [tensorModuleList, tensorModuleListOver, tensorModuleListAppendIso,
    appendBoundaryListsEq, adjacentMergeAfter, AdjacentMergeData.tensorMap]
  monoidal

theorem nilSummandInputTensorIso
    (K L M : ComplexCategory) (q p : ℤ) :
    ((nilSummandIsoOriginal K L (nilDegreeProfile K L q)).inv ⊗ₘ
        (nilSummandIsoOriginal L M (nilDegreeProfile L M p)).inv) ≫
      ((summandLastFactorIso (nilDegreeProfile K L q)).hom ⊗ₘ
        (summandFirstFactorIso (nilDegreeProfile L M p)).hom) =
    (ρ_ (factorModule (nilDegreeProfile K L q) 0)).inv ⊗ₘ
      (ρ_ (factorModule (nilDegreeProfile L M p) 0)).inv := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom,
    nilSummandIsoOriginal_inv_comp_lastFactorIso_hom,
    nilSummandIsoOriginal_inv_comp_firstFactorIso_hom]

/-- On two zero-word summands, quotient composition is the original DG composition. -/
theorem summandCompositionMap_nil_nil
    (K L M : ComplexCategory) (q p : ℤ) :
    ((nilSummandIsoOriginal K L (nilDegreeProfile K L q)).inv ⊗ₘ
        (nilSummandIsoOriginal L M (nilDegreeProfile L M p)).inv) ≫
      summandCompositionMap (nilDegreeProfile K L q) (nilDegreeProfile L M p) ≫
      (nilCompositionSummandIso K L M q p).hom ≫
      (nilSummandIsoOriginal K M (nilDegreeProfile K M (q + p))).hom =
    dgCochainCompTensor K L M (show q + p = q + p by rfl) := by
  rw [summandCompositionMap_eq_boundary_decomposition]
  simp only [Category.assoc]
  slice_lhs 1 2 =>
    rw [nilSummandInputTensorIso]
  slice_lhs 5 7 =>
    rw [nilCompositionSummandIso_from_boundary]
  change
    ((ρ_ (factorModule (nilDegreeProfile K L q) 0)).inv ⊗ₘ
        (ρ_ (factorModule (nilDegreeProfile L M p) 0)).inv) ≫
      (tensorModuleListAppendIso
        [factorModule (nilDegreeProfile K L q) 0]
        [factorModule (nilDegreeProfile L M p) 0]).hom ≫
      eqToHom (congrArg tensorModuleList
        (appendBoundaryListsEq []
          (factorModule (nilDegreeProfile K L q) 0)
          (factorModule (nilDegreeProfile L M p) 0) [])) ≫
      (adjacentMergeAfter [] (ys := [])
        (compositionBoundaryMap (nilDegreeProfile K L q)
          (nilDegreeProfile L M p))).tensorMap ≫
      (ρ_ (compositionBoundaryModule
        (nilDegreeProfile K L q) (nilDegreeProfile L M p))).hom ≫
      eqToHom (nilCompositionBoundaryModuleEq K L M q p) =
    dgCochainCompTensor K L M (show q + p = q + p by rfl)
  have hmerge := tensorModuleList_single_merge
    (compositionBoundaryMap (nilDegreeProfile K L q) (nilDegreeProfile L M p))
  have hmerge' := congrArg
    (fun f ↦ f ≫ eqToHom (nilCompositionBoundaryModuleEq K L M q p)) hmerge
  simp only [Category.assoc] at hmerge'
  exact hmerge'.trans (nilCompositionBoundaryMap K L M q p)

/-- The zero-word inclusion after coefficient change. -/
def OriginalCoefficientHomToQuotient (K L : ComplexCategory) :
    OriginalCoefficientCochainComplex K L ⟶ quotientCoefficientCochainComplex K L :=
  originalHomToQuotient K L

@[simp]
theorem OriginalCoefficientHomToQuotient_f
    (K L : ComplexCategory) (n : ℤ) :
    (OriginalCoefficientHomToQuotient K L).f n =
      ModuleCat.ofHom
        (quotientLinearMapChangeScalars (originalHomInclusion K L n).hom) :=
  rfl

/-- The zero-word inclusion preserves the DG identity. -/
theorem OriginalCoefficientDGIdentity_map (K : ComplexCategory) :
    OriginalCoefficientDGIdentity K ≫ OriginalCoefficientHomToQuotient K K =
      quotientDGIdentity K := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  rw [OriginalCoefficientDGIdentity_f_zero, quotientDGIdentity_f_zero,
    OriginalCoefficientHomToQuotient_f]
  simp only [Category.assoc]
  rw [cancel_epi]
  apply ModuleCat.hom_ext
  change (quotientLinearMapChangeScalars
        (originalHomInclusion K K 0).hom).comp
      (LinearMap.toSpanSingleton QuotientCoefficientRing _
        (ULift.up (ULift.up (identityCochain K)))) =
    LinearMap.toSpanSingleton QuotientCoefficientRing _
      (ULift.up (quotientIdentityElement K))
  rw [LinearMap.comp_toSpanSingleton]
  rfl

theorem dgCochainCompTensor_cast_tmul
    (K L M : ComplexCategory) {q p r s : ℤ}
    (hr : q + p = r) (hs : q + p = s) (h : r = s)
    (x : (dgHomZModuleCochainComplex K L).X q)
    (y : (dgHomZModuleCochainComplex L M).X p) :
    (eqToHom (congrArg
        (fun n ↦ (dgHomZModuleCochainComplex K M).X n) h)).hom
      ((dgCochainCompTensor K L M hr).hom (x ⊗ₜ[ℤ] y)) =
    (dgCochainCompTensor K L M hs).hom (x ⊗ₜ[ℤ] y) := by
  cases h
  rw [Subsingleton.elim hs hr]
  rfl

theorem dgCochainCompTensor_cast_comm_tmul
    (K L M : ComplexCategory) (q p : ℤ)
    (x : (dgHomZModuleCochainComplex K L).X q)
    (y : (dgHomZModuleCochainComplex L M).X p) :
    (eqToHom (congrArg
        (fun n ↦ (dgHomZModuleCochainComplex K M).X n)
        (Int.add_comm q p))).hom
      ((dgCochainCompTensor K L M
        (show q + p = q + p by rfl)).hom (x ⊗ₜ[ℤ] y)) =
    (dgCochainCompTensorReversed K L M
      (show p + q = p + q by rfl)).hom (y ⊗ₜ[ℤ] x) := by
  calc
    _ = (dgCochainCompTensor K L M (Int.add_comm q p)).hom
        (x ⊗ₜ[ℤ] y) :=
      dgCochainCompTensor_cast_tmul K L M rfl
        (Int.add_comm q p) (Int.add_comm q p) x y
    _ = _ := by
      rw [dgCochainCompTensor_tmul, dgCochainCompTensorReversed_tmul]

@[simp]
theorem originalHomInclusion_apply_up
    (K L : ComplexCategory) (n : ℤ)
    (x : (dgHomZModuleCochainComplex K L).X n) :
    (originalHomInclusion K L n).hom (ULift.up x) =
      (Limits.Sigma.ι
        (fun s : GradedSummandIndex K L n ↦ largeSummandModule s)
        ⟨nil K L, nilDegreeProfile K L n⟩).hom
      (ULift.up ((nilSummandIsoOriginal K L
        (nilDegreeProfile K L n)).inv.hom x)) := by
  rfl

@[simp]
theorem originalDGCompositionComponent_tmul
    (K L M : ComplexCategory) {p q n : ℤ} (h : p + q = n)
    (y : (dgHomZModuleCochainComplex L M).X p)
    (x : (dgHomZModuleCochainComplex K L).X q) :
    (originalDGCompositionComponent K L M h).hom
        (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
          ULift.up (ULift.up x)) =
      ULift.up (ULift.up
        ((dgCochainCompTensorReversed K L M h).hom (y ⊗ₜ[ℤ] x))) := by
  exact originalTensorMapChangeScalars_tmul
    (dgCochainCompTensorReversed K L M h) y x

@[simp]
theorem OriginalCoefficientHomToQuotient_apply_up
    (K L : ComplexCategory) (n : ℤ)
    (x : (dgHomZModuleCochainComplex K L).X n) :
    ((OriginalCoefficientHomToQuotient K L).f n).hom
        (ULift.up (ULift.up x)) =
      ULift.up ((originalHomInclusion K L n).hom (ULift.up x)) := by
  rfl

@[simp]
theorem originalDGCompositionThenInclusion_tmul
    (K L M : ComplexCategory) {p q n : ℤ} (h : p + q = n)
    (y : (dgHomZModuleCochainComplex L M).X p)
    (x : (dgHomZModuleCochainComplex K L).X q) :
    (originalDGCompositionComponent K L M h ≫
        (OriginalCoefficientHomToQuotient K M).f n).hom
      (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up x)) =
    ULift.up ((originalHomInclusion K M n).hom
      (ULift.up ((dgCochainCompTensorReversed K L M h).hom
        (y ⊗ₜ[ℤ] x)))) := by
  rfl

@[simp]
theorem quotientDGCompositionComponent_after_original_tmul
    (K L M : ComplexCategory) {p q n : ℤ} (h : p + q = n)
    (y : (dgHomZModuleCochainComplex L M).X p)
    (x : (dgHomZModuleCochainComplex K L).X q) :
    (((OriginalCoefficientHomToQuotient L M).f p ⊗ₘ
          (OriginalCoefficientHomToQuotient K L).f q) ≫
        quotientDGCompositionComponent K L M h).hom
      (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up x)) =
    ULift.up ((eqToHom (congrArg (quotientGradedModule K M)
        (show q + p = n by omega))).hom
      (quotientCompositionMap K L M q p
        ((originalHomInclusion K L q).hom (ULift.up x))
        ((originalHomInclusion L M p).hom (ULift.up y)))) := by
  rw [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    OriginalCoefficientHomToQuotient_apply_up,
    OriginalCoefficientHomToQuotient_apply_up]
  unfold quotientDGCompositionComponent
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply]
  change (eqToHom (congrArg
      (fun k ↦ quotientCoefficientModule (quotientGradedModule K M k))
      (show q + p = n by omega))).hom
      ((quotientCompositionTensorMap K L M q p).hom
        (ULift.up ((originalHomInclusion K L q).hom (ULift.up x)) ⊗ₜ
          ULift.up ((originalHomInclusion L M p).hom (ULift.up y)))) = _
  rw [quotientCompositionTensorMap_tmul,
    quotientCoefficient_eqToHom_apply_up]
  all_goals omega

theorem originalDGCompositionComponent_map
    (K L M : ComplexCategory) {p q n : ℤ} (h : p + q = n) :
    originalDGCompositionComponent K L M h ≫
        (OriginalCoefficientHomToQuotient K M).f n =
      ((OriginalCoefficientHomToQuotient L M).f p ⊗ₘ
          (OriginalCoefficientHomToQuotient K L).f q) ≫
        quotientDGCompositionComponent K L M h := by
  subst n
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext y x
  rcases y with ⟨y⟩
  rcases y with ⟨y⟩
  rcases x with ⟨x⟩
  rcases x with ⟨x⟩
  change CochainComplex.HomComplex.Cochain
    (underlyingComplex L) (underlyingComplex M) p at y
  change CochainComplex.HomComplex.Cochain
    (underlyingComplex K) (underlyingComplex L) q at x
  change (originalDGCompositionComponent K L M
      (show p + q = p + q by rfl) ≫
        (OriginalCoefficientHomToQuotient K M).f (p + q)).hom
      (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up x)) =
    (((OriginalCoefficientHomToQuotient L M).f p ⊗ₘ
          (OriginalCoefficientHomToQuotient K L).f q) ≫
        quotientDGCompositionComponent K L M
          (show p + q = p + q by rfl)).hom
      (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
        ULift.up (ULift.up x))
  rw [originalDGCompositionThenInclusion_tmul,
    quotientDGCompositionComponent_after_original_tmul]
  apply ULift.up_injective.{1, 1}
  apply ULift.down_injective.{1, 1}
  apply ULift.down_injective.{1, 0}
  rw [originalHomInclusion_apply_up,
    originalHomInclusion_apply_up,
    originalHomInclusion_apply_up]
  rw [quotientCompositionMap_on_summands,
    largeSummandCompositionMap_eq_inclusion]
  change (Limits.Sigma.ι
      (fun s : GradedSummandIndex K M (p + q) ↦ largeSummandModule s)
      ⟨nil K M, nilDegreeProfile K M (p + q)⟩).hom
        (ULift.up ((nilSummandIsoOriginal K M
          (nilDegreeProfile K M (p + q))).inv.hom
          ((dgCochainCompTensorReversed K L M
            (show p + q = p + q by rfl)).hom (y ⊗ₜ[ℤ] x)))) =
    (eqToHom (congrArg (quotientGradedModule K M) (Int.add_comm q p))).hom
      ((Limits.Sigma.ι
        (fun s : GradedSummandIndex K M (q + p) ↦ largeSummandModule s)
        ⟨(nil K L).append (nil L M),
          (nilDegreeProfile K L q).append (nilDegreeProfile L M p)⟩).hom
        (largeSummandCompositionValue
          (nilDegreeProfile K L q) (nilDegreeProfile L M p)
          (ULift.up ((nilSummandIsoOriginal K L
            (nilDegreeProfile K L q)).inv.hom x))
          (ULift.up ((nilSummandIsoOriginal L M
            (nilDegreeProfile L M p)).inv.hom y))))
  let s : GradedSummandIndex K M (q + p) :=
    ⟨(nil K L).append (nil L M),
      (nilDegreeProfile K L q).append (nilDegreeProfile L M p)⟩
  let t : GradedSummandIndex K M (p + q) :=
    ⟨nil K M, nilDegreeProfile K M (p + q)⟩
  let z : largeSummandModule s :=
    largeSummandCompositionValue
      (nilDegreeProfile K L q) (nilDegreeProfile L M p)
      (ULift.up ((nilSummandIsoOriginal K L
        (nilDegreeProfile K L q)).inv.hom x))
      (ULift.up ((nilSummandIsoOriginal L M
        (nilDegreeProfile L M p)).inv.hom y))
  have hι := quotientGradedModule_eqToHom_ι_of_eq
    (Int.add_comm q p) s t
    (nilCompositionGradedSummandIndexCastEq K L M q p)
  have hιapp := ConcreteCategory.congr_hom hι z
  simp only [ModuleCat.comp_apply] at hιapp
  rw [hιapp]
  apply congrArg (Limits.Sigma.ι
    (fun u : GradedSummandIndex K M (p + q) ↦ largeSummandModule u) t).hom
  have htransport := ConcreteCategory.congr_hom
    (largeSummandNilCompositionTransport K L M q p) z
  simp only [ModuleCat.comp_apply] at htransport
  rw [htransport]
  dsimp [z, largeSummandCompositionValue]
  apply ULift.down_injective
  change (nilSummandIsoOriginal K M
      (nilDegreeProfile K M (p + q))).inv.hom
        ((dgCochainCompTensorReversed K L M
          (show p + q = p + q by rfl)).hom (y ⊗ₜ[ℤ] x)) =
    (nilCompositionTransportIso K L M q p).hom
      ((summandCompositionMap
        (nilDegreeProfile K L q) (nilDegreeProfile L M p)).hom
        ((nilSummandIsoOriginal K L
          (nilDegreeProfile K L q)).inv.hom x ⊗ₜ[ℤ]
          (nilSummandIsoOriginal L M
            (nilDegreeProfile L M p)).inv.hom y))
  let A := nilSummandIsoOriginal K M (nilDegreeProfile K M (p + q))
  let v := (summandCompositionMap
    (nilDegreeProfile K L q) (nilDegreeProfile L M p)).hom
    ((nilSummandIsoOriginal K L
      (nilDegreeProfile K L q)).inv.hom x ⊗ₜ[ℤ]
      (nilSummandIsoOriginal L M
        (nilDegreeProfile L M p)).inv.hom y)
  apply (ModuleCat.mono_iff_injective A.hom).1 inferInstance
  have hA := ConcreteCategory.congr_hom A.inv_hom_id
    ((dgCochainCompTensorReversed K L M
      (show p + q = p + q by rfl)).hom (y ⊗ₜ[ℤ] x))
  simp only [ModuleCat.comp_apply] at hA
  rw [hA]
  simp only [CategoryTheory.id_apply]
  have htrans := ConcreteCategory.congr_hom
    (nilCompositionTransportIso_to_boundary K L M q p) v
  simp only [ModuleCat.comp_apply] at htrans
  rw [htrans]
  have hv : v =
      (summandCompositionMap
        (nilDegreeProfile K L q) (nilDegreeProfile L M p)).hom
        (((nilSummandIsoOriginal K L
            (nilDegreeProfile K L q)).inv ⊗ₘ
          (nilSummandIsoOriginal L M
            (nilDegreeProfile L M p)).inv).hom
          (x ⊗ₜ[ℤ] y)) := by
    dsimp [v]
  rw [hv]
  have hcomp := ConcreteCategory.congr_hom
    (summandCompositionMap_nil_nil K L M q p) (x ⊗ₜ[ℤ] y)
  simp only [ModuleCat.comp_apply] at hcomp
  rw [hcomp]
  exact (dgCochainCompTensor_cast_comm_tmul K L M q p x y).symm

theorem OriginalCoefficientDGComposition_map
    (K L M : ComplexCategory) :
    OriginalCoefficientDGComposition K L M ≫
        OriginalCoefficientHomToQuotient K M =
      (OriginalCoefficientHomToQuotient L M ⊗ₘ
          OriginalCoefficientHomToQuotient K L) ≫
        quotientDGComposition K L M := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  simp only [HomologicalComplex.comp_f]
  change HomologicalComplex.ιTensorObj
      (OriginalMappingCochain L M) (OriginalMappingCochain K L)
        p q n hpq ≫
      (OriginalCoefficientDGComposition K L M).f n ≫
        (OriginalCoefficientHomToQuotient K M).f n =
    HomologicalComplex.ιTensorObj
      (OriginalMappingCochain L M) (OriginalMappingCochain K L)
        p q n hpq ≫
      (HomologicalComplex.tensorHom
        (OriginalCoefficientHomToQuotient L M)
        (OriginalCoefficientHomToQuotient K L)).f n ≫
        (quotientDGComposition K L M).f n
  have hleft₀ := ιTensorObj_originalDGComposition K L M hpq
  have hleft := congrArg
    (fun f ↦ f ≫ (OriginalCoefficientHomToQuotient K M).f n) hleft₀
  simp only [Category.assoc] at hleft
  rw [hleft]
  rw [originalDGCompositionComponent_map K L M hpq]
  have hright₀ := ιTensorObj_tensorHom_original
    (OriginalCoefficientHomToQuotient L M)
    (OriginalCoefficientHomToQuotient K L) hpq
  have hright := congrArg
    (fun f ↦ f ≫ (quotientDGComposition K L M).f n) hright₀
  simp only [Category.assoc] at hright
  rw [hright]
  rw [ιTensorObj_quotientDGComposition K L M hpq]

/-- The coefficient-changed original DG category uses the same opposite object convention as
    the corrected quotient. -/
def OriginalCoefficientDGCategory := ComplexCategoryᵒᵖ

/-- The coefficient-changed original DG Hom in the opposite object orientation. -/
def originalCoefficientDGEnrichedHom
    (K L : OriginalCoefficientDGCategory) : QuotientDGCochain :=
  OriginalCoefficientCochainComplex L.unop K.unop

/-- The coefficient-changed original DG identity in the opposite object orientation. -/
def originalCoefficientDGEnrichedId (K : OriginalCoefficientDGCategory) :
    𝟙_ QuotientDGCochain ⟶ originalCoefficientDGEnrichedHom K K :=
  OriginalCoefficientDGIdentity K.unop

/-- The coefficient-changed original DG composition in the opposite object orientation. -/
def originalCoefficientDGEnrichedComp
    (K L M : OriginalCoefficientDGCategory) :
    originalCoefficientDGEnrichedHom K L ⊗ originalCoefficientDGEnrichedHom L M ⟶
      originalCoefficientDGEnrichedHom K M :=
  OriginalCoefficientDGComposition M.unop L.unop K.unop

/-- The original bounded-complex DG category after coefficient change. -/
@[implicit_reducible]
noncomputable instance originalCoefficientDGEnrichedCategory :
    EnrichedCategory QuotientDGCochain OriginalCoefficientDGCategory where
  Hom := originalCoefficientDGEnrichedHom
  id := originalCoefficientDGEnrichedId
  comp := originalCoefficientDGEnrichedComp
  id_comp K L := OriginalCoefficientDGIdentity_comp K.unop L.unop
  comp_id K L := OriginalCoefficientDG_comp_identity K.unop L.unop
  assoc W X Y Z := OriginalCoefficientDGComposition_assoc
    W.unop X.unop Y.unop Z.unop

/-- The canonical DG-enriched functor from the original coefficient-changed category to the
corrected Drinfeld quotient, given on Hom complexes by the zero-word inclusion. -/
noncomputable def originalToCorrectedQuotientDG :
    EnrichedFunctor QuotientDGCochain
      OriginalCoefficientDGCategory CorrectedQuotientDGCategory where
  obj K := Opposite.op K.unop
  map K L := OriginalCoefficientHomToQuotient L.unop K.unop
  map_id K := OriginalCoefficientDGIdentity_map K.unop
  map_comp K L M :=
    OriginalCoefficientDGComposition_map M.unop L.unop K.unop

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
