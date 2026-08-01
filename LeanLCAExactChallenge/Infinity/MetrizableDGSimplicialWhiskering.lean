/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModuleWhiskering

/-!
# Simplicial whiskering in the direct DG carrier

The tensor-unit representative of a bounded chain map is transported through Dold--Kan and
degreewise module forgetting. Its resulting simplicial-set vertex is the ordinary morphism in
the direct DG simplicial category represented by the original bounded map.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open AlgebraicTopology
open CategoryTheory CategoryTheory.MonoidalCategory
open Opposite Simplicial
open scoped MonoidalCategory Simplicial

/-- Naturality of the degree-zero inclusion in the direct Dold--Kan inverse. -/
theorem zModuleDoldKanInverseZeroIso_hom_naturality
    {A B : DirectZChain} (f : A ⟶ B) :
    (zModuleDoldKanInverseZeroIso A).hom ≫
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map f).app (op ⦋0⦌) =
      f.f 0 ≫ (zModuleDoldKanInverseZeroIso B).hom := by
  apply (cancel_mono (zModuleDoldKanInverseZeroIso B).inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [zModuleDoldKanInverseZeroIso_inv_naturality]
  simp

/-- The direct Dold--Kan inverse lax unit is the degree-zero identity-summand inclusion. -/
theorem zModuleDoldKanInverseLaxUnit_f_zero :
    (Functor.LaxMonoidal.ε
      DoldKanMonoidal.zModuleDoldKanEquivalence.inverse).app (op ⦋0⦌) =
      (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).hom := by
  let adj := DoldKanMonoidal.zModuleDoldKanEquivalence.toAdjunction
  let u := Functor.LaxMonoidal.ε
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse
  let X : DirectZSimp := 𝟙_ DirectZSimp
  let Y := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj (𝟙_ DirectZChain)
  let qX := (NormalizedMooreComplex.objX X 0).arrow
  let qY := (NormalizedMooreComplex.objX Y 0).arrow
  have hadj :
      DoldKanMonoidal.zModuleDoldKanEquivalence.functor.map u ≫
          DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app
            (𝟙_ DirectZChain) =
        DoldKanMonoidal.normalizedAlexanderWhitneyUnit := by
    change DoldKanMonoidal.zModuleDoldKanEquivalence.functor.map
        (adj.homEquiv _ _ DoldKanMonoidal.normalizedAlexanderWhitneyUnit) ≫
      adj.counit.app (𝟙_ DirectZChain) =
        DoldKanMonoidal.normalizedAlexanderWhitneyUnit
    exact (adj.homEquiv_counit _ _
      (adj.homEquiv _ _ DoldKanMonoidal.normalizedAlexanderWhitneyUnit)).symm.trans
        (Equiv.symm_apply_apply _ DoldKanMonoidal.normalizedAlexanderWhitneyUnit)
  have hchain := HomologicalComplex.congr_hom hadj 0
  have hincRaw := HomologicalComplex.congr_hom
    ((inclusionOfMooreComplex (ModuleCat ℤ)).naturality u) 0
  have hqX : ((inclusionOfMooreComplex (ModuleCat ℤ)).app X).f 0 = qX := by
    dsimp only [qX]
    exact inclusionOfMooreComplexMap_f _ 0
  have hqY : ((inclusionOfMooreComplex (ModuleCat ℤ)).app Y).f 0 = qY := by
    dsimp only [qY]
    exact inclusionOfMooreComplexMap_f _ 0
  have hinc :
      ((normalizedMooreComplex (ModuleCat ℤ)).map u).f 0 ≫ qY =
        qX ≫ u.app (op ⦋0⦌) := by
    rw [← hqY, ← hqX]
    exact hincRaw
  have hcounit :
      qY ≫ (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv =
        (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app
          (𝟙_ DirectZChain)).f 0 := by
    change (NormalizedMooreComplex.objX Y 0).arrow ≫
        (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv = _
    rw [zModuleDoldKanCounit_f_zero]
  have huinv :
      u.app (op ⦋0⦌) ≫
          (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv = 𝟙 _ := by
    letI : IsIso qX := by
      change IsIso (⊤ : Subobject (X.obj (op ⦋0⦌))).arrow
      infer_instance
    letI : Epi qX := IsIso.epi_of_iso qX
    apply (cancel_epi qX).1
    calc
      qX ≫ (u.app (op ⦋0⦌) ≫
          (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv) =
        (qX ≫ u.app (op ⦋0⦌)) ≫
          (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv :=
        (Category.assoc _ _ _).symm
      _ = (((normalizedMooreComplex (ModuleCat ℤ)).map u).f 0 ≫ qY) ≫
          (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv :=
        congrArg (fun t ↦ t ≫
          (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv) hinc.symm
      _ = ((normalizedMooreComplex (ModuleCat ℤ)).map u).f 0 ≫
          (qY ≫ (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv) :=
        Category.assoc _ _ _
      _ = ((normalizedMooreComplex (ModuleCat ℤ)).map u).f 0 ≫
          (DoldKanMonoidal.zModuleDoldKanEquivalence.counitIso.hom.app
            (𝟙_ DirectZChain)).f 0 := congrArg _ hcounit
      _ = DoldKanMonoidal.normalizedAlexanderWhitneyUnit.f 0 := hchain
      _ = qX := DoldKanMonoidal.normalizedAlexanderWhitneyUnit_f_zero
      _ = qX ≫ 𝟙 _ := (Category.comp_id _).symm
  apply (cancel_mono
    (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).inv).1
  rw [huinv, Iso.hom_inv_id]

/-- The direct Dold--Kan lax unit sends `1` to the degree-zero identity summand. -/
theorem zModuleDoldKanInverseLaxUnit_f_zero_apply_one :
    ((Functor.LaxMonoidal.ε
      DoldKanMonoidal.zModuleDoldKanEquivalence.inverse).app (op ⦋0⦌)).hom
        (show (𝟙_ DirectZChain).X 0 from (1 : ℤ)) =
      (zModuleDoldKanInverseZeroIso (𝟙_ DirectZChain)).hom.hom
        (show (𝟙_ DirectZChain).X 0 from (1 : ℤ)) := by
  exact ConcreteCategory.congr_hom zModuleDoldKanInverseLaxUnit_f_zero _

/-- The module-forgetful lax unit sends the unique point to the ring unit. -/
@[simp]
theorem zModuleForgetLaxUnit_apply_unit :
    Functor.LaxMonoidal.ε (forget (ModuleCat.{0} ℤ)) PUnit.unit = (1 : ℤ) := by
  change ((ModuleCat.adj ℤ).homEquiv _ _
    (Functor.OplaxMonoidal.η (ModuleCat.free ℤ))) PUnit.unit = 1
  rw [ModuleCat.adj_homEquiv]
  exact ModuleCat.free_η_freeMk ℤ PUnit.unit

/-- Forgetting a tensor-unit map of simplicial modules evaluates its vertex at `1`. -/
@[simp]
theorem zModuleSimplicialForget_unitHom_vertex
    (X : DirectZSimp)
    (φ : 𝟙_ DirectZSimp ⟶ X) :
    SSet.unitHomEquiv (zModuleSimplicialForget.obj X)
        (Functor.LaxMonoidal.ε zModuleSimplicialForget ≫
          zModuleSimplicialForget.map φ) =
      (φ.app (op ⦋0⦌)).hom
        (show (𝟙_ DirectZSimp).obj (op ⦋0⦌) from (1 : ℤ)) := by
  change ((Functor.LaxMonoidal.ε (forget (ModuleCat.{0} ℤ))) ≫
        (forget (ModuleCat.{0} ℤ)).map (φ.app (op ⦋0⦌))) PUnit.unit = _
  change (φ.app (op ⦋0⦌)).hom
      (Functor.LaxMonoidal.ε (forget (ModuleCat.{0} ℤ)) PUnit.unit) =
    (φ.app (op ⦋0⦌)).hom
      (show (𝟙_ DirectZSimp).obj (op ⦋0⦌) from (1 : ℤ))
  rw [zModuleForgetLaxUnit_apply_unit]

/-- The canonical simplicial-module map represented by a bounded chain map. -/
def dgMappingDirectZModuleMorphismSimplicialMap
    {K L : ComplexCategory} (f : K ⟶ L) :
    𝟙_ DirectZSimp ⟶ dgMappingDirectZModuleSimplicialModule K L :=
  Functor.LaxMonoidal.ε DoldKanMonoidal.zModuleDoldKanEquivalence.inverse ≫
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingDirectZModuleChainMorphismMap f)

/-- The canonical simplicial-set map represented by a bounded chain map. -/
def dgMappingDirectZModuleMorphismSSetMap
    {K L : ComplexCategory} (f : K ⟶ L) :
    𝟙_ SSet ⟶ dgMappingDirectZModuleSSet K L :=
  Functor.LaxMonoidal.ε zModuleSimplicialForget ≫
    zModuleSimplicialForget.map (dgMappingDirectZModuleMorphismSimplicialMap f)

/-- The Dold--Kan tensor-unit map has the expected degree-zero vertex. -/
theorem dgMappingDirectZModuleMorphismSimplicialMap_vertex
    {K L : ComplexCategory} (f : K ⟶ L) :
    ((dgMappingDirectZModuleMorphismSimplicialMap f).app (op ⦋0⦌)).hom
        (show (𝟙_ DirectZChain).X 0 from (1 : ℤ)) =
      (zModuleDoldKanInverseZeroIso
        (dgMappingDirectZModuleChainComplex K L)).hom.hom
          ((dgMappingDirectZModuleMorphismDegreeZero f).hom (1 : ℤ)) := by
  unfold dgMappingDirectZModuleMorphismSimplicialMap
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  rw [zModuleDoldKanInverseLaxUnit_f_zero_apply_one]
  have h := ConcreteCategory.congr_hom
    (zModuleDoldKanInverseZeroIso_hom_naturality
      (dgMappingDirectZModuleChainMorphismMap f))
    (show (𝟙_ DirectZChain).X 0 from (1 : ℤ))
  rw [dgMappingDirectZModuleChainMorphismMap_f_zero] at h
  exact h

private theorem dgMappingDirectZModuleMorphismDegreeZero_bounded
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L
        ((dgMappingDirectZModuleMorphismDegreeZero f).hom (1 : ℤ)) = f := by
  let x := (dgMappingDirectZModuleMorphismDegreeZero f).hom (1 : ℤ)
  let x' := (dgMappingZModuleChainComplexIsoDirect K L).inv.f 0 x
  have hx' : (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0 x' = x := by
    exact ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom
        (dgMappingZModuleChainComplexIsoDirect K L).inv_hom_id 0) x
  have hz := dgMappingZModuleZeroCochain_f_eq_boundedHom K L x'
  change dgMappingZModuleChainComplexZeroEquivBoundedHom K L x' = f
  apply (boundedCochainComplex MetrizableLCA.{0}).ι.map_injective
  apply HomologicalComplex.Hom.ext
  funext i
  rw [← hz i]
  change (dgMappingZModuleZeroCochain K L x').v i i (add_zero i) = _
  rw [dgMappingZModuleZeroCochain, hx']
  exact CochainComplex.HomComplex.Cochain.congr_v
    (dgMappingDirectZModuleMorphismDegreeZero_toRestriction_apply_one f)
    i i (add_zero i)

private theorem dgMappingDirectZModuleVerticesEquiv_splitting_zero
    (K L : ComplexCategory) (x : (dgMappingDirectZModuleChainComplex K L).X 0) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K L
        ((zModuleDoldKanInverseZeroIso
          (dgMappingDirectZModuleChainComplex K L)).hom.hom x) =
      dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L x := by
  change dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L
    ((zModuleDoldKanInverseZeroIso
      (dgMappingDirectZModuleChainComplex K L)).inv.hom
        ((zModuleDoldKanInverseZeroIso
          (dgMappingDirectZModuleChainComplex K L)).hom.hom x)) = _
  exact congrArg (dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L)
    (ConcreteCategory.congr_hom
      (zModuleDoldKanInverseZeroIso
        (dgMappingDirectZModuleChainComplex K L)).hom_inv_id x)

/-- The canonical simplicial-set map represents the original bounded morphism. -/
theorem dgMappingDirectZModuleMorphismSSetMap_vertex
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K L
        (SSet.unitHomEquiv (dgMappingDirectZModuleSSet K L)
          (dgMappingDirectZModuleMorphismSSetMap f)) = f := by
  rw [dgMappingDirectZModuleMorphismSSetMap,
    zModuleSimplicialForget_unitHom_vertex,
    dgMappingDirectZModuleMorphismSimplicialMap_vertex]
  rw [dgMappingDirectZModuleVerticesEquiv_splitting_zero]
  exact dgMappingDirectZModuleMorphismDegreeZero_bounded f

/-- The canonical simplicial-set representative is the enriched-Hom representative of
`directDGMorphism f`. -/
theorem dgMappingDirectZModuleMorphismSSetMap_eq_eHomEquiv
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleMorphismSSetMap f =
      eHomEquiv SSet (directDGMorphism f) := by
  apply (SSet.unitHomEquiv (dgMappingDirectZModuleSSet K L)).injective
  apply (dgMappingDirectZModuleVerticesEquivBoundedMorphisms K L).injective
  rw [dgMappingDirectZModuleMorphismSSetMap_vertex]
  change f = directDGToComplexFunctor.map (directDGMorphism f)
  exact (directDGToComplexFunctor_map_directDGMorphism f).symm

/-- The Dold--Kan tensor-unit representative acts by chain postcomposition. -/
theorem dgMappingDirectZModuleMorphismSimplicialMap_postcomposition
    (K : ComplexCategory) {L M : ComplexCategory} (g : L ⟶ M) :
    (ρ_ (dgMappingDirectZModuleSimplicialModule K L)).inv ≫
        dgMappingDirectZModuleSimplicialModule K L ◁
          dgMappingDirectZModuleMorphismSimplicialMap g ≫
        dgMappingDirectZModuleSimplicialComposition K L M =
      DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
        (dgMappingDirectZModulePostcomposition K g) := by
  let F := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse
  let A := dgMappingDirectZModuleChainComplex K L
  let B := dgMappingDirectZModuleChainComplex L M
  let c := dgTruncatedCompositionReversed K L M
  let f := dgMappingDirectZModuleChainMorphismMap g
  change (ρ_ (F.obj A)).inv ≫
      F.obj A ◁ (Functor.LaxMonoidal.ε F ≫ F.map f) ≫
      (β_ (F.obj A) (F.obj B)).hom ≫
      Functor.LaxMonoidal.μ F B A ≫ F.map c =
    F.map (dgMappingDirectZModulePostcomposition K g)
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [rightUnitor_inv_braiding_assoc]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
  rw [← F.map_comp, ← F.map_comp]
  rw [dgMappingDirectZModuleChainMorphismMap_postcomposition]

/-- The simplicial-set tensor-unit representative acts by postcomposition. -/
theorem dgMappingDirectZModuleMorphismSSetMap_postcomposition
    (K : ComplexCategory) {L M : ComplexCategory} (g : L ⟶ M) :
    (ρ_ (dgMappingDirectZModuleSSet K L)).inv ≫
        dgMappingDirectZModuleSSet K L ◁
          dgMappingDirectZModuleMorphismSSetMap g ≫
        dgMappingDirectZModuleSSetComposition K L M =
      zModuleSimplicialForget.map
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
          (dgMappingDirectZModulePostcomposition K g)) := by
  let F := zModuleSimplicialForget
  let A := dgMappingDirectZModuleSimplicialModule K L
  let B := dgMappingDirectZModuleSimplicialModule L M
  let c := dgMappingDirectZModuleSimplicialComposition K L M
  let f := dgMappingDirectZModuleMorphismSimplicialMap g
  change (ρ_ (F.obj A)).inv ≫
      F.obj A ◁ (Functor.LaxMonoidal.ε F ≫ F.map f) ≫
      simplicialZModuleTensorPairing A B ≫ F.map c =
    F.map (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingDirectZModulePostcomposition K g))
  rw [← zModuleSimplicialForget_mu_eq_pairing]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.LaxMonoidal.right_unitality_inv_assoc]
  rw [← F.map_comp, ← F.map_comp]
  rw [dgMappingDirectZModuleMorphismSimplicialMap_postcomposition]

set_option backward.isDefEq.respectTransparency true in
/-- Enriched postcomposition in the direct DG simplicial category is the Dold--Kan
realization of chain postcomposition. -/
theorem directDG_eHomWhiskerLeft_eq_postcomposition
    (K : ComplexCategory) {L M : ComplexCategory} (g : L ⟶ M) :
    eHomWhiskerLeft SSet (directDGObject K) (directDGMorphism g) =
      zModuleSimplicialForget.map
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
          (dgMappingDirectZModulePostcomposition K g)) := by
  unfold eHomWhiskerLeft
  have hcomp := directDG_sHomComp_eq K L M
  change eComp SSet
      (ForgetEnrichment.to SSet (directDGObject K))
      (ForgetEnrichment.to SSet (directDGObject L))
      (ForgetEnrichment.to SSet (directDGObject M)) =
        dgMappingDirectZModuleSSetComposition K L M at hcomp
  erw [hcomp]
  rw [← dgMappingDirectZModuleMorphismSSetMap_eq_eHomEquiv]
  convert dgMappingDirectZModuleMorphismSSetMap_postcomposition K g using 1
  · exact congrArg₂ (fun A B : SSet ↦ A ⟶ B)
      (directDG_enrichedHom_eq K L) (directDG_enrichedHom_eq K M)
  · rfl
  · rfl

/-- The Dold--Kan tensor-unit representative acts by chain precomposition. -/
theorem dgMappingDirectZModuleMorphismSimplicialMap_precomposition
    (M : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (λ_ (dgMappingDirectZModuleSimplicialModule L M)).inv ≫
        dgMappingDirectZModuleMorphismSimplicialMap f ▷
          dgMappingDirectZModuleSimplicialModule L M ≫
        dgMappingDirectZModuleSimplicialComposition K L M =
      DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
        (dgMappingDirectZModulePrecomposition M f) := by
  let F := DoldKanMonoidal.zModuleDoldKanEquivalence.inverse
  let A := dgMappingDirectZModuleChainComplex L M
  let B := dgMappingDirectZModuleChainComplex K L
  let c := dgTruncatedCompositionReversed K L M
  let q := dgMappingDirectZModuleChainMorphismMap f
  change (λ_ (F.obj A)).inv ≫
      (Functor.LaxMonoidal.ε F ≫ F.map q) ▷ F.obj A ≫
      (β_ (F.obj B) (F.obj A)).hom ≫
      Functor.LaxMonoidal.μ F A B ≫ F.map c =
    F.map (dgMappingDirectZModulePrecomposition M f)
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [leftUnitor_inv_braiding_assoc]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  rw [Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [Functor.LaxMonoidal.right_unitality_inv_assoc]
  rw [← F.map_comp, ← F.map_comp]
  rw [dgMappingDirectZModuleChainMorphismMap_precomposition]

/-- The simplicial-set tensor-unit representative acts by precomposition. -/
theorem dgMappingDirectZModuleMorphismSSetMap_precomposition
    (M : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (λ_ (dgMappingDirectZModuleSSet L M)).inv ≫
        dgMappingDirectZModuleMorphismSSetMap f ▷
          dgMappingDirectZModuleSSet L M ≫
        dgMappingDirectZModuleSSetComposition K L M =
      zModuleSimplicialForget.map
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
          (dgMappingDirectZModulePrecomposition M f)) := by
  let F := zModuleSimplicialForget
  let A := dgMappingDirectZModuleSimplicialModule L M
  let B := dgMappingDirectZModuleSimplicialModule K L
  let c := dgMappingDirectZModuleSimplicialComposition K L M
  let q := dgMappingDirectZModuleMorphismSimplicialMap f
  change (λ_ (F.obj A)).inv ≫
      (Functor.LaxMonoidal.ε F ≫ F.map q) ▷ F.obj A ≫
      simplicialZModuleTensorPairing B A ≫ F.map c =
    F.map (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingDirectZModulePrecomposition M f))
  rw [← zModuleSimplicialForget_mu_eq_pairing]
  rw [MonoidalCategory.comp_whiskerRight_assoc]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [Functor.LaxMonoidal.left_unitality_inv_assoc]
  rw [← F.map_comp, ← F.map_comp]
  rw [dgMappingDirectZModuleMorphismSimplicialMap_precomposition]

set_option backward.isDefEq.respectTransparency true in
/-- Enriched precomposition in the direct DG simplicial category is the Dold--Kan
realization of chain precomposition. -/
theorem directDG_eHomWhiskerRight_eq_precomposition
    (M : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    eHomWhiskerRight SSet (directDGMorphism f) (directDGObject M) =
      zModuleSimplicialForget.map
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
          (dgMappingDirectZModulePrecomposition M f)) := by
  unfold eHomWhiskerRight
  have hcomp := directDG_sHomComp_eq K L M
  change eComp SSet
      (ForgetEnrichment.to SSet (directDGObject K))
      (ForgetEnrichment.to SSet (directDGObject L))
      (ForgetEnrichment.to SSet (directDGObject M)) =
        dgMappingDirectZModuleSSetComposition K L M at hcomp
  erw [hcomp]
  rw [← dgMappingDirectZModuleMorphismSSetMap_eq_eHomEquiv]
  convert dgMappingDirectZModuleMorphismSSetMap_precomposition M f using 1
  · exact congrArg₂ (fun A B : SSet ↦ A ⟶ B)
      (directDG_enrichedHom_eq L M) (directDG_enrichedHom_eq K M)
  · rfl
  · rfl

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
