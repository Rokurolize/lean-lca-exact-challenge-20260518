import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientOriginalSimplicialComparison
import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence
import LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve

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
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial
open QuotientDoldKanMonoidal

/-- Degree zero of the quotient-coefficient Dold--Kan inverse. -/
def quotientModuleDoldKanInverseZeroIso (T : QuotientChain) :
    T.X 0 ≅ (quotientModuleDoldKanEquivalence.inverse.obj T).obj (op ⦋0⦌) := by
  let s := AlgebraicTopology.DoldKan.Γ₀.splitting T
  let p : ∀ A : SimplicialObject.Splitting.IndexSet (op ⦋0⦌),
      s.N A.1.unop.len ⟶ T.X 0 := fun A =>
    eqToHom (by rw [doldKanIndexSet_zero_eq_id A]; rfl)
  refine
    { hom := s.ι 0
      inv := s.desc (op ⦋0⦌) p
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← s.cofan_inj_id 0]
    exact (s.ι_desc (op ⦋0⦌) p
      (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌))).trans (by
        dsimp only [p]
        apply eqToHom_refl)
  · apply s.hom_ext'
    intro A
    have hA := doldKanIndexSet_zero_eq_id A
    subst A
    have hdesc :
        (s.cofan (op ⦋0⦌)).inj
              (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
            (s.desc (op ⦋0⦌) p ≫ s.ι 0) =
          p (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫ s.ι 0 :=
      s.ι_desc_assoc (op ⦋0⦌) p
        (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) (s.ι 0)
    refine hdesc.trans ?_
    have hp : p (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) = 𝟙 _ := by
      dsimp only [p]
      apply eqToHom_refl
    rw [hp]
    calc
      𝟙 _ ≫ s.ι 0 = s.ι 0 := Category.id_comp _
      _ = (s.cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) :=
        (s.cofan_inj_id 0).symm
      _ = (s.cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫ 𝟙 _ :=
        (Category.comp_id _).symm

/-- A bounded morphism as a degree-zero element of the coefficient-changed original Hom. -/
def originalCoefficientDGMorphismSpan {K L : ComplexCategory} (f : K ⟶ L) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      (OriginalCoefficientCochainComplex K L).X 0 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton QuotientCoefficientRing _
    (ULift.up (ULift.up (CochainComplex.HomComplex.Cochain.ofHom
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)))))

lemma originalCoefficientDGMorphismSpan_d {K L : ComplexCategory} (f : K ⟶ L) :
    originalCoefficientDGMorphismSpan f ≫
      (OriginalCoefficientCochainComplex K L).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.down_injective
  apply ULift.down_injective
  change ((dgHomZModuleCochainComplex K L).d 0 1).hom
    (x.down • CochainComplex.HomComplex.Cochain.ofHom
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) = 0
  calc
    _ = x.down • ((dgHomZModuleCochainComplex K L).d 0 1).hom
        (CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) :=
      ((dgHomZModuleCochainComplex K L).d 0 1).hom.toAddMonoidHom.map_zsmul _ _
    _ = 0 := by
      change x.down • CochainComplex.HomComplex.δ 0 1
        (CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) = 0
      rw [CochainComplex.HomComplex.δ_ofHom, zsmul_zero]

theorem originalCoefficientDGMorphismSpan_op_comp
    {K L M : ComplexCategoryᵒᵖ} (f : K ⟶ L) (g : L ⟶ M) :
    (λ_ (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv ≫
        (originalCoefficientDGMorphismSpan f.unop ⊗ₘ
          originalCoefficientDGMorphismSpan g.unop) ≫
        originalDGCompositionComponent M.unop L.unop K.unop rfl =
      originalCoefficientDGMorphismSpan (f ≫ g).unop := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change QuotientCoefficientRing at x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  change (originalDGCompositionComponent M.unop L.unop K.unop rfl).hom
      ((originalCoefficientDGMorphismSpan f.unop).hom 1 ⊗ₜ[QuotientCoefficientRing]
        (originalCoefficientDGMorphismSpan g.unop).hom x) =
    (originalCoefficientDGMorphismSpan (f ≫ g).unop).hom x
  rw [show (originalCoefficientDGMorphismSpan f.unop).hom 1 =
      ULift.up (ULift.up (CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f.unop))) by
    exact LinearMap.toSpanSingleton_apply_one _ _ _]
  rw [show (originalCoefficientDGMorphismSpan g.unop).hom x =
      x • (ULift.up (ULift.up (CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map g.unop))) :
          OriginalCoefficientModule
            ((dgHomZModuleCochainComplex M.unop L.unop).X 0)) by
    exact LinearMap.toSpanSingleton_apply _ _ _ _]
  rw [TensorProduct.tmul_smul, map_smul,
    originalDGCompositionComponent_tmul]
  apply congrArg
  apply congrArg
  rw [dgCochainCompTensorReversed_tmul]
  simp [originalCoefficientDGMorphismSpan,
    CochainComplex.HomComplex.Cochain.ofHom_comp]

@[simp]
theorem originalCoefficientDGMorphismSpan_id (K : ComplexCategory) :
    originalCoefficientDGMorphismSpan (𝟙 K) =
      OriginalCoefficientDGIdentitySpan K := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  simp [originalCoefficientDGMorphismSpan, OriginalCoefficientDGIdentitySpan,
    identityCochain]

/-- A bounded morphism in degree zero of the smart-truncated coefficient-changed Hom. -/
def originalCoefficientDGChainMorphismDegreeZero {K L : ComplexCategory} (f : K ⟶ L) :
    𝟙_ (ModuleCat.{1} QuotientCoefficientRing) ⟶
      (originalCoefficientDGChainEnrichedHom (Opposite.op L) (Opposite.op K)).X 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  exact
    (OriginalCoefficientCochainComplex K L).liftCycles'
        (originalCoefficientDGMorphismSpan f) 1 rfl
        (originalCoefficientDGMorphismSpan_d f) ≫
      ((OriginalCoefficientCochainComplex K L).truncLE'XIsoCycles
        ComplexShape.embeddingDownNat rfl hb).inv

lemma originalCoefficientDGChainMorphismDegreeZero_toRestriction
    {K L : ComplexCategory} (f : K ⟶ L) :
    originalCoefficientDGChainMorphismDegreeZero f ≫
        ((OriginalCoefficientCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      originalCoefficientDGMorphismSpan f := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  rw [quotientTruncLEToRestriction_f_zero _ hb]
  dsimp [originalCoefficientDGChainMorphismDegreeZero]
  simp only [Category.assoc]
  erw [quotientTruncLEIsoCycles_inv_hom_of_proofs_assoc
    (OriginalCoefficientCochainComplex K L) 0 0 rfl rfl hb hb]
  simp

theorem originalCoefficientDGChainMorphismDegreeZero_op_comp
    {K L M : ComplexCategoryᵒᵖ} (f : K ⟶ L) (g : L ⟶ M) :
    (λ_ (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).inv ≫
        (originalCoefficientDGChainMorphismDegreeZero f.unop ⊗ₘ
          originalCoefficientDGChainMorphismDegreeZero g.unop) ≫
        quotientTruncatedMapComponent
          (originalCoefficientDGEnrichedComp
            (show OriginalCoefficientDGCategory from K)
            (show OriginalCoefficientDGCategory from L)
            (show OriginalCoefficientDGCategory from M)) rfl =
      originalCoefficientDGChainMorphismDegreeZero (f ≫ g).unop := by
  apply (cancel_mono
    (((originalCoefficientDGEnrichedHom
      (show OriginalCoefficientDGCategory from K)
      (show OriginalCoefficientDGCategory from M)).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0)).1
  simp only [Category.assoc]
  slice_lhs 3 4 =>
    rw [originalTruncatedCompositionComponent_to_raw]
  slice_lhs 2 3 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  have hf := originalCoefficientDGChainMorphismDegreeZero_toRestriction f.unop
  change originalCoefficientDGChainMorphismDegreeZero f.unop ≫
      ((originalCoefficientDGEnrichedHom
        (show OriginalCoefficientDGCategory from K)
        (show OriginalCoefficientDGCategory from L)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
    originalCoefficientDGMorphismSpan f.unop at hf
  have hg := originalCoefficientDGChainMorphismDegreeZero_toRestriction g.unop
  change originalCoefficientDGChainMorphismDegreeZero g.unop ≫
      ((originalCoefficientDGEnrichedHom
        (show OriginalCoefficientDGCategory from L)
        (show OriginalCoefficientDGCategory from M)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
    originalCoefficientDGMorphismSpan g.unop at hg
  have hfg := originalCoefficientDGChainMorphismDegreeZero_toRestriction (f ≫ g).unop
  change originalCoefficientDGChainMorphismDegreeZero (f ≫ g).unop ≫
      ((originalCoefficientDGEnrichedHom
        (show OriginalCoefficientDGCategory from K)
        (show OriginalCoefficientDGCategory from M)).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
    originalCoefficientDGMorphismSpan (f ≫ g).unop at hfg
  rw [hf, hg, hfg]
  exact originalCoefficientDGMorphismSpan_op_comp f g

@[simp]
theorem originalCoefficientDGChainMorphismDegreeZero_id (K : ComplexCategory) :
    originalCoefficientDGChainMorphismDegreeZero (𝟙 K) =
      originalCoefficientDGChainIdentityDegreeZero
        (show OriginalCoefficientDGCategory from Opposite.op K) := by
  apply (cancel_mono
    (((OriginalCoefficientCochainComplex K K).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0)).1
  rw [originalCoefficientDGChainMorphismDegreeZero_toRestriction]
  have h := originalCoefficientDGChainIdentityDegreeZero_toRestriction
    (show OriginalCoefficientDGCategory from Opposite.op K)
  change originalCoefficientDGChainIdentityDegreeZero
      (show OriginalCoefficientDGCategory from Opposite.op K) ≫
        ((OriginalCoefficientCochainComplex K K).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 =
      OriginalCoefficientDGIdentitySpan K at h
  rw [h, originalCoefficientDGMorphismSpan_id]

/-- The vertex in the original coefficient-changed mapping simplicial set represented by `f`. -/
def originalCoefficientDGMappingVertex {K L : ComplexCategory} (f : K ⟶ L) :
    originalCoefficientDGMappingSSet K L _⦋0⦌ :=
  (quotientModuleDoldKanInverseZeroIso
    (originalCoefficientDGChainEnrichedHom (Opposite.op L) (Opposite.op K))).hom.hom
      ((originalCoefficientDGChainMorphismDegreeZero f).hom 1)

/-- A bounded morphism as a tensor-unit-shaped morphism in the smart-truncated original
coefficient DG enrichment. -/
def originalCoefficientDGChainMorphismMap
    {K L : ComplexCategoryᵒᵖ} (f : K ⟶ L) :
    𝟙_ QuotientDGChain ⟶
      originalCoefficientDGChainEnrichedHom
        (show OriginalCoefficientDGCategory from K)
        (show OriginalCoefficientDGCategory from L) :=
  (ChainComplex.fromSingle₀Equiv
    (originalCoefficientDGChainEnrichedHom
      (show OriginalCoefficientDGCategory from K)
      (show OriginalCoefficientDGCategory from L))
    (𝟙_ (ModuleCat.{1} QuotientCoefficientRing))).symm
      (originalCoefficientDGChainMorphismDegreeZero f.unop)

/-- A bounded morphism in the ordinary category underlying the smart-truncated enrichment. -/
def originalCoefficientDGChainMorphism
    {K L : ComplexCategoryᵒᵖ} (f : K ⟶ L) :
    (ForgetEnrichment.of QuotientDGChain
      (show OriginalCoefficientDGCategory from K) :
        ForgetEnrichment QuotientDGChain OriginalCoefficientDGCategory) ⟶
      ForgetEnrichment.of QuotientDGChain
        (show OriginalCoefficientDGCategory from L) :=
  ForgetEnrichment.homOf QuotientDGChain
    (originalCoefficientDGChainMorphismMap f)

@[simp]
theorem originalCoefficientDGChainMorphismMap_f_zero
    {K L : ComplexCategoryᵒᵖ} (f : K ⟶ L) :
    (originalCoefficientDGChainMorphismMap f).f 0 =
      originalCoefficientDGChainMorphismDegreeZero f.unop := by
  exact ChainComplex.fromSingle₀Equiv_symm_apply_f_zero _

set_option maxHeartbeats 1000000 in
-- Reducing the degree-zero tensor-unit transports requires extra elaboration budget.
theorem originalCoefficientDGChainMorphismMap_op_comp
    {K L M : ComplexCategoryᵒᵖ} (f : K ⟶ L) (g : L ⟶ M) :
    (λ_ (𝟙_ QuotientDGChain)).inv ≫
        (originalCoefficientDGChainMorphismMap f ⊗ₘ
          originalCoefficientDGChainMorphismMap g) ≫
        originalCoefficientDGChainEnrichedComp
          (show OriginalCoefficientDGCategory from K)
          (show OriginalCoefficientDGCategory from L)
          (show OriginalCoefficientDGCategory from M) =
      originalCoefficientDGChainMorphismMap (f ≫ g) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  have hunit : (λ_ (𝟙_ QuotientDGChain)).inv.f 0 =
      (HomologicalComplex.leftUnitor' (𝟙_ QuotientDGChain)).inv 0 := rfl
  rw [hunit, HomologicalComplex.leftUnitor'_inv]
  slice_lhs 3 4 =>
    change _ ≫ (HomologicalComplex.tensorHom
      (originalCoefficientDGChainMorphismMap f)
      (originalCoefficientDGChainMorphismMap g)).f 0
    rw [originalChain_ιTensorObj_tensorHom]
  simp only [Category.assoc,
    originalCoefficientDGChainMorphismMap_f_zero]
  dsimp only [originalCoefficientDGChainEnrichedComp]
  slice_lhs 4 5 =>
    change HomologicalComplex.ιTensorObj
      (originalCoefficientDGChainEnrichedHom
        (show OriginalCoefficientDGCategory from K)
        (show OriginalCoefficientDGCategory from L))
      (originalCoefficientDGChainEnrichedHom
        (show OriginalCoefficientDGCategory from L)
        (show OriginalCoefficientDGCategory from M)) 0 0 0 rfl ≫
        quotientTruncatedMapDegree
          (originalCoefficientDGEnrichedComp
            (show OriginalCoefficientDGCategory from K)
            (show OriginalCoefficientDGCategory from L)
            (show OriginalCoefficientDGCategory from M)) 0
    exact ιTensorObj_quotientTruncatedMapDegree
      (originalCoefficientDGEnrichedComp
        (show OriginalCoefficientDGCategory from K)
        (show OriginalCoefficientDGCategory from L)
        (show OriginalCoefficientDGCategory from M)) rfl
  simp only [Category.assoc,
    originalCoefficientDGChainMorphismMap_f_zero]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change QuotientCoefficientRing at x
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [ChainComplex.single₀ObjXSelf]
  simp only [Iso.refl_inv, ModuleCat.id_apply]
  have hcomp := ConcreteCategory.congr_hom
    (originalCoefficientDGChainMorphismDegreeZero_op_comp f g) x
  exact hcomp

@[simp]
theorem originalCoefficientDGChainMorphismMap_id (K : ComplexCategory) :
    originalCoefficientDGChainMorphismMap (𝟙 (Opposite.op K)) =
      originalCoefficientDGChainEnrichedId
        (show OriginalCoefficientDGCategory from Opposite.op K) := by
  apply HomologicalComplex.from_single_hom_ext
  rw [originalCoefficientDGChainMorphismMap_f_zero,
    originalCoefficientDGChainEnrichedId_f_zero]
  simpa using originalCoefficientDGChainMorphismDegreeZero_id K

/-- The opposite bounded-complex category maps to the ordinary category underlying the
smart-truncated coefficient-changed enrichment. -/
noncomputable def originalCoefficientDGChainOrdinaryFunctor :
    ComplexCategoryᵒᵖ ⥤
      ForgetEnrichment QuotientDGChain OriginalCoefficientDGCategory where
  obj K := ForgetEnrichment.of QuotientDGChain
    (show OriginalCoefficientDGCategory from K)
  map f := originalCoefficientDGChainMorphism f
  map_id K := by
    change originalCoefficientDGChainMorphismMap (𝟙 K) =
      originalCoefficientDGChainEnrichedId
        (show OriginalCoefficientDGCategory from K)
    simpa using originalCoefficientDGChainMorphismMap_id K.unop
  map_comp f g := by
    change originalCoefficientDGChainMorphismMap (f ≫ g) =
      ((λ_ (𝟙_ QuotientDGChain)).inv ≫
        (originalCoefficientDGChainMorphismMap f ⊗ₘ
          originalCoefficientDGChainMorphismMap g)) ≫
        originalCoefficientDGChainEnrichedComp
          (show OriginalCoefficientDGCategory from _)
          (show OriginalCoefficientDGCategory from _)
          (show OriginalCoefficientDGCategory from _)
    simpa only [Category.assoc] using
      (originalCoefficientDGChainMorphismMap_op_comp f g).symm

/-- An ordinary bounded morphism, regarded as a morphism in the original coefficient DG
simplicial category. -/
def originalCoefficientDGMorphism {K L : ComplexCategory} (f : K ⟶ L) :
    (ForgetEnrichment.of SSet
      (show OriginalCoefficientDGSSetEnrichedCategory from
        Opposite.op
          (show OriginalCoefficientDGSimplicialModuleCategory from Opposite.op K))) ⟶
      (ForgetEnrichment.of SSet
        (show OriginalCoefficientDGSSetEnrichedCategory from
          Opposite.op
            (show OriginalCoefficientDGSimplicialModuleCategory from Opposite.op L))) :=
  (SimplicialCategory.homEquiv' _ _).symm (originalCoefficientDGMappingVertex f)

lemma quotientNormalizedMooreTensorUnit_objX_succ (n : ℕ) :
    AlgebraicTopology.NormalizedMooreComplex.objX
      (𝟙_ (SimplicialObject QuotientModule)) (n + 1) = ⊥ := by
  rw [AlgebraicTopology.NormalizedMooreComplex.objX_add_one]
  apply le_antisymm
  · have hle := Finset.inf_le
      (s := Finset.univ)
      (f := fun k : Fin (n + 1) ↦
        kernelSubobject ((𝟙_ (SimplicialObject QuotientModule)).δ k.succ))
      (b := (0 : Fin (n + 1))) (by simp)
    have hk : kernelSubobject
        ((𝟙_ (SimplicialObject QuotientModule)).δ (0 : Fin (n + 1)).succ) = ⊥ := by
      change kernelSubobject (𝟙 (𝟙_ QuotientModule)) = ⊥
      apply le_antisymm
      · rw [Subobject.bot_eq_zero]
        apply Subobject.le_mk_of_comm 0
        simp only [zero_comp]
        simpa using (kernelSubobject_arrow_comp (f := 𝟙 (𝟙_ QuotientModule))).symm
      · exact bot_le
    exact hle.trans_eq hk
  · exact bot_le

theorem quotientNormalizedAlexanderWhitneyUnit_isIso :
    IsIso QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit := by
  letI (n : ℕ) :
      IsIso (QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit.f n) := by
    obtain rfl | n := n
    · rw [QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit_f_zero]
      change IsIso ((⊤ : Subobject (𝟙_ QuotientModule)).arrow)
      infer_instance
    · rw [QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit_f_succ]
      have hsrc : IsZero
          (AlgebraicTopology.NormalizedMooreComplex.objX
            (𝟙_ (SimplicialObject QuotientModule)) (n + 1) : QuotientModule) := by
        rw [quotientNormalizedMooreTensorUnit_objX_succ]
        exact IsZero.of_iso (isZero_zero QuotientModule) Subobject.botCoeIsoZero
      have htgt : IsZero ((𝟙_ QuotientChain).X (n + 1)) :=
        HomologicalComplex.isZero_single_obj_X
          (c := ComplexShape.down ℕ) 0 (𝟙_ QuotientModule) (n + 1) (by omega)
      exact Limits.IsZero.isIso hsrc htgt 0
  exact HomologicalComplex.Hom.isIso_of_components _

theorem quotientDoldKanInverseLaxUnit_isIso :
    IsIso (Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse) := by
  letI : IsIso QuotientDoldKanMonoidal.normalizedAlexanderWhitneyUnit :=
    quotientNormalizedAlexanderWhitneyUnit_isIso
  simp only [Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
  infer_instance

/-- The canonical map on tensor-unit-shaped morphisms under the quotient Dold--Kan inverse. -/
noncomputable def quotientDoldKanInverseUnitHomEquiv (T : QuotientChain) :
    (𝟙_ QuotientChain ⟶ T) ≃
      (𝟙_ QuotientSimplicialModule ⟶ quotientModuleDoldKanEquivalence.inverse.obj T) := by
  letI : IsIso (Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse) :=
    quotientDoldKanInverseLaxUnit_isIso
  exact quotientModuleDoldKanEquivalence.fullyFaithfulInverse.homEquiv.trans
    ((asIso (Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse)).symm.homCongr
      (Iso.refl _))

@[simp]
theorem quotientDoldKanInverseUnitHomEquiv_apply
    (T : QuotientChain) (f : 𝟙_ QuotientChain ⟶ T) :
    quotientDoldKanInverseUnitHomEquiv T f =
      Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse ≫
        quotientModuleDoldKanEquivalence.inverse.map f := by
  letI : IsIso (Functor.LaxMonoidal.ε quotientModuleDoldKanEquivalence.inverse) :=
    quotientDoldKanInverseLaxUnit_isIso
  simp [quotientDoldKanInverseUnitHomEquiv]

/-- Dold--Kan identifies the ordinary categories underlying the smart-truncated and simplicial
module enrichments. -/
noncomputable def originalCoefficientDGDoldKanUnderlyingEquivalence :
    ForgetEnrichment QuotientDGChain OriginalCoefficientDGCategory ≌
      ForgetEnrichment OriginalCoefficientDGSimp
        OriginalCoefficientDGSimplicialModuleCategory :=
  (TransportEnrichment.ofOrdinaryEnrichedCategoryEquiv
      (ForgetEnrichment QuotientDGChain OriginalCoefficientDGCategory)
      quotientModuleDoldKanEquivalence.inverse).symm.trans
    (TransportEnrichment.forgetEnrichmentEquiv
      quotientModuleDoldKanEquivalence.inverse
      OriginalCoefficientDGCategory
      (fun T ↦ quotientDoldKanInverseUnitHomEquiv T)
      (fun T f ↦ quotientDoldKanInverseUnitHomEquiv_apply T f))

/-- The opposite bounded-complex category transported to the Dold--Kan simplicial-module
underlying category. -/
noncomputable def originalCoefficientDGToSimplicialModuleUnderlying :
    ComplexCategoryᵒᵖ ⥤
      ForgetEnrichment OriginalCoefficientDGSimp
        OriginalCoefficientDGSimplicialModuleCategory :=
  originalCoefficientDGChainOrdinaryFunctor ⋙
    originalCoefficientDGDoldKanUnderlyingEquivalence.functor

/-- Restore geometric arrow orientation in the ordinary category underlying the Dold--Kan
simplicial-module enrichment. -/
noncomputable def originalCoefficientDGSimplicialModuleOrdinaryFunctor :
    ComplexCategory ⥤
      ForgetEnrichment OriginalCoefficientDGSimp
        OriginalCoefficientDGSimplicialModuleCategoryOp :=
  (opOpEquivalence ComplexCategory).inverse ⋙
    originalCoefficientDGToSimplicialModuleUnderlying.op ⋙
    (forgetEnrichmentOppositeEquivalence
      OriginalCoefficientDGSimp
      OriginalCoefficientDGSimplicialModuleCategory).inverse

/-- Transporting enrichment along the module-forgetful lax monoidal functor induces a
canonical functor on underlying ordinary categories. -/
noncomputable def originalCoefficientDGForgetModuleOrdinaryFunctor :
    ForgetEnrichment OriginalCoefficientDGSimp
        OriginalCoefficientDGSimplicialModuleCategoryOp ⥤
      OriginalCoefficientDGSimplicialCategory where
  obj X := ForgetEnrichment.of SSet X
  map f := ForgetEnrichment.homOf SSet
    (Functor.LaxMonoidal.ε quotientCoefficientSimplicialForget ≫
      quotientCoefficientSimplicialForget.map
        (ForgetEnrichment.homTo OriginalCoefficientDGSimp f))
  map_id X := by
    rw [ForgetEnrichment.homTo_id, ← TransportEnrichment.eId_eq]
    simp [ForgetEnrichment.to]
  map_comp f g := by
    rw [ForgetEnrichment.homTo_comp,
      quotientCoefficientSimplicialForget.map_comp,
      quotientCoefficientSimplicialForget.map_comp,
      ← Category.assoc,
      ← Functor.LaxMonoidal.left_unitality_inv,
      Category.assoc, Category.assoc, Category.assoc, Category.assoc,
      ← Functor.LaxMonoidal.μ_natural_assoc,
      ← TransportEnrichment.eComp_eq,
      ← ForgetEnrichment.homOf_comp,
      leftUnitor_inv_naturality_assoc,
      ← tensorHom_def'_assoc,
      tensorHom_comp_tensorHom_assoc]
    rfl

/-- The ordinary bounded-complex category maps canonically to the original coefficient-changed
DG simplicial category. -/
noncomputable def originalCoefficientDGOrdinaryFunctor :
    ComplexCategory ⥤ OriginalCoefficientDGSimplicialCategory :=
  originalCoefficientDGSimplicialModuleOrdinaryFunctor ⋙
    originalCoefficientDGForgetModuleOrdinaryFunctor

/-- The ordinary functor induces a nerve map even though the source and target Hom universes
differ. Both nerves live in universe one. -/
def originalCoefficientDGOrdinaryNerveMap :
    CategoryTheory.nerve ComplexCategory ⟶
      CategoryTheory.nerve OriginalCoefficientDGSimplicialCategory :=
  { app := fun _ ↦ ↾fun X ↦
      (originalCoefficientDGOrdinaryFunctor.mapComposableArrows _).obj X }

/-- The ordinary bounded-complex nerve maps to the coherent nerve of the coefficient-changed
original DG carrier. -/
def metrizableComplexNerveToOriginalCoefficientDGHomotopyCoherentNerve :
    CategoryTheory.nerve ComplexCategory ⟶
      originalCoefficientDGHomotopyCoherentNerve :=
  originalCoefficientDGOrdinaryNerveMap ≫
    OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve
      OriginalCoefficientDGSimplicialCategory

/-- The ordinary bounded-complex nerve maps to the corrected Drinfeld quotient coherent nerve. -/
def metrizableComplexNerveToCorrectedQuotientDG :
    CategoryTheory.nerve ComplexCategory ⟶ correctedQuotientDGQCat.obj :=
  metrizableComplexNerveToOriginalCoefficientDGHomotopyCoherentNerve ≫
    originalToCorrectedQuotientDGHomotopyCoherentNerve

/-- Bundled quasicategory map from ordinary bounded complexes to the corrected quotient. -/
def metrizableComplexNerveToCorrectedQuotientDGQCatMap :
    (⟨CategoryTheory.nerve ComplexCategory, inferInstance⟩ : SSet.QCat.{1}) ⟶
      correctedQuotientDGQCat :=
  ObjectProperty.homMk metrizableComplexNerveToCorrectedQuotientDG

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
