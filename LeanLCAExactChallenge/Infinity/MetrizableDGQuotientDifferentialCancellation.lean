import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDifferentialEvaluation
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientEraseFactors

/-! # Cancellation and evaluation of the Drinfeld quotient differential -/

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

theorem nil_internalSign
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n)
    (i : Fin ((nil X Y).length + 1)) :
    d.internalSign i = 1 := by
  change Fin 1 at i
  have hi : i = (0 : Fin 1) := Fin.ext (by omega)
  subst i
  simp [DegreeProfile.internalSign, DegreeProfile.prefixTotal]

theorem degreeProfile_nil_eq_nilDegreeProfile
    (X Y : ComplexCategory) (n : ℤ) (d : DegreeProfile (nil X Y) n) :
    d = nilDegreeProfile X Y n := by
  apply DegreeProfile.ext
  funext j
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Fin.ext (by omega)
  subst j
  have hd := d.totalDegree
  simpa [nil, nilDegreeProfile] using hd

theorem internalDifferentialFromSummand_nil
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    internalDifferentialFromSummand d = internalDifferentialLargeMap d 0 := by
  unfold internalDifferentialFromSummand
  rw [Fin.sum_univ_succ]
  rw [nil_internalSign, one_smul]
  have htail : (∑ i : Fin 0,
      d.internalSign i.succ • internalDifferentialLargeMap d i.succ) = 0 := by
    exact Finset.sum_empty
  exact add_eq_left.mpr htail

theorem internalDifferentialFromSummand_nil_comp_internalDifferential
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    internalDifferentialFromSummand d ≫ quotientInternalDifferential X Y (n + 1) = 0 := by
  rw [internalDifferentialFromSummand_nil]
  simp only [internalDifferentialLargeMap, Category.assoc,
    quotientInternalDifferential_inclusion]
  rw [internalDifferentialFromSummand_nil]
  unfold internalDifferentialLargeMap
  rw [← Category.assoc, ← Functor.map_comp]
  have hd : d = nilDegreeProfile X Y n :=
    degreeProfile_nil_eq_nilDegreeProfile X Y n d
  subst d
  have hmap : internalDifferentialTensorMap (nilDegreeProfile X Y n) 0 ≫
      internalDifferentialTensorMap ((nilDegreeProfile X Y n).raise 0) 0 = 0 := by
    simp only [internalDifferentialTensorMap, TensorMapData.ofFn,
      factorDifferential, ↓reduceDIte, eq_mpr_eq_cast, cast_eq,
      Fin.succ_ne_zero, TensorMapData.tensorMap, tensorHom_id]
    rw [← comp_whiskerRight]
    change (((dgHomZModuleCochainComplex
      ((nil X Y).arrowSource 0) ((nil X Y).arrowTarget 0)).d n (n + 1) ≫
        (dgHomZModuleCochainComplex
          ((nil X Y).arrowSource 0) ((nil X Y).arrowTarget 0)).d
            (n + 1) ((n + 1) + 1)) ▷ tensorModuleList []) = 0
    rw [(dgHomZModuleCochainComplex
      ((nil X Y).arrowSource 0) ((nil X Y).arrowTarget 0)).d_comp_d]
    simp
  rw [hmap, Functor.map_zero]
  simp

theorem internalDifferentialFromSummand_nil_comp_contractionDifferential
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    internalDifferentialFromSummand d ≫
        quotientContractionDifferential X Y (n + 1) = 0 := by
  rw [internalDifferentialFromSummand_nil]
  rw [internalDifferentialLargeMap_comp_contractionDifferential]
  simp [contractionDifferentialFromSummand, nil]

theorem quotientTotalDifferential_nil_square
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    (Limits.Sigma.ι
        (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) ⟨nil X Y, d⟩ ≫
      quotientTotalDifferential X Y n) ≫ quotientTotalDifferential X Y (n + 1) = 0 := by
  rw [quotientTotalDifferential_nil_inclusion]
  simp only [quotientTotalDifferential, Preadditive.comp_add]
  rw [internalDifferentialFromSummand_nil_comp_internalDifferential,
    internalDifferentialFromSummand_nil_comp_contractionDifferential, add_zero]

theorem identityCochain_d
    (K : ComplexCategory) :
    ((dgHomZModuleCochainComplex K K).d 0 1).hom (identityCochain K) = 0 := by
  exact CochainComplex.HomComplex.δ_ofHom (F := K.obj) (G := K.obj) (p := 1) (𝟙 K.obj)

set_option maxHeartbeats 400000 in
-- Normalizing the two explicit tensor factors evaluates nested monoidal coherence maps.
theorem singleton_internalDifferentialTensorMap_contractingElement
    (A : CorrectedAcyclicComplexCategory)
    (j : Fin ((singleton A.obj A.obj A).length + 1)) :
    (internalDifferentialTensorMap (singletonContractingDegreeProfile A) j).hom
        (singletonContractingElement A) = 0 := by
  fin_cases j
  · unfold internalDifferentialTensorMap singletonContractingElement
    simp only [Int.reduceNeg, Int.reduceAdd, Nat.reduceAdd, Fin.zero_eta,
      Fin.isValue, singleton_length]
    change ((dgHomZModuleCochainComplex A.obj A.obj).d 0 1).hom
      (identityCochain A.obj) ⊗ₜ[ℤ]
        (identityCochain A.obj ⊗ₜ[ℤ] (1 : ℤ)) = 0
    rw [identityCochain_d]
    simp
  · unfold internalDifferentialTensorMap singletonContractingElement
    simp only [Int.reduceNeg, Int.reduceAdd, Nat.reduceAdd, Fin.mk_one,
      Fin.isValue, singleton_length]
    change identityCochain A.obj ⊗ₜ[ℤ]
      (((dgHomZModuleCochainComplex A.obj A.obj).d 0 1).hom
        (identityCochain A.obj) ⊗ₜ[ℤ] (1 : ℤ)) = 0
    rw [identityCochain_d]
    simp

theorem singleton_internalDifferentialLargeMap_contractingElement
    (A : CorrectedAcyclicComplexCategory)
    (j : Fin ((singleton A.obj A.obj A).length + 1)) :
    (internalDifferentialLargeMap (singletonContractingDegreeProfile A) j).hom
        (ULift.up (singletonContractingElement A)) = 0 := by
  unfold internalDifferentialLargeMap
  change (Limits.Sigma.ι
      (fun s : GradedSummandIndex A.obj A.obj (-1 + 1) ↦ largeSummandModule s)
      ⟨singleton A.obj A.obj A, (singletonContractingDegreeProfile A).raise j⟩).hom
    (((ModuleCat.uliftFunctor.{1} ℤ).map
      (internalDifferentialTensorMap (singletonContractingDegreeProfile A) j)).hom
        (ULift.up (singletonContractingElement A))) = 0
  rw [uliftFunctor_map_up,
    singleton_internalDifferentialTensorMap_contractingElement]
  exact map_zero _

theorem singleton_internalDifferential_contractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (internalDifferentialFromSummand
      (singletonContractingDegreeProfile A)).hom
        (ULift.up (singletonContractingElement A)) = 0 := by
  unfold internalDifferentialFromSummand
  change (∑ i, ((singletonContractingDegreeProfile A).internalSign i •
      internalDifferentialLargeMap (singletonContractingDegreeProfile A) i).hom
        (ULift.up (singletonContractingElement A))) = 0
  apply Finset.sum_eq_zero
  intro j _
  change (singletonContractingDegreeProfile A).internalSign j •
    (internalDifferentialLargeMap (singletonContractingDegreeProfile A) j).hom
      (ULift.up (singletonContractingElement A)) = 0
  rw [singleton_internalDifferentialLargeMap_contractingElement]
  exact zsmul_zero _

theorem contractionTensorMap_singleton
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    contractionTensorMap d i = singletonContractionTensorMap X Y A d i := by
  refine Fin.cases ?_ (fun j ↦ Fin.elim0 j) i
  rw [← cancel_mono
    (singletonContractedSummandIsoAdjacentTarget X Y A d 0).hom]
  rw [contractionTensorMap_singleton_normalized]
  simp [singletonContractionTensorMap, singletonSummandIsoTensorAt,
    Category.assoc]

theorem contractionLargeMap_singleton
    (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    contractionLargeMap d i = singletonContractionLargeMap X Y A d i := by
  unfold contractionLargeMap singletonContractionLargeMap
  rw [contractionTensorMap_singleton]

theorem quotientTotalDifferential_contractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (quotientTotalDifferential A.obj A.obj (-1)).hom
        (quotientContractingElement A) =
      (originalHomInclusion A.obj A.obj 0).hom
        (ULift.up (identityCochain A.obj)) := by
  let i : Fin (singleton A.obj A.obj A).length := ⟨0, by simp⟩
  have h := quotientTotalDifferential_singleton_inclusion A.obj A.obj A
    (singletonContractingDegreeProfile A) i
  have happ := congrArg
    (fun f ↦ f.hom (ULift.up (singletonContractingElement A))) h
  change (quotientTotalDifferential A.obj A.obj (-1)).hom
      (quotientContractingElement A) =
    (internalDifferentialFromSummand (singletonContractingDegreeProfile A)).hom
        (ULift.up (singletonContractingElement A)) +
      (contractionLargeMap (singletonContractingDegreeProfile A) i).hom
        (ULift.up (singletonContractingElement A)) at happ
  rw [singleton_internalDifferential_contractingElement,
    zero_add, contractionLargeMap_singleton,
    singletonContractionLargeMap_contractingElement_eq_originalHomInclusion] at happ
  exact happ

theorem nilProfileInclusion_eq_originalHomInclusion
    (X Y : ComplexCategory) {n : ℤ} (d : DegreeProfile (nil X Y) n) :
    (ModuleCat.uliftFunctor.{1} ℤ).map (nilSummandIsoOriginal X Y d).inv ≫
        Limits.Sigma.ι
          (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s) ⟨nil X Y, d⟩ =
      originalHomInclusion X Y n := by
  have hd := degreeProfile_nil_eq_nilDegreeProfile X Y n d
  subst d
  rfl

theorem originalHomInclusion_comp_totalDifferential
    (X Y : ComplexCategory) (n : ℤ) :
    originalHomInclusion X Y n ≫ quotientTotalDifferential X Y n =
      (ModuleCat.uliftFunctor.{1} ℤ).map
          ((dgHomZModuleCochainComplex X Y).d n (n + 1)) ≫
        originalHomInclusion X Y (n + 1) := by
  unfold originalHomInclusion
  simp only [Category.assoc, quotientTotalDifferential_nil_inclusion]
  rw [internalDifferentialFromSummand_nil]
  unfold internalDifferentialLargeMap
  have hlocal :
      (nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).inv ≫
          internalDifferentialTensorMap (nilDegreeProfile X Y n) 0 =
        (dgHomZModuleCochainComplex X Y).d n (n + 1) ≫
          (nilSummandIsoOriginal X Y ((nilDegreeProfile X Y n).raise 0)).inv := by
    simp only [nilSummandIsoOriginal, eqToIso_refl, Iso.trans_refl,
      internalDifferentialTensorMap, TensorMapData.ofFn, factorDifferential,
      ↓reduceDIte, eq_mpr_eq_cast, cast_eq, Fin.succ_ne_zero,
      TensorMapData.tensorMap, tensorHom_id]
    exact (MonoidalCategory.rightUnitor_inv_naturality
      ((dgHomZModuleCochainComplex X Y).d n (n + 1))).symm
  rw [← Category.assoc, ← Functor.map_comp, hlocal, Functor.map_comp, Category.assoc]
  rw [nilProfileInclusion_eq_originalHomInclusion]
  rfl

theorem quotientTotalDifferential_sq_contractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (quotientTotalDifferential A.obj A.obj 0).hom
      ((quotientTotalDifferential A.obj A.obj (-1)).hom
        (quotientContractingElement A)) = 0 := by
  rw [quotientTotalDifferential_contractingElement]
  have h := originalHomInclusion_comp_totalDifferential A.obj A.obj 0
  have happ := congrArg (fun f ↦ f.hom (ULift.up (identityCochain A.obj))) h
  change (quotientTotalDifferential A.obj A.obj 0).hom
      ((originalHomInclusion A.obj A.obj 0).hom
        (ULift.up (identityCochain A.obj))) =
    (originalHomInclusion A.obj A.obj 1).hom
      (((ModuleCat.uliftFunctor.{1} ℤ).map
        ((dgHomZModuleCochainComplex A.obj A.obj).d 0 1)).hom
          (ULift.up (identityCochain A.obj))) at happ
  rw [uliftFunctor_map_up, identityCochain_d] at happ
  have hz : (originalHomInclusion A.obj A.obj 1).hom
      (ULift.up (0 : (dgHomZModuleCochainComplex A.obj A.obj).X 1)) = 0 :=
    map_zero _
  exact happ.trans hz

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
