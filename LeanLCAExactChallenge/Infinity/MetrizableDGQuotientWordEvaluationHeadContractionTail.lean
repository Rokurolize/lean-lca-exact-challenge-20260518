/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientWordEvaluationHeadContractionComposition

/-! # Tail assembly for positive corrected Drinfeld words

This module adjoins the original positive tail to the explicit head/formal-contraction summand.
The remaining identity factor acts as a left unit at the tail boundary, so the resulting
three-stage quotient composition is exactly the original positive head/tail tensor.
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
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

namespace AnnihilatingEnrichedFunctorData

variable {D : Type*} [EnrichedCategory QuotientDGCochain D]
    (E : AnnihilatingEnrichedFunctorData D)

/-- The raw summand produced by composing the head, formal contraction, and tail. -/
def positiveComposedRawSummand
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) :
    summandModule (positiveRawDegreeProfile d) :=
  (summandCompositionMap
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))
      (DrinfeldWord.tailDegreeProfile d)).hom
    ((summandCompositionMap
        (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
        (singletonContractingDegreeProfile (intermediate 0))).hom
      (positiveHeadSummandElement d x ⊗ₜ[ℤ]
        singletonContractingElement (intermediate 0)) ⊗ₜ[ℤ] t)

/-- The composed source summand transported back to the original word. -/
def positiveComposedSummand
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) : summandModule d :=
  (positiveRawSummandIso d).hom (positiveComposedRawSummand d x t)

/-- The direct tensor presentation of a positive-word summand. -/
def positiveTensorSummand
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) : summandModule d :=
  (eqToHom (summandModule_succ d).symm).hom (x ⊗ₜ[ℤ] t)

/-- The boundary target after the remaining identity is the first tail factor. -/
def positiveHeadContractionTailBoundaryModuleEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionBoundaryModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0)))
        (tailDegreeProfile d) =
      factorModule (tailDegreeProfile d) 0 := by
  change (dgHomZModuleCochainComplex (intermediate 0).obj
      ((tailWord (Y := Y) intermediate).arrowTarget 0)).X
        (((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))).arrowDegree
            (Fin.last (((nil X (intermediate 0).obj).append
              (singleton (intermediate 0).obj (intermediate 0).obj
                (intermediate 0))).length)) +
          (tailDegreeProfile d).arrowDegree 0) =
    (dgHomZModuleCochainComplex (intermediate 0).obj
      ((tailWord (Y := Y) intermediate).arrowTarget 0)).X
        ((tailDegreeProfile d).arrowDegree 0)
  have hindex :
      Fin.last (((nil X (intermediate 0).obj).append
        (singleton (intermediate 0).obj (intermediate 0).obj
          (intermediate 0))).length) =
        appendRightArrowIndex
          (w := nil X (intermediate 0).obj) (0 : Fin 1) := by
    apply Fin.ext
    rfl
  rw [hindex]
  change (dgHomZModuleCochainComplex (intermediate 0).obj
      ((tailWord (Y := Y) intermediate).arrowTarget 0)).X
        (appendArrowDegree
          (nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0))
          (singletonContractingDegreeProfile (intermediate 0))
          (appendRightArrowIndex (w := nil X (intermediate 0).obj) (0 : Fin 1)) +
            (tailDegreeProfile d).arrowDegree 0) = _
  rw [appendArrowDegree_right]
  simp [singletonContractingDegreeProfile]

/-- The actual boundary merge, normalized to the first tail factor. -/
def positiveHeadContractionTailBoundaryMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0)))
        (Fin.last (((nil X (intermediate 0).obj).append
          (singleton (intermediate 0).obj (intermediate 0).obj
            (intermediate 0))).length)) ⊗
      factorModule (tailDegreeProfile d) 0 ⟶
        factorModule (tailDegreeProfile d) 0 :=
  compositionBoundaryMap
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))
      (tailDegreeProfile d) ≫
    eqToHom (positiveHeadContractionTailBoundaryModuleEq d)

/-- The normalized boundary merge is a genuine left unit. -/
theorem positiveHeadContractionTailBoundaryMap_unit
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (λ_ (factorModule (tailDegreeProfile d) 0)).inv ≫
        (positiveHeadContractionLastIdentityMap d ⊗ₘ 𝟙 _) ≫
        positiveHeadContractionTailBoundaryMap d =
      𝟙 (factorModule (tailDegreeProfile d) 0) := by
  unfold positiveHeadContractionLastIdentityMap
    positiveHeadContractionTailBoundaryMap
  convert dgCochainCompTensorOfEq_left_unit_raw
    (intermediate 0).obj (intermediate 0).obj
    ((tailWord (Y := Y) intermediate).arrowTarget 0) rfl
    ((tailDegreeProfile d).arrowDegree 0) using 1 <;> rfl

/-- After the remaining identity is merged, the factor list is the original positive word. -/
theorem positiveHeadContractionTailTargetListEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    compositionLeftPrefix
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) ++
      factorModule (tailDegreeProfile d) 0 ::
        compositionRightSuffix (tailDegreeProfile d) =
      finFamilyList (factorModule d) := by
  rw [compositionLeftPrefix_succ_eq]
  change factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) 0 ::
      factorModule (tailDegreeProfile d) 0 ::
        compositionRightSuffix (tailDegreeProfile d) = _
  rw [headContractionFactor_zero d]
  rw [finFamilyList_eq_ofFn, List.ofFn_succ]
  congr 1
  rw [← finFamilyList_factorModule_eq_first_suffix (tailDegreeProfile d)]
  exact (finFamilyList_factorModule_tail d).symm.trans
    (finFamilyList_eq_ofFn (fun i : Fin (k + 1) ↦ factorModule d i.succ))

@[reassoc]
theorem positiveHeadContractionTailBoundary_tensorMap_post
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (adjacentMergeAfter
        (compositionLeftPrefix
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0))))
        (ys := compositionRightSuffix (tailDegreeProfile d))
        (compositionBoundaryMap
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))
          (tailDegreeProfile d))).tensorMap ≫
      (tensorMapDataReplaceAfter
        (compositionLeftPrefix
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0))))
        (eqToHom (positiveHeadContractionTailBoundaryModuleEq d))
        (compositionRightSuffix (tailDegreeProfile d))).tensorMap =
      (adjacentMergeAfter
        (compositionLeftPrefix
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0))))
        (ys := compositionRightSuffix (tailDegreeProfile d))
        (positiveHeadContractionTailBoundaryMap d)).tensorMap := by
  unfold positiveHeadContractionTailBoundaryMap
  exact adjacentMergeAfter_tensorMap_post
    (compositionLeftPrefix
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0))))
    (compositionBoundaryMap
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))
      (tailDegreeProfile d))
    (eqToHom (positiveHeadContractionTailBoundaryModuleEq d))
    (compositionRightSuffix (tailDegreeProfile d))

@[reassoc]
theorem positiveHeadContractionTailTarget_transport
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (congrArg tensorModuleList
        (finFamilyList_factorModule_append_boundary
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))
          (tailDegreeProfile d)).symm) ≫
        (positiveRawSummandIsoExpanded d).hom =
      (tensorMapDataReplaceAfter
        (compositionLeftPrefix
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0))))
        (eqToHom (positiveHeadContractionTailBoundaryModuleEq d))
        (compositionRightSuffix (tailDegreeProfile d))).tensorMap ≫
      eqToHom (congrArg tensorModuleList
        (positiveHeadContractionTailTargetListEq d)) := by
  rw [tensorMapDataReplaceAfter_eqToHom]
  unfold positiveRawSummandIsoExpanded positiveRawSummandIso
    positiveRawDegreeProfile
  simp only [summandModuleTransportIso, Iso.trans_hom, eqToIso.hom,
    eqToHom_trans]

/-- The original head/tail tensor object in the factor-list coordinates used by the final
head-contraction/tail merge. -/
def positiveHeadContractionTailCoordinateEq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    factorModule d 0 ⊗ summandModule (tailDegreeProfile d) =
      tensorModuleList
        (compositionLeftPrefix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))) ++
          factorModule (tailDegreeProfile d) 0 ::
            compositionRightSuffix (tailDegreeProfile d)) :=
  (summandModule_succ d).symm.trans
    (congrArg tensorModuleList
      (positiveHeadContractionTailTargetListEq d).symm)

/-- The original positive head/tail coordinate transport acts independently on the head and
tail factors. -/
theorem positiveHeadContractionTailCoordinateMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    eqToHom (positiveHeadContractionTailCoordinateEq d) =
      eqToHom (headContractionFactor_zero d).symm ⊗ₘ
        (summandFirstFactorIso (tailDegreeProfile d)).hom := by
  unfold summandFirstFactorIso
  simp only [eqToIso.hom]
  rw [← tensor_eqToHom]

/-- The unprefixed left-unit input that inserts the remaining identity immediately before the
first tail factor. -/
def positiveHeadContractionTailUnitInputMap
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tensorModuleList
        (factorModule (tailDegreeProfile d) 0 ::
          compositionRightSuffix (tailDegreeProfile d)) ⟶
      tensorModuleList
        (factorModule
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0)))
            (Fin.last (((nil X (intermediate 0).obj).append
              (singleton (intermediate 0).obj (intermediate 0).obj
                (intermediate 0))).length)) ::
          factorModule (tailDegreeProfile d) 0 ::
            compositionRightSuffix (tailDegreeProfile d)) :=
  (λ_ (tensorModuleList
      (factorModule (tailDegreeProfile d) 0 ::
        compositionRightSuffix (tailDegreeProfile d)))).inv ≫
    (positiveHeadContractionLastSingletonMap d ⊗ₘ
      𝟙 (tensorModuleList
        (factorModule (tailDegreeProfile d) 0 ::
          compositionRightSuffix (tailDegreeProfile d)))) ≫
    (tensorModuleListAppendIso
      [factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0)))
        (Fin.last (((nil X (intermediate 0).obj).append
          (singleton (intermediate 0).obj (intermediate 0).obj
            (intermediate 0))).length))]
      (factorModule (tailDegreeProfile d) 0 ::
        compositionRightSuffix (tailDegreeProfile d))).hom ≫
    eqToHom (congrArg tensorModuleList
      (appendBoundaryListsEq []
        (factorModule
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))
          (Fin.last (((nil X (intermediate 0).obj).append
            (singleton (intermediate 0).obj (intermediate 0).obj
              (intermediate 0))).length)))
        (factorModule (tailDegreeProfile d) 0)
        (compositionRightSuffix (tailDegreeProfile d))))

/-- A tensor of a composite with a fixed right-hand map factors through the transported
right-hand codomain. -/
theorem tensor_comp_fixed_right
    {A B C D F : ModuleCat.{0} ℤ}
    (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ F) :
    ((f ≫ g) ⊗ₘ h) =
      (f ⊗ₘ h) ≫ (g ⊗ₘ 𝟙 F) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- Tensoring on the left preserves composition. -/
theorem tensor_fixed_left_comp
    (A : ModuleCat.{0} ℤ) {B C F : ModuleCat.{0} ℤ}
    (f : B ⟶ C) (g : C ⟶ F) :
    𝟙 A ⊗ₘ (f ≫ g) =
      (𝟙 A ⊗ₘ f) ≫ (𝟙 A ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp

/-- The boundary-list transport for a nonempty prefix is the corresponding left tensor. -/
theorem appendBoundaryListsEq_eqToHom_cons
    (A : ModuleCat.{0} ℤ) (xs : List (ModuleCat.{0} ℤ))
    (M N : ModuleCat.{0} ℤ) (ys : List (ModuleCat.{0} ℤ)) :
    eqToHom (congrArg tensorModuleList
        (appendBoundaryListsEq (A :: xs) M N ys)) =
      𝟙 A ⊗ₘ eqToHom (congrArg tensorModuleList
        (appendBoundaryListsEq xs M N ys)) := by
  change eqToHom (congrArg tensorModuleList
      (congrArg (A :: ·) (appendBoundaryListsEq xs M N ys))) = _
  exact tensorModuleList_eqToHom_cons A
    (appendBoundaryListsEq xs M N ys)

/-- Inserting a singleton tensor after a one-factor prefix commutes with adjoining an
arbitrary right-hand tensor list. -/
theorem singletonPrefixInsertion
    (A M : ModuleCat.{0} ℤ) (Ns : List (ModuleCat.{0} ℤ))
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ M ⊗ 𝟙_ (ModuleCat.{0} ℤ)) :
    (((ρ_ A).inv ≫ (𝟙 A ⊗ₘ u)) ⊗ₘ
        𝟙 (tensorModuleList Ns)) ≫
      (tensorModuleListAppendIso [A, M] Ns).hom =
    𝟙 A ⊗ₘ
      ((λ_ (tensorModuleList Ns)).inv ≫
        (u ⊗ₘ 𝟙 (tensorModuleList Ns)) ≫
        (tensorModuleListAppendIso [M] Ns).hom) := by
  dsimp only [tensorModuleListAppendIso, tensorModuleList,
    tensorModuleListOver, List.cons_append, List.nil_append]
  rw [tensor_comp_fixed_right]
  rw [tensor_fixed_left_comp, tensor_fixed_left_comp]
  simp only [Iso.trans_hom, MonoidalCategory.tensorIso_hom,
    Iso.refl_hom, Category.assoc]
  rw [tensor_fixed_left_comp]
  monoidal

/-- The singleton-prefix insertion also commutes with the canonical boundary-list transport. -/
theorem singletonPrefixInsertionBoundary
    (A M N : ModuleCat.{0} ℤ) (ys : List (ModuleCat.{0} ℤ))
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ M ⊗ 𝟙_ (ModuleCat.{0} ℤ))
    (q : A ⊗ tensorModuleList [M] = tensorModuleList [A, M]) :
    ((((ρ_ A).inv ≫ (𝟙 A ⊗ₘ u) ≫ eqToHom q) ⊗ₘ
          𝟙 (tensorModuleList (N :: ys))) ≫
        (tensorModuleListAppendIso [A, M] (N :: ys)).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq [A] M N ys))) =
      𝟙 A ⊗ₘ
        ((λ_ (tensorModuleList (N :: ys))).inv ≫
          (u ⊗ₘ 𝟙 (tensorModuleList (N :: ys))) ≫
          (tensorModuleListAppendIso [M] (N :: ys)).hom ≫
          eqToHom (congrArg tensorModuleList
            (appendBoundaryListsEq [] M N ys))) := by
  rw [Subsingleton.elim q rfl]
  simp only [eqToHom_refl, Category.comp_id]
  rw [singletonPrefixInsertion]

/-- The singleton-prefix insertion formula, expressed using the generic left-whiskering
operation and an explicit proof that the prefix is a singleton. -/
theorem singletonPrefixInsertionBoundary_whisker
    (A M N : ModuleCat.{0} ℤ) (ys : List (ModuleCat.{0} ℤ))
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ M ⊗ 𝟙_ (ModuleCat.{0} ℤ))
    (xs : List (ModuleCat.{0} ℤ)) (hxs : xs = [A])
    (p : A ⊗ tensorModuleList (N :: ys) =
      tensorModuleList (xs ++ N :: ys))
    (q : A ⊗ tensorModuleList [M] = tensorModuleList (xs ++ [M])) :
    ((((ρ_ A).inv ≫ (𝟙 A ⊗ₘ u) ≫ eqToHom q) ⊗ₘ
          𝟙 (tensorModuleList (N :: ys))) ≫
        (tensorModuleListAppendIso (xs ++ [M]) (N :: ys)).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq xs M N ys))) =
      eqToHom p ≫
        tensorModuleListWhiskerLeft xs
          ((λ_ (tensorModuleList (N :: ys))).inv ≫
            (u ⊗ₘ 𝟙 (tensorModuleList (N :: ys))) ≫
            (tensorModuleListAppendIso [M] (N :: ys)).hom ≫
            eqToHom (congrArg tensorModuleList
              (appendBoundaryListsEq [] M N ys))) := by
  subst xs
  rw [Subsingleton.elim p rfl]
  simp only [eqToHom_refl, Category.id_comp]
  rw [tensorModuleListWhiskerLeft_singleton]
  exact singletonPrefixInsertionBoundary A M N ys u q

/-- Before the actual adjacent merge, the direct head/contraction presentation is the standard
left-unit input whiskered by the ordinary head prefix. -/
@[reassoc]
theorem positiveHeadContractionTailSource_decompose
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (headContractionDirectMap d ⊗ₘ
        𝟙 (summandModule (tailDegreeProfile d))) ≫
      ((summandLastFactorIso
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))).hom ⊗ₘ
        (summandFirstFactorIso (tailDegreeProfile d)).hom) ≫
      (tensorModuleListAppendIso
        (compositionLeftPrefix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))) ++
          [factorModule
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0)))
            (Fin.last (((nil X (intermediate 0).obj).append
              (singleton (intermediate 0).obj (intermediate 0).obj
                (intermediate 0))).length))])
        (factorModule (tailDegreeProfile d) 0 ::
          compositionRightSuffix (tailDegreeProfile d))).hom ≫
      eqToHom (congrArg tensorModuleList
        (appendBoundaryListsEq
          (compositionLeftPrefix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))))
          (factorModule
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0)))
            (Fin.last (((nil X (intermediate 0).obj).append
              (singleton (intermediate 0).obj (intermediate 0).obj
                (intermediate 0))).length)))
          (factorModule (tailDegreeProfile d) 0)
          (compositionRightSuffix (tailDegreeProfile d)))) =
      eqToHom (positiveHeadContractionTailCoordinateEq d) ≫
        tensorModuleListWhiskerLeft
          (compositionLeftPrefix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))))
          (positiveHeadContractionTailUnitInputMap d) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  simp only [Category.id_comp]
  rw [headContractionDirectMap_comp_lastFactorIso_factored]
  rw [tensor_comp_fixed_right]
  rw [← positiveHeadContractionTailCoordinateMap]
  simp only [Category.assoc]
  rw [cancel_epi]
  rw [Subsingleton.elim (headContractionLastCoordinateEq d) rfl]
  unfold positiveHeadContractionTailUnitInputMap
  have h := singletonPrefixInsertionBoundary_whisker
    (factorModule
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0))) 0)
    (factorModule
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0)))
      (Fin.last (((nil X (intermediate 0).obj).append
        (singleton (intermediate 0).obj (intermediate 0).obj
          (intermediate 0))).length)))
    (factorModule (tailDegreeProfile d) 0)
    (compositionRightSuffix (tailDegreeProfile d))
    (positiveHeadContractionLastSingletonMap d)
    (compositionLeftPrefix
      ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
        (singletonContractingDegreeProfile (intermediate 0))))
    (headContractionLeftPrefix d)
    (rfl : factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) 0 ⊗
          tensorModuleList
            (factorModule (tailDegreeProfile d) 0 ::
              compositionRightSuffix (tailDegreeProfile d)) =
      tensorModuleList
        (compositionLeftPrefix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))) ++
          factorModule (tailDegreeProfile d) 0 ::
            compositionRightSuffix (tailDegreeProfile d)))
    (rfl : factorModule
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))) 0 ⊗
          tensorModuleList
            [factorModule
              ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
                (singletonContractingDegreeProfile (intermediate 0)))
              (Fin.last (((nil X (intermediate 0).obj).append
                (singleton (intermediate 0).obj (intermediate 0).obj
                  (intermediate 0))).length))] =
      tensorModuleList
        (compositionLeftPrefix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))) ++
          [factorModule
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0)))
            (Fin.last (((nil X (intermediate 0).obj).append
              (singleton (intermediate 0).obj (intermediate 0).obj
                (intermediate 0))).length))]))
  dsimp only [tensorModuleList, tensorModuleListOver] at h ⊢
  simpa only [eqToHom_refl, Category.id_comp] using h

/-- A left-unit adjacent merge remains an identity after adjoining an arbitrary prefix. -/
theorem adjacentMergeAfter_tensorMap_eq_whiskerLeft
    (xs ys : List (ModuleCat.{0} ℤ)) {M N P : ModuleCat.{0} ℤ}
    (f : M ⊗ N ⟶ P) :
    (adjacentMergeAfter xs (ys := ys) f).tensorMap =
      tensorModuleListWhiskerLeft xs
        (AdjacentMergeData.head (Ms := ys) f).tensorMap := by
  rw [adjacentMergeAfter_eq_prefix_head]
  exact AdjacentMergeData.prefix_tensorMap (AdjacentMergeData.head f) xs

/-- A left-unit adjacent merge remains an identity after adjoining an arbitrary prefix. -/
theorem adjacentMergeAfter_tensorMap_left_unit_prefix
    (xs ys : List (ModuleCat.{0} ℤ)) {M N : ModuleCat.{0} ℤ}
    (u : 𝟙_ (ModuleCat.{0} ℤ) ⟶ M) (f : M ⊗ N ⟶ N)
    (hunit : (λ_ N).inv ≫ (u ⊗ₘ 𝟙 N) ≫ f = 𝟙 N) :
    tensorModuleListWhiskerLeft xs
      ((λ_ (tensorModuleList (N :: ys))).inv ≫
        ((u ≫ (ρ_ M).inv) ⊗ₘ 𝟙 (tensorModuleList (N :: ys))) ≫
        (tensorModuleListAppendIso [M] (N :: ys)).hom ≫
        eqToHom (congrArg tensorModuleList
          (appendBoundaryListsEq [] M N ys)) ≫
        (AdjacentMergeData.head (Ms := ys) f).tensorMap) =
      𝟙 (tensorModuleList (xs ++ N :: ys)) := by
  have hunit' :
      (λ_ (tensorModuleList (N :: ys))).inv ≫
          ((u ≫ (ρ_ M).inv) ⊗ₘ 𝟙 (tensorModuleList (N :: ys))) ≫
          (tensorModuleListAppendIso [M] (N :: ys)).hom ≫
          eqToHom (congrArg tensorModuleList
            (appendBoundaryListsEq [] M N ys)) ≫
          (AdjacentMergeData.head (Ms := ys) f).tensorMap =
        𝟙 (tensorModuleList (N :: ys)) := by
    simpa only [adjacentMergeAfter] using
      adjacentMergeAfter_tensorMap_left_unit ys u f hunit
  rw [hunit']
  simp [tensorModuleListWhiskerLeft]

/-- The standard positive-tail unit input followed by its boundary merge is the identity after
whiskering by the head prefix. -/
theorem positiveHeadContractionTailWhiskeredBoundary_identity
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    tensorModuleListWhiskerLeft
        (compositionLeftPrefix
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0))))
        (positiveHeadContractionTailUnitInputMap d ≫
          (AdjacentMergeData.head
            (Ms := compositionRightSuffix (tailDegreeProfile d))
            (positiveHeadContractionTailBoundaryMap d)).tensorMap) =
      𝟙 (tensorModuleList
        (compositionLeftPrefix
            ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
              (singletonContractingDegreeProfile (intermediate 0))) ++
          factorModule (tailDegreeProfile d) 0 ::
            compositionRightSuffix (tailDegreeProfile d))) := by
  unfold positiveHeadContractionTailUnitInputMap
    positiveHeadContractionLastSingletonMap
  simpa only [Category.assoc] using
    adjacentMergeAfter_tensorMap_left_unit_prefix
      (compositionLeftPrefix
        ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
          (singletonContractingDegreeProfile (intermediate 0))))
      (compositionRightSuffix (tailDegreeProfile d))
      (positiveHeadContractionLastIdentityMap d)
      (positiveHeadContractionTailBoundaryMap d)
      (positiveHeadContractionTailBoundaryMap_unit d)

set_option maxHeartbeats 4000000 in
-- Normalizing the dependent tensor transports in the map-level comparison is expensive.
/-- Composing the explicit head/contraction summand with the tail is the standard positive-word
coordinate map. -/
theorem positiveHeadContractionTailMap_eq
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n) :
    (headContractionDirectMap d ⊗ₘ 𝟙 (summandModule (tailDegreeProfile d))) ≫
        summandCompositionMap
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))
          (tailDegreeProfile d) ≫
        (positiveRawSummandIso d).hom =
      eqToHom (summandModule_succ d).symm := by
  change (headContractionDirectMap d ⊗ₘ
      𝟙 (summandModule (tailDegreeProfile d))) ≫
        summandCompositionMap
          ((nilDegreeProfile X (intermediate 0).obj (d.arrowDegree 0)).append
            (singletonContractingDegreeProfile (intermediate 0)))
          (tailDegreeProfile d) ≫
        (positiveRawSummandIsoExpanded d).hom = _
  apply (cancel_mono (eqToHom (summandModule_succ d))).mp
  simp only [Category.assoc, eqToHom_trans]
  rw [summandCompositionMap_eq_boundary_decomposition]
  simp only [Category.assoc]
  rw [positiveHeadContractionTailSource_decompose_assoc]
  rw [positiveHeadContractionTailTarget_transport_assoc]
  rw [positiveHeadContractionTailBoundary_tensorMap_post_assoc]
  rw [adjacentMergeAfter_tensorMap_eq_whiskerLeft]
  slice_lhs 2 3 =>
    rw [← tensorModuleListWhiskerLeft_comp]
  rw [positiveHeadContractionTailWhiskeredBoundary_identity]
  simp only [Category.id_comp, eqToHom_trans]

set_option maxHeartbeats 4000000 in
-- Applying the preceding transported map equality to a pure tensor has the same elaboration cost.
/-- The explicit head/contraction/tail composition is the original positive-word tensor. -/
theorem positiveComposedSummand_eq_positiveTensorSummand
    {X Y : ComplexCategory} {k : ℕ}
    {intermediate : Fin (k + 1) → CorrectedAcyclicComplexCategory}
    {n : ℤ}
    (d : DegreeProfile
      ({ length := k + 1, intermediate := intermediate } : DrinfeldWord X Y) n)
    (x : factorModule d 0)
    (t : summandModule (tailDegreeProfile d)) :
    positiveComposedSummand d x t = positiveTensorSummand d x t := by
  unfold positiveComposedSummand positiveComposedRawSummand positiveTensorSummand
  rw [headContractionComposition_apply]
  have h := ConcreteCategory.congr_hom
    (positiveHeadContractionTailMap_eq d) (x ⊗ₜ[ℤ] t)
  simp only [ModuleCat.comp_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul,
    CategoryTheory.id_apply] at h
  have hdirect : (headContractionDirectMap d).hom x =
      headContractionDirectSummand d x := by
    unfold headContractionDirectMap headContractionDirectSummand
    simp only [ModuleCat.comp_apply,
      ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul]
    rw [headContractionIdentityTailMap_apply_one]
  rw [hdirect] at h
  exact h

end AnnihilatingEnrichedFunctorData
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
