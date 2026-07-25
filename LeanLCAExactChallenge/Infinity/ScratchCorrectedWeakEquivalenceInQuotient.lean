/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDifferentialCancellation
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDGBundle
import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientInclusionFunctor
import LeanLCAExactChallenge.Infinity.MetrizableDGStableConstructions
import LeanLCAExactChallenge.Infinity.Relative
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

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

/-- The corrected acyclic cone associated to a raw corrected weak equivalence. -/
def correctedWeakEquivalenceCone {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) : CorrectedAcyclicComplexCategory :=
  ⟨dgMappingConeObject f, hf⟩

/-- The zero-word quotient element represented by an ordinary bounded morphism. -/
def quotientOriginalMorphismElement {K L : ComplexCategory} (f : K ⟶ L) :
    quotientGradedModule K L 0 :=
  (originalHomInclusion K L 0).hom
    (ULift.up (CochainComplex.HomComplex.Cochain.ofHom f.hom))

/-- The zero-word quotient element represented by an arbitrary Hom cochain. -/
def quotientOriginalCochainElement {K L : ComplexCategory} {n : ℤ}
    (x : (dgHomZModuleCochainComplex K L).X n) :
    quotientGradedModule K L n :=
  (originalHomInclusion K L n).hom (ULift.up x)

/-- The cone inclusion in the corrected quotient. -/
def quotientConeInr {K L : ComplexCategory} (f : K ⟶ L) :
    quotientGradedModule L (dgMappingConeObject f) 0 :=
  quotientOriginalMorphismElement (dgMappingConeInr f)

/-- The degree-minus-one cone inclusion in the corrected quotient. -/
def quotientConeInl {K L : ComplexCategory} (f : K ⟶ L) :
    quotientGradedModule K (dgMappingConeObject f) (-1) :=
  quotientOriginalCochainElement (dgMappingConeInl f)

/-- The degree-one first projection from the mapping cone. -/
def quotientConeFst {K L : ComplexCategory} (f : K ⟶ L) :
    quotientGradedModule (dgMappingConeObject f) K 1 :=
  quotientOriginalCochainElement
    (CochainComplex.mappingCone.fst
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1

/-- The degree-zero second projection from the mapping cone. -/
def quotientConeSnd {K L : ComplexCategory} (f : K ⟶ L) :
    quotientGradedModule (dgMappingConeObject f) L 0 :=
  quotientOriginalCochainElement
    (CochainComplex.mappingCone.snd
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))

/-- The formal contraction of the corrected acyclic cone. -/
def quotientConeContraction {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) :
    quotientGradedModule (dgMappingConeObject f) (dgMappingConeObject f) (-1) :=
  quotientContractingElement (correctedWeakEquivalenceCone f hf)

/-- First compose two corrected quotient elements. -/
def quotientCompose {X Y Z : ComplexCategory} {n m : ℤ}
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    quotientGradedModule X Z (n + m) :=
  quotientCompositionMap X Y Z n m x y

/-- The target inclusion followed by the cone contraction. -/
def quotientConeInrContraction {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) :
    quotientGradedModule L (dgMappingConeObject f) (-1) :=
  quotientCompose (quotientConeInr f) (quotientConeContraction f hf)

/-- The source cone inclusion followed by the cone contraction. -/
def quotientConeInlContraction {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) :
    quotientGradedModule K (dgMappingConeObject f) (-2) :=
  quotientCompose (quotientConeInl f) (quotientConeContraction f hf)

/-- The inverse candidate supplied by the contraction of the mapping cone. -/
def correctedWeakEquivalenceInverseElement {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) : quotientGradedModule L K 0 :=
  quotientCompose
    (quotientCompose (quotientConeInr f) (quotientConeContraction f hf))
    (quotientConeFst f)

/-- The inverse candidate displayed as its raw threefold composite transported to degree zero. -/
theorem correctedWeakEquivalenceInverseElement_eq_cast
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (eqToHom (congrArg (quotientGradedModule L K)
      (show ((0 : ℤ) + -1) + 1 = 0 by omega))).hom
      (quotientCompose
        (quotientCompose (quotientConeInr f) (quotientConeContraction f hf))
        (quotientConeFst f)) =
      correctedWeakEquivalenceInverseElement f hf := by
  unfold correctedWeakEquivalenceInverseElement
  rfl

/-- The inverse candidate displayed from the already bundled `inr ≫ H` factor. -/
theorem correctedWeakEquivalenceInverseElement_eq_cast_normalized
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f)
    (h : (-1 : ℤ) + 1 = 0) :
    (eqToHom (congrArg (quotientGradedModule L K) h)).hom
      (quotientCompose (quotientConeInrContraction f hf) (quotientConeFst f)) =
      correctedWeakEquivalenceInverseElement f hf := by
  unfold correctedWeakEquivalenceInverseElement quotientConeInrContraction quotientCompose
  rfl

/-- The left inverse homotopy candidate. -/
def correctedWeakEquivalenceLeftHomotopyElement {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) : quotientGradedModule K K (-1) :=
  quotientCompose
    (quotientCompose (quotientConeInl f) (quotientConeContraction f hf))
    (quotientConeFst f)

/-- The right inverse homotopy candidate. -/
def correctedWeakEquivalenceRightHomotopyElement {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) : quotientGradedModule L L (-1) :=
  - (eqToHom (congrArg (quotientGradedModule L L)
      (show (-1 : ℤ) + 0 = -1 by omega))).hom
      (quotientCompose (quotientConeInrContraction f hf) (quotientConeSnd f))

/-- Elementwise Leibniz identity for the corrected quotient composition. -/
theorem quotientCompositionMap_d
    (X Y Z : ComplexCategory) (n m : ℤ)
    (x : quotientGradedModule X Y n)
    (y : quotientGradedModule Y Z m) :
    (quotientTotalDifferential X Z (n + m)).hom
        (quotientCompositionMap X Y Z n m x y) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (rightLeibnizDegreeEq n m))).hom
          (quotientCompositionMap X Y Z n (m + 1) x
            ((quotientTotalDifferential Y Z m).hom y)) +
        m.negOnePow •
          (eqToHom (congrArg (quotientGradedModule X Z)
            (leftLeibnizDegreeEq n m))).hom
            (quotientCompositionMap X Y Z (n + 1) m
              ((quotientTotalDifferential X Y n).hom x) y) := by
  have h := ConcreteCategory.congr_hom
    (quotientCompositionTensorMap_leibniz X Y Z n m)
    (ULift.up x ⊗ₜ[QuotientCoefficientRing] ULift.up y)
  unfold quotientCoefficientDifferential at h
  rw [quotientCompositionTensorMap_comp_changeScalars_tmul] at h
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at h
  rw [quotientCompositionTensorMap_changeScalars_right_cast_tmul] at h <;> try omega
  rw [Units.smul_def] at h
  simp only [ModuleCat.hom_smul, LinearMap.smul_apply] at h
  rw [quotientCompositionTensorMap_changeScalars_left_cast_tmul] at h <;> try omega
  have hdown := congrArg ULift.down h
  change (quotientTotalDifferential X Z (n + m)).hom
      (quotientCompositionMap X Y Z n m x y) =
    (eqToHom (congrArg (quotientGradedModule X Z)
      (rightLeibnizDegreeEq n m))).hom
        (quotientCompositionMap X Y Z n (m + 1) x
          ((quotientTotalDifferential Y Z m).hom y)) +
      m.negOnePow •
        (eqToHom (congrArg (quotientGradedModule X Z)
          (leftLeibnizDegreeEq n m))).hom
          (quotientCompositionMap X Y Z (n + 1) m
            ((quotientTotalDifferential X Y n).hom x) y) at hdown
  exact hdown

/-- Composition of two zero-word elements is the zero-word image of ordinary DG composition. -/
theorem quotientOriginalCochainElement_comp
    (K L M : ComplexCategory) {p q : ℤ}
    (y : (dgHomZModuleCochainComplex L M).X p)
    (x : (dgHomZModuleCochainComplex K L).X q) :
    (eqToHom (congrArg (quotientGradedModule K M) (Int.add_comm q p))).hom
        (quotientCompositionMap K L M q p
          (quotientOriginalCochainElement x)
          (quotientOriginalCochainElement y)) =
      quotientOriginalCochainElement
        ((dgCochainCompTensorReversed K L M rfl).hom (y ⊗ₜ[ℤ] x)) := by
  have hmap := ConcreteCategory.congr_hom
    (originalDGCompositionComponent_map K L M
      (show p + q = p + q by rfl))
    (ULift.up (ULift.up y) ⊗ₜ[QuotientCoefficientRing]
      ULift.up (ULift.up x))
  rw [originalDGCompositionThenInclusion_tmul,
    quotientDGCompositionComponent_after_original_tmul] at hmap
  have hdown := congrArg ULift.down hmap
  change quotientOriginalCochainElement
      ((dgCochainCompTensorReversed K L M rfl).hom (y ⊗ₜ[ℤ] x)) =
    (eqToHom (congrArg (quotientGradedModule K M) (Int.add_comm q p))).hom
      (quotientCompositionMap K L M q p
        (quotientOriginalCochainElement x)
        (quotientOriginalCochainElement y)) at hdown
  exact hdown.symm

/-- The zero-word inclusion commutes with the quotient differential. -/
theorem quotientOriginalCochainElement_d {K L : ComplexCategory} {n : ℤ}
    (x : (dgHomZModuleCochainComplex K L).X n) :
    (quotientTotalDifferential K L n).hom
        (quotientOriginalCochainElement x) =
      quotientOriginalCochainElement
        (((dgHomZModuleCochainComplex K L).d n (n + 1)).hom x) := by
  have h := ConcreteCategory.congr_hom
    (originalHomInclusion_comp_totalDifferential K L n) (ULift.up x)
  change (quotientTotalDifferential K L n).hom
      ((originalHomInclusion K L n).hom (ULift.up x)) =
    (originalHomInclusion K L (n + 1)).hom
      (ULift.up (((dgHomZModuleCochainComplex K L).d n (n + 1)).hom x))
  simpa only [ModuleCat.comp_apply, uliftFunctor_map_up] using h

/-- The zero-word inclusion preserves zero. -/
theorem quotientOriginalCochainElement_zero
    (K L : ComplexCategory) (n : ℤ) :
    quotientOriginalCochainElement
      (0 : (dgHomZModuleCochainComplex K L).X n) = 0 := by
  unfold quotientOriginalCochainElement
  change (originalHomInclusion K L n).hom (0 :
    (ModuleCat.uliftFunctor.{1} ℤ).obj ((dgHomZModuleCochainComplex K L).X n)) = 0
  exact map_zero (originalHomInclusion K L n).hom

/-- The zero-word inclusion preserves negation. -/
theorem quotientOriginalCochainElement_neg {K L : ComplexCategory} {n : ℤ}
    (x : (dgHomZModuleCochainComplex K L).X n) :
    quotientOriginalCochainElement (-x) = - quotientOriginalCochainElement x := by
  unfold quotientOriginalCochainElement
  change (originalHomInclusion K L n).hom (-(ULift.up x)) = _
  exact map_neg (originalHomInclusion K L n).hom (ULift.up x)

/-- The quotient cone contraction has boundary the quotient identity. -/
theorem quotientConeContraction_d {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential (dgMappingConeObject f) (dgMappingConeObject f) (-1)).hom
        (quotientConeContraction f hf) =
      quotientIdentityElement (dgMappingConeObject f) := by
  exact quotientTotalDifferential_contractingElement
    (correctedWeakEquivalenceCone f hf)

/-- The cone contraction boundary, displayed as a transported degree-zero identity. -/
theorem quotientConeContraction_d_cast {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f)
    (h0 : (0 : ℤ) = -1 + 1) :
    (quotientTotalDifferential (dgMappingConeObject f) (dgMappingConeObject f) (-1)).hom
        (quotientConeContraction f hf) =
      (eqToHom (congrArg
        (quotientGradedModule (dgMappingConeObject f) (dgMappingConeObject f)) h0)).hom
        (quotientIdentityElement (dgMappingConeObject f)) := by
  rw [quotientConeContraction_d]
  have hh : h0 = rfl := Subsingleton.elim _ _
  cases hh
  rfl

/-- Right composition with an identity transported to an equal degree is still the identity. -/
theorem quotientCompositionMap_right_unit_transport
    (X Y : ComplexCategory) (n m t : ℤ)
    (h0m : 0 = m) (hout : n + m = t) (hnt : n = t)
    (x : quotientGradedModule X Y n) :
    (eqToHom (congrArg (quotientGradedModule X Y) hout)).hom
        (quotientCompositionMap X Y Y n m x
          ((eqToHom (congrArg (quotientGradedModule Y Y) h0m)).hom
            (quotientIdentityElement Y))) =
      (eqToHom (congrArg (quotientGradedModule X Y) hnt)).hom x := by
  subst m
  subst t
  have hhout : hout = Int.add_zero n := Subsingleton.elim _ _
  cases hhout
  simpa only [eqToHom_refl, CategoryTheory.id_apply] using
    quotientCompositionMap_right_unit X Y n x

/-- Two transports along equalities with the same endpoints agree on every element. -/
theorem quotientGradedModule_cast_eq
    (X Y : ComplexCategory) {p q : ℤ} (h₁ h₂ : p = q)
    (x : quotientGradedModule X Y p) :
    (eqToHom (congrArg (quotientGradedModule X Y) h₁)).hom x =
      (eqToHom (congrArg (quotientGradedModule X Y) h₂)).hom x := by
  have h : h₁ = h₂ := Subsingleton.elim _ _
  cases h
  rfl

/-- Transporting the degree of the left input commutes with quotient composition. -/
theorem quotientCompositionMap_cast_left_transport
    (X Y Z : ComplexCategory) {n n' m : ℤ} (h : n = n')
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    quotientCompositionMap X Y Z n' m
        ((eqToHom (congrArg (quotientGradedModule X Y) h)).hom x) y =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (congrArg (fun k ↦ k + m) h))).hom
        (quotientCompositionMap X Y Z n m x y) := by
  subst n'
  rfl

/-- Transporting the degree of the right input commutes with quotient composition. -/
theorem quotientCompositionMap_cast_right_transport
    (X Y Z : ComplexCategory) {n m m' : ℤ} (h : m = m')
    (x : quotientGradedModule X Y n) (y : quotientGradedModule Y Z m) :
    quotientCompositionMap X Y Z n m' x
        ((eqToHom (congrArg (quotientGradedModule Y Z) h)).hom y) =
      (eqToHom (congrArg (quotientGradedModule X Z)
        (congrArg (fun k ↦ n + k) h))).hom
        (quotientCompositionMap X Y Z n m x y) := by
  subst m'
  rfl

/-- The quotient differential commutes with transport of the input degree. -/
theorem quotientTotalDifferential_cast
    (X Y : ComplexCategory) {n n' : ℤ} (h : n = n')
    (x : quotientGradedModule X Y n) :
    (quotientTotalDifferential X Y n').hom
        ((eqToHom (congrArg (quotientGradedModule X Y) h)).hom x) =
      (eqToHom (congrArg (quotientGradedModule X Y)
        (congrArg (fun k ↦ k + 1) h))).hom
        ((quotientTotalDifferential X Y n).hom x) := by
  subst n'
  rfl

/-- A transported composition with a zero left factor is zero. -/
theorem quotientCompositionMap_zero_left_transport
    (X Y Z : ComplexCategory) (n m t : ℤ) (hout : n + m = t)
    (y : quotientGradedModule Y Z m) :
    (eqToHom (congrArg (quotientGradedModule X Z) hout)).hom
        (quotientCompositionMap X Y Z n m 0 y) = 0 := by
  rw [map_zero]
  exact map_zero _

/-- A transported composition with a zero right factor is zero. -/
theorem quotientCompositionMap_zero_right_transport
    (X Y Z : ComplexCategory) (n m t : ℤ) (hout : n + m = t)
    (x : quotientGradedModule X Y n) :
    (eqToHom (congrArg (quotientGradedModule X Z) hout)).hom
        (quotientCompositionMap X Y Z n m x 0) = 0 := by
  rw [map_zero]
  exact map_zero _

/-- The quotient image of the degree-zero cone inclusion is closed. -/
theorem quotientConeInr_d {K L : ComplexCategory} (f : K ⟶ L) :
    (quotientTotalDifferential L (dgMappingConeObject f) 0).hom
        (quotientConeInr f) = 0 := by
  change (quotientTotalDifferential L (dgMappingConeObject f) 0).hom
    (quotientOriginalCochainElement
      (CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeInr f)))) = 0
  rw [quotientOriginalCochainElement_d]
  change quotientOriginalCochainElement
      (CochainComplex.HomComplex.δ 0 1
        (CochainComplex.HomComplex.Cochain.ofHom
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeInr f)))) = 0
  rw [CochainComplex.HomComplex.δ_ofHom]
  exact map_zero _

/-- The quotient image of the cone first projection is closed. -/
theorem quotientConeFst_d {K L : ComplexCategory} (f : K ⟶ L) :
    (quotientTotalDifferential (dgMappingConeObject f) K 1).hom
        (quotientConeFst f) = 0 := by
  change (quotientTotalDifferential (dgMappingConeObject f) K 1).hom
    (quotientOriginalCochainElement
      (CochainComplex.mappingCone.fst
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1) = 0
  rw [quotientOriginalCochainElement_d]
  change quotientOriginalCochainElement
      (CochainComplex.HomComplex.δ
        (F := underlyingComplex (dgMappingConeObject f))
        (G := underlyingComplex K) 1 2
        (CochainComplex.mappingCone.fst
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1) = 0
  rw [CochainComplex.HomComplex.Cocycle.δ_eq_zero]
  exact map_zero _

/-- The cone inclusion followed by the first projection vanishes in the quotient. -/
theorem quotientConeInr_comp_fst {K L : ComplexCategory} (f : K ⟶ L) :
    quotientCompose (quotientConeInr f) (quotientConeFst f) = 0 := by
  let inrC : (dgHomZModuleCochainComplex L (dgMappingConeObject f)).X 0 :=
    CochainComplex.HomComplex.Cochain.ofHom (dgMappingConeInr f).hom
  let fstC : (dgHomZModuleCochainComplex (dgMappingConeObject f) K).X 1 :=
    (CochainComplex.mappingCone.fst
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1
  have hcomp := quotientOriginalCochainElement_comp
    L (dgMappingConeObject f) K fstC inrC
  have hdeg : Int.add_comm (0 : ℤ) 1 = rfl := Subsingleton.elim _ _
  rw [hdeg, eqToHom_refl] at hcomp
  change quotientCompose (quotientConeInr f) (quotientConeFst f) =
    quotientOriginalCochainElement
      ((dgCochainCompTensorReversed L (dgMappingConeObject f) K rfl).hom
        (fstC ⊗ₜ[ℤ] inrC)) at hcomp
  rw [dgCochainCompTensorReversed_tmul] at hcomp
  have hinr : (dgMappingConeInr f).hom =
      CochainComplex.mappingCone.inr f.hom := by
    simpa using boundedInclusion_map_dgMappingConeInr f
  have hz : inrC.comp fstC rfl = 0 := by
    dsimp [inrC, fstC]
    rw [hinr]
    exact CochainComplex.mappingCone.inr_fst f.hom
  rw [hz] at hcomp
  exact hcomp.trans (quotientOriginalCochainElement_zero L K 1)

/-- The cone inclusion and first projection compose to the source identity. -/
theorem quotientConeInl_comp_fst {K L : ComplexCategory} (f : K ⟶ L) :
    quotientCompose (quotientConeInl f) (quotientConeFst f) =
      quotientIdentityElement K := by
  let inlC : (dgHomZModuleCochainComplex K (dgMappingConeObject f)).X (-1) :=
    dgMappingConeInl f
  let fstC : (dgHomZModuleCochainComplex (dgMappingConeObject f) K).X 1 :=
    (CochainComplex.mappingCone.fst
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1
  have hcomp := quotientOriginalCochainElement_comp
    K (dgMappingConeObject f) K fstC inlC
  have hdeg : Int.add_comm (-1 : ℤ) 1 = rfl := Subsingleton.elim _ _
  rw [hdeg, eqToHom_refl] at hcomp
  change quotientCompose (quotientConeInl f) (quotientConeFst f) =
    quotientOriginalCochainElement
      ((dgCochainCompTensorReversed K (dgMappingConeObject f) K rfl).hom
        (fstC ⊗ₜ[ℤ] inlC)) at hcomp
  rw [dgCochainCompTensorReversed_tmul] at hcomp
  have hid : inlC.comp fstC rfl = identityCochain K := by
    dsimp [inlC, fstC, identityCochain]
    exact CochainComplex.mappingCone.inl_fst
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)
  rw [hid] at hcomp
  exact hcomp

/-- The target inclusion and second projection compose to the target identity. -/
theorem quotientConeInr_comp_snd {K L : ComplexCategory} (f : K ⟶ L) :
    quotientCompose (quotientConeInr f) (quotientConeSnd f) =
      quotientIdentityElement L := by
  let inrC : (dgHomZModuleCochainComplex L (dgMappingConeObject f)).X 0 :=
    CochainComplex.HomComplex.Cochain.ofHom (dgMappingConeInr f).hom
  let sndC : (dgHomZModuleCochainComplex (dgMappingConeObject f) L).X 0 :=
    CochainComplex.mappingCone.snd
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)
  have hcomp := quotientOriginalCochainElement_comp
    L (dgMappingConeObject f) L sndC inrC
  have hdeg : Int.add_comm (0 : ℤ) 0 = rfl := Subsingleton.elim _ _
  rw [hdeg, eqToHom_refl] at hcomp
  change quotientCompose (quotientConeInr f) (quotientConeSnd f) =
    quotientOriginalCochainElement
      ((dgCochainCompTensorReversed L (dgMappingConeObject f) L rfl).hom
        (sndC ⊗ₜ[ℤ] inrC)) at hcomp
  rw [dgCochainCompTensorReversed_tmul] at hcomp
  have hinr : (dgMappingConeInr f).hom =
      CochainComplex.mappingCone.inr f.hom := by
    simpa using boundedInclusion_map_dgMappingConeInr f
  have hid : inrC.comp sndC rfl = identityCochain L := by
    dsimp [inrC, sndC, identityCochain]
    rw [hinr]
    exact CochainComplex.mappingCone.inr_snd f.hom
  rw [hid] at hcomp
  exact hcomp

/-- The boundary of the quotient cone inclusion is the ordinary cone-triangle composite. -/
theorem quotientConeInl_d {K L : ComplexCategory} (f : K ⟶ L) :
    (quotientTotalDifferential K (dgMappingConeObject f) (-1)).hom
        (quotientConeInl f) =
      (eqToHom (congrArg (quotientGradedModule K (dgMappingConeObject f))
        (show (0 : ℤ) + 0 = -1 + 1 by omega))).hom
        (quotientCompose (quotientOriginalMorphismElement f) (quotientConeInr f)) := by
  change (quotientTotalDifferential K (dgMappingConeObject f) (-1)).hom
    (quotientOriginalCochainElement (dgMappingConeInl f)) = _
  rw [quotientOriginalCochainElement_d]
  change quotientOriginalCochainElement
      (CochainComplex.HomComplex.δ
        (F := underlyingComplex K)
        (G := underlyingComplex (dgMappingConeObject f)) (-1) 0
        (dgMappingConeInl f)) = _
  rw [dgMappingConeInl_delta]
  have hcomp := quotientOriginalCochainElement_comp K L (dgMappingConeObject f)
    (CochainComplex.HomComplex.Cochain.ofHom
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeInr f)))
    (CochainComplex.HomComplex.Cochain.ofHom
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))
  change quotientOriginalCochainElement
      (CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map
          (f ≫ dgMappingConeInr f))) = _
  have hdeg : (show (0 : ℤ) + 0 = -1 + 1 by omega) =
      Int.add_comm 0 0 := Subsingleton.elim _ _
  rw [hdeg]
  change quotientOriginalCochainElement
      (CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map
          (f ≫ dgMappingConeInr f))) =
    (eqToHom (congrArg (quotientGradedModule K (dgMappingConeObject f))
      (Int.add_comm 0 0))).hom
      (quotientCompositionMap K L (dgMappingConeObject f) 0 0
        (quotientOriginalCochainElement
          (CochainComplex.HomComplex.Cochain.ofHom
            ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)))
        (quotientOriginalCochainElement
          (CochainComplex.HomComplex.Cochain.ofHom
            ((boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeInr f)))))
  rw [hcomp]
  apply congrArg quotientOriginalCochainElement
  rw [Functor.map_comp, CochainComplex.HomComplex.Cochain.ofHom_comp]
  exact (dgCochainCompTensorReversed_tmul K L (dgMappingConeObject f)
    (show (0 : ℤ) + 0 = 0 by rfl)
    (CochainComplex.HomComplex.Cochain.ofHom
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeInr f)))
    (CochainComplex.HomComplex.Cochain.ofHom
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))).symm

/-- The boundary of the second cone projection is minus first projection followed by `f`. -/
theorem quotientConeSnd_d {K L : ComplexCategory} (f : K ⟶ L) :
    (quotientTotalDifferential (dgMappingConeObject f) L 0).hom
        (quotientConeSnd f) =
      - (eqToHom (congrArg (quotientGradedModule (dgMappingConeObject f) L)
        (show (1 : ℤ) + 0 = 0 + 1 by omega))).hom
        (quotientCompose (quotientConeFst f) (quotientOriginalMorphismElement f)) := by
  change (quotientTotalDifferential (dgMappingConeObject f) L 0).hom
    (quotientOriginalCochainElement
      (CochainComplex.mappingCone.snd
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))) = _
  rw [quotientOriginalCochainElement_d]
  change quotientOriginalCochainElement
      (CochainComplex.HomComplex.δ
        (F := underlyingComplex (dgMappingConeObject f))
        (G := underlyingComplex L) 0 1
        (CochainComplex.mappingCone.snd
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))) = _
  rw [CochainComplex.mappingCone.δ_snd]
  rw [quotientOriginalCochainElement_neg]
  let fstC : (dgHomZModuleCochainComplex (dgMappingConeObject f) K).X 1 :=
    (CochainComplex.mappingCone.fst
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1
  let fC : (dgHomZModuleCochainComplex K L).X 0 :=
    CochainComplex.HomComplex.Cochain.ofHom f.hom
  have hcomp := quotientOriginalCochainElement_comp
    (dgMappingConeObject f) K L fC fstC
  congr 1
  have hdeg : (show (1 : ℤ) + 0 = 0 + 1 by omega) =
      Int.add_comm 1 0 := Subsingleton.elim _ _
  rw [hdeg]
  change quotientOriginalCochainElement (fstC.comp fC rfl) =
    (eqToHom (congrArg (quotientGradedModule (dgMappingConeObject f) L)
      (Int.add_comm 1 0))).hom
      (quotientCompositionMap (dgMappingConeObject f) K L 1 0
        (quotientOriginalCochainElement fstC)
        (quotientOriginalCochainElement fC))
  rw [hcomp]
  apply congrArg quotientOriginalCochainElement
  exact (dgCochainCompTensorReversed_tmul (dgMappingConeObject f) K L
    (show (0 : ℤ) + 1 = 1 by rfl) fC fstC).symm

/-- The boundary of `inr ≫ H` is `inr`. -/
theorem quotientConeInrContraction_d {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential L (dgMappingConeObject f) (-1)).hom
        (quotientConeInrContraction f hf) =
      (eqToHom (congrArg (quotientGradedModule L (dgMappingConeObject f))
        (show (0 : ℤ) = (0 + -1) + 1 by omega))).hom (quotientConeInr f) := by
  let C := dgMappingConeObject f
  let x := quotientConeInr f
  let H := quotientConeContraction f hf
  let h0 : (0 : ℤ) = -1 + 1 := by omega
  let hr := rightLeibnizDegreeEq (0 : ℤ) (-1)
  let hl := leftLeibnizDegreeEq (0 : ℤ) (-1)
  have hleib := quotientCompositionMap_d L C C 0 (-1) x H
  change (quotientTotalDifferential L C (-1)).hom
      (quotientConeInrContraction f hf) = _ at hleib
  have hfirst :
      (eqToHom (congrArg (quotientGradedModule L C) hr)).hom
          (quotientCompositionMap L C C 0 (-1 + 1) x
            ((quotientTotalDifferential C C (-1)).hom H)) =
        (eqToHom (congrArg (quotientGradedModule L C)
          (show (0 : ℤ) = (0 + -1) + 1 by omega))).hom x := by
    rw [quotientConeContraction_d_cast f hf h0]
    exact quotientCompositionMap_right_unit_transport L C 0 (-1 + 1)
      ((0 + -1) + 1) h0 hr (by omega) x
  have hsecond :
      (-1).negOnePow •
          (eqToHom (congrArg (quotientGradedModule L C) hl)).hom
            (quotientCompositionMap L C C (0 + 1) (-1)
              ((quotientTotalDifferential L C 0).hom x) H) = 0 := by
    have hdx : (quotientTotalDifferential L C 0).hom x = 0 :=
      quotientConeInr_d f
    have hz := quotientCompositionMap_zero_left_transport
      L C C (0 + 1) (-1) ((0 + -1) + 1) hl H
    calc
      _ = (-1).negOnePow •
          (eqToHom (congrArg (quotientGradedModule L C) hl)).hom
            (quotientCompositionMap L C C (0 + 1) (-1) 0 H) := by rw [hdx]
      _ = (-1).negOnePow • 0 := congrArg ((-1).negOnePow • ·) hz
      _ = 0 := by
        rw [Units.smul_def, zsmul_zero]
  calc
    _ = (eqToHom (congrArg (quotientGradedModule L C) hr)).hom
          (quotientCompositionMap L C C 0 (-1 + 1) x
            ((quotientTotalDifferential C C (-1)).hom H)) +
        (-1).negOnePow •
          (eqToHom (congrArg (quotientGradedModule L C) hl)).hom
            (quotientCompositionMap L C C (0 + 1) (-1)
              ((quotientTotalDifferential L C 0).hom x) H) := hleib
    _ = _ + 0 := congrArg₂ (· + ·) hfirst hsecond
    _ = _ := add_zero _

/-- The boundary of `inr ≫ H`, displayed at the standard degree-zero source. -/
theorem quotientConeInrContraction_d_cast {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) (h0 : (0 : ℤ) = -1 + 1) :
    (quotientTotalDifferential L (dgMappingConeObject f) (-1)).hom
        (quotientConeInrContraction f hf) =
      (eqToHom (congrArg (quotientGradedModule L (dgMappingConeObject f)) h0)).hom
        (quotientConeInr f) := by
  rw [quotientConeInrContraction_d]
  have hh : (show (0 : ℤ) = (0 + -1) + 1 by omega) = h0 := Subsingleton.elim _ _
  cases hh
  rfl

/-- The boundary of `inl ≫ H` is `inl - d(inl) ≫ H`. -/
theorem quotientConeInlContraction_d {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential K (dgMappingConeObject f) (-2)).hom
        (quotientConeInlContraction f hf) =
      (eqToHom (congrArg (quotientGradedModule K (dgMappingConeObject f))
        (show (-1 : ℤ) = (-1 + -1) + 1 by omega))).hom (quotientConeInl f) -
        (eqToHom (congrArg (quotientGradedModule K (dgMappingConeObject f))
          (leftLeibnizDegreeEq (-1) (-1)))).hom
          (quotientCompose
            ((quotientTotalDifferential K (dgMappingConeObject f) (-1)).hom
              (quotientConeInl f))
            (quotientConeContraction f hf)) := by
  let C := dgMappingConeObject f
  let x := quotientConeInl f
  let H := quotientConeContraction f hf
  let h0 : (0 : ℤ) = -1 + 1 := by omega
  let hr := rightLeibnizDegreeEq (-1 : ℤ) (-1)
  let hl := leftLeibnizDegreeEq (-1 : ℤ) (-1)
  have hleib := quotientCompositionMap_d K C C (-1) (-1) x H
  change (quotientTotalDifferential K C (-2)).hom
      (quotientConeInlContraction f hf) = _ at hleib
  have hfirst :
      (eqToHom (congrArg (quotientGradedModule K C) hr)).hom
          (quotientCompositionMap K C C (-1) (-1 + 1) x
            ((quotientTotalDifferential C C (-1)).hom H)) =
        (eqToHom (congrArg (quotientGradedModule K C)
          (show (-1 : ℤ) = (-1 + -1) + 1 by omega))).hom x := by
    rw [quotientConeContraction_d_cast f hf h0]
    exact quotientCompositionMap_right_unit_transport K C (-1) (-1 + 1)
      ((-1 + -1) + 1) h0 hr (by omega) x
  have hsecond :
      (-1).negOnePow •
          (eqToHom (congrArg (quotientGradedModule K C) hl)).hom
            (quotientCompositionMap K C C (-1 + 1) (-1)
              ((quotientTotalDifferential K C (-1)).hom x) H) =
        - (eqToHom (congrArg (quotientGradedModule K C) hl)).hom
            (quotientCompose
              ((quotientTotalDifferential K C (-1)).hom x) H) := by
    unfold quotientCompose
    simp only [Int.negOnePow_neg, Int.negOnePow_one]
    exact neg_one_zsmul _
  calc
    _ = (eqToHom (congrArg (quotientGradedModule K C) hr)).hom
          (quotientCompositionMap K C C (-1) (-1 + 1) x
            ((quotientTotalDifferential C C (-1)).hom H)) +
        (-1).negOnePow •
          (eqToHom (congrArg (quotientGradedModule K C) hl)).hom
            (quotientCompositionMap K C C (-1 + 1) (-1)
              ((quotientTotalDifferential K C (-1)).hom x) H) := hleib
    _ = _ + (- _) := congrArg₂ (· + ·) hfirst hsecond
    _ = _ := by rw [sub_eq_add_neg]

/-- The boundary of `inl ≫ H`, normalized to the degree used by its next composition. -/
theorem quotientConeInlContraction_d_cast
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f)
    (hInl : (-1 : ℤ) = -2 + 1)
    (hComp : ((-1 : ℤ) + 1) + (-1) = -2 + 1) :
    (quotientTotalDifferential K (dgMappingConeObject f) (-2)).hom
        (quotientConeInlContraction f hf) =
      (eqToHom (congrArg (quotientGradedModule K (dgMappingConeObject f)) hInl)).hom
          (quotientConeInl f) -
        (eqToHom (congrArg (quotientGradedModule K (dgMappingConeObject f)) hComp)).hom
          (quotientCompose
            ((quotientTotalDifferential K (dgMappingConeObject f) (-1)).hom
              (quotientConeInl f))
            (quotientConeContraction f hf)) := by
  rw [quotientConeInlContraction_d]
  congr 1

/-- The inverse candidate is a closed degree-zero quotient morphism. -/
theorem correctedWeakEquivalenceInverseElement_d
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential L K 0).hom
        (correctedWeakEquivalenceInverseElement f hf) = 0 := by
  let C := dgMappingConeObject f
  let a := quotientConeInrContraction f hf
  let b := quotientConeFst f
  let hr := rightLeibnizDegreeEq (-1 : ℤ) 1
  let hl := leftLeibnizDegreeEq (-1 : ℤ) 1
  have hleib := quotientCompositionMap_d L C K (-1) 1 a b
  change (quotientTotalDifferential L K 0).hom
      (correctedWeakEquivalenceInverseElement f hf) = _ at hleib
  have hfirst :
      (eqToHom (congrArg (quotientGradedModule L K) hr)).hom
          (quotientCompositionMap L C K (-1) (1 + 1) a
            ((quotientTotalDifferential C K 1).hom b)) = 0 := by
    have hdb : (quotientTotalDifferential C K 1).hom b = 0 :=
      quotientConeFst_d f
    rw [hdb]
    exact quotientCompositionMap_zero_right_transport
      L C K (-1) (1 + 1) ((-1 + 1) + 1) hr a
  have hsecondInner :
      (eqToHom (congrArg (quotientGradedModule L K) hl)).hom
          (quotientCompositionMap L C K (-1 + 1) 1
            ((quotientTotalDifferential L C (-1)).hom a) b) = 0 := by
    have hz : quotientCompositionMap L C K 0 1 (quotientConeInr f) b = 0 := by
      simpa only [quotientCompose, C, b] using quotientConeInr_comp_fst f
    rw [quotientConeInrContraction_d_cast f hf (by omega)]
    rw [quotientCompositionMap_cast_left_transport] <;> try omega
    rw [hz, map_zero, map_zero]
  have hsecond :
      (1 : ℤ).negOnePow •
          (eqToHom (congrArg (quotientGradedModule L K) hl)).hom
            (quotientCompositionMap L C K (-1 + 1) 1
              ((quotientTotalDifferential L C (-1)).hom a) b) = 0 := by
    rw [hsecondInner, Units.smul_def, zsmul_zero]
  calc
    _ = (eqToHom (congrArg (quotientGradedModule L K) hr)).hom
          (quotientCompositionMap L C K (-1) (1 + 1) a
            ((quotientTotalDifferential C K 1).hom b)) +
        (1 : ℤ).negOnePow •
          (eqToHom (congrArg (quotientGradedModule L K) hl)).hom
            (quotientCompositionMap L C K (-1 + 1) 1
              ((quotientTotalDifferential L C (-1)).hom a) b) := hleib
    _ = 0 + 0 := congrArg₂ (· + ·) hfirst hsecond
    _ = 0 := add_zero 0

/-- Raw Leibniz form of the left inverse homotopy boundary. -/
theorem correctedWeakEquivalenceLeftHomotopyElement_d_raw
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential K K (-1)).hom
        (correctedWeakEquivalenceLeftHomotopyElement f hf) =
      - (eqToHom (congrArg (quotientGradedModule K K)
          (leftLeibnizDegreeEq (-2) 1))).hom
          (quotientCompositionMap K (dgMappingConeObject f) K (-2 + 1) 1
            ((quotientTotalDifferential K (dgMappingConeObject f) (-2)).hom
              (quotientConeInlContraction f hf))
            (quotientConeFst f)) := by
  let C := dgMappingConeObject f
  let a := quotientConeInlContraction f hf
  let b := quotientConeFst f
  let hr := rightLeibnizDegreeEq (-2 : ℤ) 1
  let hl := leftLeibnizDegreeEq (-2 : ℤ) 1
  have hleib := quotientCompositionMap_d K C K (-2) 1 a b
  change (quotientTotalDifferential K K (-1)).hom
      (correctedWeakEquivalenceLeftHomotopyElement f hf) = _ at hleib
  have hfirst :
      (eqToHom (congrArg (quotientGradedModule K K) hr)).hom
          (quotientCompositionMap K C K (-2) (1 + 1) a
            ((quotientTotalDifferential C K 1).hom b)) = 0 := by
    have hdb : (quotientTotalDifferential C K 1).hom b = 0 := quotientConeFst_d f
    rw [hdb]
    exact quotientCompositionMap_zero_right_transport
      K C K (-2) (1 + 1) ((-2 + 1) + 1) hr a
  have hsecond :
      (1 : ℤ).negOnePow •
          (eqToHom (congrArg (quotientGradedModule K K) hl)).hom
            (quotientCompositionMap K C K (-2 + 1) 1
              ((quotientTotalDifferential K C (-2)).hom a) b) =
        - (eqToHom (congrArg (quotientGradedModule K K) hl)).hom
            (quotientCompositionMap K C K (-2 + 1) 1
              ((quotientTotalDifferential K C (-2)).hom a) b) := by
    simp only [Int.negOnePow_one]
    exact neg_one_zsmul _
  calc
    _ = (eqToHom (congrArg (quotientGradedModule K K) hr)).hom
          (quotientCompositionMap K C K (-2) (1 + 1) a
            ((quotientTotalDifferential C K 1).hom b)) +
        (1 : ℤ).negOnePow •
          (eqToHom (congrArg (quotientGradedModule K K) hl)).hom
            (quotientCompositionMap K C K (-2 + 1) 1
              ((quotientTotalDifferential K C (-2)).hom a) b) := hleib
    _ = 0 + (- _) := congrArg₂ (· + ·) hfirst hsecond
    _ = _ := zero_add _

/-- The left homotopy boundary separated into its correction and identity terms. -/
theorem correctedWeakEquivalenceLeftHomotopyElement_d_decompose
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential K K (-1)).hom
        (correctedWeakEquivalenceLeftHomotopyElement f hf) =
      (eqToHom (congrArg (quotientGradedModule K K)
        (leftLeibnizDegreeEq (-2) 1))).hom
        (quotientCompositionMap K (dgMappingConeObject f) K (-2 + 1) 1
          ((eqToHom (congrArg
            (quotientGradedModule K (dgMappingConeObject f))
            (show (((-1 : ℤ) + 1) + -1) = -2 + 1 by omega))).hom
            (quotientCompose
              ((quotientTotalDifferential K (dgMappingConeObject f) (-1)).hom
                (quotientConeInl f))
              (quotientConeContraction f hf)))
          (quotientConeFst f)) -
        (eqToHom (congrArg (quotientGradedModule K K)
          (leftLeibnizDegreeEq (-2) 1))).hom
          (quotientCompositionMap K (dgMappingConeObject f) K (-2 + 1) 1
            ((eqToHom (congrArg
              (quotientGradedModule K (dgMappingConeObject f))
              (show (-1 : ℤ) = -2 + 1 by omega))).hom
              (quotientConeInl f))
            (quotientConeFst f)) := by
  rw [correctedWeakEquivalenceLeftHomotopyElement_d_raw]
  rw [quotientConeInlContraction_d_cast f hf (by omega) (by omega)]
  rw [map_sub]
  simp only [LinearMap.sub_apply]
  rw [map_sub]
  exact neg_sub _ _

/-- The identity term in the left homotopy boundary is the quotient identity. -/
theorem correctedWeakEquivalenceLeftHomotopyIdentityTerm
    {K L : ComplexCategory} (f : K ⟶ L) :
    (eqToHom (congrArg (quotientGradedModule K K)
      (leftLeibnizDegreeEq (-2) 1))).hom
      (quotientCompositionMap K (dgMappingConeObject f) K (-2 + 1) 1
        ((eqToHom (congrArg
          (quotientGradedModule K (dgMappingConeObject f))
          (show (-1 : ℤ) = -2 + 1 by omega))).hom
          (quotientConeInl f))
        (quotientConeFst f)) =
      quotientIdentityElement K := by
  let C := dgMappingConeObject f
  let b := quotientConeFst f
  have hz : quotientCompositionMap K C K (-1) 1 (quotientConeInl f) b =
      quotientIdentityElement K := by
    simpa only [quotientCompose, C, b] using quotientConeInl_comp_fst f
  rw [quotientCompositionMap_cast_left_transport] <;> try omega
  rw [hz]
  rfl

/-- The correction term in the left homotopy boundary is `f` followed by its inverse candidate. -/
theorem correctedWeakEquivalenceLeftHomotopyCorrectionTerm
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (eqToHom (congrArg (quotientGradedModule K K)
      (leftLeibnizDegreeEq (-2) 1))).hom
      (quotientCompositionMap K (dgMappingConeObject f) K (-2 + 1) 1
        ((eqToHom (congrArg
          (quotientGradedModule K (dgMappingConeObject f))
          (show (((-1 : ℤ) + 1) + -1) = -2 + 1 by omega))).hom
          (quotientCompose
            ((quotientTotalDifferential K (dgMappingConeObject f) (-1)).hom
              (quotientConeInl f))
            (quotientConeContraction f hf)))
        (quotientConeFst f)) =
      (eqToHom (congrArg (quotientGradedModule K K)
        (show (0 : ℤ) + 0 = 0 by omega))).hom
        (quotientCompose (quotientOriginalMorphismElement f)
          (correctedWeakEquivalenceInverseElement f hf)) := by
  rw [quotientConeInl_d]
  rw [quotientCompositionMap_cast_left_transport] <;> try omega
  unfold quotientCompose
  rw [quotientCompositionMap_cast_left_transport] <;> try omega
  rw [← correctedWeakEquivalenceInverseElement_eq_cast f hf]
  rw [quotientCompositionMap_cast_right_transport] <;> try omega
  unfold quotientCompose
  rw [← quotientCompositionMap_assoc K L (dgMappingConeObject f) K
    0 (0 + -1) 1
    (quotientOriginalMorphismElement f)
    (quotientCompositionMap L (dgMappingConeObject f) (dgMappingConeObject f)
      0 (-1) (quotientConeInr f) (quotientConeContraction f hf))
    (quotientConeFst f)]
  rw [← quotientCompositionMap_assoc K L (dgMappingConeObject f)
    (dgMappingConeObject f) 0 0 (-1)
    (quotientOriginalMorphismElement f) (quotientConeInr f)
    (quotientConeContraction f hf)]
  congr 1

/-- The left homotopy witnesses `f ≫ g` minus the source identity. -/
theorem correctedWeakEquivalenceLeftHomotopyElement_d
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential K K (-1)).hom
        (correctedWeakEquivalenceLeftHomotopyElement f hf) =
      (eqToHom (congrArg (quotientGradedModule K K)
        (show (0 : ℤ) + 0 = 0 by omega))).hom
          (quotientCompose (quotientOriginalMorphismElement f)
            (correctedWeakEquivalenceInverseElement f hf)) -
        quotientIdentityElement K := by
  rw [correctedWeakEquivalenceLeftHomotopyElement_d_decompose f hf]
  rw [correctedWeakEquivalenceLeftHomotopyCorrectionTerm f hf]
  rw [correctedWeakEquivalenceLeftHomotopyIdentityTerm f]

/-- Raw Leibniz form of the right inverse homotopy boundary. -/
theorem correctedWeakEquivalenceRightHomotopyElement_d_raw
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential L L (-1)).hom
        (correctedWeakEquivalenceRightHomotopyElement f hf) =
      - (eqToHom (congrArg (quotientGradedModule L L)
          (show (((-1 : ℤ) + 0) + 1) = -1 + 1 by omega))).hom
        ((eqToHom (congrArg (quotientGradedModule L L)
            (rightLeibnizDegreeEq (-1) 0))).hom
            (quotientCompositionMap L (dgMappingConeObject f) L (-1) (0 + 1)
              (quotientConeInrContraction f hf)
              ((quotientTotalDifferential (dgMappingConeObject f) L 0).hom
                (quotientConeSnd f))) +
          (eqToHom (congrArg (quotientGradedModule L L)
            (leftLeibnizDegreeEq (-1) 0))).hom
            (quotientCompositionMap L (dgMappingConeObject f) L (-1 + 1) 0
              ((quotientTotalDifferential L (dgMappingConeObject f) (-1)).hom
                (quotientConeInrContraction f hf))
              (quotientConeSnd f))) := by
  have hleib := quotientCompositionMap_d L (dgMappingConeObject f) L (-1) 0
    (quotientConeInrContraction f hf) (quotientConeSnd f)
  unfold correctedWeakEquivalenceRightHomotopyElement
  rw [map_neg]
  rw [quotientTotalDifferential_cast]
  unfold quotientCompose
  rw [hleib]
  simp only [Int.negOnePow_zero, one_smul]
  congr 2

/-- The right homotopy boundary separated into its correction and identity terms. -/
theorem correctedWeakEquivalenceRightHomotopyElement_d_decompose
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential L L (-1)).hom
        (correctedWeakEquivalenceRightHomotopyElement f hf) =
      (eqToHom (congrArg (quotientGradedModule L L)
        (show (((-1 : ℤ) + 0) + 1) = -1 + 1 by omega))).hom
        ((eqToHom (congrArg (quotientGradedModule L L)
          (rightLeibnizDegreeEq (-1) 0))).hom
          (quotientCompositionMap L (dgMappingConeObject f) L (-1) (0 + 1)
            (quotientConeInrContraction f hf)
            ((eqToHom (congrArg (quotientGradedModule (dgMappingConeObject f) L)
              (show (1 : ℤ) + 0 = 0 + 1 by omega))).hom
              (quotientCompose (quotientConeFst f)
                (quotientOriginalMorphismElement f))))) -
        (eqToHom (congrArg (quotientGradedModule L L)
          (show (((-1 : ℤ) + 0) + 1) = -1 + 1 by omega))).hom
          ((eqToHom (congrArg (quotientGradedModule L L)
            (leftLeibnizDegreeEq (-1) 0))).hom
            (quotientCompositionMap L (dgMappingConeObject f) L (-1 + 1) 0
              ((eqToHom (congrArg
                (quotientGradedModule L (dgMappingConeObject f))
                (show (0 : ℤ) = -1 + 1 by omega))).hom
                (quotientConeInr f))
              (quotientConeSnd f))) := by
  rw [correctedWeakEquivalenceRightHomotopyElement_d_raw]
  rw [quotientConeSnd_d]
  rw [quotientConeInrContraction_d_cast f hf (by omega)]
  simp only [map_add, map_neg]
  abel

/-- The identity term in the right homotopy boundary is the quotient identity. -/
theorem correctedWeakEquivalenceRightHomotopyIdentityTerm
    {K L : ComplexCategory} (f : K ⟶ L) :
    (eqToHom (congrArg (quotientGradedModule L L)
      (show (((-1 : ℤ) + 0) + 1) = -1 + 1 by omega))).hom
      ((eqToHom (congrArg (quotientGradedModule L L)
        (leftLeibnizDegreeEq (-1) 0))).hom
        (quotientCompositionMap L (dgMappingConeObject f) L (-1 + 1) 0
          ((eqToHom (congrArg
            (quotientGradedModule L (dgMappingConeObject f))
            (show (0 : ℤ) = -1 + 1 by omega))).hom
            (quotientConeInr f))
          (quotientConeSnd f))) =
      quotientIdentityElement L := by
  let C := dgMappingConeObject f
  let s := quotientConeSnd f
  have hz : quotientCompositionMap L C L 0 0 (quotientConeInr f) s =
      quotientIdentityElement L := by
    simpa only [quotientCompose, C, s] using quotientConeInr_comp_snd f
  rw [quotientCompositionMap_cast_left_transport] <;> try omega
  rw [hz]
  rfl

/-- The correction term in the right homotopy boundary is `g` followed by `f`. -/
theorem correctedWeakEquivalenceRightHomotopyCorrectionTerm
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (eqToHom (congrArg (quotientGradedModule L L)
      (show (((-1 : ℤ) + 0) + 1) = -1 + 1 by omega))).hom
      ((eqToHom (congrArg (quotientGradedModule L L)
        (rightLeibnizDegreeEq (-1) 0))).hom
        (quotientCompositionMap L (dgMappingConeObject f) L (-1) (0 + 1)
          (quotientConeInrContraction f hf)
          ((eqToHom (congrArg (quotientGradedModule (dgMappingConeObject f) L)
            (show (1 : ℤ) + 0 = 0 + 1 by omega))).hom
            (quotientCompose (quotientConeFst f)
              (quotientOriginalMorphismElement f))))) =
      (eqToHom (congrArg (quotientGradedModule L L)
        (show (0 : ℤ) + 0 = 0 by omega))).hom
        (quotientCompose (correctedWeakEquivalenceInverseElement f hf)
          (quotientOriginalMorphismElement f)) := by
  rw [quotientCompositionMap_cast_right_transport] <;> try omega
  unfold quotientCompose
  rw [← quotientCompositionMap_assoc L (dgMappingConeObject f) K L
    (-1) 1 0 (quotientConeInrContraction f hf) (quotientConeFst f)
    (quotientOriginalMorphismElement f)]
  rw [← correctedWeakEquivalenceInverseElement_eq_cast_normalized f hf (by omega)]
  rw [quotientCompositionMap_cast_left_transport] <;> try omega
  congr 1

/-- The right homotopy witnesses `g ≫ f` minus the target identity. -/
theorem correctedWeakEquivalenceRightHomotopyElement_d
    {K L : ComplexCategory} (f : K ⟶ L) (hf : CorrectedWeakEquivalence f) :
    (quotientTotalDifferential L L (-1)).hom
        (correctedWeakEquivalenceRightHomotopyElement f hf) =
      (eqToHom (congrArg (quotientGradedModule L L)
        (show (0 : ℤ) + 0 = 0 by omega))).hom
          (quotientCompose (correctedWeakEquivalenceInverseElement f hf)
            (quotientOriginalMorphismElement f)) -
        quotientIdentityElement L := by
  rw [correctedWeakEquivalenceRightHomotopyElement_d_decompose f hf]
  rw [correctedWeakEquivalenceRightHomotopyCorrectionTerm f hf]
  rw [correctedWeakEquivalenceRightHomotopyIdentityTerm f]

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
