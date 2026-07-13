import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientFoundation

/-!
# Evaluation of the corrected Drinfeld quotient differential

The quotient internal differential is defined by a coproduct descent.  This file exposes the
corresponding elementwise computation on a chosen homogeneous word summand.  It is the reduction
step needed to compute the differential of the formal contracting generator.
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

/-- Evaluating the quotient internal differential on an included homogeneous word element is
the signed sum of the internal differentials of that word. -/
theorem quotientInternalDifferential_inclusion_apply
    (X Y : ComplexCategory) (n : ℤ)
    (s : GradedSummandIndex X Y n) (x : largeSummandModule s) :
    (quotientInternalDifferential X Y n).hom
        ((CategoryTheory.Limits.Sigma.ι
          (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s).hom x) =
      (internalDifferentialFromSummand s.2).hom x := by
  have h := quotientInternalDifferential_inclusion X Y n s
  exact congrArg (fun f ↦ f.hom x) h

/-- The internal differential of the formal contracting generator reduces to the internal
differential of its one-letter summand. -/
theorem quotientInternalDifferential_contractingElement
    (A : CorrectedAcyclicComplexCategory) :
    (quotientInternalDifferential A.obj A.obj (-1)).hom
        (quotientContractingElement A) =
      (internalDifferentialFromSummand
        (singletonContractingDegreeProfile A)).hom
          (ULift.up (singletonContractingElement A)) := by
  exact quotientInternalDifferential_inclusion_apply A.obj A.obj (-1)
    ⟨singleton A.obj A.obj A, singletonContractingDegreeProfile A⟩
    (ULift.up (singletonContractingElement A))

private theorem degreeProfile_nil_eq_nilDegreeProfile
    (X Y : ComplexCategory) (n : ℤ) (d : DegreeProfile (nil X Y) n) :
    d = nilDegreeProfile X Y n := by
  apply DegreeProfile.ext
  funext j
  change Fin 1 at j
  have hj : j = (0 : Fin 1) := Fin.ext (by omega)
  subst j
  have hd := d.totalDegree
  simpa [nil, nilDegreeProfile] using hd

private theorem cast_degreeProfile_eq_castWord
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) :
    cast (congrArg (fun q : DrinfeldWord X Y ↦ DegreeProfile q n) h) d =
      d.castWord h := by
  subst h
  rfl

private theorem singletonContractingSummandIndex_eq_nil
    (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton A.obj A.obj A).length) :
    (⟨eraseIntermediate (singleton A.obj A.obj A) i,
        (singletonContractingDegreeProfile A).contract i⟩ :
      GradedSummandIndex A.obj A.obj (-1 + 1)) =
      ⟨nil A.obj A.obj, nilDegreeProfile A.obj A.obj (-1 + 1)⟩ := by
  let hw := eraseIntermediate_singleton A.obj A.obj A i
  apply Sigma.ext hw
  have hp : ((singletonContractingDegreeProfile A).contract i).castWord hw =
      nilDegreeProfile A.obj A.obj (-1 + 1) :=
    degreeProfile_nil_eq_nilDegreeProfile _ _ _ _
  have hhp : ((singletonContractingDegreeProfile A).contract i).castWord hw ≍
      nilDegreeProfile A.obj A.obj (-1 + 1) := by
    exact heq_of_eq hp
  let hty := congrArg (fun w : DrinfeldWord A.obj A.obj ↦
    DegreeProfile w (-1 + 1)) hw
  apply (cast_heq_iff_heq hty
    ((singletonContractingDegreeProfile A).contract i)
    (nilDegreeProfile A.obj A.obj (-1 + 1))).mp
  convert hhp using 1
  exact cast_degreeProfile_eq_castWord hw _

private theorem sigma_castWord_inv_element_eq
    {X Y : ComplexCategory} {w v : DrinfeldWord X Y} {n : ℤ}
    (h : w = v) (d : DegreeProfile w n) (e : DegreeProfile v n)
    (hp : d.castWord h = e) (x : summandModule e) :
    (⟨⟨w, d⟩, ULift.up ((summandModuleCastWordIso h d).inv
      ((eqToIso (congrArg summandModule hp)).inv x))⟩ :
      Σ s : GradedSummandIndex X Y n, largeSummandModule s) =
    ⟨⟨v, e⟩, ULift.up x⟩ := by
  subst h
  subst hp
  rfl

private theorem sigma_nilSummand_inv_eq
    {X Y : ComplexCategory} {n : ℤ}
    (d : DegreeProfile (nil X Y) n)
    (e : DegreeProfile (nil X Y) n)
    (hp : d = e) (x : (dgHomZModuleCochainComplex X Y).X n) :
    (⟨⟨nil X Y, d⟩,
      ULift.up ((nilSummandIsoOriginal X Y d).inv x)⟩ :
      Σ s : GradedSummandIndex X Y n, largeSummandModule s) =
    ⟨⟨nil X Y, e⟩, ULift.up ((nilSummandIsoOriginal X Y e).inv x)⟩ := by
  subst hp
  rfl

/-- The contraction part of the differential of the formal generator is the original
degree-zero identity summand. -/
theorem singletonContractionLargeMap_contractingElement_eq_originalHomInclusion
    (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton A.obj A.obj A).length) :
    (singletonContractionLargeMap A.obj A.obj A
        (singletonContractingDegreeProfile A) i).hom
        (ULift.up (singletonContractingElement A)) =
      (originalHomInclusion A.obj A.obj 0).hom
        (ULift.up (identityCochain A.obj)) := by
  let i₀ := singletonIndex A.obj A.obj A
  have hi : i = i₀ := Fin.ext (by simp [i₀])
  subst i
  rw [singletonContractionLargeMap_contractingElement]
  unfold originalHomInclusion
  let hs := singletonContractingSummandIndex_eq_nil A i₀
  let z₁ : Σ s : GradedSummandIndex A.obj A.obj (-1 + 1),
      largeSummandModule s :=
    ⟨⟨eraseIntermediate (singleton A.obj A.obj A) i₀,
      (singletonContractingDegreeProfile A).contract i₀⟩,
      ULift.up ((singletonContractedSummandIsoOriginal A.obj A.obj A
        (singletonContractingDegreeProfile A) i₀).inv (identityCochain A.obj))⟩
  let z₂ : Σ s : GradedSummandIndex A.obj A.obj (-1 + 1),
      largeSummandModule s :=
    ⟨⟨nil A.obj A.obj, nilDegreeProfile A.obj A.obj (-1 + 1)⟩,
      ULift.up ((nilSummandIsoOriginal A.obj A.obj
        (nilDegreeProfile A.obj A.obj (-1 + 1))).inv (identityCochain A.obj))⟩
  have hz : z₁ = z₂ := by
    let hw := eraseIntermediate_singleton A.obj A.obj A i₀
    let d := (singletonContractingDegreeProfile A).contract i₀
    let e := nilDegreeProfile A.obj A.obj (-1 + 1)
    have hp : d.castWord hw = e :=
      degreeProfile_nil_eq_nilDegreeProfile _ _ _ _
    cases hw
    simpa [z₁, z₂, d, e, i₀, singletonContractedSummandIsoOriginal] using
      sigma_nilSummand_inv_eq d e hp (identityCochain A.obj)
  exact congrArg (fun z : Σ s : GradedSummandIndex A.obj A.obj (-1 + 1),
    largeSummandModule s ↦
      (CategoryTheory.Limits.Sigma.ι
        (fun t : GradedSummandIndex A.obj A.obj (-1 + 1) ↦ largeSummandModule t)
        z.1).hom z.2) hz

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
