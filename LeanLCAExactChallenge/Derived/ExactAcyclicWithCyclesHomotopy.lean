import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesContractible

/-!
# Homotopy-category surface for cycle-object acyclicity

This module lifts `exactAcyclicWithCycles` to the homotopy category and relates the
corrected bounded mapping-cone weak equivalences to the corresponding `trW` class.
-/

set_option autoImplicit false

noncomputable section

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- Corrected acyclic complexes as an object predicate on the homotopy category. -/
def exactAcyclicWithCyclesHomotopyObject :
    ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K => exactAcyclicWithCycles C K.as

/-- On quotient objects, the corrected homotopy-object predicate is the original predicate. -/
theorem exactAcyclicWithCyclesHomotopyObject_quotient_obj_iff
    (K : CochainComplex C ℤ) :
    exactAcyclicWithCyclesHomotopyObject C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ↔
      exactAcyclicWithCycles C K := by
  rfl

/-- Object-level input for making corrected acyclicity descend to the homotopy category. -/
structure ExactAcyclicWithCyclesHomotopyEquivInvarianceInput : Prop where
  exactAcyclicWithCycles_of_homotopyEquiv :
    ∀ {K L : CochainComplex C ℤ}, HomotopyEquiv K L →
      exactAcyclicWithCycles C K → exactAcyclicWithCycles C L

/-- Homotopy-equivalence invariance makes the corrected homotopy object predicate iso-closed. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance
    (I : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C) :
    (exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms where
  of_iso := by
    intro X Y e hX
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
    exact I.exactAcyclicWithCycles_of_homotopyEquiv
      (HomotopyCategory.homotopyEquivOfIso e) hX

/-- Corrected acyclic homotopy objects contain a zero object. -/
instance exactAcyclicWithCyclesHomotopyObject_containsZero [HasZeroObject C] :
    (exactAcyclicWithCyclesHomotopyObject C).ContainsZero where
  exists_zero := by
    refine ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (0 : CochainComplex C ℤ),
      ?_, ?_⟩
    · exact Functor.map_isZero (HomotopyCategory.quotient C (ComplexShape.up ℤ))
        (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))
    · exact exactAcyclicWithCycles_zero C

/-- The isomorphism closure of corrected acyclic homotopy objects. -/
abbrev exactAcyclicWithCyclesHomotopyIsoClosure :
    ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (exactAcyclicWithCyclesHomotopyObject C).isoClosure

/-- The isomorphism closure is closed under homotopy-category isomorphisms by construction. -/
instance exactAcyclicWithCyclesHomotopyIsoClosure_isClosedUnderIsomorphisms :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).IsClosedUnderIsomorphisms := by
  dsimp [exactAcyclicWithCyclesHomotopyIsoClosure]
  infer_instance

/-- The isomorphism closure still contains a zero object. -/
instance exactAcyclicWithCyclesHomotopyIsoClosure_containsZero [HasZeroObject C] :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).ContainsZero := by
  dsimp [exactAcyclicWithCyclesHomotopyIsoClosure]
  infer_instance

/-- The isomorphism closure of corrected acyclic homotopy objects is stable under shifts. -/
noncomputable instance exactAcyclicWithCyclesHomotopyIsoClosure_isStableUnderShift :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := by
    refine ⟨?_⟩
    rintro K ⟨K', hK', ⟨e⟩⟩
    obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K'
    refine ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (K₀⟦n⟧),
      exactAcyclicWithCycles_shift C K₀ n hK', ?_⟩
    exact ⟨(shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).mapIso e ≪≫
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app K₀).symm⟩

/-- Closing corrected acyclic homotopy objects under isomorphism does not change `trW`. -/
theorem exactAcyclicWithCyclesHomotopyIsoClosure_trW
    [HasZeroObject C] [HasBinaryBiproducts C] :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW =
      (exactAcyclicWithCyclesHomotopyObject C).trW := by
  exact ObjectProperty.trW_isoClosure (exactAcyclicWithCyclesHomotopyObject C)

/-- If the corrected predicate descends to the homotopy category, it is shift-stable there. -/
noncomputable instance
    exactAcyclicWithCyclesHomotopyObject_isStableUnderShift_of_isClosedUnderIsomorphisms
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms] :
    (exactAcyclicWithCyclesHomotopyObject C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := by
    refine ⟨?_⟩
    intro K hK
    obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    exact (exactAcyclicWithCyclesHomotopyObject C).prop_of_iso
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app K₀)
      (exactAcyclicWithCycles_shift C K₀ n hK)

/-- A map whose cone is corrected acyclic lies in the corrected homotopy `trW` class. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hf : exactAcyclicWithCycles C (CochainComplex.mappingCone f)) :
    (exactAcyclicWithCyclesHomotopyObject C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := by
  exact ⟨_, _, _, HomotopyCategory.mappingCone_triangleh_distinguished f, hf⟩

/-- Under homotopy-category descent, the corrected homotopy `trW` condition is cone acyclicity. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_iff_exactAcyclicWithCycles_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (exactAcyclicWithCyclesHomotopyObject C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ↔
      exactAcyclicWithCycles C (CochainComplex.mappingCone f) := by
  constructor
  · intro hf
    exact ((exactAcyclicWithCyclesHomotopyObject C).trW_iff_of_distinguished
      (CochainComplex.mappingCone.triangleh f)
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hf
  · intro hf
    exact
      exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone
        C f hf

/-- Exact acyclic mapping cones also give `trW` morphisms for the isomorphism closure. -/
theorem
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hf : exactAcyclicWithCycles C (CochainComplex.mappingCone f)) :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := by
  rw [exactAcyclicWithCyclesHomotopyIsoClosure_trW]
  exact
    exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone
      C f hf

/-- For the isomorphism closure, `trW` detects the cone object up to homotopy isomorphism. -/
theorem exactAcyclicWithCyclesHomotopyIsoClosure_trW_quotient_map_iff_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ↔
      exactAcyclicWithCyclesHomotopyIsoClosure C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone f)) := by
  exact ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f))

/-- Under homotopy-category descent, the iso-closed corrected `trW` condition is cone acyclicity. -/
theorem
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_quotient_map_iff_exactAcyclicWithCycles_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ↔
      exactAcyclicWithCycles C (CochainComplex.mappingCone f) := by
  rw [exactAcyclicWithCyclesHomotopyIsoClosure_trW C]
  exact
    exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_iff_exactAcyclicWithCycles_mappingCone
      C f

/-- Corrected direct bounded weak equivalences map into the corrected homotopy `trW` class. -/
theorem
    boundedExactWeakEquivalenceWithCycles_le_exactAcyclicWithCyclesHomotopy_trW_inverseImage
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedExactWeakEquivalenceWithCycles C ≤
      (exactAcyclicWithCyclesHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotient C) := by
  intro K L f hf
  exact
    exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone
      C ((BoundedComplexCategory.ι C).map f) hf

/-- Under homotopy-category descent, direct corrected weak equivalences are the corrected
`trW` pullback. -/
theorem
    boundedExactWeakEquivalenceWithCycles_eq_exactAcyclicWithCyclesHomotopy_trW_inverseImage
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms] :
    boundedExactWeakEquivalenceWithCycles C =
      (exactAcyclicWithCyclesHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotient C) := by
  ext K L f
  constructor
  · intro hf
    exact
      boundedExactWeakEquivalenceWithCycles_le_exactAcyclicWithCyclesHomotopy_trW_inverseImage
        C f hf
  · intro hf
    exact ((exactAcyclicWithCyclesHomotopyObject C).trW_iff_of_distinguished
      (CochainComplex.mappingCone.triangleh ((BoundedComplexCategory.ι C).map f))
      (HomotopyCategory.mappingCone_triangleh_distinguished
        ((BoundedComplexCategory.ι C).map f))).1 hf

/-- Corrected bounded morphisms whose homotopy image lies in the iso-closed `trW` class. -/
abbrev boundedHomotopyExactWeakEquivalenceWithCycles
    [HasZeroObject C] [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.inverseImage
    (BoundedComplexCategory.homotopyQuotient C)

/-- Direct corrected weak equivalences map into the iso-closed homotopy pullback class. -/
theorem boundedExactWeakEquivalenceWithCycles_le_boundedHomotopyExactWeakEquivalenceWithCycles
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedExactWeakEquivalenceWithCycles C ≤ boundedHomotopyExactWeakEquivalenceWithCycles C := by
  intro K L f hf
  dsimp [boundedHomotopyExactWeakEquivalenceWithCycles, BoundedComplexCategory.homotopyQuotient]
  exact
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone
      C ((BoundedComplexCategory.ι C).map f) hf

/-- The iso-closed homotopy pullback class is membership of the corrected cone object. -/
theorem boundedHomotopyExactWeakEquivalenceWithCycles_iff_mappingCone_isoClosure
    [HasZeroObject C] [HasBinaryBiproducts C] {K L : BoundedComplexCategory C} (f : K ⟶ L) :
    boundedHomotopyExactWeakEquivalenceWithCycles C f ↔
      exactAcyclicWithCyclesHomotopyIsoClosure C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f))) := by
  dsimp [boundedHomotopyExactWeakEquivalenceWithCycles, BoundedComplexCategory.homotopyQuotient]
  exact exactAcyclicWithCyclesHomotopyIsoClosure_trW_quotient_map_iff_mappingCone
    C ((BoundedComplexCategory.ι C).map f)

/-- If the corrected object predicate descends, the direct and homotopy pullback classes agree. -/
theorem
    boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms] :
    boundedExactWeakEquivalenceWithCycles C =
      boundedHomotopyExactWeakEquivalenceWithCycles C := by
  dsimp [boundedHomotopyExactWeakEquivalenceWithCycles]
  rw [exactAcyclicWithCyclesHomotopyIsoClosure_trW C]
  exact boundedExactWeakEquivalenceWithCycles_eq_exactAcyclicWithCyclesHomotopy_trW_inverseImage C

/-- Homotopy-equivalence invariance is the explicit input needed for the homotopy comparison. -/
theorem
    boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_homotopyEquivInvariance
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C) :
    boundedExactWeakEquivalenceWithCycles C =
      boundedHomotopyExactWeakEquivalenceWithCycles C := by
  haveI : (exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms :=
    exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance
      C I
  exact boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_isoClosed C

end LeanLCAExactChallenge
