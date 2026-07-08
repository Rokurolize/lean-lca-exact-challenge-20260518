import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesContractible
import LeanLCAExactChallenge.Derived.BoundedDerivedWithCycles

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

/-- Homotopy-category iso-closedness gives homotopy-equivalence invariance. -/
theorem
    exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_isClosedUnderIsomorphisms
    (hP : (exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms) :
    ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C := by
  haveI := hP
  exact
    { exactAcyclicWithCycles_of_homotopyEquiv := by
        intro K L e hK
        exact (exactAcyclicWithCyclesHomotopyObject C).prop_of_iso
          (HomotopyCategory.isoOfHomotopyEquiv e) hK }

/-- The explicit homotopy-equivalence input is exactly homotopy-category iso-closedness. -/
theorem
    exactAcyclicWithCyclesHomotopyEquivInvarianceInput_iff_isClosedUnderIsomorphisms :
    ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C ↔
      (exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms := by
  constructor
  · exact
      exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance
        C
  · exact
      exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_isClosedUnderIsomorphisms
        C

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

/-- The isomorphism closure is triangulated once distinguished-triangle closure is supplied. -/
theorem
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulated where

/-- Distinguished-triangle closure of the underlying predicate transfers to its iso-closure. -/
theorem
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂ := by
  infer_instance

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

/-- With iso-closedness, the remaining triangulated-subcategory obligation is closed₂. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_isTriangulated_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyObject C).IsTriangulated where

/-- A triangulated corrected object predicate gives left calculus for its `trW` class. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulated] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  infer_instance

/-- A triangulated corrected object predicate gives right calculus for its `trW` class. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulated] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasRightCalculusOfFractions := by
  infer_instance

/-- Iso-closedness and closed₂ give left calculus for the corrected object `trW` class. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    exactAcyclicWithCyclesHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  exact
    exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated
      C

/-- Iso-closedness and closed₂ give right calculus for the corrected object `trW` class. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    exactAcyclicWithCyclesHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  exact
    exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated
      C

/-- Triangulating the iso-closure gives left calculus for the corrected object `trW`. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_isoClosureClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  rw [← exactAcyclicWithCyclesHomotopyIsoClosure_trW C]
  infer_instance

/-- Triangulating the iso-closure gives right calculus for the corrected object `trW`. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_isoClosureClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  rw [← exactAcyclicWithCyclesHomotopyIsoClosure_trW C]
  infer_instance

/-- Closed₂ for the underlying predicate gives left calculus through the iso-closure. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  exact
    exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_isoClosureClosed2
      C

/-- Closed₂ for the underlying predicate gives right calculus through the iso-closure. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyObject C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  exact
    exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_isoClosureClosed2
      C

/-- Closed₂ for the iso-closure gives Verdier left calculus directly. -/
theorem
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  infer_instance

/-- Closed₂ for the iso-closure gives Verdier right calculus directly. -/
theorem
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  infer_instance

/-- Corrected acyclic bounded homotopy objects inside the bounded homotopy category. -/
abbrev boundedExactAcyclicWithCyclesHomotopyObject :
    ObjectProperty (BoundedHomotopyCategory C) :=
  (exactAcyclicWithCyclesHomotopyIsoClosure C).inverseImage (BoundedHomotopyCategory.ι C)

/-- Corrected acyclic bounded homotopy objects are isomorphism-closed. -/
instance boundedExactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms :
    (boundedExactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms := by
  dsimp [boundedExactAcyclicWithCyclesHomotopyObject]
  infer_instance

/-- Corrected acyclic bounded homotopy objects contain zero. -/
instance boundedExactAcyclicWithCyclesHomotopyObject_containsZero [HasZeroObject C] :
    (boundedExactAcyclicWithCyclesHomotopyObject C).ContainsZero := by
  dsimp [boundedExactAcyclicWithCyclesHomotopyObject]
  infer_instance

/-- Corrected acyclic bounded homotopy objects are shift-stable once the source is triangulated. -/
noncomputable instance boundedExactAcyclicWithCyclesHomotopyObject_isStableUnderShift
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    (boundedExactAcyclicWithCyclesHomotopyObject C).IsStableUnderShift ℤ := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  dsimp [boundedExactAcyclicWithCyclesHomotopyObject]
  infer_instance

/-- Under the two closed₂ inputs, corrected acyclic bounded homotopy objects are triangulated. -/
theorem boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  haveI : (boundedHomotopyObject C).IsTriangulated :=
    boundedHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  haveI : (exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  dsimp [boundedExactAcyclicWithCyclesHomotopyObject]
  infer_instance

/-- The corrected bounded homotopy Verdier quotient under the bounded-source closure input. -/
abbrev BoundedExactAcyclicWithCyclesHomotopyVerdierCategory
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] : Type (max u v) :=
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Localization

/-- The bounded corrected Verdier weak equivalences map to the ambient corrected `trW`. -/
abbrev boundedExactAcyclicWithCyclesHomotopyObjectToIsoClosure_trW
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    LocalizerMorphism (boundedExactAcyclicWithCyclesHomotopyObject C).trW
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  refine
    { functor := BoundedHomotopyCategory.ι C
      map := ?_ }
  intro X Y f hf
  rcases hf with ⟨Z, g, h, hT, hZ⟩
  refine ⟨(BoundedHomotopyCategory.ι C).obj Z, (BoundedHomotopyCategory.ι C).map g,
    (BoundedHomotopyCategory.ι C).map h ≫
      ((BoundedHomotopyCategory.ι C).commShiftIso (1 : ℤ)).hom.app X, ?_, hZ⟩
  exact (BoundedHomotopyCategory.ι C).map_distinguished _ hT

/-- Under closed₂ hypotheses, the corrected bounded homotopy Verdier quotient is preadditive. -/
noncomputable instance
    boundedExactAcyclicWithCyclesHomotopyVerdierCategory_preadditive_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Preadditive (BoundedExactAcyclicWithCyclesHomotopyVerdierCategory C) := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  haveI : (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  exact Localization.preadditive W.Q W

/-- Under closed₂ hypotheses, the corrected bounded homotopy Verdier functor is additive. -/
instance boundedExactAcyclicWithCyclesHomotopyVerdierCategory_localization_additive_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    ((boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q).Additive := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  haveI : (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  exact Localization.functor_additive W.Q W

/-- Under closed₂ hypotheses, the corrected bounded homotopy Verdier quotient has zero. -/
instance boundedExactAcyclicWithCyclesHomotopyVerdierCategory_hasZeroObject_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasZeroObject (BoundedExactAcyclicWithCyclesHomotopyVerdierCategory C) := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  change HasZeroObject W.Localization
  exact W.Q.hasZeroObject_of_additive

/-- Under closed₂ hypotheses, the corrected bounded homotopy Verdier quotient has shifts. -/
noncomputable instance boundedExactAcyclicWithCyclesHomotopyVerdierCategory_hasShift_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasShift (BoundedExactAcyclicWithCyclesHomotopyVerdierCategory C) ℤ := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  haveI : (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2 C
  haveI : W.IsCompatibleWithShift ℤ := by
    dsimp [W]
    infer_instance
  exact HasShift.localized W.Q W ℤ

/-- Under closed₂ hypotheses, the corrected bounded homotopy localization commutes with shifts. -/
noncomputable instance
    boundedExactAcyclicWithCyclesHomotopyVerdierCategory_localization_commShift_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    ((boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q).CommShift ℤ := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  haveI : (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2 C
  haveI : W.IsCompatibleWithShift ℤ := by
    dsimp [W]
    infer_instance
  exact Functor.CommShift.localized W.Q W ℤ

/-- Under closed₂ hypotheses, localized shifts on the corrected quotient are additive. -/
instance boundedExactAcyclicWithCyclesHomotopyVerdierCategory_shiftFunctor_additive_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] (n : ℤ) :
    (shiftFunctor (BoundedExactAcyclicWithCyclesHomotopyVerdierCategory C) n).Additive := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  haveI : (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  change (shiftFunctor W.Localization n).Additive
  rw [Localization.functor_additive_iff W.Q W]
  exact Functor.additive_of_iso (W.Q.commShiftIso n)

/-- Under closed₂ hypotheses, the corrected bounded homotopy Verdier quotient is pretriangulated. -/
noncomputable instance
    boundedExactAcyclicWithCyclesHomotopyVerdierCategory_pretriangulated_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Pretriangulated (BoundedExactAcyclicWithCyclesHomotopyVerdierCategory C) := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  haveI : (boundedHomotopyObject C).IsTriangulated :=
    boundedHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  haveI : (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  haveI : W.IsCompatibleWithTriangulation := by
    dsimp [W]
    infer_instance
  exact Triangulated.Localization.pretriangulated W.Q W

/-- Under closed₂ hypotheses, the corrected bounded homotopy Verdier quotient is triangulated. -/
instance boundedExactAcyclicWithCyclesHomotopyVerdierCategory_isTriangulated_of_closed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    IsTriangulated (BoundedExactAcyclicWithCyclesHomotopyVerdierCategory C) := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let W : MorphismProperty (BoundedHomotopyCategory C) :=
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW
  haveI : (boundedHomotopyObject C).IsTriangulated :=
    boundedHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  haveI : (boundedExactAcyclicWithCyclesHomotopyObject C).IsTriangulated :=
    boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  haveI : W.IsCompatibleWithTriangulation := by
    dsimp [W]
    infer_instance
  haveI : W.Q.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor W.Q W
  change IsTriangulated W.Localization
  exact Triangulated.Localization.isTriangulated W.Q W

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

/-- The corrected homotopy pullback weak equivalences contain identities. -/
noncomputable instance boundedHomotopyExactWeakEquivalenceWithCycles_containsIdentities
    [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).ContainsIdentities := by
  dsimp [boundedHomotopyExactWeakEquivalenceWithCycles]
  infer_instance

/-- The homotopy pullback class maps to the ambient corrected homotopy `trW`. -/
abbrev boundedHomotopyExactWeakEquivalenceWithCyclesToIsoClosure_trW
    [HasZeroObject C] [HasBinaryBiproducts C] :
    LocalizerMorphism (boundedHomotopyExactWeakEquivalenceWithCycles C)
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW where
  functor := BoundedComplexCategory.homotopyQuotient C
  map := by
    intro K L f hf
    exact hf

/-- The homotopy pullback class maps to the bounded corrected homotopy `trW`. -/
noncomputable abbrev boundedHomotopyExactWeakEquivalenceWithCyclesToBoundedHomotopy_trW
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    LocalizerMorphism (boundedHomotopyExactWeakEquivalenceWithCycles C)
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  refine
    { functor := BoundedComplexCategory.homotopyQuotientBounded C
      map := ?_ }
  intro K L f hf
  change (boundedExactAcyclicWithCyclesHomotopyObject C).trW
    ((BoundedComplexCategory.homotopyQuotientBounded C).map f)
  rw [ObjectProperty.inverseImage_trW_iff]
  simpa [boundedHomotopyExactWeakEquivalenceWithCycles,
    BoundedComplexCategory.homotopyQuotientBounded] using hf

/-- The homotopy pullback class is the bounded corrected homotopy `trW` pullback. -/
theorem
    boundedHomotopyExactWeakEquivalenceWithCycles_eq_boundedHomotopy_trW_inverseImage
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    boundedHomotopyExactWeakEquivalenceWithCycles C =
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotientBounded C) := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  haveI : (boundedHomotopyObject C).IsTriangulated :=
    boundedHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  ext K L f
  change (exactAcyclicWithCyclesHomotopyIsoClosure C).trW
        ((BoundedComplexCategory.homotopyQuotient C).map f) ↔
      ((exactAcyclicWithCyclesHomotopyIsoClosure C).inverseImage
          (BoundedHomotopyCategory.ι C)).trW
        ((BoundedComplexCategory.homotopyQuotientBounded C).map f)
  rw [ObjectProperty.inverseImage_trW_iff]
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW
  let e := Arrow.isoOfNatIso (BoundedComplexCategory.homotopyQuotientBounded_comp_ι_iso C)
    (Arrow.mk f)
  exact (W.arrow_mk_iso_iff e).symm

/-- The bounded-complex functor into the corrected homotopy Verdier quotient. -/
noncomputable abbrev boundedHomotopyWithCyclesLocalizedVerdierFunctor
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory C ⥤
      MorphismProperty.Localization ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW) :=
  BoundedComplexCategory.homotopyQuotient C ⋙
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q

/-- Adjunction input for pulling Verdier left calculus back to bounded complexes. -/
structure BoundedHomotopyWithCyclesLocalizedRightAdjointInput
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  rightAdjoint :
    MorphismProperty.Localization ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW) ⥤
      BoundedComplexCategory C
  adjunction :
    boundedHomotopyWithCyclesLocalizedVerdierFunctor C ⊣ rightAdjoint
  unit_mem :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).functorCategory
      (BoundedComplexCategory C) adjunction.unit

/-- Adjunction input for pulling Verdier right calculus back to bounded complexes. -/
structure BoundedHomotopyWithCyclesLocalizedLeftAdjointInput
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) where
  leftAdjoint :
    MorphismProperty.Localization ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW) ⥤
      BoundedComplexCategory C
  adjunction :
    leftAdjoint ⊣ boundedHomotopyWithCyclesLocalizedVerdierFunctor C
  counit_mem :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).functorCategory
      (BoundedComplexCategory C) adjunction.counit

/-- A localized right adjoint gives left calculus for the corrected homotopy pullback. -/
theorem
    boundedHomotopyExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_adjoint
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicWithCyclesHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions]
    (I : BoundedHomotopyWithCyclesLocalizedRightAdjointInput C) :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions :=
  inverseImage_hasLeftCalculusOfFractions_of_localizedRightAdjoint
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW)
    I.rightAdjoint I.adjunction I.unit_mem

/-- Closed₂ plus a localized right adjoint give left calculus for the homotopy pullback. -/
theorem
    boundedHomotopyExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (I : BoundedHomotopyWithCyclesLocalizedRightAdjointInput C) :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions := by
  haveI : ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW).HasLeftCalculusOfFractions :=
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_closed2 C
  exact
    boundedHomotopyExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_adjoint
      C I

/-- A localized left adjoint gives right calculus for the corrected homotopy pullback. -/
theorem
    boundedHomotopyExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_adjoint
    [HasZeroObject C] [HasBinaryBiproducts C]
    [((exactAcyclicWithCyclesHomotopyIsoClosure C).trW).HasRightCalculusOfFractions]
    (I : BoundedHomotopyWithCyclesLocalizedLeftAdjointInput C) :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions :=
  inverseImage_hasRightCalculusOfFractions_of_localizedLeftAdjoint
    (BoundedComplexCategory.homotopyQuotient C)
    ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW)
    I.leftAdjoint I.adjunction I.counit_mem

/-- Closed₂ plus a localized left adjoint give right calculus for the homotopy pullback. -/
theorem
    boundedHomotopyExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (I : BoundedHomotopyWithCyclesLocalizedLeftAdjointInput C) :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions := by
  haveI : ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW).HasRightCalculusOfFractions :=
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_closed2 C
  exact
    boundedHomotopyExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_adjoint
      C I

/-- Direct corrected weak equivalences map into the iso-closed homotopy pullback class. -/
theorem boundedExactWeakEquivalenceWithCycles_le_boundedHomotopyExactWeakEquivalenceWithCycles
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedExactWeakEquivalenceWithCycles C ≤ boundedHomotopyExactWeakEquivalenceWithCycles C := by
  intro K L f hf
  dsimp [boundedHomotopyExactWeakEquivalenceWithCycles, BoundedComplexCategory.homotopyQuotient]
  exact
    exactAcyclicWithCyclesHomotopyIsoClosure_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone
      C ((BoundedComplexCategory.ι C).map f) hf

/-- The identity functor sends direct corrected weak equivalences to the corrected homotopy
pullback weak equivalences. -/
abbrev boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCycles
    [HasZeroObject C] [HasBinaryBiproducts C] :
    LocalizerMorphism (boundedExactWeakEquivalenceWithCycles C)
      (boundedHomotopyExactWeakEquivalenceWithCycles C) where
  functor := 𝟭 _
  map := by
    intro K L f hf
    exact boundedExactWeakEquivalenceWithCycles_le_boundedHomotopyExactWeakEquivalenceWithCycles
      C f hf

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

/-- Under homotopy descent, the identity localizer morphism is induced by equality of the
direct and corrected homotopy pullback weak-equivalence classes. -/
abbrev boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCyclesOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms] :
    LocalizerMorphism (boundedExactWeakEquivalenceWithCycles C)
      (boundedHomotopyExactWeakEquivalenceWithCycles C) :=
  LocalizerMorphism.ofEq (F := 𝟭 (BoundedComplexCategory C)) (by
    ext K L f
    simp only [MorphismProperty.inverseImage, Functor.id_map]
    rw [boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_isoClosed C]
    rfl)

instance boundedExactWeakEquivalenceWithCyclesToHomotopyOfIsoClosed_localizedEquivalence
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms] :
    (boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCyclesOfIsoClosed
      C).IsLocalizedEquivalence := by
  haveI :
      (boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCyclesOfIsoClosed
        C).functor.IsEquivalence := by
    dsimp
      [boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCyclesOfIsoClosed]
    infer_instance
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  intro K L f hf
  refine ⟨K, L, f, ?_, ?_⟩
  · rw [boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_isoClosed C]
    exact hf
  · simpa
      [boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCyclesOfIsoClosed]
      using (Nonempty.intro (Iso.refl (Arrow.mk f)))

/-- Direct corrected weak equivalences also map to the corrected homotopy Verdier weak
equivalences. -/
abbrev boundedExactWeakEquivalenceWithCyclesToExactAcyclicWithCyclesHomotopyIsoClosure_trW
    [HasZeroObject C] [HasBinaryBiproducts C] :
    LocalizerMorphism (boundedExactWeakEquivalenceWithCycles C)
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW :=
  (boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCycles C).comp
    (boundedHomotopyExactWeakEquivalenceWithCyclesToIsoClosure_trW C)

/-- Direct corrected weak equivalences also map to the bounded corrected homotopy Verdier weak
equivalences by first passing through the corrected homotopy pullback class. -/
noncomputable abbrev
    boundedExactWeakEquivalenceWithCyclesToBoundedExactAcyclicWithCyclesHomotopy_trW
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    LocalizerMorphism (boundedExactWeakEquivalenceWithCycles C)
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  exact (boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCycles C).comp
    (boundedHomotopyExactWeakEquivalenceWithCyclesToBoundedHomotopy_trW C)

/-- Homotopy-category descent transfers left calculus from the homotopy pullback class. -/
theorem
    boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions] :
    (boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions := by
  rw [boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_isoClosed C]
  infer_instance

/-- Homotopy-category descent transfers right calculus from the homotopy pullback class. -/
theorem
    boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions] :
    (boundedExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions := by
  rw [boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_isoClosed C]
  infer_instance

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

/-- Homotopy descent identifies direct weak equivalences with bounded homotopy `trW`. -/
theorem
    boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopy_trW_of_homotopyEquivInvariance
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂]
    (I : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C) :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    boundedExactWeakEquivalenceWithCycles C =
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotientBounded C) := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  rw [boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_homotopyEquivInvariance
    C I]
  exact boundedHomotopyExactWeakEquivalenceWithCycles_eq_boundedHomotopy_trW_inverseImage C

/-- Homotopy-equivalence invariance transfers left calculus from the homotopy pullback class. -/
theorem
    boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_homotopyEquivInvariance
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C)
    [(boundedHomotopyExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions] :
    (boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms :=
    exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance
      C I
  exact boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_isoClosed C

/-- Homotopy-equivalence invariance transfers right calculus from the homotopy pullback class. -/
theorem
    boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_homotopyEquivInvariance
    [HasZeroObject C] [HasBinaryBiproducts C]
    (I : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C)
    [(boundedHomotopyExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions] :
    (boundedExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions := by
  haveI : (exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms :=
    exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance
      C I
  exact boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_isoClosed C

/-- Closed₂, a localized right adjoint, and homotopy descent give direct left calculus. -/
theorem
    boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (H : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C)
    (I : BoundedHomotopyWithCyclesLocalizedRightAdjointInput C) :
    (boundedExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions := by
  haveI : (boundedHomotopyExactWeakEquivalenceWithCycles C).HasLeftCalculusOfFractions :=
    boundedHomotopyExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint
      C I
  exact
    boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_homotopyEquivInvariance
      C H

/-- Closed₂, a localized left adjoint, and homotopy descent give direct right calculus. -/
theorem
    boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyIsoClosure C).IsTriangulatedClosed₂]
    (H : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput C)
    (I : BoundedHomotopyWithCyclesLocalizedLeftAdjointInput C) :
    (boundedExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions := by
  haveI : (boundedHomotopyExactWeakEquivalenceWithCycles C).HasRightCalculusOfFractions :=
    boundedHomotopyExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint
      C I
  exact
    boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_homotopyEquivInvariance
      C H

/-!
## Localized comparison categories

The following declarations mirror the legacy Q/Qh comparison layer, but every localizer is
the corrected cycle-object weak equivalence or its corrected homotopy pullback.
-/

/-- The corrected homotopy/Verdier pullback localization. -/
abbrev BoundedHomotopyDerivedCategoryWithCycles
    [HasZeroObject C] [HasBinaryBiproducts C] : Type (max u v) :=
  (boundedHomotopyExactWeakEquivalenceWithCycles C).Localization

namespace BoundedHomotopyDerivedCategoryWithCycles

/-- The comparison from the corrected homotopy pullback localization to the ambient corrected
homotopy Verdier quotient. -/
noncomputable abbrev verdierComparison [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedHomotopyDerivedCategoryWithCycles C ⥤
      MorphismProperty.Localization ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW) :=
  (boundedHomotopyExactWeakEquivalenceWithCyclesToIsoClosure_trW C).localizedFunctor
    (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q

/-- The corrected homotopy pullback comparison commutes with the two localization functors. -/
noncomputable def verdierComparisonLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory.homotopyQuotient C ⋙
        (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q ≅
      (boundedHomotopyExactWeakEquivalenceWithCycles C).Q ⋙
        BoundedHomotopyDerivedCategoryWithCycles.verdierComparison C :=
  let Φ := boundedHomotopyExactWeakEquivalenceWithCyclesToIsoClosure_trW C
  letI : CatCommSq Φ.functor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q
      (Φ.localizedFunctor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
        (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q) :=
    Φ.catCommSq (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q
  CatCommSq.iso Φ.functor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q
    (Φ.localizedFunctor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q)

/-- The corrected homotopy pullback localization factors through the bounded corrected
homotopy Verdier quotient. -/
noncomputable abbrev boundedVerdierComparison
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    BoundedHomotopyDerivedCategoryWithCycles C ⥤
      BoundedExactAcyclicWithCyclesHomotopyVerdierCategory C := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  exact (boundedHomotopyExactWeakEquivalenceWithCyclesToBoundedHomotopy_trW
    C).localizedFunctor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q

/-- The corrected bounded Verdier comparison commutes with the bounded homotopy quotient and
the two localization functors. -/
noncomputable def boundedVerdierComparisonLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyObject C).IsTriangulatedClosed₂] :
    letI : Pretriangulated (BoundedHomotopyCategory C) :=
      boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
    BoundedComplexCategory.homotopyQuotientBounded C ⋙
        (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q ≅
      (boundedHomotopyExactWeakEquivalenceWithCycles C).Q ⋙
        BoundedHomotopyDerivedCategoryWithCycles.boundedVerdierComparison C := by
  letI : Pretriangulated (BoundedHomotopyCategory C) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 C
  let Φ := boundedHomotopyExactWeakEquivalenceWithCyclesToBoundedHomotopy_trW C
  letI : CatCommSq Φ.functor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q
      (Φ.localizedFunctor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
        (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q) :=
    Φ.catCommSq (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q
  exact CatCommSq.iso Φ.functor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
    (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q
    (Φ.localizedFunctor (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q)

end BoundedHomotopyDerivedCategoryWithCycles

namespace DboundedWithCycles

/-- The comparison from the direct corrected bounded localization to the corrected homotopy
pullback localization. -/
noncomputable abbrev homotopyComparison [HasZeroObject C] [HasBinaryBiproducts C] :
    DboundedWithCycles C ⥤ BoundedHomotopyDerivedCategoryWithCycles C :=
  (boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCycles C).localizedFunctor
    (DboundedWithCycles.localization C) (boundedHomotopyExactWeakEquivalenceWithCycles C).Q

/-- The corrected homotopy comparison commutes with the localization functors. -/
noncomputable def homotopyComparisonLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyExactWeakEquivalenceWithCycles C).Q ≅
      DboundedWithCycles.localization C ⋙ DboundedWithCycles.homotopyComparison C :=
  let Φ := boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCycles C
  letI : CatCommSq Φ.functor (DboundedWithCycles.localization C)
      (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
      (Φ.localizedFunctor (DboundedWithCycles.localization C)
        (boundedHomotopyExactWeakEquivalenceWithCycles C).Q) :=
    Φ.catCommSq (DboundedWithCycles.localization C)
      (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
  by
    simpa [boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCycles,
      DboundedWithCycles.homotopyComparison] using
      CatCommSq.iso Φ.functor (DboundedWithCycles.localization C)
        (boundedHomotopyExactWeakEquivalenceWithCycles C).Q
        (Φ.localizedFunctor (DboundedWithCycles.localization C)
          (boundedHomotopyExactWeakEquivalenceWithCycles C).Q)

/-- The comparison from the direct corrected bounded localization to the ambient corrected
homotopy Verdier quotient, routed through the corrected homotopy pullback localization. -/
noncomputable abbrev verdierComparison [HasZeroObject C] [HasBinaryBiproducts C] :
    DboundedWithCycles C ⥤
      MorphismProperty.Localization ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW) :=
  DboundedWithCycles.homotopyComparison C ⋙
    BoundedHomotopyDerivedCategoryWithCycles.verdierComparison C

/-- The routed corrected bounded-to-Verdier comparison commutes with the localization
functors. -/
noncomputable def verdierComparisonLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory.homotopyQuotient C ⋙
        (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q ≅
      DboundedWithCycles.localization C ⋙ DboundedWithCycles.verdierComparison C :=
  BoundedHomotopyDerivedCategoryWithCycles.verdierComparisonLocalizationIso C ≪≫
    Functor.isoWhiskerRight (DboundedWithCycles.homotopyComparisonLocalizationIso C)
      (BoundedHomotopyDerivedCategoryWithCycles.verdierComparison C) ≪≫
    Functor.associator _ _ _

/-- The comparison from the direct corrected bounded localization to the ambient corrected
homotopy Verdier quotient, induced directly by the composite localizer morphism. -/
noncomputable abbrev verdierComparisonDirect [HasZeroObject C] [HasBinaryBiproducts C] :
    DboundedWithCycles C ⥤
      MorphismProperty.Localization ((exactAcyclicWithCyclesHomotopyIsoClosure C).trW) :=
  (boundedExactWeakEquivalenceWithCyclesToExactAcyclicWithCyclesHomotopyIsoClosure_trW
    C).localizedFunctor (DboundedWithCycles.localization C)
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q

/-- The direct corrected bounded-to-Verdier comparison commutes with the localization
functors. -/
noncomputable def verdierComparisonDirectLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory.homotopyQuotient C ⋙
        (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q ≅
      DboundedWithCycles.localization C ⋙ DboundedWithCycles.verdierComparisonDirect C :=
  let Φ := boundedExactWeakEquivalenceWithCyclesToExactAcyclicWithCyclesHomotopyIsoClosure_trW C
  letI : CatCommSq Φ.functor (DboundedWithCycles.localization C)
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q
      (Φ.localizedFunctor (DboundedWithCycles.localization C)
        (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q) :=
    Φ.catCommSq (DboundedWithCycles.localization C)
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q
  CatCommSq.iso Φ.functor (DboundedWithCycles.localization C)
    (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q
    (Φ.localizedFunctor (DboundedWithCycles.localization C)
      (exactAcyclicWithCyclesHomotopyIsoClosure C).trW.Q)

/-- Under homotopy descent, the direct corrected localization and corrected homotopy pullback
localization are equivalent. -/
noncomputable def homotopyComparisonEquivalenceOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicWithCyclesHomotopyObject C).IsClosedUnderIsomorphisms] :
    DboundedWithCycles C ≌ BoundedHomotopyDerivedCategoryWithCycles C :=
  ((boundedExactWeakEquivalenceWithCyclesToHomotopyExactWeakEquivalenceWithCyclesOfIsoClosed
    C).localizedFunctor (DboundedWithCycles.localization C)
      (boundedHomotopyExactWeakEquivalenceWithCycles C).Q).asEquivalence

end DboundedWithCycles

end LeanLCAExactChallenge
