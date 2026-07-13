import LeanLCAExactChallenge.Derived.BoundedDerivedWithCycles
import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesHomotopy

/-!
# Corrected ordinary triangulated semantics

This module exposes the unconditional corrected bounded-homotopy Verdier package. It deliberately excludes the former assumption-parameterized stable-route adapters and does not claim that an ordinary triangulated nerve is a stable infinity-category.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace BoundedDerivedWithCycles
namespace Metrizable

/-- Bounded cochain complexes over default-universe metrizable LCA groups. -/
abbrev ComplexCategory : Type 1 :=
  BoundedComplexCategory MetrizableLCA.{0}

/-- The corrected ordinary bounded derived category for default-universe `MetrizableLCA`. -/
abbrev OrdinaryCategory : Type 1 :=
  DboundedWithCycles MetrizableLCA.{0}

/-- Corrected bounded weak equivalences for default-universe `MetrizableLCA`. -/
abbrev WeakEquivalence : MorphismProperty ComplexCategory :=
  boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}

/-- The corrected localization functor for default-universe `MetrizableLCA`. -/
abbrev localization : ComplexCategory ⥤ OrdinaryCategory :=
  DboundedWithCycles.localization MetrizableLCA.{0}

/-- The ordinary quasicategory nerve attached to the corrected metrizable localization. -/
abbrev infinityCategory : SSet.QCat :=
  BoundedDerivedOrdinaryQuasicategoryWithCycles MetrizableLCA.{0}

/-- Bounded homotopy objects over default-universe metrizable LCA groups are directly closed under distinguished triangles. -/
noncomputable instance metrizableBoundedHomotopyObject_isTriangulatedClosed2 :
    (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  boundedHomotopyObject_isTriangulatedClosed2_direct MetrizableLCA.{0}

/-- The induced pretriangulation on the bounded homotopy category. -/
noncomputable instance metrizableBoundedHomotopyCategory_pretriangulated :
    Pretriangulated (BoundedHomotopyCategory MetrizableLCA.{0}) :=
  boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 MetrizableLCA.{0}

/-- The induced triangulation on the bounded homotopy category. -/
noncomputable instance metrizableBoundedHomotopyCategory_isTriangulated :
    IsTriangulated (BoundedHomotopyCategory MetrizableLCA.{0}) :=
  boundedHomotopyCategory_isTriangulated_of_isTriangulatedClosed2 MetrizableLCA.{0}

/-- The Verdier weak equivalences used in the corrected bounded homotopy quotient. -/
abbrev HomotopyVerdierWeakEquivalence :
    MorphismProperty (BoundedHomotopyCategory MetrizableLCA.{0}) :=
  (boundedExactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).trW

/-- The corrected bounded homotopy Verdier quotient for metrizable LCA groups. -/
abbrev HomotopyVerdierCategory : Type 1 :=
  BoundedExactAcyclicWithCyclesHomotopyVerdierCategory MetrizableLCA.{0}

/-- The localization functor into the corrected bounded homotopy Verdier quotient. -/
abbrev homotopyVerdierLocalization :
    BoundedHomotopyCategory MetrizableLCA.{0} ⥤ HomotopyVerdierCategory := by
  letI : Pretriangulated (BoundedHomotopyCategory MetrizableLCA.{0}) :=
    boundedHomotopyCategory_pretriangulated_of_isTriangulatedClosed2 MetrizableLCA.{0}
  exact (boundedExactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).trW.Q

/-- The ordinary quasicategory nerve of the corrected bounded homotopy Verdier quotient. This does not claim a genuine stable infinity-category enhancement. -/
abbrev HomotopyVerdierOrdinaryNerve : SSet.QCat :=
  ⟨CategoryTheory.nerve HomotopyVerdierCategory, inferInstance⟩

/-- Unconditional triangulated semantics for the corrected bounded homotopy Verdier quotient. Ordinary finite limits and colimits are deliberately absent. -/
structure HomotopyVerdierTriangulatedPackage : Type 2 where
  ordinaryNerveCarrier :
    HomotopyVerdierOrdinaryNerve =
      ⟨CategoryTheory.nerve HomotopyVerdierCategory, inferInstance⟩
  weakEquivalenceClass :
    HomotopyVerdierWeakEquivalence =
      (boundedExactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).trW
  leftCalculus : HomotopyVerdierWeakEquivalence.HasLeftCalculusOfFractions
  rightCalculus : HomotopyVerdierWeakEquivalence.HasRightCalculusOfFractions
  preadditive : Preadditive HomotopyVerdierCategory
  finiteProductInstance : HasFiniteProducts HomotopyVerdierCategory
  finiteBiproductInstance : HasFiniteBiproducts HomotopyVerdierCategory
  finiteCoproductInstance : HasFiniteCoproducts HomotopyVerdierCategory
  zeroObjectInstance : HasZeroObject HomotopyVerdierCategory
  shiftAdditiveAll :
    letI : Preadditive HomotopyVerdierCategory := preadditive
    ∀ n : ℤ, (shiftFunctor HomotopyVerdierCategory n).Additive
  suspensionAdditive :
    letI : Preadditive HomotopyVerdierCategory := preadditive
    letI : ∀ n : ℤ, (shiftFunctor HomotopyVerdierCategory n).Additive := shiftAdditiveAll
    (shiftFunctor HomotopyVerdierCategory (1 : ℤ)).Additive
  pretriangulatedStructure :
    letI : Preadditive HomotopyVerdierCategory := preadditive
    letI : HasZeroObject HomotopyVerdierCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor HomotopyVerdierCategory n).Additive := shiftAdditiveAll
    Pretriangulated HomotopyVerdierCategory
  triangulatedStructure :
    letI : Preadditive HomotopyVerdierCategory := preadditive
    letI : HasZeroObject HomotopyVerdierCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor HomotopyVerdierCategory n).Additive := shiftAdditiveAll
    letI : Pretriangulated HomotopyVerdierCategory := pretriangulatedStructure
    IsTriangulated HomotopyVerdierCategory

/-- The corrected bounded homotopy Verdier quotient has its ordinary triangulated semantics without topological realization, homology-detection, or finite-shape transfer inputs. -/
def homotopyVerdierTriangulatedPackage : HomotopyVerdierTriangulatedPackage where
  ordinaryNerveCarrier := rfl
  weakEquivalenceClass := rfl
  leftCalculus := by
    letI :
        (boundedExactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsTriangulated :=
      boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2
        MetrizableLCA.{0}
    infer_instance
  rightCalculus := by
    letI :
        (boundedExactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsTriangulated :=
      boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2
        MetrizableLCA.{0}
    infer_instance
  preadditive := by infer_instance
  finiteProductInstance := by infer_instance
  finiteBiproductInstance := by infer_instance
  finiteCoproductInstance := by infer_instance
  zeroObjectInstance := by infer_instance
  shiftAdditiveAll := by
    intro n
    infer_instance
  suspensionAdditive := by infer_instance
  pretriangulatedStructure := by infer_instance
  triangulatedStructure := by infer_instance

/-- Corrected weak equivalences are exactly the cycle-object acyclic mapping-cone maps. -/
theorem weakEquivalence_iff_exactAcyclicWithCyclesMappingCone
    {K L : ComplexCategory} (f : K ⟶ L) :
    WeakEquivalence f ↔
      exactAcyclicWithCycles MetrizableLCA
        (CochainComplex.mappingCone ((BoundedComplexCategory.ι MetrizableLCA).map f)) :=
  Iff.rfl

end Metrizable
end BoundedDerivedWithCycles

end LeanLCAExactChallenge
