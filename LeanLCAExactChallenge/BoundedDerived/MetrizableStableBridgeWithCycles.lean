import LeanLCAExactChallenge.Derived.BoundedDerivedWithCycles
import LeanLCAExactChallenge.Derived.ComparisonBijectivityRoute
import LeanLCAExactChallenge.Derived.ExactAcyclicWithCyclesHomotopy

/-!
# Corrected metrizable stable bridge for cycle-object acyclicity

This module gives the corrected `DboundedWithCycles` route its own stable package surface.
The fields are typed against `DboundedWithCycles MetrizableLCA` and the weak equivalences
are `boundedExactWeakEquivalenceWithCycles`.

The file intentionally keeps the remaining stable facts as explicit assumptions. It does
not use the legacy `Dbounded` semantic package as evidence for the corrected route.
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

/-- Bounded homotopy objects over default-universe metrizable LCA groups are directly
closed under distinguished triangles. -/
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

/-- The ordinary quasicategory nerve of the corrected bounded homotopy Verdier quotient.

This is only the ordinary nerve of a triangulated category; the declaration does not claim
that a genuine stable infinity-category enhancement has been constructed. -/
abbrev HomotopyVerdierOrdinaryNerve : SSet.QCat :=
  ⟨CategoryTheory.nerve HomotopyVerdierCategory, inferInstance⟩

/-- Unconditional triangulated semantics for the corrected bounded homotopy Verdier quotient.

Finite limits and colimits are deliberately absent: a triangulated homotopy category need
not have ordinary finite limits or colimits. -/
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

/-- The corrected bounded homotopy Verdier quotient has its ordinary triangulated semantics
without any topological realization, homology-detection, or WPP-transfer input. -/
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

/-- W821 supplies homology existence for every default-universe metrizable cochain complex. -/
theorem hasHomologyOfComparisonBijectivity :
    ∀ (K : CochainComplex MetrizableLCA.{0} ℤ) (i : ℤ), K.HasHomology i := by
  letI : CategoryWithHomology MetrizableLCA.{0} :=
    MetrizableLCA.categoryWithHomology_of_leftRightComparisonBijectiveW821
  intro K i
  infer_instance

/-- Add W821 homology existence to the route's boundary-topology input. -/
def exactAtReverseDetectionInputOfBoundaryTopology
    (input : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    ExactAcyclicWithCyclesExactAtReverseDetectionInput MetrizableLCA.{0} :=
  exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableBoundaryTopology
    hasHomologyOfComparisonBijectivity input

/-- Boundary topology plus W821 gives homology detection for the corrected predicate. -/
def homologyDetectionInputOfBoundaryTopology
    (input : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    ExactAcyclicWithCyclesHomologyDetectionInput MetrizableLCA.{0} :=
  exactAcyclicWithCyclesHomologyDetectionInput_of_exactAtDetection
    MetrizableLCA.{0}
    (exactAcyclicWithCyclesExactAtDetectionInput_of_metrizableReverse
      (exactAtReverseDetectionInputOfBoundaryTopology input))

/-- The W821 degree-zero homological kernel in the homotopy category. -/
abbrev comparisonHomologyKernelObject :
    ObjectProperty (HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ)) := by
  letI : CategoryWithHomology MetrizableLCA.{0} :=
    MetrizableLCA.categoryWithHomology_of_leftRightComparisonBijectiveW821
  exact (HomotopyCategory.homologyFunctor MetrizableLCA.{0} (ComplexShape.up ℤ) 0).homologicalKernel

/-- Under the route's boundary-topology input, the corrected acyclic homotopy objects are
exactly the W821 homological kernel. -/
theorem exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject
    (input : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0} =
      comparisonHomologyKernelObject := by
  letI : CategoryWithHomology MetrizableLCA.{0} :=
    MetrizableLCA.categoryWithHomology_of_leftRightComparisonBijectiveW821
  exact exactAcyclicWithCyclesHomotopyObject_eq_homologicalKernel_of_homologyDetection
    MetrizableLCA.{0} (homologyDetectionInputOfBoundaryTopology input)

/-- The forgetful degree-zero homology functor to abelian groups. -/
noncomputable abbrev forgetfulHomologyKernelFunctor :
    HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ) ⥤ AddCommGrpCat.{0} :=
  ((forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapHomotopyCategory
    (ComplexShape.up ℤ)) ⋙
    HomotopyCategory.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) (0 : ℤ)

/-- Corrected acyclic homotopy objects lie in the forgetful homological kernel. -/
theorem forgetfulHomologicalKernel_of_exactAcyclicWithCyclesHomotopyObject :
    exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0} ≤
      forgetfulHomologyKernelFunctor.homologicalKernel := by
  intro X hX n
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hShiftZero :
      IsZero
        (forgetfulHomologyKernelFunctor.obj
          ((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj
            (K⟦n⟧))) := by
    let Kf : CochainComplex AddCommGrpCat.{0} ℤ :=
      ((forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K⟦n⟧)
    have hKshift : exactAcyclicWithCycles MetrizableLCA.{0} (K⟦n⟧) :=
      exactAcyclicWithCycles_shift MetrizableLCA.{0} K n hX
    have hExactAt : Kf.ExactAt (0 : ℤ) :=
      MetrizableLCA.forgetToAddCommGrpCat_exactAt_of_exactAcyclicWithCycles
        hKshift (0 : ℤ)
    have hZero : IsZero (Kf.homology (0 : ℤ)) :=
      (HomologicalComplex.exactAt_iff_isZero_homology (K := Kf) (i := (0 : ℤ))).mp
        hExactAt
    change
      IsZero
        ((HomotopyCategory.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) (0 : ℤ)).obj
          ((HomotopyCategory.quotient AddCommGrpCat.{0} (ComplexShape.up ℤ)).obj Kf))
    exact IsZero.of_iso hZero
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{0}
        (ComplexShape.up ℤ) (0 : ℤ)).app Kf)
  exact IsZero.of_iso hShiftZero
    (forgetfulHomologyKernelFunctor.mapIso
      (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).commShiftIso n).app
        K).symm)

/-- Input reflecting the forgetful homological kernel back to degreewise exactness in
`MetrizableLCA`. -/
abbrev ExactAcyclicWithCyclesForgetfulHomologicalKernelExactAtInput : Prop :=
  ∀ (K : CochainComplex MetrizableLCA.{0} ℤ),
    forgetfulHomologyKernelFunctor.homologicalKernel
      ((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj K) →
    ∀ i : ℤ, K.ExactAt i

/-- The forgetful homological kernel reflects to degreewise `MetrizableLCA` exactness. -/
theorem forgetfulHomologicalKernelExactAtInput :
    ExactAcyclicWithCyclesForgetfulHomologicalKernelExactAtInput := by
  intro K hKernel i
  letI : CategoryWithHomology MetrizableLCA.{0} :=
    MetrizableLCA.categoryWithHomology_of_leftRightComparisonBijectiveW821
  have hShifted :
      IsZero
        (forgetfulHomologyKernelFunctor.obj
          (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj K)⟦i⟧)) :=
    hKernel i
  have hQShift :
      IsZero
        (forgetfulHomologyKernelFunctor.obj
          ((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj (K⟦i⟧))) := by
    exact IsZero.of_iso hShifted
      (forgetfulHomologyKernelFunctor.mapIso
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).commShiftIso i).app
          K))
  let Kf : CochainComplex AddCommGrpCat.{0} ℤ :=
    ((forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (K⟦i⟧)
  have hQShift' :
      IsZero
        ((HomotopyCategory.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) (0 : ℤ)).obj
          ((HomotopyCategory.quotient AddCommGrpCat.{0} (ComplexShape.up ℤ)).obj Kf)) := by
    exact hQShift
  have hZero : IsZero (Kf.homology (0 : ℤ)) :=
    IsZero.of_iso hQShift'
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{0}
        (ComplexShape.up ℤ) (0 : ℤ)).app Kf).symm
  have hForgetExactAt : Kf.ExactAt (0 : ℤ) :=
    (HomologicalComplex.exactAt_iff_isZero_homology (K := Kf) (i := (0 : ℤ))).mpr
      hZero
  have hShiftExact : (K⟦i⟧).ExactAt (0 : ℤ) :=
    MetrizableLCA.exactAt_of_forgetToAddCommGrpCat_exactAt
      hasHomologyOfComparisonBijectivity hForgetExactAt
  rw [HomologicalComplex.exactAt_iff] at hShiftExact
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_iso
    ((CochainComplex.shiftShortComplexFunctorIso MetrizableLCA.{0} i (0 : ℤ) i
      (by simp)).app K)
    hShiftExact

/-- Global forgetful homology preservation is a compatibility route for the exactness
reflection input.  It is not used by the main corrected route. -/
theorem forgetfulHomologicalKernelExactAtInput_of_preservesHomology
    (forgetPreservesHomology :
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology) :
    ExactAcyclicWithCyclesForgetfulHomologicalKernelExactAtInput := by
  intro K hKernel i
  letI : CategoryWithHomology MetrizableLCA.{0} :=
    MetrizableLCA.categoryWithHomology_of_leftRightComparisonBijectiveW821
  have hShifted :
      IsZero
        (forgetfulHomologyKernelFunctor.obj
          (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj K)⟦i⟧)) :=
    hKernel i
  have hQShift :
      IsZero
        (forgetfulHomologyKernelFunctor.obj
          ((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).obj (K⟦i⟧))) := by
    exact IsZero.of_iso hShifted
      (forgetfulHomologyKernelFunctor.mapIso
        (((HomotopyCategory.quotient MetrizableLCA.{0} (ComplexShape.up ℤ)).commShiftIso i).app
          K))
  let Kf : CochainComplex AddCommGrpCat.{0} ℤ :=
    ((forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (K⟦i⟧)
  have hQShift' :
      IsZero
        ((HomotopyCategory.homologyFunctor AddCommGrpCat.{0} (ComplexShape.up ℤ) (0 : ℤ)).obj
          ((HomotopyCategory.quotient AddCommGrpCat.{0} (ComplexShape.up ℤ)).obj Kf)) := by
    exact hQShift
  have hZero : IsZero (Kf.homology (0 : ℤ)) :=
    IsZero.of_iso hQShift'
      ((HomotopyCategory.homologyFunctorFactors AddCommGrpCat.{0}
        (ComplexShape.up ℤ) (0 : ℤ)).app Kf).symm
  have hForgetExactAt : Kf.ExactAt (0 : ℤ) :=
    (HomologicalComplex.exactAt_iff_isZero_homology (K := Kf) (i := (0 : ℤ))).mpr
      hZero
  rw [HomologicalComplex.exactAt_iff] at hForgetExactAt
  have hShiftExact : (K⟦i⟧).ExactAt (0 : ℤ) := by
    rw [HomologicalComplex.exactAt_iff]
    letI : (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology :=
      forgetPreservesHomology
    exact
      (ShortComplex.exact_iff_exact_map_forget₂
        (S :=
          (HomologicalComplex.sc
            ((shiftFunctor (CochainComplex MetrizableLCA.{0} ℤ) i).obj K) 0))).mpr
        hForgetExactAt
  rw [HomologicalComplex.exactAt_iff] at hShiftExact
  rw [HomologicalComplex.exactAt_iff]
  exact ShortComplex.exact_of_iso
    ((CochainComplex.shiftShortComplexFunctorIso MetrizableLCA.{0} i (0 : ℤ) i
      (by simp)).app K)
    hShiftExact

/-- The remaining direction of the forgetful homological-kernel route. -/
abbrev ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload : Prop :=
  forgetfulHomologyKernelFunctor.homologicalKernel ≤
    exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}

/-- Boundary topology plus forgetful-kernel exactness reflection gives the reverse
forgetful homological-kernel payload. -/
theorem forgetfulHomologicalKernelReversePayload_of_exactAtInput
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0})
    (exactAtInput : ExactAcyclicWithCyclesForgetfulHomologicalKernelExactAtInput) :
    ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload := by
  intro X hKernel
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  exact MetrizableLCA.exactAcyclicWithCycles_of_exactAtCanonicalCycleStrictInput
    (MetrizableLCA.exactAtCanonicalCycleStrictInput_of_boundaryTopologyInput
      hasHomologyOfComparisonBijectivity boundary)
    K (exactAtInput K hKernel)

/-- Boundary topology plus global forgetful homology preservation is a compatibility
reducer for the reverse forgetful-kernel payload. -/
theorem forgetfulHomologicalKernelReversePayload_of_boundaryTopologyPreservesHomology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0})
    (forgetPreservesHomology :
      (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).PreservesHomology) :
    ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload :=
  forgetfulHomologicalKernelReversePayload_of_exactAtInput boundary
    (forgetfulHomologicalKernelExactAtInput_of_preservesHomology forgetPreservesHomology)

/-- Boundary topology now supplies the reverse forgetful-kernel payload, because exactness
reflection from the forgetful homological kernel is checked directly. -/
theorem forgetfulHomologicalKernelReversePayload_of_boundaryTopology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload :=
  forgetfulHomologicalKernelReversePayload_of_exactAtInput boundary
    forgetfulHomologicalKernelExactAtInput

/-- A reverse forgetful-kernel payload identifies the corrected object predicate with the
forgetful homological kernel. -/
theorem exactAcyclicWithCyclesHomotopyObject_eq_forgetfulHomologicalKernel
    (reverse : ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload) :
    ∀ X : HomotopyCategory MetrizableLCA.{0} (ComplexShape.up ℤ),
      exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0} X ↔
        forgetfulHomologyKernelFunctor.homologicalKernel X :=
  fun X => ⟨forgetfulHomologicalKernel_of_exactAcyclicWithCyclesHomotopyObject X,
    reverse X⟩

/-- A reverse forgetful-kernel payload gives corrected homotopy-object `Closed₂`. -/
theorem exactAcyclicWithCyclesHomotopyObjectClosed2OfForgetfulHomologicalKernel
    (reverse : ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload) :
    (exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  exactAcyclicWithCyclesHomotopyObject_isTriangulatedClosed2_of_homologicalKernel
    (C := MetrizableLCA.{0}) (F := forgetfulHomologyKernelFunctor)
    (exactAcyclicWithCyclesHomotopyObject_eq_forgetfulHomologicalKernel reverse)

/-- A reverse forgetful-kernel payload also gives homotopy descent. -/
theorem exactAcyclicWithCyclesHomotopyEquivInvarianceInputOfForgetfulHomologicalKernel
    (reverse : ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload) :
    ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0} := by
  haveI :
      (exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsClosedUnderIsomorphisms :=
    { of_iso := by
        intro X Y e hX
        have hKernelX : forgetfulHomologyKernelFunctor.homologicalKernel X :=
          forgetfulHomologicalKernel_of_exactAcyclicWithCyclesHomotopyObject X hX
        exact reverse Y
          (forgetfulHomologyKernelFunctor.homologicalKernel.prop_of_iso e hKernelX) }
  exact exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_isClosedUnderIsomorphisms
    MetrizableLCA.{0} inferInstance

/--
Product-facing stable bounded-derived data for the corrected metrizable route.

The carrier and weak-equivalence class are recorded as fields so the package cannot be
mistaken for the legacy localization surface.
-/
structure StablePackage : Type 2 where
  quasicategoryCarrier :
    infinityCategory = BoundedDerivedOrdinaryQuasicategoryWithCycles MetrizableLCA.{0}
  weakEquivalenceClass :
    WeakEquivalence = boundedExactWeakEquivalenceWithCycles MetrizableLCA.{0}
  preadditive : Preadditive OrdinaryCategory
  finiteProductInstance : HasFiniteProducts OrdinaryCategory
  finiteBiproductInstance : HasFiniteBiproducts OrdinaryCategory
  finiteCoproductInstance : HasFiniteCoproducts OrdinaryCategory
  finiteLimitInstance : HasFiniteLimits OrdinaryCategory
  finiteColimitInstance : HasFiniteColimits OrdinaryCategory
  zeroObjectInstance : HasZeroObject OrdinaryCategory
  shiftAdditiveAll :
    letI : Preadditive OrdinaryCategory := preadditive
    ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive
  suspensionAdditive :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    (shiftFunctor OrdinaryCategory (1 : ℤ)).Additive
  pretriangulatedStructure :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : HasZeroObject OrdinaryCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    Pretriangulated OrdinaryCategory
  triangulatedStructure :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : HasZeroObject OrdinaryCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory := pretriangulatedStructure
    IsTriangulated OrdinaryCategory

/-- Corrected stable package together with the source-facing left-calculus field. -/
structure StablePackageWithLeftCalculus : Type 2 where
  package : StablePackage
  leftCalculus : WeakEquivalence.HasLeftCalculusOfFractions

/-- Stable semantic fields that do not depend on WPP finite-limit transfer. -/
structure StableCorePackage : Type 2 where
  preadditive : Preadditive OrdinaryCategory
  finiteProductInstance : HasFiniteProducts OrdinaryCategory
  finiteBiproductInstance : HasFiniteBiproducts OrdinaryCategory
  finiteCoproductInstance : HasFiniteCoproducts OrdinaryCategory
  zeroObjectInstance : HasZeroObject OrdinaryCategory
  shiftAdditiveAll :
    letI : Preadditive OrdinaryCategory := preadditive
    ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive
  suspensionAdditive :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    (shiftFunctor OrdinaryCategory (1 : ℤ)).Additive
  pretriangulatedStructure :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : HasZeroObject OrdinaryCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    Pretriangulated OrdinaryCategory
  triangulatedStructure :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : HasZeroObject OrdinaryCategory := zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory := pretriangulatedStructure
    IsTriangulated OrdinaryCategory

/-- The explicit source-facing left-calculus assumption for the corrected weak equivalences. -/
structure LeftCalculusAssumption : Type 1 where
  leftCalculus : WeakEquivalence.HasLeftCalculusOfFractions

/-- The explicit source-facing right-calculus assumption for the corrected weak equivalences. -/
structure RightCalculusAssumption : Type 1 where
  rightCalculus : WeakEquivalence.HasRightCalculusOfFractions

/-- Build corrected left calculus from the homotopy Verdier route inputs. -/
def leftCalculusAssumptionOfHomotopyVerdier
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}) :
    LeftCalculusAssumption where
  leftCalculus :=
    boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint
      MetrizableLCA.{0} descent adjoint

/-- Build corrected right calculus from the homotopy Verdier route inputs. -/
def rightCalculusAssumptionOfHomotopyVerdier
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedLeftAdjointInput MetrizableLCA.{0}) :
    RightCalculusAssumption where
  rightCalculus :=
    boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint
      MetrizableLCA.{0} descent adjoint

/-- Build corrected preadditivity from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev preadditiveOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    Preadditive OrdinaryCategory :=
  DboundedWithCycles.preadditiveOfBoundedVerdierLocalizationInput MetrizableLCA.{0} input

/-- Build a corrected zero object from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasZeroObjectOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasZeroObject OrdinaryCategory :=
  DboundedWithCycles.hasZeroObjectOfBoundedVerdierLocalizationInput MetrizableLCA.{0} input

/-- Build corrected finite products from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasFiniteProductsOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasFiniteProducts OrdinaryCategory :=
  DboundedWithCycles.hasFiniteProductsOfBoundedVerdierLocalizationInput MetrizableLCA.{0} input

/-- Build corrected finite coproducts from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasFiniteCoproductsOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasFiniteCoproducts OrdinaryCategory :=
  DboundedWithCycles.hasFiniteCoproductsOfBoundedVerdierLocalizationInput MetrizableLCA.{0}
    input

/-- Build corrected finite limits from WPP equalizers and the finite products supplied by the
bounded corrected homotopy Verdier localization comparison. -/
abbrev hasFiniteLimitsOfWalkingParallelPairBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (transferInputs :
      DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs)
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasFiniteLimits OrdinaryCategory := by
  letI : HasFiniteProducts OrdinaryCategory :=
    hasFiniteProductsOfBoundedVerdierLocalizationInput input
  letI : HasEqualizers OrdinaryCategory :=
    DboundedWithCycles.MetrizableLCA.hasEqualizersOfWalkingParallelPairTransfer
      transferInputs
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Build corrected finite colimits from WPP coequalizers and the finite coproducts supplied by
the bounded corrected homotopy Verdier localization comparison. -/
abbrev hasFiniteColimitsOfWalkingParallelPairBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (transferInputs :
      DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs)
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    HasFiniteColimits OrdinaryCategory := by
  letI : HasFiniteCoproducts OrdinaryCategory :=
    hasFiniteCoproductsOfBoundedVerdierLocalizationInput input
  letI : HasCoequalizers OrdinaryCategory :=
    DboundedWithCycles.MetrizableLCA.hasCoequalizersOfWalkingParallelPairTransfer
      transferInputs
  exact hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-- Build corrected finite biproducts from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev hasFiniteBiproductsOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    HasFiniteBiproducts OrdinaryCategory :=
  DboundedWithCycles.hasFiniteBiproductsOfBoundedVerdierLocalizationInput MetrizableLCA.{0}
    input

/-- Build corrected shift additivity from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev shiftFunctorAdditiveOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0})
    (n : ℤ) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    (shiftFunctor OrdinaryCategory n).Additive :=
  DboundedWithCycles.shiftFunctor_additiveOfBoundedVerdierLocalizationInput
    MetrizableLCA.{0} input n

/-- Build corrected pretriangulation from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev pretriangulatedOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    letI : HasZeroObject OrdinaryCategory :=
      hasZeroObjectOfBoundedVerdierLocalizationInput input
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      shiftFunctorAdditiveOfBoundedVerdierLocalizationInput input
    Pretriangulated OrdinaryCategory :=
  DboundedWithCycles.pretriangulatedOfBoundedVerdierLocalizationInput
    MetrizableLCA.{0} input

/-- Build corrected triangulation from the bounded corrected homotopy Verdier localization
comparison, without a chain-level left-calculus hypothesis. -/
abbrev isTriangulatedOfBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (input :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    letI : Preadditive OrdinaryCategory :=
      preadditiveOfBoundedVerdierLocalizationInput input
    letI : HasZeroObject OrdinaryCategory :=
      hasZeroObjectOfBoundedVerdierLocalizationInput input
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      shiftFunctorAdditiveOfBoundedVerdierLocalizationInput input
    letI : Pretriangulated OrdinaryCategory :=
      pretriangulatedOfBoundedVerdierLocalizationInput input
    IsTriangulated OrdinaryCategory :=
  DboundedWithCycles.isTriangulatedOfBoundedVerdierLocalizationInput
    MetrizableLCA.{0} input

/-- Bounded homotopy objects over metrizable LCA groups are directly `Closed₂`. -/
abbrev boundedHomotopyClosed2 :
    (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  boundedHomotopyObject_isTriangulatedClosed2_direct MetrizableLCA.{0}

/-- Build bounded-homotopy `Closed₂` from the strict endpoint realization input. -/
abbrev boundedHomotopyClosed2OfTrianglehIso13Realization
    (realize : boundedHomotopyObjectTrianglehIso13Realization MetrizableLCA.{0}) :
    (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  boundedHomotopyObject_isTriangulatedClosed2_of_triangleh_iso13_realization
    MetrizableLCA.{0} realize

/-- Build corrected homotopy-object `Closed₂` from descent and strict realization. -/
abbrev exactAcyclicWithCyclesHomotopyObjectClosed2OfDescentRealization
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (realize :
      exactAcyclicWithCyclesHomotopyIsoClosureTrianglehIso13Realization MetrizableLCA.{0}) :
    (exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
  exactAcyclicWithCyclesHomotopyObject_isTriangulatedClosed2_of_descent_realization
    MetrizableLCA.{0} descent realize

/-- WPP-free stable core fields from a reverse forgetful-kernel payload. -/
def stableCorePackageOfForgetfulKernelReverse
    (reverse : ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload) :
    StableCorePackage := by
  letI : (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    boundedHomotopyClosed2
  let descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0} :=
    exactAcyclicWithCyclesHomotopyEquivInvarianceInputOfForgetfulHomologicalKernel reverse
  letI : (exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyObjectClosed2OfForgetfulHomologicalKernel reverse
  letI : (exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
      MetrizableLCA.{0}
  let boundedInput :=
    BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.ofHomotopy
      MetrizableLCA.{0} descent
      (BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.of_comp
        MetrizableLCA.{0})
  exact
    { preadditive := preadditiveOfBoundedVerdierLocalizationInput boundedInput
      finiteProductInstance := hasFiniteProductsOfBoundedVerdierLocalizationInput boundedInput
      finiteBiproductInstance := hasFiniteBiproductsOfBoundedVerdierLocalizationInput boundedInput
      finiteCoproductInstance := hasFiniteCoproductsOfBoundedVerdierLocalizationInput boundedInput
      zeroObjectInstance := hasZeroObjectOfBoundedVerdierLocalizationInput boundedInput
      shiftAdditiveAll := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput
      suspensionAdditive := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput 1
      pretriangulatedStructure := pretriangulatedOfBoundedVerdierLocalizationInput boundedInput
      triangulatedStructure := isTriangulatedOfBoundedVerdierLocalizationInput boundedInput }

/-- Boundary topology supplies WPP-free stable core fields through the forgetful-kernel route. -/
def stableCorePackageOfForgetfulKernelBoundaryTopology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    StableCorePackage :=
  stableCorePackageOfForgetfulKernelReverse
    (forgetfulHomologicalKernelReversePayload_of_boundaryTopology boundary)

/-- Direct corrected preadditivity from boundary topology, without WPP transfer. -/
@[reducible]
def preadditiveOfForgetfulKernelBoundaryTopology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    Preadditive OrdinaryCategory :=
  (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).preadditive

/-- Direct corrected finite products from boundary topology, without WPP transfer. -/
@[reducible]
def finiteProductsOfForgetfulKernelBoundaryTopology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    HasFiniteProducts OrdinaryCategory :=
  (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).finiteProductInstance

/-- Direct corrected finite coproducts from boundary topology, without WPP transfer. -/
@[reducible]
def finiteCoproductsOfForgetfulKernelBoundaryTopology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    HasFiniteCoproducts OrdinaryCategory :=
  (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).finiteCoproductInstance

/-- Direct corrected pretriangulated structure from boundary topology, without WPP transfer. -/
@[reducible]
def pretriangulatedOfForgetfulKernelBoundaryTopology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    letI : Preadditive OrdinaryCategory :=
      (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).pretriangulatedStructure

/-- Direct corrected triangulated structure from boundary topology, without WPP transfer. -/
@[reducible]
def isTriangulatedOfForgetfulKernelBoundaryTopology
    (boundary : MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}) :
    letI : Preadditive OrdinaryCategory :=
      (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stableCorePackageOfForgetfulKernelBoundaryTopology boundary).triangulatedStructure

/-- Semantic fields supplied by corrected left calculus and corrected finite-product closure. -/
structure LeftCalculusSemanticFields : Type 1 where
  leftCalculus : WeakEquivalence.HasLeftCalculusOfFractions
  preadditive : Preadditive OrdinaryCategory
  zeroObject : HasZeroObject OrdinaryCategory
  finiteProducts : HasFiniteProducts OrdinaryCategory
  finiteBiproducts : HasFiniteBiproducts OrdinaryCategory
  finiteCoproducts : HasFiniteCoproducts OrdinaryCategory
  shiftAdditiveAll :
    letI : Preadditive OrdinaryCategory := preadditive
    ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive
  suspensionAdditive :
    letI : Preadditive OrdinaryCategory := preadditive
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive := shiftAdditiveAll
    (shiftFunctor OrdinaryCategory (1 : ℤ)).Additive

/-- Build the corrected semantic fields that are available from left calculus. -/
def leftCalculusSemanticFields
    (assumption : LeftCalculusAssumption) : LeftCalculusSemanticFields where
  leftCalculus := assumption.leftCalculus
  preadditive := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.preadditiveOfHasLeftCalculusOfFractions MetrizableLCA.{0}
  zeroObject := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasZeroObject
  finiteProducts := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteProducts
  finiteBiproducts := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteBiproducts
  finiteCoproducts := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteCoproducts
  shiftAdditiveAll := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    intro n
    exact DboundedWithCycles.shiftFunctor_additiveOfHasLeftCalculusOfFractions
      MetrizableLCA.{0} n
  suspensionAdditive := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := assumption.leftCalculus
    exact DboundedWithCycles.shiftFunctor_additiveOfHasLeftCalculusOfFractions
      MetrizableLCA.{0} 1

/-- Remaining stable fields for the corrected metrizable route after left calculus. -/
structure RemainingStableSemanticFields (available : LeftCalculusSemanticFields) :
    Type 1 where
  equalizers : HasEqualizers OrdinaryCategory
  coequalizers : HasCoequalizers OrdinaryCategory
  pretriangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated OrdinaryCategory
  triangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory := pretriangulated
    IsTriangulated OrdinaryCategory

/-- Full corrected stable semantic input, split into derived and still-assumed fields. -/
structure StableSemanticInput : Type 1 where
  available : LeftCalculusSemanticFields
  remaining : RemainingStableSemanticFields available

/-- Assemble the full corrected stable semantic input from an explicit left-calculus field. -/
def stableSemanticInputOfLeftCalculus
    (assumption : LeftCalculusAssumption)
    (remaining : RemainingStableSemanticFields (leftCalculusSemanticFields assumption)) :
    StableSemanticInput where
  available := leftCalculusSemanticFields assumption
  remaining := remaining

/-- Transfer data that supplies the finite-shape part of the remaining corrected fields. -/
structure WalkingParallelPairTransferStableSemanticInputs
    (available : LeftCalculusSemanticFields) : Type 1 where
  transferInputs :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs
  pretriangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    Pretriangulated OrdinaryCategory
  triangulated :
    letI : Preadditive OrdinaryCategory := available.preadditive
    letI : HasZeroObject OrdinaryCategory := available.zeroObject
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      available.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory := pretriangulated
    IsTriangulated OrdinaryCategory

/-- WPP finite-shape transfer supplies equalizers and coequalizers for the remaining fields. -/
def remainingStableSemanticFieldsOfWalkingParallelPairTransfer
    {available : LeftCalculusSemanticFields}
    (inputs : WalkingParallelPairTransferStableSemanticInputs available) :
    RemainingStableSemanticFields available where
  equalizers :=
    DboundedWithCycles.MetrizableLCA.hasEqualizersOfWalkingParallelPairTransfer
      inputs.transferInputs
  coequalizers :=
    DboundedWithCycles.MetrizableLCA.hasCoequalizersOfWalkingParallelPairTransfer
      inputs.transferInputs
  pretriangulated := inputs.pretriangulated
  triangulated := inputs.triangulated

/-- Build the corrected stable package from its checked semantic input surface. -/
def stablePackageOfSemanticInput (input : StableSemanticInput) : StablePackage where
  quasicategoryCarrier := rfl
  weakEquivalenceClass := rfl
  preadditive := input.available.preadditive
  finiteProductInstance := input.available.finiteProducts
  finiteBiproductInstance := input.available.finiteBiproducts
  finiteCoproductInstance := input.available.finiteCoproducts
  finiteLimitInstance := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := input.available.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteLimitsOfEqualizers
      input.remaining.equalizers
  finiteColimitInstance := by
    letI : WeakEquivalence.HasLeftCalculusOfFractions := input.available.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteColimitsOfCoequalizers
      input.remaining.coequalizers
  zeroObjectInstance := input.available.zeroObject
  shiftAdditiveAll := input.available.shiftAdditiveAll
  suspensionAdditive := input.available.suspensionAdditive
  pretriangulatedStructure := input.remaining.pretriangulated
  triangulatedStructure := input.remaining.triangulated

/-- Build the corrected stable package directly from left calculus plus remaining fields. -/
def stablePackageOfLeftCalculus
    (assumption : LeftCalculusAssumption)
    (remaining : RemainingStableSemanticFields (leftCalculusSemanticFields assumption)) :
    StablePackage :=
  stablePackageOfSemanticInput (stableSemanticInputOfLeftCalculus assumption remaining)

/-- Assemble the corrected stable input from the homotopy Verdier left-calculus route and WPP
finite-shape transfer. -/
def stableSemanticInputOfHomotopyVerdierWalkingParallelPairTransfer
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0})
    (inputs : WalkingParallelPairTransferStableSemanticInputs
      (leftCalculusSemanticFields
        (leftCalculusAssumptionOfHomotopyVerdier descent adjoint))) :
    StableSemanticInput :=
  stableSemanticInputOfLeftCalculus (leftCalculusAssumptionOfHomotopyVerdier descent adjoint)
    (remainingStableSemanticFieldsOfWalkingParallelPairTransfer inputs)

/-- Build the corrected stable package from the homotopy Verdier left-calculus route and WPP
finite-shape transfer. -/
def stablePackageOfHomotopyVerdierWalkingParallelPairTransfer
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0})
    (inputs : WalkingParallelPairTransferStableSemanticInputs
      (leftCalculusSemanticFields
        (leftCalculusAssumptionOfHomotopyVerdier descent adjoint))) :
    StablePackage :=
  stablePackageOfSemanticInput
    (stableSemanticInputOfHomotopyVerdierWalkingParallelPairTransfer descent adjoint inputs)

/-- Build the corrected stable package from the homotopy Verdier left-calculus route, WPP
finite-shape transfer, and bounded Verdier localized-equivalence input. -/
def stablePackageOfHomotopyVerdierWalkingParallelPairBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0})
    (adjoint : BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0})
    (transferInputs :
      DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs)
    (boundedInput :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    StablePackage where
  quasicategoryCarrier := rfl
  weakEquivalenceClass := rfl
  preadditive := preadditiveOfBoundedVerdierLocalizationInput boundedInput
  finiteProductInstance := hasFiniteProductsOfBoundedVerdierLocalizationInput boundedInput
  finiteBiproductInstance := hasFiniteBiproductsOfBoundedVerdierLocalizationInput boundedInput
  finiteCoproductInstance := hasFiniteCoproductsOfBoundedVerdierLocalizationInput boundedInput
  finiteLimitInstance := by
    let left := leftCalculusAssumptionOfHomotopyVerdier descent adjoint
    letI : WeakEquivalence.HasLeftCalculusOfFractions := left.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteLimitsOfWalkingParallelPairTransfer
      transferInputs
  finiteColimitInstance := by
    let left := leftCalculusAssumptionOfHomotopyVerdier descent adjoint
    letI : WeakEquivalence.HasLeftCalculusOfFractions := left.leftCalculus
    exact DboundedWithCycles.MetrizableLCA.hasFiniteColimitsOfWalkingParallelPairTransfer
      transferInputs
  zeroObjectInstance := hasZeroObjectOfBoundedVerdierLocalizationInput boundedInput
  shiftAdditiveAll := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput
  suspensionAdditive := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput 1
  pretriangulatedStructure := pretriangulatedOfBoundedVerdierLocalizationInput boundedInput
  triangulatedStructure := isTriangulatedOfBoundedVerdierLocalizationInput boundedInput

/-- Build the corrected stable package from WPP finite-shape transfer and the checked bounded
Verdier localized-equivalence input, without a chain-level left-calculus hypothesis. -/
def stablePackageOfWalkingParallelPairBoundedVerdierLocalizationInput
    [(boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂]
    [(exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂]
    (transferInputs :
      DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs)
    (boundedInput :
      BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput MetrizableLCA.{0}) :
    StablePackage where
  quasicategoryCarrier := rfl
  weakEquivalenceClass := rfl
  preadditive := preadditiveOfBoundedVerdierLocalizationInput boundedInput
  finiteProductInstance := hasFiniteProductsOfBoundedVerdierLocalizationInput boundedInput
  finiteBiproductInstance := hasFiniteBiproductsOfBoundedVerdierLocalizationInput boundedInput
  finiteCoproductInstance := hasFiniteCoproductsOfBoundedVerdierLocalizationInput boundedInput
  finiteLimitInstance :=
    hasFiniteLimitsOfWalkingParallelPairBoundedVerdierLocalizationInput
      transferInputs boundedInput
  finiteColimitInstance :=
    hasFiniteColimitsOfWalkingParallelPairBoundedVerdierLocalizationInput
      transferInputs boundedInput
  zeroObjectInstance := hasZeroObjectOfBoundedVerdierLocalizationInput boundedInput
  shiftAdditiveAll := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput
  suspensionAdditive := shiftFunctorAdditiveOfBoundedVerdierLocalizationInput boundedInput 1
  pretriangulatedStructure := pretriangulatedOfBoundedVerdierLocalizationInput boundedInput
  triangulatedStructure := isTriangulatedOfBoundedVerdierLocalizationInput boundedInput

/-- Route-specific inputs that remain before the corrected stable package is fully inhabited. -/
structure RouteSpecificInputs : Type 1 where
  exactAtCanonicalCycleBoundaryTopology :
    MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}
  walkingParallelPairTransfer :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized

/-- Route-specific inputs where canonical boundary openness is supplied by ordinary
differential openness. -/
structure RouteSpecificDifferentialOpenMapInputs : Type 1 where
  exactAtCanonicalCycleDifferentialTopology :
    MetrizableLCA.ExactAtCanonicalCycleDifferentialTopologyInput.{0}
  walkingParallelPairTransfer :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized

/-- Route-specific inputs where canonical boundary openness is supplied by sigma-compact source
objects and the open mapping theorem. -/
structure RouteSpecificSigmaCompactSourceInputs : Type 1 where
  exactAtCanonicalCycleSigmaCompactSourceTopology :
    MetrizableLCA.ExactAtCanonicalCycleSigmaCompactSourceTopologyInput.{0}
  walkingParallelPairTransfer :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized

/-- Ordinary differential openness is one way to supply the route's canonical boundary
open-map input. -/
def routeSpecificInputsOfDifferentialOpenMap
    (inputs : RouteSpecificDifferentialOpenMapInputs) : RouteSpecificInputs where
  exactAtCanonicalCycleBoundaryTopology :=
    MetrizableLCA.exactAtCanonicalCycleBoundaryTopologyInput_of_differentialTopologyInput
      inputs.exactAtCanonicalCycleDifferentialTopology
  walkingParallelPairTransfer := inputs.walkingParallelPairTransfer

/-- Sigma-compact source objects are another way to supply the route's canonical boundary
open-map input. -/
def routeSpecificInputsOfSigmaCompactSource
    (inputs : RouteSpecificSigmaCompactSourceInputs) : RouteSpecificInputs where
  exactAtCanonicalCycleBoundaryTopology :=
    MetrizableLCA.exactAtCanonicalCycleBoundaryTopologyInput_of_sigmaCompactSourceTopologyInput
      inputs.exactAtCanonicalCycleSigmaCompactSourceTopology
  walkingParallelPairTransfer := inputs.walkingParallelPairTransfer

/-- Route-specific inputs give homology detection by their canonical-boundary topology field. -/
def homologyDetectionInputOfRouteSpecificInputs
    (inputs : RouteSpecificInputs) :
    ExactAcyclicWithCyclesHomologyDetectionInput MetrizableLCA.{0} :=
  homologyDetectionInputOfBoundaryTopology inputs.exactAtCanonicalCycleBoundaryTopology

/-- Route-specific inputs identify corrected acyclic homotopy objects with the W821
homological kernel. -/
theorem exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_routeSpecific
    (inputs : RouteSpecificInputs) :
    exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0} =
      comparisonHomologyKernelObject :=
  exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject
    inputs.exactAtCanonicalCycleBoundaryTopology

/-- Differential-open route inputs also identify corrected acyclic homotopy objects with the
W821 homological kernel. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_differential
    (inputs : RouteSpecificDifferentialOpenMapInputs) :
    exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0} =
      comparisonHomologyKernelObject :=
  exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_routeSpecific
    (routeSpecificInputsOfDifferentialOpenMap inputs)

/-- Sigma-compact-source route inputs also identify corrected acyclic homotopy objects with
the W821 homological kernel. -/
theorem
    exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_sigmaCompact
    (inputs : RouteSpecificSigmaCompactSourceInputs) :
    exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0} =
      comparisonHomologyKernelObject :=
  exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_routeSpecific
    (routeSpecificInputsOfSigmaCompactSource inputs)

/-- Extra route input needed only for the source-facing corrected left-calculus field. -/
structure RouteSpecificLeftCalculusInputs : Type 1 extends RouteSpecificInputs where
  localizedRightAdjoint :
    BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}

/-- Differential-open route inputs plus the extra localized right-adjoint field needed for
source-facing corrected left calculus. -/
structure RouteSpecificDifferentialOpenMapLeftCalculusInputs : Type 1
    extends RouteSpecificDifferentialOpenMapInputs where
  localizedRightAdjoint :
    BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}

/-- Sigma-compact-source route inputs plus the extra localized right-adjoint field needed for
source-facing corrected left calculus. -/
structure RouteSpecificSigmaCompactSourceLeftCalculusInputs : Type 1
    extends RouteSpecificSigmaCompactSourceInputs where
  localizedRightAdjoint :
    BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}

/-- Promote differential-open route data to the canonical-boundary-open left-calculus input. -/
def routeSpecificLeftCalculusInputsOfDifferentialOpenMap
    (inputs : RouteSpecificDifferentialOpenMapLeftCalculusInputs) :
    RouteSpecificLeftCalculusInputs where
  toRouteSpecificInputs :=
    routeSpecificInputsOfDifferentialOpenMap inputs.toRouteSpecificDifferentialOpenMapInputs
  localizedRightAdjoint := inputs.localizedRightAdjoint

/-- Promote sigma-compact-source route data to the canonical-boundary-open left-calculus input. -/
def routeSpecificLeftCalculusInputsOfSigmaCompactSource
    (inputs : RouteSpecificSigmaCompactSourceLeftCalculusInputs) :
    RouteSpecificLeftCalculusInputs where
  toRouteSpecificInputs :=
    routeSpecificInputsOfSigmaCompactSource inputs.toRouteSpecificSigmaCompactSourceInputs
  localizedRightAdjoint := inputs.localizedRightAdjoint

/-- Build the corrected stable package from the bundled route-specific inputs. -/
def stablePackageOfRouteSpecificInputs (inputs : RouteSpecificInputs) : StablePackage := by
  letI : (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    boundedHomotopyClosed2
  let homologyDetection : ExactAcyclicWithCyclesHomologyDetectionInput MetrizableLCA.{0} :=
    homologyDetectionInputOfRouteSpecificInputs inputs
  let descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0} :=
    exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_homologyDetection
      MetrizableLCA.{0} homologyDetection
  let boundedInput :=
    BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.ofHomotopy
      MetrizableLCA.{0} descent
      (BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.of_comp
        MetrizableLCA.{0})
  let transferInputs :=
    DboundedWithCycles.MetrizableLCA.walkingParallelPairFiniteShapeTransferInputs_of_normalized
      inputs.walkingParallelPairTransfer
  exact stablePackageOfWalkingParallelPairBoundedVerdierLocalizationInput
    transferInputs boundedInput

/-- Build the corrected stable package from route inputs whose topological component is
ordinary differential openness. -/
def stablePackageOfRouteSpecificDifferentialOpenMapInputs
    (inputs : RouteSpecificDifferentialOpenMapInputs) : StablePackage :=
  stablePackageOfRouteSpecificInputs (routeSpecificInputsOfDifferentialOpenMap inputs)

/-- Build the corrected stable package from route inputs whose topological component is
sigma-compact source data. -/
def stablePackageOfRouteSpecificSigmaCompactSourceInputs
    (inputs : RouteSpecificSigmaCompactSourceInputs) : StablePackage :=
  stablePackageOfRouteSpecificInputs (routeSpecificInputsOfSigmaCompactSource inputs)

/-- Direct corrected finite limits from the bundled route-specific inputs. -/
@[reducible]
def finiteLimitsOfRouteSpecificInputs (inputs : RouteSpecificInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificInputs inputs).finiteLimitInstance

/-- Direct corrected finite colimits from the bundled route-specific inputs. -/
@[reducible]
def finiteColimitsOfRouteSpecificInputs (inputs : RouteSpecificInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificInputs inputs).finiteColimitInstance

/-- Direct corrected pretriangulated structure from the bundled route-specific inputs. -/
@[reducible]
def pretriangulatedOfRouteSpecificInputs (inputs : RouteSpecificInputs) :
    letI : Preadditive OrdinaryCategory := (stablePackageOfRouteSpecificInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificInputs inputs).shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificInputs inputs).pretriangulatedStructure

/-- Direct corrected triangulated structure from the bundled route-specific inputs. -/
@[reducible]
def isTriangulatedOfRouteSpecificInputs (inputs : RouteSpecificInputs) :
    letI : Preadditive OrdinaryCategory := (stablePackageOfRouteSpecificInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificInputs inputs).shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageOfRouteSpecificInputs inputs).pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificInputs inputs).triangulatedStructure

/-- Direct corrected finite limits from differential-open route inputs. -/
@[reducible]
def finiteLimitsOfRouteSpecificDifferentialOpenMapInputs
    (inputs : RouteSpecificDifferentialOpenMapInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).finiteLimitInstance

/-- Direct corrected finite colimits from differential-open route inputs. -/
@[reducible]
def finiteColimitsOfRouteSpecificDifferentialOpenMapInputs
    (inputs : RouteSpecificDifferentialOpenMapInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).finiteColimitInstance

/-- Direct corrected pretriangulated structure from differential-open route inputs. -/
@[reducible]
def pretriangulatedOfRouteSpecificDifferentialOpenMapInputs
    (inputs : RouteSpecificDifferentialOpenMapInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).pretriangulatedStructure

/-- Direct corrected triangulated structure from differential-open route inputs. -/
@[reducible]
def isTriangulatedOfRouteSpecificDifferentialOpenMapInputs
    (inputs : RouteSpecificDifferentialOpenMapInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificDifferentialOpenMapInputs inputs).triangulatedStructure

/-- Direct corrected finite limits from sigma-compact-source route inputs. -/
@[reducible]
def finiteLimitsOfRouteSpecificSigmaCompactSourceInputs
    (inputs : RouteSpecificSigmaCompactSourceInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).finiteLimitInstance

/-- Direct corrected finite colimits from sigma-compact-source route inputs. -/
@[reducible]
def finiteColimitsOfRouteSpecificSigmaCompactSourceInputs
    (inputs : RouteSpecificSigmaCompactSourceInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).finiteColimitInstance

/-- Direct corrected pretriangulated structure from sigma-compact-source route inputs. -/
@[reducible]
def pretriangulatedOfRouteSpecificSigmaCompactSourceInputs
    (inputs : RouteSpecificSigmaCompactSourceInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).pretriangulatedStructure

/-- Direct corrected triangulated structure from sigma-compact-source route inputs. -/
@[reducible]
def isTriangulatedOfRouteSpecificSigmaCompactSourceInputs
    (inputs : RouteSpecificSigmaCompactSourceInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificSigmaCompactSourceInputs inputs).triangulatedStructure

/-- Build the corrected stable package together with corrected left calculus from route inputs. -/
def stablePackageWithLeftCalculusOfRouteSpecificInputs
    (inputs : RouteSpecificLeftCalculusInputs) : StablePackageWithLeftCalculus := by
  let routeInputs : RouteSpecificInputs := inputs.toRouteSpecificInputs
  let homologyDetection : ExactAcyclicWithCyclesHomologyDetectionInput MetrizableLCA.{0} :=
    homologyDetectionInputOfRouteSpecificInputs routeInputs
  let descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0} :=
    exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_homologyDetection
      MetrizableLCA.{0} homologyDetection
  exact
    { package := stablePackageOfRouteSpecificInputs routeInputs
      leftCalculus :=
        (leftCalculusAssumptionOfHomotopyVerdier
          descent inputs.localizedRightAdjoint).leftCalculus }

/-- Direct source-facing corrected left calculus from the bundled route-specific inputs. -/
@[reducible]
def leftCalculusOfRouteSpecificInputs
    (inputs : RouteSpecificLeftCalculusInputs) :
    WeakEquivalence.HasLeftCalculusOfFractions :=
  (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).leftCalculus

/-- Direct corrected finite limits from the same input bundle that gives left calculus. -/
@[reducible]
def finiteLimitsOfRouteSpecificLeftCalculusInputs
    (inputs : RouteSpecificLeftCalculusInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.finiteLimitInstance

/-- Direct corrected finite colimits from the same input bundle that gives left calculus. -/
@[reducible]
def finiteColimitsOfRouteSpecificLeftCalculusInputs
    (inputs : RouteSpecificLeftCalculusInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.finiteColimitInstance

/-- Direct corrected pretriangulated structure from the same input bundle that gives left
calculus. -/
@[reducible]
def pretriangulatedOfRouteSpecificLeftCalculusInputs
    (inputs : RouteSpecificLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.pretriangulatedStructure

/-- Direct corrected triangulated structure from the same input bundle that gives left
calculus. -/
@[reducible]
def isTriangulatedOfRouteSpecificLeftCalculusInputs
    (inputs : RouteSpecificLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificInputs inputs).package.triangulatedStructure

/-- Build the corrected stable package with left calculus from differential-open route inputs. -/
def stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
    (inputs : RouteSpecificDifferentialOpenMapLeftCalculusInputs) :
    StablePackageWithLeftCalculus :=
  stablePackageWithLeftCalculusOfRouteSpecificInputs
    (routeSpecificLeftCalculusInputsOfDifferentialOpenMap inputs)

/-- Build the corrected stable package with left calculus from sigma-compact-source route inputs. -/
def stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
    (inputs : RouteSpecificSigmaCompactSourceLeftCalculusInputs) :
    StablePackageWithLeftCalculus :=
  stablePackageWithLeftCalculusOfRouteSpecificInputs
    (routeSpecificLeftCalculusInputsOfSigmaCompactSource inputs)

/-- Direct source-facing corrected left calculus from differential-open route inputs. -/
@[reducible]
def leftCalculusOfRouteSpecificDifferentialOpenMapInputs
    (inputs : RouteSpecificDifferentialOpenMapLeftCalculusInputs) :
    WeakEquivalence.HasLeftCalculusOfFractions :=
  (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs inputs).leftCalculus

/-- Direct corrected finite limits from differential-open left-calculus route inputs. -/
@[reducible]
def finiteLimitsOfRouteSpecificDifferentialOpenMapLeftCalculusInputs
    (inputs : RouteSpecificDifferentialOpenMapLeftCalculusInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
    inputs).package.finiteLimitInstance

/-- Direct corrected finite colimits from differential-open left-calculus route inputs. -/
@[reducible]
def finiteColimitsOfRouteSpecificDifferentialOpenMapLeftCalculusInputs
    (inputs : RouteSpecificDifferentialOpenMapLeftCalculusInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
    inputs).package.finiteColimitInstance

/-- Direct corrected pretriangulated structure from differential-open left-calculus route
inputs. -/
@[reducible]
def pretriangulatedOfRouteSpecificDifferentialOpenMapLeftCalculusInputs
    (inputs : RouteSpecificDifferentialOpenMapLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
        inputs).package.shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
    inputs).package.pretriangulatedStructure

/-- Direct corrected triangulated structure from differential-open left-calculus route inputs. -/
@[reducible]
def isTriangulatedOfRouteSpecificDifferentialOpenMapLeftCalculusInputs
    (inputs : RouteSpecificDifferentialOpenMapLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
        inputs).package.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
        inputs).package.pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs
    inputs).package.triangulatedStructure

/-- Direct source-facing corrected left calculus from sigma-compact-source route inputs. -/
@[reducible]
def leftCalculusOfRouteSpecificSigmaCompactSourceInputs
    (inputs : RouteSpecificSigmaCompactSourceLeftCalculusInputs) :
    WeakEquivalence.HasLeftCalculusOfFractions :=
  (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs inputs).leftCalculus

/-- Direct corrected finite limits from sigma-compact-source left-calculus route inputs. -/
@[reducible]
def finiteLimitsOfRouteSpecificSigmaCompactSourceLeftCalculusInputs
    (inputs : RouteSpecificSigmaCompactSourceLeftCalculusInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
    inputs).package.finiteLimitInstance

/-- Direct corrected finite colimits from sigma-compact-source left-calculus route inputs. -/
@[reducible]
def finiteColimitsOfRouteSpecificSigmaCompactSourceLeftCalculusInputs
    (inputs : RouteSpecificSigmaCompactSourceLeftCalculusInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
    inputs).package.finiteColimitInstance

/-- Direct corrected pretriangulated structure from sigma-compact-source left-calculus route
inputs. -/
@[reducible]
def pretriangulatedOfRouteSpecificSigmaCompactSourceLeftCalculusInputs
    (inputs : RouteSpecificSigmaCompactSourceLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
        inputs).package.shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
    inputs).package.pretriangulatedStructure

/-- Direct corrected triangulated structure from sigma-compact-source left-calculus route
inputs. -/
@[reducible]
def isTriangulatedOfRouteSpecificSigmaCompactSourceLeftCalculusInputs
    (inputs : RouteSpecificSigmaCompactSourceLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
        inputs).package.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
        inputs).package.pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs
    inputs).package.triangulatedStructure

/-- Alternate route-specific inputs: a reverse forgetful homological-kernel theorem replaces
both boundary topology and strict-realization inputs. -/
structure RouteSpecificForgetfulKernelInputs : Type 1 where
  forgetfulKernelReverse : ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload
  walkingParallelPairTransfer :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized

/-- Alternate forgetful-kernel route plus the extra localized right-adjoint field needed for
source-facing corrected left calculus. -/
structure RouteSpecificForgetfulKernelLeftCalculusInputs : Type 1
    extends RouteSpecificForgetfulKernelInputs where
  localizedRightAdjoint :
    BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}

/-- Alternate forgetful-kernel route after exactness reflection has been discharged. -/
structure RouteSpecificForgetfulKernelBoundaryInputs : Type 1 where
  exactAtCanonicalCycleBoundaryTopology :
    MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}
  walkingParallelPairTransfer :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized

/-- Boundary-only forgetful-kernel route plus the localized right-adjoint field needed for
source-facing corrected left calculus. -/
structure RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs : Type 1
    extends RouteSpecificForgetfulKernelBoundaryInputs where
  localizedRightAdjoint :
    BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}

/-- Alternate forgetful-kernel route with the reverse payload decomposed into exactness
reflection plus canonical boundary topology. -/
structure RouteSpecificForgetfulKernelExactAtInputs : Type 1 where
  exactAtCanonicalCycleBoundaryTopology :
    MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput.{0}
  forgetfulKernelExactAt :
    ExactAcyclicWithCyclesForgetfulHomologicalKernelExactAtInput
  walkingParallelPairTransfer :
    DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized

/-- Exactness-reflection forgetful-kernel route plus the extra localized right-adjoint field
needed for source-facing corrected left calculus. -/
structure RouteSpecificForgetfulKernelExactAtLeftCalculusInputs : Type 1
    extends RouteSpecificForgetfulKernelExactAtInputs where
  localizedRightAdjoint :
    BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA.{0}

/-- Convert exactness-reflection route data to the reverse-payload forgetful-kernel route. -/
def routeSpecificForgetfulKernelInputsOfExactAt
    (inputs : RouteSpecificForgetfulKernelExactAtInputs) :
    RouteSpecificForgetfulKernelInputs where
  forgetfulKernelReverse :=
    forgetfulHomologicalKernelReversePayload_of_exactAtInput
      inputs.exactAtCanonicalCycleBoundaryTopology inputs.forgetfulKernelExactAt
  walkingParallelPairTransfer := inputs.walkingParallelPairTransfer

/-- Convert exactness-reflection route data to the full reverse-payload forgetful-kernel route
with source-facing left calculus. -/
def routeSpecificForgetfulKernelLeftCalculusInputsOfExactAt
    (inputs : RouteSpecificForgetfulKernelExactAtLeftCalculusInputs) :
    RouteSpecificForgetfulKernelLeftCalculusInputs where
  toRouteSpecificForgetfulKernelInputs :=
    routeSpecificForgetfulKernelInputsOfExactAt
      inputs.toRouteSpecificForgetfulKernelExactAtInputs
  localizedRightAdjoint := inputs.localizedRightAdjoint

/-- Convert boundary-only route data to the reverse-payload forgetful-kernel route. -/
def routeSpecificForgetfulKernelInputsOfBoundary
    (inputs : RouteSpecificForgetfulKernelBoundaryInputs) :
    RouteSpecificForgetfulKernelInputs where
  forgetfulKernelReverse :=
    forgetfulHomologicalKernelReversePayload_of_boundaryTopology
      inputs.exactAtCanonicalCycleBoundaryTopology
  walkingParallelPairTransfer := inputs.walkingParallelPairTransfer

/-- Convert boundary-only route data to the full reverse-payload forgetful-kernel route with
source-facing left calculus. -/
def routeSpecificForgetfulKernelLeftCalculusInputsOfBoundary
    (inputs : RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs) :
    RouteSpecificForgetfulKernelLeftCalculusInputs where
  toRouteSpecificForgetfulKernelInputs :=
    routeSpecificForgetfulKernelInputsOfBoundary
      inputs.toRouteSpecificForgetfulKernelBoundaryInputs
  localizedRightAdjoint := inputs.localizedRightAdjoint

/-- Build the corrected stable package from the alternate forgetful-kernel route. -/
def stablePackageOfRouteSpecificForgetfulKernelInputs
    (inputs : RouteSpecificForgetfulKernelInputs) : StablePackage := by
  letI : (boundedHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    boundedHomotopyClosed2
  let descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0} :=
    exactAcyclicWithCyclesHomotopyEquivInvarianceInputOfForgetfulHomologicalKernel
      inputs.forgetfulKernelReverse
  letI : (exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyObjectClosed2OfForgetfulHomologicalKernel
      inputs.forgetfulKernelReverse
  letI : (exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
      MetrizableLCA.{0}
  let boundedInput :=
    BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.ofHomotopy
      MetrizableLCA.{0} descent
      (BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.of_comp
        MetrizableLCA.{0})
  let transferInputs :=
    DboundedWithCycles.MetrizableLCA.walkingParallelPairFiniteShapeTransferInputs_of_normalized
      inputs.walkingParallelPairTransfer
  exact stablePackageOfWalkingParallelPairBoundedVerdierLocalizationInput
    transferInputs boundedInput

/-- Build the corrected stable package with left calculus from the alternate
forgetful-kernel route. -/
def stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
    (inputs : RouteSpecificForgetfulKernelLeftCalculusInputs) :
    StablePackageWithLeftCalculus := by
  let routeInputs : RouteSpecificForgetfulKernelInputs :=
    inputs.toRouteSpecificForgetfulKernelInputs
  let descent : ExactAcyclicWithCyclesHomotopyEquivInvarianceInput MetrizableLCA.{0} :=
    exactAcyclicWithCyclesHomotopyEquivInvarianceInputOfForgetfulHomologicalKernel
      routeInputs.forgetfulKernelReverse
  letI : (exactAcyclicWithCyclesHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyObjectClosed2OfForgetfulHomologicalKernel
      routeInputs.forgetfulKernelReverse
  letI : (exactAcyclicWithCyclesHomotopyIsoClosure MetrizableLCA.{0}).IsTriangulatedClosed₂ :=
    exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
      MetrizableLCA.{0}
  exact
    { package := stablePackageOfRouteSpecificForgetfulKernelInputs routeInputs
      leftCalculus :=
        (leftCalculusAssumptionOfHomotopyVerdier
          descent inputs.localizedRightAdjoint).leftCalculus }

/-- Direct source-facing corrected left calculus from the alternate forgetful-kernel route. -/
@[reducible]
def leftCalculusOfRouteSpecificForgetfulKernelInputs
    (inputs : RouteSpecificForgetfulKernelLeftCalculusInputs) :
    WeakEquivalence.HasLeftCalculusOfFractions :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs inputs).leftCalculus

/-- Direct corrected finite limits from the alternate forgetful-kernel left-calculus route. -/
@[reducible]
def finiteLimitsOfRouteSpecificForgetfulKernelLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelLeftCalculusInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
    inputs).package.finiteLimitInstance

/-- Direct corrected finite colimits from the alternate forgetful-kernel left-calculus route. -/
@[reducible]
def finiteColimitsOfRouteSpecificForgetfulKernelLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelLeftCalculusInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
    inputs).package.finiteColimitInstance

/-- Direct corrected pretriangulated structure from the alternate forgetful-kernel
left-calculus route. -/
@[reducible]
def pretriangulatedOfRouteSpecificForgetfulKernelLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
        inputs).package.shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
    inputs).package.pretriangulatedStructure

/-- Direct corrected triangulated structure from the alternate forgetful-kernel
left-calculus route. -/
@[reducible]
def isTriangulatedOfRouteSpecificForgetfulKernelLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
        inputs).package.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
        inputs).package.pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
    inputs).package.triangulatedStructure

/-- Build the corrected stable package from the exactness-reflection forgetful-kernel route. -/
def stablePackageOfRouteSpecificForgetfulKernelExactAtInputs
    (inputs : RouteSpecificForgetfulKernelExactAtInputs) : StablePackage :=
  stablePackageOfRouteSpecificForgetfulKernelInputs
    (routeSpecificForgetfulKernelInputsOfExactAt inputs)

/-- Build the corrected stable package with left calculus from the exactness-reflection
forgetful-kernel route. -/
def stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
    (inputs : RouteSpecificForgetfulKernelExactAtLeftCalculusInputs) :
    StablePackageWithLeftCalculus :=
  stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
    (routeSpecificForgetfulKernelLeftCalculusInputsOfExactAt inputs)

/-- Build the corrected stable package from boundary topology and WPP transfer. -/
def stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryInputs) : StablePackage :=
  stablePackageOfRouteSpecificForgetfulKernelInputs
    (routeSpecificForgetfulKernelInputsOfBoundary inputs)

/-- Build the corrected stable package with left calculus from boundary topology, WPP transfer,
and localized right-adjoint data. -/
def stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs) :
    StablePackageWithLeftCalculus :=
  stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs
    (routeSpecificForgetfulKernelLeftCalculusInputsOfBoundary inputs)

/-- Direct corrected finite limits from the boundary-only forgetful-kernel route. -/
@[reducible]
def finiteLimitsOfRouteSpecificForgetfulKernelBoundaryInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).finiteLimitInstance

/-- Direct corrected finite colimits from the boundary-only forgetful-kernel route. -/
@[reducible]
def finiteColimitsOfRouteSpecificForgetfulKernelBoundaryInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).finiteColimitInstance

/-- Direct corrected pretriangulated structure from the boundary-only forgetful-kernel route. -/
@[reducible]
def pretriangulatedOfRouteSpecificForgetfulKernelBoundaryInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).pretriangulatedStructure

/-- Direct corrected triangulated structure from the boundary-only forgetful-kernel route. -/
@[reducible]
def isTriangulatedOfRouteSpecificForgetfulKernelBoundaryInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs inputs).triangulatedStructure

/-- Direct source-facing corrected left calculus from the boundary-only forgetful-kernel route. -/
@[reducible]
def leftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs) :
    WeakEquivalence.HasLeftCalculusOfFractions :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
    inputs).leftCalculus

/-- Direct corrected finite limits from the boundary-only forgetful-kernel left-calculus route. -/
@[reducible]
def finiteLimitsOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
    inputs).package.finiteLimitInstance

/-- Direct corrected finite colimits from the boundary-only forgetful-kernel left-calculus route. -/
@[reducible]
def finiteColimitsOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
    inputs).package.finiteColimitInstance

/-- Direct corrected pretriangulated structure from the boundary-only forgetful-kernel
left-calculus route. -/
@[reducible]
def pretriangulatedOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
        inputs).package.shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
    inputs).package.pretriangulatedStructure

/-- Direct corrected triangulated structure from the boundary-only forgetful-kernel
left-calculus route. -/
@[reducible]
def isTriangulatedOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
        inputs).package.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
        inputs).package.pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs
    inputs).package.triangulatedStructure

/-- Direct corrected finite limits from the exactness-reflection forgetful-kernel route. -/
@[reducible]
def finiteLimitsOfRouteSpecificForgetfulKernelExactAtInputs
    (inputs : RouteSpecificForgetfulKernelExactAtInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).finiteLimitInstance

/-- Direct corrected finite colimits from the exactness-reflection forgetful-kernel route. -/
@[reducible]
def finiteColimitsOfRouteSpecificForgetfulKernelExactAtInputs
    (inputs : RouteSpecificForgetfulKernelExactAtInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).finiteColimitInstance

/-- Direct corrected pretriangulated structure from the exactness-reflection
forgetful-kernel route. -/
@[reducible]
def pretriangulatedOfRouteSpecificForgetfulKernelExactAtInputs
    (inputs : RouteSpecificForgetfulKernelExactAtInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).pretriangulatedStructure

/-- Direct corrected triangulated structure from the exactness-reflection forgetful-kernel
route. -/
@[reducible]
def isTriangulatedOfRouteSpecificForgetfulKernelExactAtInputs
    (inputs : RouteSpecificForgetfulKernelExactAtInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageOfRouteSpecificForgetfulKernelExactAtInputs inputs).triangulatedStructure

/-- Direct source-facing corrected left calculus from the exactness-reflection
forgetful-kernel route. -/
@[reducible]
def leftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
    (inputs : RouteSpecificForgetfulKernelExactAtLeftCalculusInputs) :
    WeakEquivalence.HasLeftCalculusOfFractions :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
    inputs).leftCalculus

/-- Direct corrected finite limits from the exactness-reflection forgetful-kernel
left-calculus route. -/
@[reducible]
def finiteLimitsOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelExactAtLeftCalculusInputs) :
    HasFiniteLimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
    inputs).package.finiteLimitInstance

/-- Direct corrected finite colimits from the exactness-reflection forgetful-kernel
left-calculus route. -/
@[reducible]
def finiteColimitsOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelExactAtLeftCalculusInputs) :
    HasFiniteColimits OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
    inputs).package.finiteColimitInstance

/-- Direct corrected pretriangulated structure from the exactness-reflection
forgetful-kernel left-calculus route. -/
@[reducible]
def pretriangulatedOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelExactAtLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
        inputs).package.shiftAdditiveAll
    Pretriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
    inputs).package.pretriangulatedStructure

/-- Direct corrected triangulated structure from the exactness-reflection forgetful-kernel
left-calculus route. -/
@[reducible]
def isTriangulatedOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs
    (inputs : RouteSpecificForgetfulKernelExactAtLeftCalculusInputs) :
    letI : Preadditive OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
        inputs).package.preadditive
    letI : HasZeroObject OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
        inputs).package.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor OrdinaryCategory n).Additive :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
        inputs).package.shiftAdditiveAll
    letI : Pretriangulated OrdinaryCategory :=
      (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
        inputs).package.pretriangulatedStructure
    IsTriangulated OrdinaryCategory :=
  (stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs
    inputs).package.triangulatedStructure

/-- Names of route-specific inputs still to discharge for a fully inhabited corrected package. -/
def routeSpecificInputNames : List String :=
  ["MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput",
    "DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized"]

/-- Two route-specific inputs remain before the conditional raw-localization package is
inhabited. -/
theorem routeSpecificInputNames_count :
    routeSpecificInputNames.length = 2 :=
  rfl

/-- Names of route-specific inputs still to discharge for the full corrected package with
source-facing left calculus. -/
def routeSpecificLeftCalculusInputNames : List String :=
  routeSpecificInputNames ++
    ["BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA"]

/-- Three route-specific inputs remain before corrected raw-chain left calculus is inhabited. -/
theorem routeSpecificLeftCalculusInputNames_count :
    routeSpecificLeftCalculusInputNames.length = 3 :=
  rfl

/-- Names of inputs still to discharge for the alternate forgetful-kernel stable route. -/
def routeSpecificForgetfulKernelInputNames : List String :=
  ["ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload",
    "DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized"]

/-- Two inputs remain for the alternate forgetful-kernel stable semantic package. -/
theorem routeSpecificForgetfulKernelInputNames_count :
    routeSpecificForgetfulKernelInputNames.length = 2 :=
  rfl

/-- Names of inputs for the boundary-only forgetful-kernel stable route. -/
def routeSpecificForgetfulKernelBoundaryInputNames : List String :=
  ["MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput",
    "DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized"]

/-- Two inputs remain for the boundary-only forgetful-kernel stable package. -/
theorem routeSpecificForgetfulKernelBoundaryInputNames_count :
    routeSpecificForgetfulKernelBoundaryInputNames.length = 2 :=
  rfl

/-- Names of inputs for the exactness-reflection forgetful-kernel stable route. -/
def routeSpecificForgetfulKernelExactAtInputNames : List String :=
  ["MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput",
    "ExactAcyclicWithCyclesForgetfulHomologicalKernelExactAtInput",
    "DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized"]

/-- Three inputs remain for the exactness-reflection forgetful-kernel stable package. -/
theorem routeSpecificForgetfulKernelExactAtInputNames_count :
    routeSpecificForgetfulKernelExactAtInputNames.length = 3 :=
  rfl

/-- Names of inputs still to discharge for the alternate forgetful-kernel route with
source-facing left calculus. -/
def routeSpecificForgetfulKernelLeftCalculusInputNames : List String :=
  routeSpecificForgetfulKernelInputNames ++
    ["BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA"]

/-- Three inputs remain for the alternate forgetful-kernel package with left calculus. -/
theorem routeSpecificForgetfulKernelLeftCalculusInputNames_count :
    routeSpecificForgetfulKernelLeftCalculusInputNames.length = 3 :=
  rfl

/-- Names of inputs still to discharge for the boundary-only forgetful-kernel route with
source-facing left calculus. -/
def routeSpecificForgetfulKernelBoundaryLeftCalculusInputNames : List String :=
  routeSpecificForgetfulKernelBoundaryInputNames ++
    ["BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA"]

/-- Three inputs remain for the boundary-only forgetful-kernel package with left calculus. -/
theorem routeSpecificForgetfulKernelBoundaryLeftCalculusInputNames_count :
    routeSpecificForgetfulKernelBoundaryLeftCalculusInputNames.length = 3 :=
  rfl

/-- Names of inputs still to discharge for the exactness-reflection forgetful-kernel route
with source-facing left calculus. -/
def routeSpecificForgetfulKernelExactAtLeftCalculusInputNames : List String :=
  routeSpecificForgetfulKernelExactAtInputNames ++
    ["BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA"]

/-- Four inputs remain for the exactness-reflection forgetful-kernel package with left
calculus. -/
theorem routeSpecificForgetfulKernelExactAtLeftCalculusInputNames_count :
    routeSpecificForgetfulKernelExactAtLeftCalculusInputNames.length = 4 :=
  rfl

/-- The corrected stable package carrier is the corrected ordinary quasicategory nerve. -/
theorem stablePackage_carrier (P : StablePackage) :
    P.quasicategoryCarrier = rfl :=
  rfl

/-- The corrected stable package records the corrected weak-equivalence class. -/
theorem stablePackage_weakEquivalenceClass (P : StablePackage) :
    P.weakEquivalenceClass = rfl :=
  rfl

/-- Names of semantic fields derived from corrected left calculus in this bridge. -/
def leftCalculusSemanticFieldNames : List String :=
  ["(boundedExactWeakEquivalenceWithCycles MetrizableLCA).HasLeftCalculusOfFractions",
    "Preadditive (DboundedWithCycles MetrizableLCA)",
    "HasZeroObject (DboundedWithCycles MetrizableLCA)",
    "HasFiniteProducts (DboundedWithCycles MetrizableLCA)",
    "HasFiniteBiproducts (DboundedWithCycles MetrizableLCA)",
    "HasFiniteCoproducts (DboundedWithCycles MetrizableLCA)",
    "forall n, (shiftFunctor (DboundedWithCycles MetrizableLCA) n).Additive",
    "(shiftFunctor (DboundedWithCycles MetrizableLCA) 1).Additive"]

/-- Corrected left calculus currently supplies eight named semantic fields. -/
theorem leftCalculusSemanticFieldNames_count :
    leftCalculusSemanticFieldNames.length = 8 :=
  rfl

/-- Remaining stable assumptions for the corrected route after the fields above. -/
def remainingStableSemanticFieldNames : List String :=
  ["HasEqualizers (DboundedWithCycles MetrizableLCA)",
    "HasCoequalizers (DboundedWithCycles MetrizableLCA)",
    "Pretriangulated (DboundedWithCycles MetrizableLCA)",
    "IsTriangulated (DboundedWithCycles MetrizableLCA)"]

/-- Four stable semantic fields remain explicit in this checked corrected bridge. -/
theorem remainingStableSemanticFieldNames_count :
    remainingStableSemanticFieldNames.length = 4 :=
  rfl

/-- Current corrected bridge state: the assumption surface is checked, not inhabited. -/
def currentMetrizableStableBridgeWithCyclesProductSuccessClaimed : Bool :=
  false

/-- The corrected bridge does not claim product success without the remaining inputs. -/
theorem currentMetrizableStableBridgeWithCycles_productSuccess :
    currentMetrizableStableBridgeWithCyclesProductSuccessClaimed = false :=
  rfl

end Metrizable
end BoundedDerivedWithCycles

end LeanLCAExactChallenge
