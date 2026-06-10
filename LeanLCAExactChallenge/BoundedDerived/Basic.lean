import LeanLCAExactChallenge.Derived.Bounded

/-!
Short product-facing API for the bounded derived category.

This file names the ordinary localization, its quasicategory nerve, and the
metrizable LCA specialization without route-history terminology.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace BoundedDerived

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- The ordinary category `D^b(C, E)` obtained from bounded complexes by exact localization. -/
abbrev OrdinaryCategory [HasBinaryBiproducts C] : Type (max u v) :=
  Dbounded C

/-- The localization functor from bounded complexes to `D^b(C, E)`. -/
abbrev localization [HasBinaryBiproducts C] :
    (boundedCochainComplex C).FullSubcategory ⥤ BoundedDerived.OrdinaryCategory C :=
  Dbounded.localization C

/-- Promote a bounded cochain complex to `D^b(C, E)`. -/
abbrev of [HasBinaryBiproducts C]
    (K : (boundedCochainComplex C).FullSubcategory) : BoundedDerived.OrdinaryCategory C :=
  Dbounded.of C K

/-- The ordinary quasicategory nerve attached to `D^b(C, E)`. -/
noncomputable abbrev infinityCategory [HasBinaryBiproducts C] : SSet.QCat :=
  Dbounded.infinityCategory C

/-- The underlying simplicial set of the bounded derived quasicategory. -/
noncomputable abbrev infinityNerve [HasBinaryBiproducts C] : SSet :=
  Dbounded.infinityNerve C

/-- The bounded derived nerve is a quasicategory. -/
theorem infinityNerve_quasicategory [HasBinaryBiproducts C] :
    SSet.Quasicategory (BoundedDerived.infinityNerve C) :=
  Dbounded.infinityNerve_quasicategory (C := C)

/-- The homotopy category of the bounded derived quasicategory recovers `D^b(C, E)`. -/
noncomputable def homotopyCategoryIso [HasBinaryBiproducts C] :
    SSet.hoFunctor.obj (BoundedDerived.infinityNerve C) ≅
      Cat.of (BoundedDerived.OrdinaryCategory C) :=
  Dbounded.homotopyCategoryIso (C := C)

namespace Metrizable

/-- Bounded cochain complexes over metrizable LCA groups. -/
abbrev ComplexCategory : Type 1 :=
  Dbounded.MetrizableBoundedComplexCategory

/-- The ordinary bounded derived category `D^b(MetrizableLCA, E)`. -/
abbrev OrdinaryCategory : Type 1 :=
  Dbounded.MetrizableCategory

/-- The localization functor defining `D^b(MetrizableLCA, E)`. -/
abbrev localization : BoundedDerived.Metrizable.ComplexCategory ⥤
    BoundedDerived.Metrizable.OrdinaryCategory :=
  Dbounded.metrizableLocalization

/-- Promote a bounded metrizable LCA cochain complex to `D^b(MetrizableLCA, E)`. -/
abbrev of (K : BoundedDerived.Metrizable.ComplexCategory) :
    BoundedDerived.Metrizable.OrdinaryCategory :=
  Dbounded.metrizableOf K

/-- The bounded derived quasicategory attached to metrizable LCA groups. -/
noncomputable abbrev infinityCategory : SSet.QCat :=
  Dbounded.metrizableInfinityCategory

/-- The underlying simplicial set of the metrizable LCA bounded derived quasicategory. -/
noncomputable abbrev infinityNerve : SSet :=
  Dbounded.metrizableInfinityNerve

/-- The metrizable LCA bounded derived nerve is a quasicategory. -/
theorem infinityNerve_quasicategory :
    SSet.Quasicategory BoundedDerived.Metrizable.infinityNerve :=
  Dbounded.metrizableInfinityNerve_quasicategory

/-- The homotopy category of the metrizable LCA bounded derived quasicategory is the
localized bounded derived category. -/
noncomputable def homotopyCategoryIso :
    SSet.hoFunctor.obj BoundedDerived.Metrizable.infinityNerve ≅
      Cat.of BoundedDerived.Metrizable.OrdinaryCategory :=
  Dbounded.metrizableHomotopyCategoryIso

/-- Bounded exact weak equivalences for `D^b(MetrizableLCA, E)`. -/
noncomputable abbrev WeakEquivalence :
    MorphismProperty BoundedDerived.Metrizable.ComplexCategory :=
  Dbounded.metrizableWeakEquivalence

/-- Exact-acyclic mapping-cone condition for a bounded metrizable LCA morphism. -/
abbrev exactAcyclicMappingCone
    {K L : BoundedDerived.Metrizable.ComplexCategory} (f : K ⟶ L) : Prop :=
  Dbounded.metrizableExactAcyclicMappingCone f

/-- Metrizable bounded weak equivalences are exactly exact-acyclic mapping-cone morphisms. -/
theorem weakEquivalence_iff_exactAcyclicMappingCone
    {K L : BoundedDerived.Metrizable.ComplexCategory} (f : K ⟶ L) :
    BoundedDerived.Metrizable.WeakEquivalence f ↔
      BoundedDerived.Metrizable.exactAcyclicMappingCone f :=
  Dbounded.metrizableWeakEquivalence_iff_exactAcyclicMappingCone f

/-- Stable bounded-derived package type for `D^b(MetrizableLCA, E)`. -/
abbrev StablePackage : Type 2 :=
  BoundedDerivedInfinityCategory MetrizableLCA.{0}
    (BoundedDerived.Metrizable.infinityCategory)

/-- The carrier of a stable metrizable bounded-derived package is the canonical nerve. -/
theorem stablePackage_carrier (P : BoundedDerived.Metrizable.StablePackage) :
    P.quasicategoryCarrier = rfl :=
  rfl

/-- Extract the preadditive structure from a stable metrizable bounded-derived package. -/
abbrev stablePackage_preadditive (P : BoundedDerived.Metrizable.StablePackage) :
    Preadditive BoundedDerived.Metrizable.OrdinaryCategory :=
  P.preadditive

/-- Extract finite limits from a stable metrizable bounded-derived package. -/
theorem stablePackage_finiteLimits (P : BoundedDerived.Metrizable.StablePackage) :
    HasFiniteLimits BoundedDerived.Metrizable.OrdinaryCategory :=
  P.finiteLimitInstance

/-- Extract finite colimits from a stable metrizable bounded-derived package. -/
theorem stablePackage_finiteColimits (P : BoundedDerived.Metrizable.StablePackage) :
    HasFiniteColimits BoundedDerived.Metrizable.OrdinaryCategory :=
  P.finiteColimitInstance

/-- Extract the zero object from a stable metrizable bounded-derived package. -/
theorem stablePackage_zeroObject (P : BoundedDerived.Metrizable.StablePackage) :
    HasZeroObject BoundedDerived.Metrizable.OrdinaryCategory :=
  P.zeroObjectInstance

/-- Extract shift additivity from a stable metrizable bounded-derived package. -/
theorem stablePackage_shiftAdditive (P : BoundedDerived.Metrizable.StablePackage) (n : ℤ) :
    letI : Preadditive BoundedDerived.Metrizable.OrdinaryCategory := P.preadditive
    (shiftFunctor BoundedDerived.Metrizable.OrdinaryCategory n).Additive :=
  P.shiftAdditiveAll n

/-- Extract suspension additivity from a stable metrizable bounded-derived package. -/
theorem stablePackage_suspensionAdditive (P : BoundedDerived.Metrizable.StablePackage) :
    letI : Preadditive BoundedDerived.Metrizable.OrdinaryCategory := P.preadditive
    letI : ∀ n : ℤ, (shiftFunctor BoundedDerived.Metrizable.OrdinaryCategory n).Additive :=
      P.shiftAdditiveAll
    (shiftFunctor BoundedDerived.Metrizable.OrdinaryCategory (1 : ℤ)).Additive :=
  P.suspensionAdditive

/-- Extract the pretriangulated structure from a stable metrizable bounded-derived package. -/
abbrev stablePackage_pretriangulated (P : BoundedDerived.Metrizable.StablePackage) :
    letI : Preadditive BoundedDerived.Metrizable.OrdinaryCategory := P.preadditive
    letI : HasZeroObject BoundedDerived.Metrizable.OrdinaryCategory := P.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor BoundedDerived.Metrizable.OrdinaryCategory n).Additive :=
      P.shiftAdditiveAll
    Pretriangulated BoundedDerived.Metrizable.OrdinaryCategory :=
  P.pretriangulatedStructure

/-- Extract the triangulated structure from a stable metrizable bounded-derived package. -/
theorem stablePackage_triangulated (P : BoundedDerived.Metrizable.StablePackage) :
    letI : Preadditive BoundedDerived.Metrizable.OrdinaryCategory := P.preadditive
    letI : HasZeroObject BoundedDerived.Metrizable.OrdinaryCategory := P.zeroObjectInstance
    letI : ∀ n : ℤ, (shiftFunctor BoundedDerived.Metrizable.OrdinaryCategory n).Additive :=
      P.shiftAdditiveAll
    letI : Pretriangulated BoundedDerived.Metrizable.OrdinaryCategory :=
      P.pretriangulatedStructure
    IsTriangulated BoundedDerived.Metrizable.OrdinaryCategory :=
  P.triangulatedStructure

/-- Forget a stable metrizable bounded-derived package back to the ordinary
semantic input used by the four-projection stable certificate gate. -/
noncomputable def stablePackage_ordinaryStableSemanticInput
    (P : BoundedDerived.Metrizable.StablePackage) :
    Dbounded.MetrizableOrdinaryStableSemanticInput where
  preadditive := P.preadditive
  finiteLimits := P.finiteLimitInstance
  finiteColimits := P.finiteColimitInstance
  zeroObject := P.zeroObjectInstance
  shiftAdditiveAll := P.shiftAdditiveAll
  suspensionAdditive := P.suspensionAdditive
  pretriangulated := P.pretriangulatedStructure
  triangulated := P.triangulatedStructure

/-- Rebuilding the stable package from its ordinary semantic fields recovers the
same product-facing stable package. -/
theorem stablePackage_of_ordinaryStableSemanticInput
    (P : BoundedDerived.Metrizable.StablePackage) :
    Dbounded.boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
        (stablePackage_ordinaryStableSemanticInput P) =
      P :=
  rfl

/-- The four-projection stable certificate extracted from a stable package is ready. -/
theorem stablePackage_fourProjectionCertificate_ready
    (P : BoundedDerived.Metrizable.StablePackage) :
    (Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput
      (stablePackage_ordinaryStableSemanticInput P)).ready :=
  Dbounded.stableFourProjectionCertificateOfMetrizableOrdinaryInput_ready
    (stablePackage_ordinaryStableSemanticInput P)

/-- Any stable package supplies the accepted stable `Dbounded` gate object. -/
noncomputable def stablePackage_acceptedStable
    (P : BoundedDerived.Metrizable.StablePackage) :
    Dbounded.AcceptedStableBoundedDerivedInfinityCategory MetrizableLCA.{0} :=
  Dbounded.acceptedStableBoundedDerivedInfinityCategoryOfMetrizableOrdinaryInput
    (stablePackage_ordinaryStableSemanticInput P)

/-- The accepted gate object extracted from a stable package is accepted by the
stable route gate. -/
theorem stablePackage_acceptedStable_routeAccepted
    (P : BoundedDerived.Metrizable.StablePackage) :
    Dbounded.StableRouteAttempt.accepted (C := MetrizableLCA.{0})
        (.fullCertificate (stablePackage_acceptedStable P).certificate) =
      true :=
  (stablePackage_acceptedStable P).accepted

end Metrizable

end BoundedDerived

end LeanLCAExactChallenge
