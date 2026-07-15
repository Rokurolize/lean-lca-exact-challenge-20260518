/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableEquivalenceForcing

/-!
# The ordinary localization comparison induced by equivalence forcing

The relative infinity functor gives an ordinary functor into the homotopy category of the
equivalence-forcing quasicategory. Its inversion theorem supplies a canonical factorization
through the corrected ordinary bounded derived localization. No claim that this comparison
is an equivalence is made here.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory

/-- The functor from complexes to the homotopy category of equivalence forcing. -/
def metrizableEquivalenceForcingHomotopyFunctor :
    ComplexCategory ⥤ SSet.hoFunctor.obj metrizableEquivalenceForcingQCat.obj :=
  metrizableEquivalenceForcingRelativeInfinityFunctor.homotopyFunctor

/-- Raw corrected weak equivalences are inverted on the homotopy category. -/
theorem metrizableEquivalenceForcingHomotopyFunctor_inverts
    {K L : ComplexCategory} (f : K ⟶ L)
    (hf : CorrectedWeakEquivalence f) :
    IsIso (metrizableEquivalenceForcingHomotopyFunctor.map f) :=
  RelativeInfinityFunctor.homotopyFunctor_inverts
    metrizableEquivalenceForcingRelativeInfinityFunctor f
    (correctedWeakEquivalence_le_generated f hf)

/-- The induced functor from the corrected ordinary bounded derived localization. -/
def metrizableCorrectedDerivedToEquivalenceForcingHomotopy :
    DboundedWithCycles MetrizableLCA.{0} ⥤
      SSet.hoFunctor.obj metrizableEquivalenceForcingQCat.obj :=
  Localization.lift metrizableEquivalenceForcingHomotopyFunctor
    (fun _ _ f hf =>
      metrizableEquivalenceForcingHomotopyFunctor_inverts f hf)
    (DboundedWithCycles.localization MetrizableLCA.{0})

/-- The comparison commutes with the source functor up to the localization isomorphism. -/
def metrizableCorrectedDerivedToEquivalenceForcingHomotopy_fac :
    DboundedWithCycles.localization MetrizableLCA.{0} ⋙
        metrizableCorrectedDerivedToEquivalenceForcingHomotopy ≅
      metrizableEquivalenceForcingHomotopyFunctor :=
  Localization.fac metrizableEquivalenceForcingHomotopyFunctor
    (fun _ _ f hf =>
      metrizableEquivalenceForcingHomotopyFunctor_inverts f hf)
    (DboundedWithCycles.localization MetrizableLCA.{0})

/-- Once the homotopy functor is identified as the ordinary localization, the
named comparison functor is an equivalence by uniqueness of localization. -/
theorem metrizableCorrectedDerivedToEquivalenceForcingHomotopy_isEquivalence_of_isLocalization
    (h : metrizableEquivalenceForcingHomotopyFunctor.IsLocalization
      CorrectedWeakEquivalence) :
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy.IsEquivalence := by
  letI : metrizableEquivalenceForcingHomotopyFunctor.IsLocalization
      CorrectedWeakEquivalence := h
  let e := Localization.uniq
    (DboundedWithCycles.localization MetrizableLCA.{0})
    metrizableEquivalenceForcingHomotopyFunctor CorrectedWeakEquivalence
  let comparisonIso := Localization.isoUniqFunctor
    (DboundedWithCycles.localization MetrizableLCA.{0})
    metrizableEquivalenceForcingHomotopyFunctor CorrectedWeakEquivalence
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy
    metrizableCorrectedDerivedToEquivalenceForcingHomotopy_fac
  haveI : e.functor.IsEquivalence := by infer_instance
  exact Functor.isEquivalence_of_iso comparisonIso.symm

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
