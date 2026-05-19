import LeanLCAExactChallenge.Derived.Bounded

/-!
Stable certificate field provider scout.

This non-product audit records the current provider status for the four stable
infinity-category certificate projections required beyond ordinary `Dbounded` evidence.
No row is marked `supplied`.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace StableCertificateFieldProviderScoutW124

/--
Provider status for the four future stable certificate projections.

`ordinaryOnly` means the declaration is useful context, but it lives on the ordinary
category, ordinary nerve, or ordinary triangulated-category side and does not provide the
stable infinity-category field.
-/
inductive ProviderStatus where
  | missing
  | ordinaryOnly
  | supplied

/-- One row of the provider map for a future `Dbounded` stable certificate field. -/
structure FieldProvider where
  fieldName : String
  status : ProviderStatus
  bestCurrentCandidate : String
  whyNotProvider : String

/-- Current project/local-mathlib provider map for the four required stable fields. -/
structure StableFieldProviderMap where
  finiteLimits : FieldProvider
  finiteColimits : FieldProvider
  suspensionLoopEquivalence : FieldProvider
  pushoutPullbackCompatibility : FieldProvider

/--
The exact current provider map found by this scout.

No row is `supplied`: the available declarations are ordinary quasicategory, ordinary
homotopy-category, or ordinary triangulated-category declarations. They do not supply
finite-limit, finite-colimit, suspension/loop, or pushout/pullback projections from a
single stable infinity-category certificate for `Dbounded`.
-/
def currentProviderMap : StableFieldProviderMap where
  finiteLimits :=
    { fieldName := "finiteLimits"
      status := .missing
      bestCurrentCandidate :=
        "No `Dbounded.infinityCategory` finite-limit provider found; closest ordinary data are zero-object/localization declarations."
      whyNotProvider :=
        "A zero object or ordinary localized category structure is not finite limits of the stable quasicategory." }
  finiteColimits :=
    { fieldName := "finiteColimits"
      status := .missing
      bestCurrentCandidate :=
        "No `Dbounded.infinityCategory` finite-colimit provider found; closest ordinary data are zero-object/localization declarations."
      whyNotProvider :=
        "A zero object or ordinary localized category structure is not finite colimits of the stable quasicategory." }
  suspensionLoopEquivalence :=
    { fieldName := "suspensionLoopEquivalence"
      status := .ordinaryOnly
      bestCurrentCandidate :=
        "`HasShift`, `CommShift`, and ordinary triangulated localization declarations."
      whyNotProvider :=
        "Ordinary shift and triangulated-category data do not expose a suspension-loop equivalence projection on a stable quasicategory." }
  pushoutPullbackCompatibility :=
    { fieldName := "pushoutPullbackCompatibility"
      status := .ordinaryOnly
      bestCurrentCandidate :=
        "`Triangulated.Localization.pretriangulated`, `Triangulated.Localization.isTriangulated`, and bounded Verdier quotient triangulated instances."
      whyNotProvider :=
        "Ordinary triangulated localization does not expose the stable infinity-category theorem that pushouts and pullbacks agree." }

/-- The finite-limit provider is absent. -/
theorem finiteLimits_not_supplied :
    currentProviderMap.finiteLimits.status = ProviderStatus.missing := rfl

/-- The finite-colimit provider is absent. -/
theorem finiteColimits_not_supplied :
    currentProviderMap.finiteColimits.status = ProviderStatus.missing := rfl

/-- The current suspension/loop candidates are ordinary shift data only. -/
theorem suspensionLoop_only_ordinary :
    currentProviderMap.suspensionLoopEquivalence.status = ProviderStatus.ordinaryOnly := rfl

/-- The current pushout/pullback candidates are ordinary triangulated data only. -/
theorem pushoutPullback_only_ordinary :
    currentProviderMap.pushoutPullbackCompatibility.status = ProviderStatus.ordinaryOnly := rfl

/-- A provider map has all four stable certificate fields only when every row is supplied. -/
def allFieldsSupplied (m : StableFieldProviderMap) : Prop :=
  m.finiteLimits.status = ProviderStatus.supplied ∧
    m.finiteColimits.status = ProviderStatus.supplied ∧
    m.suspensionLoopEquivalence.status = ProviderStatus.supplied ∧
    m.pushoutPullbackCompatibility.status = ProviderStatus.supplied

/-- The current map is not a stable certificate provider: finite limits are still missing. -/
theorem currentProviderMap_not_allFieldsSupplied :
    ¬ allFieldsSupplied currentProviderMap := by
  intro h
  cases h.1

/-- The current finite-limit row is not a supplied stable certificate field. -/
theorem finiteLimits_not_supplied_status :
    currentProviderMap.finiteLimits.status ≠ ProviderStatus.supplied := by
  intro h
  cases h

/-- The current finite-colimit row is not a supplied stable certificate field. -/
theorem finiteColimits_not_supplied_status :
    currentProviderMap.finiteColimits.status ≠ ProviderStatus.supplied := by
  intro h
  cases h

/-- The current suspension/loop row is ordinary-only, not a supplied stable field. -/
theorem suspensionLoop_not_supplied_status :
    currentProviderMap.suspensionLoopEquivalence.status ≠ ProviderStatus.supplied := by
  intro h
  cases h

/-- The current pushout/pullback row is ordinary-only, not a supplied stable field. -/
theorem pushoutPullback_not_supplied_status :
    currentProviderMap.pushoutPullbackCompatibility.status ≠ ProviderStatus.supplied := by
  intro h
  cases h

section Checks

#check Dbounded.infinityCategory
#check Dbounded.infinityNerve
#check Dbounded.infinityNerve_quasicategory
#check Dbounded.homotopyCategoryIso
#check Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions
#check Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions
#check boundedExactAcyclicHomotopyVerdierCategory_hasZeroObject_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_hasShift_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_localization_commShift_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_pretriangulated_of_closed2
#check boundedExactAcyclicHomotopyVerdierCategory_isTriangulated_of_closed2
#check Triangulated.Localization.pretriangulated
#check Triangulated.Localization.isTriangulated
#check currentProviderMap
#check finiteLimits_not_supplied
#check finiteColimits_not_supplied
#check suspensionLoop_only_ordinary
#check pushoutPullback_only_ordinary
#check allFieldsSupplied
#check currentProviderMap_not_allFieldsSupplied
#check finiteLimits_not_supplied_status
#check finiteColimits_not_supplied_status
#check suspensionLoop_not_supplied_status
#check pushoutPullback_not_supplied_status

end Checks

end StableCertificateFieldProviderScoutW124

end LeanLCAExactChallenge
