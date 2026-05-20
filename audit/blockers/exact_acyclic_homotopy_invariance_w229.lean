import LeanLCAExactChallenge.Derived.BoundedFiniteProducts

/-!
Boundary audit for exact-acyclic homotopy invariance.

W221 and W225 isolate the wanted theorem
`exactAcyclic C K -> HomotopyEquiv K L -> exactAcyclic C L`. This file records a
different route: mathlib already turns a homotopy equivalence into homology isomorphisms, so the
remaining local input is a bridge from degreewise short-complex quasi-isomorphisms to the local
`QuillenExactCategory.Conflation` predicate used by `exactAcyclic`.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

namespace ExactAcyclicHomotopyInvarianceW229

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The target theorem requested by the surrounding iso-closure collapse route. -/
abbrev ExactAcyclicTransportOfHomotopyEquiv [QuillenExactCategory C] : Prop :=
  ∀ {K L : CochainComplex C ℤ},
    exactAcyclic C K → HomotopyEquiv K L → exactAcyclic C L

/--
The local exact-category bridge missing on the homology route.

For every short-complex morphism whose induced homology map is an isomorphism, this says the
local conflation predicate is transported from the source short complex to the target short complex.
This is stronger than strict isomorphism transport and is exactly the kind of theorem needed after
using `HomotopyEquiv.toHomologyIso` degreewise.
-/
abbrev ShortComplexQuasiIsoConflationTransport [QuillenExactCategory C] : Prop :=
  ∀ {S T : ShortComplex C} (φ : S ⟶ T) [S.HasHomology] [T.HasHomology],
    QuillenExactCategory.Conflation S → ShortComplex.QuasiIso φ →
      QuillenExactCategory.Conflation T

/--
Homotopy equivalences give degreewise quasi-isomorphisms of the associated short complexes,
provided those short complexes have mathlib homology objects.
-/
theorem shortComplex_quasiIso_of_homotopyEquiv
    {K L : CochainComplex C ℤ} (e : HomotopyEquiv K L) (i : ℤ)
    [(K.sc i).HasHomology] [(L.sc i).HasHomology] :
    ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map e.hom) := by
  rw [ShortComplex.quasiIso_iff]
  change IsIso (homologyMap e.hom i)
  exact (e.toHomologyIso i).isIso_hom

/--
The homology route to exact-acyclic homotopy invariance.

This reduces the original target to two concrete inputs: degreewise existence of mathlib homology
for the selected cochain complexes, and quasi-isomorphism invariance of the local conflation
predicate. The latter is not currently exposed by the local `QuillenExactCategory` API.
-/
theorem exactAcyclicTransportOfHomotopyEquiv_of_shortComplexQuasiIso
    [QuillenExactCategory C]
    (hhom : ∀ (M : CochainComplex C ℤ) (i : ℤ), (M.sc i).HasHomology)
    (hqi : ShortComplexQuasiIsoConflationTransport C) :
    ExactAcyclicTransportOfHomotopyEquiv C := by
  intro K L hK e i
  haveI : (K.sc i).HasHomology := hhom K i
  haveI : (L.sc i).HasHomology := hhom L i
  exact hqi ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map e.hom)
    (hK i) (shortComplex_quasiIso_of_homotopyEquiv C e i)

/-- The exact missing local theorem if homology objects are available degreewise. -/
def missingShortComplexBridge : String :=
  "ShortComplexQuasiIsoConflationTransport: quasi-isomorphic short complexes transport QuillenExactCategory.Conflation"

/-- Route status for downstream review. -/
def exactAcyclicHomotopyInvarianceRouteStatus : List String :=
  ["proved: HomotopyEquiv gives degreewise ShortComplex.QuasiIso via HomotopyEquiv.toHomologyIso",
    "proved: degreewise homology plus ShortComplexQuasiIsoConflationTransport implies ExactAcyclicTransportOfHomotopyEquiv",
    "missing: local QuillenExactCategory.Conflation invariance under short-complex quasi-isomorphism"]

theorem exactAcyclicHomotopyInvarianceRouteStatus_count :
    exactAcyclicHomotopyInvarianceRouteStatus.length = 3 := rfl

section Checks

#check ExactAcyclicTransportOfHomotopyEquiv
#check ShortComplexQuasiIsoConflationTransport
#check shortComplex_quasiIso_of_homotopyEquiv
#check exactAcyclicTransportOfHomotopyEquiv_of_shortComplexQuasiIso
#check missingShortComplexBridge
#check exactAcyclicHomotopyInvarianceRouteStatus
#check exactAcyclicHomotopyInvarianceRouteStatus_count
#check HomotopyEquiv.toHomologyIso
#check ShortComplex.quasiIso_iff
#check QuillenExactCategory.conflation_iso_transport

end Checks

end ExactAcyclicHomotopyInvarianceW229

end LeanLCAExactChallenge
