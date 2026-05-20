import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
Boundary audit for transporting conflations across short-complex quasi-isomorphisms.

W229 shows that a homotopy equivalence of cochain complexes gives degreewise
`ShortComplex.QuasiIso` maps. This file isolates the exact local theorem needed after that step.
The currently available exact-category API transports conflations across short-complex isomorphisms;
it does not expose a theorem converting a homology isomorphism of short complexes into
`QuillenExactCategory.Conflation` transport.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex

namespace ShortComplexQuasiIsoConflationW232

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The exact bridge requested by the W229 homology route. -/
abbrev ShortComplexQuasiIsoConflationTransport [QuillenExactCategory C] : Prop :=
  ∀ {S T : ShortComplex C} (φ : S ⟶ T) [S.HasHomology] [T.HasHomology],
    QuillenExactCategory.Conflation S → ShortComplex.QuasiIso φ →
      QuillenExactCategory.Conflation T

/-- The strict-isomorphism transport already supplied by the local exact-category interface. -/
abbrev ShortComplexIsoConflationTransport [QuillenExactCategory C] : Prop :=
  ∀ {S T : ShortComplex C}, (S ≅ T) →
    QuillenExactCategory.Conflation S → QuillenExactCategory.Conflation T

theorem shortComplexIsoConflationTransport [QuillenExactCategory C] :
    ShortComplexIsoConflationTransport C := by
  intro S T e hS
  exact QuillenExactCategory.conflation_iso_transport e hS

/--
A strong comparison theorem from short-complex quasi-isomorphisms to short-complex isomorphisms
would be enough for the requested bridge. This records a sufficient input, not a claim that such a
comparison exists in the current API.
-/
theorem shortComplexQuasiIsoConflationTransport_of_quasiIsoIso
    [QuillenExactCategory C]
    (toIso :
      ∀ {S T : ShortComplex C} (φ : S ⟶ T) [S.HasHomology] [T.HasHomology],
        ShortComplex.QuasiIso φ → (S ≅ T)) :
    ShortComplexQuasiIsoConflationTransport C := by
  intro S T φ _ _ hS hφ
  exact QuillenExactCategory.conflation_iso_transport (toIso φ hφ) hS

/--
Concrete cochain-complex consumer: degreewise short-complex quasi-isomorphisms transport
`exactAcyclic` once the local short-complex bridge is supplied.
-/
theorem exactAcyclicTransportOfCochainMap_of_shortComplexQuasiIso
    [QuillenExactCategory C]
    (hqi : ShortComplexQuasiIsoConflationTransport C)
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : exactAcyclic C K)
    (hKhom : ∀ i : ℤ, (K.sc i).HasHomology)
    (hLhom : ∀ i : ℤ, (L.sc i).HasHomology)
    (hf : ∀ i : ℤ,
      ShortComplex.QuasiIso
        ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map f)) :
    exactAcyclic C L := by
  intro i
  haveI : (K.sc i).HasHomology := hKhom i
  haveI : (L.sc i).HasHomology := hLhom i
  exact hqi ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map f)
    (hK i) (hf i)

/-- W229's homotopy-equivalence-to-degreewise-quasi-isomorphism step, kept local for review. -/
theorem shortComplex_quasiIso_of_homotopyEquiv
    {K L : CochainComplex C ℤ} (e : HomotopyEquiv K L) (i : ℤ)
    [(K.sc i).HasHomology] [(L.sc i).HasHomology] :
    ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).map e.hom) := by
  rw [ShortComplex.quasiIso_iff]
  change IsIso (homologyMap e.hom i)
  exact (e.toHomologyIso i).isIso_hom

/-- W229 plus the local bridge gives the requested homotopy-invariance consumer. -/
theorem exactAcyclicTransportOfHomotopyEquiv_of_shortComplexQuasiIso
    [QuillenExactCategory C]
    (hqi : ShortComplexQuasiIsoConflationTransport C)
    {K L : CochainComplex C ℤ} (e : HomotopyEquiv K L)
    (hK : exactAcyclic C K)
    (hKhom : ∀ i : ℤ, (K.sc i).HasHomology)
    (hLhom : ∀ i : ℤ, (L.sc i).HasHomology) :
    exactAcyclic C L :=
  exactAcyclicTransportOfCochainMap_of_shortComplexQuasiIso C hqi e.hom hK hKhom hLhom
    (fun i => shortComplex_quasiIso_of_homotopyEquiv C e i)

/-- The strict metrizable LCA specialization of the requested bridge. -/
abbrev MetrizableLCAShortComplexQuasiIsoStrictTransport : Prop :=
  ∀ {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T) [S.HasHomology] [T.HasHomology],
    MetrizableLCA.strictShortExact S → ShortComplex.QuasiIso φ →
      MetrizableLCA.strictShortExact T

theorem metrizableLCA_shortComplexQuasiIsoStrictTransport_of_general
    (h : ShortComplexQuasiIsoConflationTransport MetrizableLCA.{u}) :
    MetrizableLCAShortComplexQuasiIsoStrictTransport.{u} := by
  intro S T φ _ _ hS hφ
  exact h φ hS hφ

theorem shortComplexQuasiIsoConflationTransport_of_metrizableLCA
    (h : MetrizableLCAShortComplexQuasiIsoStrictTransport.{u}) :
    ShortComplexQuasiIsoConflationTransport MetrizableLCA.{u} := by
  intro S T φ _ _ hS hφ
  exact h φ hS hφ

/-- The currently missing local theorem, in the form needed by W229 and cochain consumers. -/
def missingShortComplexQuasiIsoConflationBridge : String :=
  "ShortComplex.QuasiIso φ should transport QuillenExactCategory.Conflation S to T"

/-- Why the metrizable LCA specialization is still blocked. -/
def missingMetrizableLCAStrictBridge : String :=
  "For MetrizableLCA, the bridge must turn homology isomorphism data into strictShortExact T"

/-- Compact status for downstream review. -/
def shortComplexQuasiIsoConflationStatus : List String :=
  ["proved: QuillenExactCategory already transports conflations across short-complex isomorphisms",
    "proved: degreewise ShortComplex.QuasiIso plus the local bridge transports exactAcyclic for cochain maps",
    "proved: HomotopyEquiv gives the needed degreewise ShortComplex.QuasiIso maps",
    "missing: local Conflation transport across ShortComplex.QuasiIso",
    "missing: in MetrizableLCA, homology-isomorphism data must imply strictShortExact for the target"]

theorem shortComplexQuasiIsoConflationStatus_count :
    shortComplexQuasiIsoConflationStatus.length = 5 := rfl

section Checks

#check ShortComplexQuasiIsoConflationTransport
#check ShortComplexIsoConflationTransport
#check shortComplexIsoConflationTransport
#check shortComplexQuasiIsoConflationTransport_of_quasiIsoIso
#check exactAcyclicTransportOfCochainMap_of_shortComplexQuasiIso
#check shortComplex_quasiIso_of_homotopyEquiv
#check exactAcyclicTransportOfHomotopyEquiv_of_shortComplexQuasiIso
#check MetrizableLCAShortComplexQuasiIsoStrictTransport
#check metrizableLCA_shortComplexQuasiIsoStrictTransport_of_general
#check shortComplexQuasiIsoConflationTransport_of_metrizableLCA
#check missingShortComplexQuasiIsoConflationBridge
#check missingMetrizableLCAStrictBridge
#check shortComplexQuasiIsoConflationStatus
#check shortComplexQuasiIsoConflationStatus_count
#check QuillenExactCategory.conflation_iso_transport
#check MetrizableLCA.strictShortExact_iso
#check HomotopyEquiv.toHomologyIso
#check ShortComplex.quasiIso_iff

end Checks

end ShortComplexQuasiIsoConflationW232

end LeanLCAExactChallenge
