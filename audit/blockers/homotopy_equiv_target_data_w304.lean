import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
W304: parent-side target-data boundary for safe HomotopyEquiv exact-acyclic transport.

Support W282 observed a useful nonterminal improvement to the W279 safe transport
route.  A plain short-complex quasi-isomorphism does not preserve the concrete
`MetrizableLCA.strictShortExact` predicate, as W296 already showed.  This file
therefore keeps the target topology and right-end data explicit, but removes one
source-side input: source degreewise categorical exactness follows from
`exactAcyclic MetrizableLCA K` under the same homology inputs used by the local
short-complex API.

No product-completion claim is made here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Topology

namespace HomotopyEquivTargetDataW304

/-- Concrete kernel/range equality needed to reconstruct strict short exactness. -/
abbrev TargetKernelEquality (T : ShortComplex MetrizableLCA.{u}) : Prop :=
  ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂

/--
The target-side data not supplied by categorical exactness transport.  These
fields are exactly the topology and right-end endpoint conditions needed by the
current `MetrizableLCA.strictShortExact` constructor.
-/
structure TargetTopologyAndCokernelData (T : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_embedding_f : IsClosedEmbedding (T.f : T.X₁ → T.X₂)
  open_map_g : IsOpenMap (T.g : T.X₂ → T.X₃)
  cokernel_top_g : MetrizableLCA.cokernelSubgroup T.g = ⊤

/-- A strict short exact sequence gives categorical `ShortComplex.Exact`. -/
theorem exact_of_strictShortExact
    {S : ShortComplex MetrizableLCA.{u}}
    (hhom : S.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hS : MetrizableLCA.strictShortExact S) :
    S.Exact := by
  letI := hhom
  letI := hpres
  rw [ShortComplex.exact_iff_exact_map_forget₂]
  change (S.map MetrizableLCA.forgetToAddCommGrpCat).Exact
  exact MetrizableLCA.forgetToAddCommGrpCat_exact_of_strict hS

/-- Source degreewise categorical exactness follows from exact acyclicity. -/
theorem source_exact_of_exactAcyclic
    (hhom : ∀ (M : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), (M.sc i).HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : exactAcyclic MetrizableLCA.{u} K) :
    ∀ i : ℤ, (K.sc i).Exact := by
  intro i
  exact exact_of_strictShortExact (hhom K i) hpres (hK i)

/-- Categorical exactness gives the element-level kernel/range equality. -/
theorem targetKernelEquality_of_exact
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact) :
    TargetKernelEquality T := by
  letI := hhom
  letI := hpres
  intro x₂
  constructor
  · intro hx₂
    exact (ShortComplex.exact_iff_of_hasForget T).mp hT x₂ hx₂
  · rintro ⟨x₁, rfl⟩
    change (T.f ≫ T.g : T.X₁ ⟶ T.X₃) x₁ = (0 : T.X₁ ⟶ T.X₃) x₁
    exact congrArg (fun h : T.X₁ ⟶ T.X₃ => h x₁) T.zero

/-- Categorical exactness plus explicit target data reconstructs strict short exactness. -/
theorem strictShortExact_of_exact_of_targetData
    {T : ShortComplex MetrizableLCA.{u}}
    (hhom : T.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hT : T.Exact)
    (hdata : TargetTopologyAndCokernelData T) :
    MetrizableLCA.strictShortExact T :=
  MetrizableLCA.strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
    (targetKernelEquality_of_exact hhom hpres hT)
    hdata.closed_embedding_f hdata.open_map_g hdata.cokernel_top_g

/-- A short-complex quasi-isomorphism transports categorical exactness only. -/
theorem exact_of_quasiIso
    {S T : ShortComplex MetrizableLCA.{u}} (φ : S ⟶ T)
    [S.HasHomology] [T.HasHomology]
    (hS : S.Exact) (hφ : ShortComplex.QuasiIso φ) :
    T.Exact := by
  haveI : ShortComplex.QuasiIso φ := hφ
  exact (ShortComplex.QuasiIso.exact_iff φ).1 hS

/-- A homotopy equivalence supplies the degreewise short-complex quasi-isomorphisms. -/
theorem shortComplex_quasiIso_of_homotopyEquiv
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (e : HomotopyEquiv K L) (i : ℤ)
    [(K.sc i).HasHomology] [(L.sc i).HasHomology] :
    ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor MetrizableLCA.{u} (ComplexShape.up ℤ) i).map e.hom) := by
  rw [ShortComplex.quasiIso_iff]
  change IsIso (homologyMap e.hom i)
  exact (e.toHomologyIso i).isIso_hom

/--
Safe W304 transport theorem.  The source exactness input is now just
`exactAcyclic MetrizableLCA K`; the target topology/right-end and homology
preservation inputs remain explicit.
-/
theorem exactAcyclic_of_homotopyEquiv_of_exactAcyclic_targetData
    (hhom : ∀ (M : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), (M.sc i).HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (e : HomotopyEquiv K L)
    (hK : exactAcyclic MetrizableLCA.{u} K)
    (hLdata : ∀ i : ℤ, TargetTopologyAndCokernelData (L.sc i)) :
    exactAcyclic MetrizableLCA.{u} L := by
  intro i
  haveI : (K.sc i).HasHomology := hhom K i
  haveI : (L.sc i).HasHomology := hhom L i
  exact strictShortExact_of_exact_of_targetData
    (T := L.sc i) inferInstance hpres
    (exact_of_quasiIso
      ((HomologicalComplex.shortComplexFunctor MetrizableLCA.{u} (ComplexShape.up ℤ) i).map e.hom)
      (source_exact_of_exactAcyclic hhom hpres hK i)
      (shortComplex_quasiIso_of_homotopyEquiv e i))
    (hLdata i)

/-- Machine-readable frontier state for W304. -/
structure HomotopyEquivTargetDataState : Type where
  seed : String
  selectedRoute : String
  provedReduction : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Reproducible W304 boundary state. -/
def currentHomotopyEquivTargetDataState : HomotopyEquivTargetDataState where
  seed := "w304-parent-20260520T1645Z"
  selectedRoute :=
    "safe HomotopyEquiv transport with explicit target topology and cokernel data"
  provedReduction :=
    "exactAcyclic source replaces the W279 source-side categorical exactness input"
  remainingInputs :=
    ["degreewise HasHomology for source and target short complexes",
      "forget₂ MetrizableLCA AddCommGrpCat PreservesHomology",
      "degreewise target closed embedding and open map fields",
      "degreewise target cokernelSubgroup top, or an equivalent endpoint input"]
  productSuccessClaimed := false

theorem currentHomotopyEquivTargetDataState_productSuccess :
    currentHomotopyEquivTargetDataState.productSuccessClaimed = false := rfl

/-- Named declarations checked by this audit file. -/
def homotopyEquivTargetDataDeclarationNames : List String :=
  ["TargetKernelEquality",
    "TargetTopologyAndCokernelData",
    "exact_of_strictShortExact",
    "source_exact_of_exactAcyclic",
    "targetKernelEquality_of_exact",
    "strictShortExact_of_exact_of_targetData",
    "exact_of_quasiIso",
    "shortComplex_quasiIso_of_homotopyEquiv",
    "exactAcyclic_of_homotopyEquiv_of_exactAcyclic_targetData",
    "currentHomotopyEquivTargetDataState"]

theorem homotopyEquivTargetDataDeclarationNames_count :
    homotopyEquivTargetDataDeclarationNames.length = 10 := rfl

section Checks

#check TargetKernelEquality
#check TargetTopologyAndCokernelData
#check exact_of_strictShortExact
#check source_exact_of_exactAcyclic
#check targetKernelEquality_of_exact
#check strictShortExact_of_exact_of_targetData
#check exact_of_quasiIso
#check shortComplex_quasiIso_of_homotopyEquiv
#check exactAcyclic_of_homotopyEquiv_of_exactAcyclic_targetData
#check currentHomotopyEquivTargetDataState
#check currentHomotopyEquivTargetDataState_productSuccess
#check homotopyEquivTargetDataDeclarationNames
#check homotopyEquivTargetDataDeclarationNames_count
#check ShortComplex.exact_iff_exact_map_forget₂
#check MetrizableLCA.forgetToAddCommGrpCat_exact_of_strict
#check ShortComplex.QuasiIso.exact_iff
#check HomotopyEquiv.toHomologyIso

end Checks

end HomotopyEquivTargetDataW304

end LeanLCAExactChallenge
