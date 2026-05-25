import LeanLCAExactChallenge.Derived.CategoryHomologyComparisonBijectiveOpenRoute

/-!
W815: expose the kernel/cokernel projection topology used by the W814
left-right homology comparison target.

The W814 target mirrors the `TopModuleCat` homology proof: one needs open
quotient projections and closed kernel inclusions for the chosen left and right
homology data.  This helper packages those facts for arbitrary MetrizableLCA
short-complex homology data, without claiming the comparison map is already an
isomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

universe u

/-- A limiting cokernel cofork in `MetrizableLCA` has a surjective projection. -/
theorem cokernelCofork_π_surjective_of_isColimitW815
    {A B Q : MetrizableLCA.{u}} {f : A ⟶ B} {π : B ⟶ Q}
    {w : f ≫ π = 0}
    (hπ : IsColimit (CokernelCofork.ofπ π w)) :
    Function.Surjective (π : B → Q) := by
  let ck₀ : CokernelCofork f :=
    CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)
  let ck : CokernelCofork f := CokernelCofork.ofπ π w
  let e : ck₀.pt ≅ ck.pt :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsColimit f) hπ
  have hπe : ck₀.π ≫ e.hom = ck.π := by
    simpa [ck₀, ck, e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsColimit f) hπ WalkingParallelPair.one)
  have hsurj :
      Function.Surjective ((cokernelπ f ≫ e.hom : B ⟶ Q) : B → Q) := by
    exact surjective_comp_iso (cokernelπ f) e
      (quotientMap_surjective B (cokernelSubgroup f)
        (AddSubgroup.isClosed_topologicalClosure _))
  simpa [ck₀, ck, hπe] using hsurj

/-- A limiting cokernel cofork in `MetrizableLCA` has an open projection. -/
theorem cokernelCofork_π_openMap_of_isColimitW815
    {A B Q : MetrizableLCA.{u}} {f : A ⟶ B} {π : B ⟶ Q}
    {w : f ≫ π = 0}
    (hπ : IsColimit (CokernelCofork.ofπ π w)) :
    IsOpenMap (π : B → Q) := by
  let ck₀ : CokernelCofork f :=
    CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)
  let ck : CokernelCofork f := CokernelCofork.ofπ π w
  let e : ck₀.pt ≅ ck.pt :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsColimit f) hπ
  have hπe : ck₀.π ≫ e.hom = ck.π := by
    simpa [ck₀, ck, e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        (cokernelIsColimit f) hπ WalkingParallelPair.one)
  have hopen :
      IsOpenMap ((cokernelπ f ≫ e.hom : B ⟶ Q) : B → Q) := by
    exact openMap_comp_iso (cokernelπ f) e
      (quotientMap_openMap B (cokernelSubgroup f)
        (AddSubgroup.isClosed_topologicalClosure _))
  simpa [ck₀, ck, hπe] using hopen

/-- A limiting kernel fork in `MetrizableLCA` has a closed-embedding inclusion. -/
theorem kernelFork_ι_closedEmbedding_of_isLimitW815
    {A B K : MetrizableLCA.{u}} {g : A ⟶ B} {ι : K ⟶ A}
    {w : ι ≫ g = 0}
    (hι : IsLimit (KernelFork.ofι ι w)) :
    IsClosedEmbedding (ι : K → A) := by
  let fork : Fork g 0 := Fork.ofι ι (by simpa using w)
  have hfork : IsLimit fork := by
    simpa [fork] using hι
  have hclosed : IsClosedEmbedding (fork.ι : fork.pt → A) :=
    isLimit_fork_ι_closedEmbedding (r := g) (s := 0) hfork
  simpa [fork] using hclosed

/-- The cycle inclusion in any left homology data is a closed embedding. -/
theorem leftHomologyData_i_closedEmbeddingW815
    {S : ShortComplex MetrizableLCA.{u}} (h : S.LeftHomologyData) :
    IsClosedEmbedding (h.i : h.K → S.X₂) :=
  kernelFork_ι_closedEmbedding_of_isLimitW815 h.hi

/-- The left homology projection in any left homology data is surjective. -/
theorem leftHomologyData_π_surjectiveW815
    {S : ShortComplex MetrizableLCA.{u}} (h : S.LeftHomologyData) :
    Function.Surjective (h.π : h.K → h.H) :=
  cokernelCofork_π_surjective_of_isColimitW815 h.hπ

/-- The left homology projection in any left homology data is open. -/
theorem leftHomologyData_π_openMapW815
    {S : ShortComplex MetrizableLCA.{u}} (h : S.LeftHomologyData) :
    IsOpenMap (h.π : h.K → h.H) :=
  cokernelCofork_π_openMap_of_isColimitW815 h.hπ

/-- The cokernel projection in any right homology data is surjective. -/
theorem rightHomologyData_p_surjectiveW815
    {S : ShortComplex MetrizableLCA.{u}} (h : S.RightHomologyData) :
    Function.Surjective (h.p : S.X₂ → h.Q) :=
  cokernelCofork_π_surjective_of_isColimitW815 h.hp

/-- The cokernel projection in any right homology data is open. -/
theorem rightHomologyData_p_openMapW815
    {S : ShortComplex MetrizableLCA.{u}} (h : S.RightHomologyData) :
    IsOpenMap (h.p : S.X₂ → h.Q) :=
  cokernelCofork_π_openMap_of_isColimitW815 h.hp

/-- The right homology inclusion in any right homology data is a closed embedding. -/
theorem rightHomologyData_ι_closedEmbeddingW815
    {S : ShortComplex MetrizableLCA.{u}} (h : S.RightHomologyData) :
    IsClosedEmbedding (h.ι : h.H → h.Q) :=
  kernelFork_ι_closedEmbedding_of_isLimitW815 h.hι

/-- The canonical cycle inclusion is a closed embedding. -/
theorem iCycles_closedEmbeddingW815
    (S : ShortComplex MetrizableLCA.{u}) [S.HasLeftHomology] :
    IsClosedEmbedding (S.iCycles : S.cycles → S.X₂) :=
  leftHomologyData_i_closedEmbeddingW815 S.leftHomologyData

/-- The canonical left homology projection is surjective. -/
theorem leftHomologyπ_surjectiveW815
    (S : ShortComplex MetrizableLCA.{u}) [S.HasLeftHomology] :
    Function.Surjective (S.leftHomologyπ : S.cycles → S.leftHomology) :=
  leftHomologyData_π_surjectiveW815 S.leftHomologyData

/-- The canonical left homology projection is open. -/
theorem leftHomologyπ_openMapW815
    (S : ShortComplex MetrizableLCA.{u}) [S.HasLeftHomology] :
    IsOpenMap (S.leftHomologyπ : S.cycles → S.leftHomology) :=
  leftHomologyData_π_openMapW815 S.leftHomologyData

/-- The canonical opcycles projection is surjective. -/
theorem pOpcycles_surjectiveW815
    (S : ShortComplex MetrizableLCA.{u}) [S.HasRightHomology] :
    Function.Surjective (S.pOpcycles : S.X₂ → S.opcycles) :=
  rightHomologyData_p_surjectiveW815 S.rightHomologyData

/-- The canonical opcycles projection is open. -/
theorem pOpcycles_openMapW815
    (S : ShortComplex MetrizableLCA.{u}) [S.HasRightHomology] :
    IsOpenMap (S.pOpcycles : S.X₂ → S.opcycles) :=
  rightHomologyData_p_openMapW815 S.rightHomologyData

/-- The canonical right homology inclusion is a closed embedding. -/
theorem rightHomologyι_closedEmbeddingW815
    (S : ShortComplex MetrizableLCA.{u}) [S.HasRightHomology] :
    IsClosedEmbedding (S.rightHomologyι : S.rightHomology → S.opcycles) :=
  rightHomologyData_ι_closedEmbeddingW815 S.rightHomologyData

/-- Input names removed from the next W814 comparison-topology proof. -/
def comparisonProjectionTopologyInputNamesW815 :
    List String :=
  ["open quotient projection for left homology data",
    "surjective quotient projection for left homology data",
    "open quotient projection for right homology data",
    "surjective quotient projection for right homology data",
    "closed-embedding kernel inclusion for left homology data",
    "closed-embedding kernel inclusion for right homology data"]

theorem comparisonProjectionTopologyInputNamesW815_count :
    comparisonProjectionTopologyInputNamesW815.length = 6 :=
  rfl

/-- Current checked W815 state for projection-topology support. -/
structure ComparisonProjectionTopologyRouteStateW815 :
    Type where
  seed : String
  declarations : List String
  topologyResult : String
  feedsTarget : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W815 state. -/
def currentComparisonProjectionTopologyRouteSupportStateW815 :
    ComparisonProjectionTopologyRouteStateW815
    where
  seed := "w815-comparison-projection-topology-route"
  declarations :=
    ["cokernelCofork_π_surjective_of_isColimitW815",
      "cokernelCofork_π_openMap_of_isColimitW815",
      "kernelFork_ι_closedEmbedding_of_isLimitW815",
      "leftHomologyData_i_closedEmbeddingW815",
      "leftHomologyData_π_surjectiveW815",
      "leftHomologyData_π_openMapW815",
      "rightHomologyData_p_surjectiveW815",
      "rightHomologyData_p_openMapW815",
      "rightHomologyData_ι_closedEmbeddingW815",
      "iCycles_closedEmbeddingW815",
      "leftHomologyπ_surjectiveW815",
      "leftHomologyπ_openMapW815",
      "pOpcycles_surjectiveW815",
      "pOpcycles_openMapW815",
      "rightHomologyι_closedEmbeddingW815"]
  topologyResult :=
    "proved: arbitrary MetrizableLCA left/right homology data carries the open, " ++
      "surjective, and closed-embedding projection facts used by the W814 comparison proof"
  feedsTarget :=
    "next step: combine these projection-topology facts with the algebraic comparison " ++
      "argument to prove comparisonBijectiveOpenTargetW814"
  remainingInputs :=
    ["algebraic bijectivity of the canonical left-right homology comparison",
      "topological embedding/open-map bridge for the canonical comparison map",
      "the final comparisonBijectiveOpenTargetW814 theorem for arbitrary short complexes"]
  productSuccessClaimed := false

/-- Short alias used by the checked product-success marker. -/
abbrev currentComparisonProjectionTopologyRouteStateW815 :
    ComparisonProjectionTopologyRouteStateW815 :=
  currentComparisonProjectionTopologyRouteSupportStateW815

theorem currentComparisonProjectionTopologyRouteStateW815_productSuccess :
    currentComparisonProjectionTopologyRouteStateW815.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
