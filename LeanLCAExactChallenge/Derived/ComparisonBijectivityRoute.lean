import LeanLCAExactChallenge.Derived.RightCokernelClosureRoute

/-!
W821: prove algebraic bijectivity of the canonical left-right homology
comparison in `MetrizableLCA`, then feed W820 to obtain
`CategoryWithHomology MetrizableLCA`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

universe u

/--
For any limiting cokernel cofork in `MetrizableLCA`, membership in the closed
range of the source morphism forces the cokernel projection to vanish.
-/
theorem isColimit_cokernel_cofork_eq_zero_of_mem_closure_rangeW821
    {A B Q : MetrizableLCA.{u}} {f : A ⟶ B} {p : B ⟶ Q}
    {wp : f ≫ p = 0}
    (_hp : IsColimit (CokernelCofork.ofπ p wp)) {b : B}
    (hb : b ∈ closure (Set.range (f : A → B))) :
    p b = 0 := by
  have hb' : b ∈ cokernelSubgroup f := by
    change b ∈ ((cokernelSubgroup f : AddSubgroup B) : Set B)
    simpa [cokernelSubgroup, AddSubgroup.topologicalClosure_coe,
      rangeSubgroup_coe f] using hb
  exact cokernel_desc_ker_le (f := f) (k := p) wp hb'

/--
Closed boundary membership can be pulled back along the closed embedded cycle
inclusion supplied by left homology data.
-/
theorem leftHomologyData_mem_closure_boundary_of_i_mem_closure_boundaryW821
    {S : ShortComplex MetrizableLCA.{u}} (h₁ : S.LeftHomologyData) {k : h₁.K}
    (hk : h₁.i k ∈ closure (Set.range (S.f : S.X₁ → S.X₂))) :
    k ∈ closure (Set.range (h₁.f' : S.X₁ → h₁.K)) := by
  have himage :
      (h₁.i : h₁.K → S.X₂) ''
          Set.range (h₁.f' : S.X₁ → h₁.K) =
        Set.range (S.f : S.X₁ → S.X₂) := by
    ext x
    constructor
    · rintro ⟨k', ⟨a, rfl⟩, rfl⟩
      refine ⟨a, ?_⟩
      exact (congrArg (fun f : S.X₁ ⟶ S.X₂ => (f : S.X₁ → S.X₂) a)
        h₁.f'_i).symm
    · rintro ⟨a, rfl⟩
      refine ⟨h₁.f' a, ⟨a, rfl⟩, ?_⟩
      exact congrArg (fun f : S.X₁ ⟶ S.X₂ => (f : S.X₁ → S.X₂) a)
        h₁.f'_i
  have hkpre :
      k ∈ (h₁.i : h₁.K → S.X₂) ⁻¹'
        closure ((h₁.i : h₁.K → S.X₂) ''
          Set.range (h₁.f' : S.X₁ → h₁.K)) := by
    simpa [himage] using hk
  have hiemb := (leftHomologyData_i_closedEmbeddingW815 h₁).isEmbedding
  rw [← hiemb.closure_eq_preimage_closure_image
    (Set.range (h₁.f' : S.X₁ → h₁.K))] at hkpre
  exact hkpre

/-- The canonical left-right homology comparison is surjective. -/
theorem leftRightHomologyComparison'_surjectiveW821
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    Function.Surjective
      (ShortComplex.leftRightHomologyComparison' h₁ h₂ : h₁.H → h₂.H) := by
  intro y
  rcases rightHomologyData_p_surjectiveW815 h₂ (h₂.ι y) with ⟨x, hx⟩
  have hgx : S.g x = 0 := by
    have hy : h₂.g' (h₂.ι y) = 0 := by
      exact congrArg (fun f : h₂.H ⟶ S.X₃ => (f : h₂.H → S.X₃) y) h₂.ι_g'
    calc
      S.g x = h₂.g' (h₂.p x) := by
        exact (congrArg (fun f : S.X₂ ⟶ S.X₃ => (f : S.X₂ → S.X₃) x)
          h₂.p_g').symm
      _ = h₂.g' (h₂.ι y) := by rw [hx]
      _ = 0 := hy
  rcases kernelFork_range_of_apply_eq_zeroW819 h₁.hi hgx with ⟨k, hk⟩
  refine ⟨h₁.π k, ?_⟩
  apply (rightHomologyData_ι_closedEmbeddingW815 h₂).isEmbedding.injective
  calc
    h₂.ι (ShortComplex.leftRightHomologyComparison' h₁ h₂ (h₁.π k)) =
        h₂.p (h₁.i k) := by
      exact congrArg (fun f : h₁.K → h₂.Q => f k)
        (leftRightHomologyComparison'_squareW818 h₁ h₂)
    _ = h₂.p x := by rw [hk]
    _ = h₂.ι y := hx

/-- The canonical left-right homology comparison is injective. -/
theorem leftRightHomologyComparison'_injectiveW821
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    Function.Injective
      (ShortComplex.leftRightHomologyComparison' h₁ h₂ : h₁.H → h₂.H) := by
  intro a b hab
  rcases leftHomologyData_π_surjectiveW815 h₁ a with ⟨ka, hka⟩
  rcases leftHomologyData_π_surjectiveW815 h₁ b with ⟨kb, hkb⟩
  have hp_eq : h₂.p (h₁.i ka) = h₂.p (h₁.i kb) := by
    have hsq_a := congrArg (fun f : h₁.K → h₂.Q => f ka)
      (leftRightHomologyComparison'_squareW818 h₁ h₂)
    have hsq_b := congrArg (fun f : h₁.K → h₂.Q => f kb)
      (leftRightHomologyComparison'_squareW818 h₁ h₂)
    calc
      h₂.p (h₁.i ka) =
          h₂.ι (ShortComplex.leftRightHomologyComparison' h₁ h₂ (h₁.π ka)) :=
        hsq_a.symm
      _ = h₂.ι (ShortComplex.leftRightHomologyComparison' h₁ h₂ a) := by rw [hka]
      _ = h₂.ι (ShortComplex.leftRightHomologyComparison' h₁ h₂ b) := by rw [hab]
      _ = h₂.ι (ShortComplex.leftRightHomologyComparison' h₁ h₂ (h₁.π kb)) := by
        rw [hkb]
      _ = h₂.p (h₁.i kb) := hsq_b
  have hp_zero : h₂.p (h₁.i (ka - kb)) = 0 := by
    calc
      h₂.p (h₁.i (ka - kb)) =
          h₂.p (h₁.i ka - h₁.i kb) := by
        rw [map_sub h₁.i.hom]
      _ = h₂.p (h₁.i ka) - h₂.p (h₁.i kb) := map_sub h₂.p.hom _ _
      _ = 0 := by simp [hp_eq]
  have hclosed_x :
      h₁.i (ka - kb) ∈ closure (Set.range (S.f : S.X₁ → S.X₂)) :=
    isColimit_cokernel_cofork_eq_zero_mem_closure_rangeW820
      (f := S.f) (p := h₂.p) h₂.hp hp_zero
  have hclosed_k :
      ka - kb ∈ closure (Set.range (h₁.f' : S.X₁ → h₁.K)) :=
    leftHomologyData_mem_closure_boundary_of_i_mem_closure_boundaryW821 h₁ hclosed_x
  have hπ_zero : h₁.π (ka - kb) = 0 :=
    isColimit_cokernel_cofork_eq_zero_of_mem_closure_rangeW821
      (f := h₁.f') (p := h₁.π) h₁.hπ hclosed_k
  have hπ_eq : h₁.π ka = h₁.π kb := by
    calc
      h₁.π ka = h₁.π ((ka - kb) + kb) := by rw [sub_add_cancel]
      _ = h₁.π (ka - kb) + h₁.π kb := map_add h₁.π.hom _ _
      _ = h₁.π kb := by simp [hπ_zero]
  calc
    a = h₁.π ka := hka.symm
    _ = h₁.π kb := hπ_eq
    _ = b := hkb

/-- The canonical left-right homology comparison is bijective. -/
theorem leftRightHomologyComparison'_bijectiveW821
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    Function.Bijective
      (ShortComplex.leftRightHomologyComparison' h₁ h₂ : h₁.H → h₂.H) :=
  ⟨leftRightHomologyComparison'_injectiveW821 h₁ h₂,
    leftRightHomologyComparison'_surjectiveW821 h₁ h₂⟩

/-- W821 supplies W820's universal algebraic-bijectivity target. -/
theorem comparisonBijectiveTargetW821
    (S : ShortComplex MetrizableLCA.{0}) :
    comparisonBijectiveTargetW820 S := by
  simpa [comparisonBijectiveTargetW820, ShortComplex.leftRightHomologyComparison]
    using leftRightHomologyComparison'_bijectiveW821
      S.leftHomologyData S.rightHomologyData

/-- W821 proves the homology structure for the strict metrizable LCA category. -/
theorem categoryWithHomology_of_leftRightComparisonBijectiveW821 :
    CategoryWithHomology MetrizableLCA.{0} :=
  categoryWithHomology_of_comparisonBijectiveW820
    (fun S => comparisonBijectiveTargetW821 S)

/-- Input names for the W821 comparison-bijectivity route. -/
def comparisonBijectivityInputNamesW821 :
    List String :=
  []

theorem comparisonBijectivityInputNamesW821_count :
    comparisonBijectivityInputNamesW821.length = 0 :=
  rfl

/-- Current checked W821 state for the comparison-bijectivity route. -/
structure ComparisonBijectivityRouteStateW821 :
    Type where
  seed : String
  declarations : List String
  result : String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W821 state. -/
def currentComparisonBijectivityRouteStateW821 :
    ComparisonBijectivityRouteStateW821
    where
  seed := "w821-comparison-bijectivity-route"
  declarations :=
    ["isColimit_cokernel_cofork_eq_zero_of_mem_closure_rangeW821",
      "leftHomologyData_mem_closure_boundary_of_i_mem_closure_boundaryW821",
      "leftRightHomologyComparison'_surjectiveW821",
      "leftRightHomologyComparison'_injectiveW821",
      "leftRightHomologyComparison'_bijectiveW821",
      "comparisonBijectiveTargetW821",
      "categoryWithHomology_of_leftRightComparisonBijectiveW821",
      "comparisonBijectivityInputNamesW821",
      "comparisonBijectivityInputNamesW821_count"]
  result :=
    "proved: the canonical left-right homology comparison is bijective for " ++
      "every ShortComplex in MetrizableLCA, yielding CategoryWithHomology"
  remainingInputs :=
    comparisonBijectivityInputNamesW821
  productSuccessClaimed := false

theorem currentComparisonBijectivityRouteStateW821_productSuccess :
    currentComparisonBijectivityRouteStateW821.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
