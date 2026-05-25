import LeanLCAExactChallenge.Derived.ComparisonFiberSaturationRoute
import LeanLCAExactChallenge.LCA.StrictExact

/-!
W820: discharge the right-cokernel closure input from W819.

W819 reduced W818's fiber-saturation condition to a precise cokernel-fiber
closure statement.  In `MetrizableLCA`, every cokernel is isomorphic to the
explicit closed-range quotient, so equality under a right homology cokernel
projection already says that the difference lies in the closed boundary range.
The comparison target is therefore reduced to algebraic bijectivity of the
canonical left-right homology comparison.
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
Membership in the explicit `MetrizableLCA` cokernel subgroup is membership in
the closure of the underlying range.
-/
theorem cokernelSubgroup_mem_closure_rangeW820
    {A B : MetrizableLCA.{u}} (f : A ⟶ B) {b : B}
    (hb : b ∈ cokernelSubgroup f) :
    b ∈ closure (Set.range (f : A → B)) := by
  change b ∈ ((cokernelSubgroup f : AddSubgroup B) : Set B) at hb
  rw [cokernelSubgroup, AddSubgroup.topologicalClosure_coe,
    rangeSubgroup_coe f] at hb
  exact hb

/--
For any limiting cokernel cofork in `MetrizableLCA`, the zero fiber of its
projection is the closed range of the original morphism.
-/
theorem isColimit_cokernel_cofork_eq_zero_mem_closure_rangeW820
    {A B Q : MetrizableLCA.{u}} {f : A ⟶ B} {p : B ⟶ Q}
    {wp : f ≫ p = 0}
    (hp : IsColimit (CokernelCofork.ofπ p wp)) {b : B} (hb : p b = 0) :
    b ∈ closure (Set.range (f : A → B)) := by
  let e : Q ≅ cokernelObj f :=
    IsColimit.coconePointUniqueUpToIso hp (cokernelIsColimit f)
  have hpe : p ≫ e.hom = cokernelπ f := by
    simpa [e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom
        hp (cokernelIsColimit f) WalkingParallelPair.one)
  have hcok0 : cokernelπ f b = 0 := by
    calc
      cokernelπ f b = (p ≫ e.hom) b := by
        exact congrArg
          (fun q : B ⟶ cokernelObj f => (q : B → cokernelObj f) b)
          hpe.symm
      _ = e.hom (p b) := rfl
      _ = 0 := by simp [hb]
  have hmem : b ∈ cokernelSubgroup f := by
    change ((b : B) : B ⧸ cokernelSubgroup f) = 0 at hcok0
    rwa [QuotientAddGroup.eq_zero_iff] at hcok0
  exact cokernelSubgroup_mem_closure_rangeW820 f hmem

/--
The remaining W819 right-cokernel fiber-closure input follows directly from
the cokernel condition in any right homology data.
-/
theorem rightCokernelFiberClosure_of_rightHomologyDataW820
    {S : ShortComplex MetrizableLCA.{u}}
    (h₁ : S.LeftHomologyData) (h₂ : S.RightHomologyData) :
    rightCokernelFiberClosureTargetW819 h₁ h₂ := by
  intro x k hx
  have hp_zero : h₂.p (x - h₁.i k) = 0 := by
    calc
      h₂.p (x - h₁.i k) = h₂.p x - h₂.p (h₁.i k) :=
        map_sub h₂.p.hom x (h₁.i k)
      _ = 0 := by simp [hx]
  exact isColimit_cokernel_cofork_eq_zero_mem_closure_rangeW820
    (f := S.f) (p := h₂.p) h₂.hp hp_zero

/-- W820's remaining comparison input is algebraic bijectivity. -/
def comparisonBijectiveTargetW820
    (S : ShortComplex MetrizableLCA.{0}) : Prop :=
  Function.Bijective (S.leftRightHomologyComparison :
    S.leftHomology → S.rightHomology)

/--
Algebraic bijectivity alone supplies the W819 target, because W820 proves the
right-cokernel fiber-closure part.
-/
theorem comparisonRightCokernelFiberClosureTarget_of_bijectiveW820
    (S : ShortComplex MetrizableLCA.{0})
    (hbij : comparisonBijectiveTargetW820 S) :
    comparisonRightCokernelFiberClosureTargetW819 S :=
  ⟨hbij,
    rightCokernelFiberClosure_of_rightHomologyDataW820
      S.leftHomologyData S.rightHomologyData⟩

/-- Algebraic bijectivity alone now supplies W818's fiber-saturation target. -/
theorem comparisonFiberSaturationTarget_of_bijectiveW820
    (S : ShortComplex MetrizableLCA.{0})
    (hbij : comparisonBijectiveTargetW820 S) :
    comparisonFiberSaturationTargetW818 S :=
  comparisonFiberSaturationTarget_of_rightCokernelFiberClosureW819 S
    (comparisonRightCokernelFiberClosureTarget_of_bijectiveW820 S hbij)

/-- Algebraic bijectivity alone supplies W816's bijective-embedding target. -/
theorem comparisonBijectiveEmbeddingTarget_of_bijectiveW820
    (S : ShortComplex MetrizableLCA.{0})
    (hbij : comparisonBijectiveTargetW820 S) :
    comparisonBijectiveEmbeddingTargetW816 S :=
  comparisonBijectiveEmbeddingTarget_of_fiberSaturationW818 S
    (comparisonFiberSaturationTarget_of_bijectiveW820 S hbij)

/--
W820 final route: a universal algebraic-bijectivity proof for the canonical
comparison is enough to produce `CategoryWithHomology MetrizableLCA`.
-/
theorem categoryWithHomology_of_comparisonBijectiveW820
    (h : ∀ S : ShortComplex MetrizableLCA.{0},
      comparisonBijectiveTargetW820 S) :
    CategoryWithHomology MetrizableLCA.{0} :=
  categoryWithHomology_of_comparisonFiberSaturationW818
    (fun S => comparisonFiberSaturationTarget_of_bijectiveW820 S (h S))

/-- Input names for the W820 right-cokernel closure route. -/
def rightCokernelClosureInputNamesW820 :
    List String :=
  ["algebraic bijectivity of the canonical left-right homology comparison"]

theorem rightCokernelClosureInputNamesW820_count :
    rightCokernelClosureInputNamesW820.length = 1 :=
  rfl

/-- Current checked W820 state for the right-cokernel closure route. -/
structure RightCokernelClosureRouteStateW820 :
    Type where
  seed : String
  declarations : List String
  topologyResult : String
  removedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W820 state. -/
def currentRightCokernelClosureRouteStateW820 :
    RightCokernelClosureRouteStateW820
    where
  seed := "w820-right-cokernel-closure-route"
  declarations :=
    ["cokernelSubgroup_mem_closure_rangeW820",
      "isColimit_cokernel_cofork_eq_zero_mem_closure_rangeW820",
      "rightCokernelFiberClosure_of_rightHomologyDataW820",
      "comparisonBijectiveTargetW820",
      "comparisonRightCokernelFiberClosureTarget_of_bijectiveW820",
      "comparisonFiberSaturationTarget_of_bijectiveW820",
      "comparisonBijectiveEmbeddingTarget_of_bijectiveW820",
      "categoryWithHomology_of_comparisonBijectiveW820",
      "rightCokernelClosureInputNamesW820",
      "rightCokernelClosureInputNamesW820_count"]
  topologyResult :=
    "proved: the zero fiber of any limiting MetrizableLCA cokernel projection " ++
      "is the closed range of the source morphism"
  removedInputs :=
    ["right cokernel equality detects closed boundary-closure differences"]
  remainingInputs :=
    rightCokernelClosureInputNamesW820
  productSuccessClaimed := false

theorem currentRightCokernelClosureRouteStateW820_productSuccess :
    currentRightCokernelClosureRouteStateW820.productSuccessClaimed =
      false :=
  rfl

end MetrizableLCA

end LeanLCAExactChallenge
