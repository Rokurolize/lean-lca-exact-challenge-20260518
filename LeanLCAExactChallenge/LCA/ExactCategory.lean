import LeanLCAExactChallenge.LCA.Pullback
import LeanLCAExactChallenge.LCA.Pushout

/-!
The intended exact-category structure on strict metrizable LCA sequences.

Pushout stability is proved by the explicit quotient construction in
`LCA.Pushout`; pullback stability is proved locally in `LCA.Pullback`.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

/-- The Quillen exact-category structure on strict metrizable LCA sequences. -/
@[reducible]
def quillenExactCategory : QuillenExactCategory MetrizableLCA.{u} where
  Conflation := strictShortExact
  conflation_iso e hS := strictShortExact_iso e hS
  split_conflation _ hS := split_strictShortExact hS
  pushout_inflation {S} hS {Y} a :=
    strictShortExact_categorical_pushout (S := S) hS (Y := Y) a
  pullback_deflation {S} hS {Y} a :=
    strictShortExact_categorical_pullback (S := S) hS (Y := Y) a

instance instQuillenExactCategory : QuillenExactCategory MetrizableLCA.{u} :=
  quillenExactCategory

/-- In the canonical exact-category instance, conflations are exactly strict
short exact sequences of metrizable LCA groups. -/
theorem quillenConflation_iff_strictShortExact {S : ShortComplex MetrizableLCA.{u}} :
    QuillenExactCategory.Conflation S ↔ strictShortExact S := by
  rfl

/-- Recover strict short exactness from a canonical Quillen conflation. -/
theorem strictShortExact_of_quillenConflation {S : ShortComplex MetrizableLCA.{u}}
    (hS : QuillenExactCategory.Conflation S) : strictShortExact S :=
  quillenConflation_iff_strictShortExact.mp hS

/-- Regard a strict short exact sequence as a canonical Quillen conflation. -/
theorem quillenConflation_of_strictShortExact {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) : QuillenExactCategory.Conflation S :=
  quillenConflation_iff_strictShortExact.mpr hS

/-- In the canonical exact-category instance, conflations are exactly the
challenge's closed-inclusion/open-surjection algebraically exact sequences. -/
theorem quillenConflation_iff_closed_inclusion_open_surjection_algebraic_exact
    {S : ShortComplex MetrizableLCA.{u}} :
    QuillenExactCategory.Conflation S ↔
      IsClosedEmbedding (S.f : S.X₁ → S.X₂) ∧
      IsOpenMap (S.g : S.X₂ → S.X₃) ∧
      Function.Surjective (S.g : S.X₂ → S.X₃) ∧
      ∀ x₂ : S.X₂, S.g x₂ = 0 → ∃ x₁ : S.X₁, S.f x₁ = x₂ := by
  constructor
  · intro hS
    have hStrict := strictShortExact_of_quillenConflation hS
    exact ⟨hStrict.closed_inclusion, hStrict.open_map, hStrict.surjective,
      hStrict.algebraic_exact⟩
  · rintro ⟨hclosed, hopen, hsurj, hexact⟩
    exact quillenConflation_of_strictShortExact
      { closed_inclusion := hclosed
        open_map := hopen
        surjective := hsurj
        algebraic_exact := hexact }

/-- Build a canonical Quillen conflation from the closed-inclusion/open-
surjection algebraically exact data stated in the challenge. -/
theorem quillenConflation_of_closed_inclusion_open_surjection_algebraic_exact
    {S : ShortComplex MetrizableLCA.{u}}
    (hclosed : IsClosedEmbedding (S.f : S.X₁ → S.X₂))
    (hopen : IsOpenMap (S.g : S.X₂ → S.X₃))
    (hsurj : Function.Surjective (S.g : S.X₂ → S.X₃))
    (hexact : ∀ x₂ : S.X₂, S.g x₂ = 0 → ∃ x₁ : S.X₁, S.f x₁ = x₂) :
    QuillenExactCategory.Conflation S :=
  quillenConflation_iff_closed_inclusion_open_surjection_algebraic_exact.mpr
    ⟨hclosed, hopen, hsurj, hexact⟩

/-- The left map of a canonical Quillen conflation is a closed embedding. -/
theorem closed_inclusion_of_quillenConflation {S : ShortComplex MetrizableLCA.{u}}
    (hS : QuillenExactCategory.Conflation S) :
    IsClosedEmbedding (S.f : S.X₁ → S.X₂) :=
  (quillenConflation_iff_closed_inclusion_open_surjection_algebraic_exact.mp hS).1

/-- The right map of a canonical Quillen conflation is an open surjection. -/
theorem open_surjection_of_quillenConflation {S : ShortComplex MetrizableLCA.{u}}
    (hS : QuillenExactCategory.Conflation S) :
    IsOpenMap (S.g : S.X₂ → S.X₃) ∧ Function.Surjective (S.g : S.X₂ → S.X₃) := by
  have hfields :=
    quillenConflation_iff_closed_inclusion_open_surjection_algebraic_exact.mp hS
  exact ⟨hfields.2.1, hfields.2.2.1⟩

/-- A canonical Quillen conflation has the expected algebraic kernel. -/
theorem algebraic_kernel_of_quillenConflation {S : ShortComplex MetrizableLCA.{u}}
    (hS : QuillenExactCategory.Conflation S) :
    Function.Injective (S.f : S.X₁ → S.X₂) ∧
      ∀ x₂ : S.X₂, S.g x₂ = 0 ↔ ∃ x₁ : S.X₁, S.f x₁ = x₂ :=
  algebraic_kernel_of_strict (strictShortExact_of_quillenConflation hS)

/-- After forgetting topology, a canonical Quillen conflation is exact as a
short complex of abelian groups. -/
theorem forgetToAddCommGrpCat_exact_of_quillenConflation
    {S : ShortComplex MetrizableLCA.{u}} (hS : QuillenExactCategory.Conflation S) :
    (S.map forgetToAddCommGrpCat).Exact :=
  forgetToAddCommGrpCat_exact_of_strict (strictShortExact_of_quillenConflation hS)

/-- After forgetting topology, the left map of a canonical Quillen conflation is
the kernel of the right map in abelian groups. -/
noncomputable def forgetToAddCommGrpCat_kernelForkOfQuillenConflation
    {S : ShortComplex MetrizableLCA.{u}} (hS : QuillenExactCategory.Conflation S) :
    IsLimit (KernelFork.ofι (S.map forgetToAddCommGrpCat).f
      (S.map forgetToAddCommGrpCat).zero) :=
  forgetToAddCommGrpCat_kernelForkOfStrictShortExact
    (strictShortExact_of_quillenConflation hS)

/-- After forgetting topology, the right map of a canonical Quillen conflation is
the cokernel of the left map in abelian groups. -/
noncomputable def forgetToAddCommGrpCat_cokernelCoforkOfQuillenConflation
    {S : ShortComplex MetrizableLCA.{u}} (hS : QuillenExactCategory.Conflation S) :
    IsColimit (CokernelCofork.ofπ (S.map forgetToAddCommGrpCat).g
      (S.map forgetToAddCommGrpCat).zero) :=
  forgetToAddCommGrpCat_cokernelCoforkOfStrictShortExact
    (strictShortExact_of_quillenConflation hS)

/-- A canonical Quillen conflation has the expected categorical kernel fork. -/
noncomputable def kernelForkOfQuillenConflation {S : ShortComplex MetrizableLCA.{u}}
    (hS : QuillenExactCategory.Conflation S) :
    IsLimit (KernelFork.ofι S.f S.zero) :=
  kernelForkOfStrictShortExact (strictShortExact_of_quillenConflation hS)

/-- A canonical Quillen conflation has the expected categorical cokernel cofork. -/
noncomputable def cokernelCoforkOfQuillenConflation {S : ShortComplex MetrizableLCA.{u}}
    (hS : QuillenExactCategory.Conflation S) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  cokernelCoforkOfStrictShortExact (strictShortExact_of_quillenConflation hS)

/-- In the canonical exact-category instance, inflations are precisely maps that
occur as the left map of a strict short exact sequence. -/
theorem quillenInflation_iff_exists_strictShortExact {X Y : MetrizableLCA.{u}}
    (i : X ⟶ Y) :
    QuillenExactCategory.inflation i ↔
      ∃ (Z : MetrizableLCA.{u}) (g : Y ⟶ Z) (zero : i ≫ g = 0),
        strictShortExact (ShortComplex.mk i g zero) := by
  constructor
  · rintro ⟨Z, g, zero, hS⟩
    exact ⟨Z, g, zero, strictShortExact_of_quillenConflation hS⟩
  · rintro ⟨Z, g, zero, hS⟩
    exact ⟨Z, g, zero, quillenConflation_of_strictShortExact hS⟩

/-- In the canonical metrizable LCA exact category, inflations are stable under
composition.  The composite's displayed cokernel is the explicit LCA quotient
by the closed algebraic range of the composite. -/
theorem quillenInflation_comp {X Y Z : MetrizableLCA.{u}} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : QuillenExactCategory.inflation i) (hj : QuillenExactCategory.inflation j) :
    QuillenExactCategory.inflation (i ≫ j) := by
  rw [quillenInflation_iff_exists_strictShortExact] at hi hj ⊢
  rcases hi with ⟨Zi, gi, zi, hSi⟩
  rcases hj with ⟨Zj, gj, zj, hSj⟩
  refine ⟨cokernelObj (i ≫ j), cokernelπ (i ≫ j), comp_cokernelπ (i ≫ j), ?_⟩
  refine
    { closed_inclusion := ?_
      open_map := ?_
      surjective := ?_
      algebraic_exact := ?_ }
  · exact hSj.closed_inclusion.comp hSi.closed_inclusion
  · exact quotientMap_openMap Z (cokernelSubgroup (i ≫ j))
      (AddSubgroup.isClosed_topologicalClosure _)
  · exact quotientMap_surjective Z (cokernelSubgroup (i ≫ j))
      (AddSubgroup.isClosed_topologicalClosure _)
  · intro z hz
    have hmem : z ∈ cokernelSubgroup (i ≫ j) := by
      change ((z : Z) : Z ⧸ cokernelSubgroup (i ≫ j)) = 0 at hz
      rwa [QuotientAddGroup.eq_zero_iff] at hz
    let R : AddSubgroup Z :=
      AddSubgroup.map (i ≫ j).hom.toAddMonoidHom (⊤ : AddSubgroup X)
    have hR_closed : IsClosed (R : Set Z) := by
      have hset : IsClosed (Set.range ((i ≫ j) : X → Z)) :=
        (hSj.closed_inclusion.comp hSi.closed_inclusion).isClosed_range
      have hR_set : (R : Set Z) = Set.range ((i ≫ j) : X → Z) := by
        ext z
        constructor
        · rintro ⟨x, _hx, rfl⟩
          exact ⟨x, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨x, trivial, rfl⟩
      rwa [hR_set]
    have hle : cokernelSubgroup (i ≫ j) ≤ R := by
      rw [cokernelSubgroup]
      apply AddSubgroup.topologicalClosure_minimal
      · intro _ hy
        exact hy
      · exact hR_closed
    rcases hle hmem with ⟨x, _hx, hx⟩
    exact ⟨x, hx⟩

/-- In the canonical exact-category instance, deflations are precisely maps that
occur as the right map of a strict short exact sequence. -/
theorem quillenDeflation_iff_exists_strictShortExact {X Y : MetrizableLCA.{u}}
    (p : X ⟶ Y) :
    QuillenExactCategory.deflation p ↔
      ∃ (W : MetrizableLCA.{u}) (f : W ⟶ X) (zero : f ≫ p = 0),
        strictShortExact (ShortComplex.mk f p zero) := by
  constructor
  · rintro ⟨W, f, zero, hS⟩
    exact ⟨W, f, zero, strictShortExact_of_quillenConflation hS⟩
  · rintro ⟨W, f, zero, hS⟩
    exact ⟨W, f, zero, quillenConflation_of_strictShortExact hS⟩

/-- In the canonical metrizable LCA exact category, pushouts preserve inflations. -/
theorem quillenInflation_pushout {X Y Y' : MetrizableLCA.{u}} {i : X ⟶ Y}
    (hi : QuillenExactCategory.inflation i) (a : X ⟶ Y') [HasPushout i a] :
    QuillenExactCategory.inflation (pushout.inr i a) :=
  QuillenExactCategory.pushout_inflation_of_inflation hi a

/-- In the canonical metrizable LCA exact category, pullbacks preserve deflations. -/
theorem quillenDeflation_pullback {X Y Y' : MetrizableLCA.{u}} {p : X ⟶ Y}
    (hp : QuillenExactCategory.deflation p) (a : Y' ⟶ Y) [HasPullback a p] :
    QuillenExactCategory.deflation (pullback.fst a p) :=
  QuillenExactCategory.pullback_deflation_of_deflation hp a

end MetrizableLCA

end LeanLCAExactChallenge
