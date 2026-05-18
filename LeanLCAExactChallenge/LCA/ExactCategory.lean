import LeanLCAExactChallenge.LCA.StrictExact

/-!
The intended exact-category structure on strict metrizable LCA sequences.

The construction below is intentionally parameterized by explicit source-patch
assumptions.  Current mathlib provides the underlying categorical and
topological anchors used here, but not the quasi-abelian/exact-category theorem
needed to prove the strict LCA axioms internally.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

/-- Source-patch assumptions needed to upgrade strict LCA sequences to a Quillen exact category. -/
structure StrictExactQuillenAxioms : Prop where
  iso {S T : ShortComplex MetrizableLCA.{u}} (e : S ≅ T) :
    strictShortExact S → strictShortExact T
  split (S : ShortComplex MetrizableLCA.{u}) : S.ShortExact → strictShortExact S
  pushout {S : ShortComplex MetrizableLCA.{u}} (hS : strictShortExact S) {Y : MetrizableLCA.{u}}
    (a : S.X₁ ⟶ Y) [HasPushout S.f a] :
    ∃ (Z : MetrizableLCA.{u}) (g : pushout S.f a ⟶ Z)
      (zero : pushout.inr S.f a ≫ g = 0),
      strictShortExact (ShortComplex.mk (pushout.inr S.f a) g zero)
  pullback {S : ShortComplex MetrizableLCA.{u}} (hS : strictShortExact S) {Y : MetrizableLCA.{u}}
    (a : Y ⟶ S.X₃) [HasPullback a S.g] :
    ∃ (X : MetrizableLCA.{u}) (f : X ⟶ pullback a S.g)
      (zero : f ≫ pullback.fst a S.g = 0),
      strictShortExact (ShortComplex.mk f (pullback.fst a S.g) zero)

/--
The Quillen exact-category structure obtained once the missing strict LCA
stability theorem is supplied.
-/
@[reducible]
def quillenExactCategory (h : StrictExactQuillenAxioms.{u}) :
    QuillenExactCategory MetrizableLCA.{u} where
  Conflation := strictShortExact
  conflation_iso e hS := h.iso e hS
  split_conflation S hS := h.split S hS
  pushout_inflation {S} hS {Y} a := h.pushout (S := S) hS (Y := Y) a
  pullback_deflation {S} hS {Y} a := h.pullback (S := S) hS (Y := Y) a

end MetrizableLCA

end LeanLCAExactChallenge
