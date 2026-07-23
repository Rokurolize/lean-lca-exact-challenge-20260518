/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.MetrizableDGQuotientDGBundle
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Monoidal Dold--Kan reduction for the corrected quotient coefficient ring

An Alexander--Whitney oplax monoidal structure on normalized Moore chains over the corrected
quotient coefficient ring induces a coherent lax monoidal structure on the Dold--Kan inverse.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientDoldKanMonoidal

open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- Modules over the universe-lifted quotient coefficient ring. -/
abbrev QuotientModule := ModuleCat.{1} QuotientCoefficientRing

/-- Nonnegative chain complexes over the quotient coefficient ring. -/
abbrev QuotientChain := ChainComplex QuotientModule ℕ

/-- Simplicial modules over the quotient coefficient ring. -/
abbrev QuotientSimplicialModule := SimplicialObject QuotientModule

/-- The Dold--Kan equivalence over the corrected quotient coefficient ring. -/
abbrev quotientModuleDoldKanEquivalence :
    QuotientSimplicialModule ≌ QuotientChain :=
  CategoryTheory.Abelian.DoldKan.equivalence
    (A := ModuleCat.{1} QuotientCoefficientRing)

/-- The Alexander--Whitney oplax structure required on normalized Moore chains. -/
abbrev NormalizedMooreOplaxMonoidal :=
  quotientModuleDoldKanEquivalence.functor.OplaxMonoidal

/-- Transfer an oplax structure on normalization to the Dold--Kan inverse. -/
@[implicit_reducible]
def inverseLaxMonoidalOfNormalizedOplax
    (h : NormalizedMooreOplaxMonoidal) :
    quotientModuleDoldKanEquivalence.inverse.LaxMonoidal := by
  letI := h
  exact quotientModuleDoldKanEquivalence.toAdjunction.rightAdjointLaxMonoidal

/-- The induced tensorator on the quotient Dold--Kan inverse. -/
def inverseTensorator (h : NormalizedMooreOplaxMonoidal)
    (K L : QuotientChain) :
    quotientModuleDoldKanEquivalence.inverse.obj K ⊗
        quotientModuleDoldKanEquivalence.inverse.obj L ⟶
      quotientModuleDoldKanEquivalence.inverse.obj (K ⊗ L) := by
  letI := inverseLaxMonoidalOfNormalizedOplax h
  exact Functor.LaxMonoidal.μ quotientModuleDoldKanEquivalence.inverse K L

/-- The tensorator is adjoint to Alexander--Whitney followed by the two counits. -/
theorem inverseTensorator_eq_adjunct (h : NormalizedMooreOplaxMonoidal)
    (K L : QuotientChain) :
    inverseTensorator h K L =
      quotientModuleDoldKanEquivalence.toAdjunction.homEquiv _ _
        (Functor.OplaxMonoidal.δ quotientModuleDoldKanEquivalence.functor
            (quotientModuleDoldKanEquivalence.inverse.obj K)
            (quotientModuleDoldKanEquivalence.inverse.obj L) ≫
          (quotientModuleDoldKanEquivalence.counitIso.hom.app K ⊗ₘ
            quotientModuleDoldKanEquivalence.counitIso.hom.app L)) := by
  letI := h
  rfl

end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
