import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Monoidal Dold--Kan reduction

For integer modules, an Alexander--Whitney oplax monoidal structure on the normalized Moore
complex functor automatically induces a coherent lax monoidal structure on the Dold--Kan
inverse, because the latter is its right adjoint.  This file formalizes that reduction.

It does not construct the Alexander--Whitney maps themselves.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace DoldKanMonoidal

open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- The Dold--Kan equivalence for integer modules with their algebraic tensor product. -/
abbrev zModuleDoldKanEquivalence :
    SimplicialObject (ModuleCat.{0} ℤ) ≌ ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  CategoryTheory.Abelian.DoldKan.equivalence (A := ModuleCat.{0} ℤ)

/-- The precise remaining Alexander--Whitney structure on normalized Moore chains. -/
abbrev NormalizedMooreOplaxMonoidal :=
  zModuleDoldKanEquivalence.functor.OplaxMonoidal

/-- An Alexander--Whitney oplax structure on normalization induces all coherent lax-monoidal
data on the Dold--Kan inverse by adjunction. -/
@[implicit_reducible]
def inverseLaxMonoidalOfNormalizedOplax
    (h : NormalizedMooreOplaxMonoidal) :
    zModuleDoldKanEquivalence.inverse.LaxMonoidal := by
  letI := h
  exact zModuleDoldKanEquivalence.toAdjunction.rightAdjointLaxMonoidal

/-- The induced Dold--Kan tensorator. -/
def inverseTensorator (h : NormalizedMooreOplaxMonoidal)
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    zModuleDoldKanEquivalence.inverse.obj K ⊗
        zModuleDoldKanEquivalence.inverse.obj L ⟶
      zModuleDoldKanEquivalence.inverse.obj (K ⊗ L) := by
  letI := inverseLaxMonoidalOfNormalizedOplax h
  exact Functor.LaxMonoidal.μ zModuleDoldKanEquivalence.inverse K L

/-- The induced tensorator is the adjoint of Alexander--Whitney followed by the two
Dold--Kan counits. -/
theorem inverseTensorator_eq_adjunct (h : NormalizedMooreOplaxMonoidal)
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    inverseTensorator h K L =
      zModuleDoldKanEquivalence.toAdjunction.homEquiv _ _
        (Functor.OplaxMonoidal.δ zModuleDoldKanEquivalence.functor
            (zModuleDoldKanEquivalence.inverse.obj K)
            (zModuleDoldKanEquivalence.inverse.obj L) ≫
          (zModuleDoldKanEquivalence.counitIso.hom.app K ⊗ₘ
            zModuleDoldKanEquivalence.counitIso.hom.app L)) := by
  letI := h
  rfl

end DoldKanMonoidal
end Infinity
end LeanLCAExactChallenge
