import LeanLCAExactChallenge.Infinity.Basic
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# Infinity-categorical limits and pointedness

Limits and colimits in a quasicategory are expressed here by bicategorical adjoints to the
constant-diagram map.  In mathlib v4.30 the internal hom into a quasicategory has not yet
been proved to be a quasicategory, so that proof is an explicit argument rather than a
hidden assumption.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

/-- The terminal simplicial set is a quasicategory. -/
instance terminalSSet_quasicategory : SSet.Quasicategory (⊤_ SSet.{u}) where
  hornFilling' _ _ _σ₀ _ _ :=
    ⟨Limits.terminal.from _, Limits.terminalIsTerminal.hom_ext _ _⟩

/-- The terminal simplicial set, bundled as a quasicategory. -/
def terminalQCat : SSet.QCat.{u} :=
  ⟨⊤_ SSet.{u}, inferInstance⟩

/-- The unique map from a quasicategory to the terminal quasicategory. -/
def toTerminalQCat (Q : SSet.QCat.{u}) : Q ⟶ terminalQCat :=
  ⟨Limits.terminal.from Q.obj⟩

/-- A chosen zero object.

The two adjunctions state that the selected object is both initial and terminal in the
strict bicategory of quasicategories. -/
structure PointedStructure (Q : SSet.QCat.{u}) where
  zeroObject : terminalQCat ⟶ Q
  initialAdjunction : Bicategory.Adjunction zeroObject (toTerminalQCat Q)
  terminalAdjunction : Bicategory.Adjunction (toTerminalQCat Q) zeroObject

/-- The internal hom from `K` to `Q`, bundled as a quasicategory using an explicit proof. -/
def functorQCat (K : SSet.{u}) (Q : SSet.QCat.{u})
    (h : SSet.Quasicategory ((ihom K).obj Q.obj)) : SSet.QCat.{u} :=
  ⟨(ihom K).obj Q.obj, h⟩

/-- The constant `K`-diagram map into the functor quasicategory. -/
def constantDiagram (K : SSet.{u}) (Q : SSet.QCat.{u})
    (h : SSet.Quasicategory ((ihom K).obj Q.obj)) :
    Q ⟶ functorQCat K Q h :=
  ⟨curry (snd K Q.obj)⟩

/-- `Q` has `K`-shaped limits when the constant-diagram map has a right infinity-adjoint. -/
def HasLimitsOfShape (K : SSet.{u}) (Q : SSet.QCat.{u})
    (h : SSet.Quasicategory ((ihom K).obj Q.obj)) : Prop :=
  Bicategory.IsLeftAdjoint (constantDiagram K Q h)

/-- `Q` has `K`-shaped colimits when the constant-diagram map has a left infinity-adjoint. -/
def HasColimitsOfShape (K : SSet.{u}) (Q : SSet.QCat.{u})
    (h : SSet.Quasicategory ((ihom K).obj Q.obj)) : Prop :=
  Bicategory.IsRightAdjoint (constantDiagram K Q h)

/-- A quasicategory has finite infinity-limits when it has limits for every finite
simplicial-set shape. -/
def HasFiniteInfinityLimits (Q : SSet.QCat.{u}) : Prop :=
  ∀ (K : SSet.{u}), SSet.Finite K →
    ∃ h : SSet.Quasicategory ((ihom K).obj Q.obj),
      HasLimitsOfShape K Q h

/-- A quasicategory has finite infinity-colimits when it has colimits for every finite
simplicial-set shape. -/
def HasFiniteInfinityColimits (Q : SSet.QCat.{u}) : Prop :=
  ∀ (K : SSet.{u}), SSet.Finite K →
    ∃ h : SSet.Quasicategory ((ihom K).obj Q.obj),
      HasColimitsOfShape K Q h

/-- Finite bicompleteness in the infinity-categorical sense. -/
def HasFiniteInfinityBicompleteness (Q : SSet.QCat.{u}) : Prop :=
  HasFiniteInfinityLimits Q ∧ HasFiniteInfinityColimits Q

end Infinity
end LeanLCAExactChallenge
