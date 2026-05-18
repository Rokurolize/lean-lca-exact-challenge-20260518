import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.CategoryTheory.Localization.HasLocalization
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
Bounded derived localization for the local Quillen exact-category interface.

The object category is the full subcategory of cochain complexes that are
strictly supported between two integer bounds. Its weak equivalences are the
morphisms whose mapping cone is exact in the chosen Quillen exact structure.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- Bounded cochain complexes over an exact category. -/
def boundedCochainComplex : ObjectProperty (CochainComplex C ℤ) :=
  fun K => ∃ (a b : ℤ), K.IsStrictlyGE a ∧ K.IsStrictlyLE b

/-- Exact complexes in the Quillen exact-category sense. -/
def exactAcyclic (K : CochainComplex C ℤ) : Prop :=
  ∀ i : ℤ, QuillenExactCategory.Conflation (K.sc i)

/-- Exact quasi-isomorphisms between bounded complexes, detected by the mapping cone. -/
noncomputable def boundedExactWeakEquivalence [HasBinaryBiproducts C] :
    MorphismProperty ((boundedCochainComplex C).FullSubcategory) :=
  fun _ _ f => exactAcyclic C (CochainComplex.mappingCone ((boundedCochainComplex C).ι.map f))

/-- The bounded derived category obtained by localizing bounded complexes at exact weak
equivalences. -/
abbrev BoundedDerivedInfinityCategory [HasBinaryBiproducts C] : Type (max u v) :=
  (boundedExactWeakEquivalence C).Localization

/-- The bounded derived category for a local Quillen exact category. -/
abbrev Dbounded [HasBinaryBiproducts C] : Type (max u v) :=
  BoundedDerivedInfinityCategory C

/-- The localization functor from bounded complexes to the bounded derived category. -/
abbrev Dbounded.localization [HasBinaryBiproducts C] :
    (boundedCochainComplex C).FullSubcategory ⥤ Dbounded C :=
  (boundedExactWeakEquivalence C).Q

/-- Promote a bounded cochain complex to the bounded derived category. -/
abbrev Dbounded.of [HasBinaryBiproducts C]
    (K : (boundedCochainComplex C).FullSubcategory) : Dbounded C :=
  (Dbounded.localization C).obj K

/-- Checked abelian-category comparison target provided by mathlib. -/
abbrev abelianDerivedCategory (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{v} A] : Type (max u v) :=
  DerivedCategory A

end LeanLCAExactChallenge
