import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
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

/-- The bounded derived ordinary category obtained by localizing bounded complexes at exact weak
equivalences. -/
abbrev BoundedDerivedCategory [HasBinaryBiproducts C] : Type (max u v) :=
  (boundedExactWeakEquivalence C).Localization

/-- The bounded derived infinity-category as the quasicategory nerve of the bounded derived
ordinary category. -/
noncomputable abbrev BoundedDerivedInfinityCategory [HasBinaryBiproducts C] : SSet.QCat :=
  ⟨CategoryTheory.nerve (BoundedDerivedCategory C), inferInstance⟩

/-- The bounded derived category for a local Quillen exact category. -/
abbrev Dbounded [HasBinaryBiproducts C] : Type (max u v) :=
  BoundedDerivedCategory C

/-- The localization functor from bounded complexes to the bounded derived category. -/
abbrev Dbounded.localization [HasBinaryBiproducts C] :
    (boundedCochainComplex C).FullSubcategory ⥤ Dbounded C :=
  (boundedExactWeakEquivalence C).Q

/-- Promote a bounded cochain complex to the bounded derived category. -/
abbrev Dbounded.of [HasBinaryBiproducts C]
    (K : (boundedCochainComplex C).FullSubcategory) : Dbounded C :=
  (Dbounded.localization C).obj K

/-- The bounded derived category, regarded as an object of the category of quasicategories. -/
noncomputable abbrev Dbounded.infinityCategory [HasBinaryBiproducts C] : SSet.QCat :=
  BoundedDerivedInfinityCategory C

/-- The underlying simplicial set of the bounded derived quasicategory. -/
noncomputable abbrev Dbounded.infinityNerve [HasBinaryBiproducts C] : SSet :=
  (Dbounded.infinityCategory C).1

/-- The bounded derived nerve is a quasicategory. -/
theorem Dbounded.infinityNerve_quasicategory [HasBinaryBiproducts C] :
    SSet.Quasicategory (Dbounded.infinityNerve C) := by
  dsimp [Dbounded.infinityNerve, Dbounded.infinityCategory, BoundedDerivedInfinityCategory]
  infer_instance

/-- The homotopy category of the bounded derived quasicategory recovers `Dbounded`. -/
noncomputable def Dbounded.homotopyCategoryIso [HasBinaryBiproducts C] :
    SSet.hoFunctor.obj (Dbounded.infinityNerve C) ≅ Cat.of (Dbounded C) :=
  CategoryTheory.nerveFunctorCompHoFunctorIso.app (Cat.of (Dbounded C))

/-- Checked abelian-category comparison target provided by mathlib. -/
abbrev abelianDerivedCategory (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{v} A] : Type (max u v) :=
  DerivedCategory A

end LeanLCAExactChallenge
