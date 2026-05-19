import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
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

/-- Boundedness is invariant under isomorphism of cochain complexes. -/
instance boundedCochainComplex_isClosedUnderIsomorphisms :
    (boundedCochainComplex C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨a, b, hge, hle⟩
    letI : K.IsStrictlyGE a := hge
    letI : K.IsStrictlyLE b := hle
    exact ⟨a, b, CochainComplex.isStrictlyGE_of_iso e a,
      CochainComplex.isStrictlyLE_of_iso e b⟩

/-- Bounded cochain complexes are closed under the cochain shift. -/
instance boundedCochainComplex_isStableUnderShift :
    (boundedCochainComplex C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := by
    refine ⟨?_⟩
    rintro K ⟨a, b, hge, hle⟩
    letI : K.IsStrictlyGE a := hge
    letI : K.IsStrictlyLE b := hle
    exact ⟨a - n, b - n, K.isStrictlyGE_shift a n (a - n) (by omega),
      K.isStrictlyLE_shift b n (b - n) (by omega)⟩

/-- The full category of bounded cochain complexes before localization. -/
abbrev BoundedComplexCategory : Type (max u v) :=
  (boundedCochainComplex C).FullSubcategory

/-- The inclusion of bounded complexes into all cochain complexes. -/
abbrev BoundedComplexCategory.ι : BoundedComplexCategory C ⥤ CochainComplex C ℤ :=
  (boundedCochainComplex C).ι

/-- Exact complexes in the Quillen exact-category sense. -/
def exactAcyclic (K : CochainComplex C ℤ) : Prop :=
  ∀ i : ℤ, QuillenExactCategory.Conflation (K.sc i)

/-- Exact acyclicity is invariant under isomorphism of cochain complexes. -/
theorem exactAcyclic_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L)
    (hK : exactAcyclic C K) : exactAcyclic C L := by
  intro i
  exact QuillenExactCategory.conflation_iso
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).mapIso e) (hK i)

/-- Exact acyclicity is stable under cochain shifts. -/
theorem exactAcyclic_shift (K : CochainComplex C ℤ) (n : ℤ)
    (hK : exactAcyclic C K) : exactAcyclic C (K⟦n⟧) := by
  intro i
  exact QuillenExactCategory.conflation_iso
    ((CochainComplex.shiftShortComplexFunctorIso C n i (n + i) rfl).app K).symm
    (hK (n + i))

/-- Exact acyclicity is invariant under cochain shifts. -/
theorem exactAcyclic_shift_iff (K : CochainComplex C ℤ) (n : ℤ) :
    exactAcyclic C (K⟦n⟧) ↔ exactAcyclic C K := by
  constructor
  · intro hK i
    exact QuillenExactCategory.conflation_iso
      ((CochainComplex.shiftShortComplexFunctorIso C n (i - n) i (by omega)).app K)
      (hK (i - n))
  · exact exactAcyclic_shift C K n

/-- Exact acyclicity of mapping cones is invariant under cochain shifts. -/
theorem exactAcyclic_mappingCone_shift_iff [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    exactAcyclic C (CochainComplex.mappingCone (f⟦n⟧')) ↔
      exactAcyclic C (CochainComplex.mappingCone f) := by
  constructor
  · intro hf
    have hShift : exactAcyclic C ((CochainComplex.mappingCone f)⟦n⟧) :=
      exactAcyclic_of_iso C (CochainComplex.mappingCone.shiftIso f n).symm hf
    exact (exactAcyclic_shift_iff C (CochainComplex.mappingCone f) n).1 hShift
  · intro hf
    exact exactAcyclic_of_iso C (CochainComplex.mappingCone.shiftIso f n)
      (exactAcyclic_shift C (CochainComplex.mappingCone f) n hf)

/-- A commuting square whose vertical maps are isomorphisms induces an isomorphism of mapping
cones. -/
noncomputable def mappingConeIsoOfCommIso [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
    (eK : K₁ ≅ K₂) (eL : L₁ ≅ L₂)
    (comm : φ₁ ≫ eL.hom = eK.hom ≫ φ₂) :
    CochainComplex.mappingCone φ₁ ≅ CochainComplex.mappingCone φ₂ where
  hom := CochainComplex.mappingCone.map φ₁ φ₂ eK.hom eL.hom comm
  inv := CochainComplex.mappingCone.map φ₂ φ₁ eK.inv eL.inv (by
    rw [← cancel_mono eL.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [comm]
    simp)
  hom_inv_id := by
    rw [← CochainComplex.mappingCone.map_comp φ₁ φ₂ φ₁ eK.hom eL.hom comm eK.inv eL.inv]
    simpa using CochainComplex.mappingCone.map_id φ₁
  inv_hom_id := by
    rw [← CochainComplex.mappingCone.map_comp φ₂ φ₁ φ₂ eK.inv eL.inv _ eK.hom eL.hom]
    simpa using CochainComplex.mappingCone.map_id φ₂

/-- Exact acyclicity of mapping cones is invariant under isomorphic commutative squares. -/
theorem exactAcyclic_mappingCone_congr_iff [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
    (eK : K₁ ≅ K₂) (eL : L₁ ≅ L₂)
    (comm : φ₁ ≫ eL.hom = eK.hom ≫ φ₂) :
    exactAcyclic C (CochainComplex.mappingCone φ₁) ↔
      exactAcyclic C (CochainComplex.mappingCone φ₂) := by
  constructor
  · exact exactAcyclic_of_iso C (mappingConeIsoOfCommIso C eK eL comm)
  · exact exactAcyclic_of_iso C (mappingConeIsoOfCommIso C eK eL comm).symm

/-- Exact quasi-isomorphisms between bounded complexes, detected by the mapping cone. -/
noncomputable def boundedExactWeakEquivalence [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  fun _ _ f => exactAcyclic C (CochainComplex.mappingCone ((boundedCochainComplex C).ι.map f))

/-- Exact weak equivalences of bounded complexes are invariant under cochain shifts. -/
theorem boundedExactWeakEquivalence_shift_iff [HasBinaryBiproducts C]
    {K L : BoundedComplexCategory C} (f : K ⟶ L) (n : ℤ) :
    boundedExactWeakEquivalence C (f⟦n⟧') ↔ boundedExactWeakEquivalence C f := by
  let ι : BoundedComplexCategory C ⥤ CochainComplex C ℤ := (boundedCochainComplex C).ι
  change exactAcyclic C (CochainComplex.mappingCone (ι.map (f⟦n⟧'))) ↔
    exactAcyclic C (CochainComplex.mappingCone (ι.map f))
  exact (exactAcyclic_mappingCone_congr_iff C ((ι.commShiftIso n).app K)
    ((ι.commShiftIso n).app L) (by
      simpa using Functor.commShiftIso_hom_naturality ι f n)).trans
    (exactAcyclic_mappingCone_shift_iff C (ι.map f) n)

/-- The exact weak equivalences on bounded complexes are compatible with shifts. -/
noncomputable instance boundedExactWeakEquivalence_isCompatibleWithShift [HasBinaryBiproducts C] :
    (boundedExactWeakEquivalence C).IsCompatibleWithShift ℤ where
  condition n := by
    ext K L f
    exact boundedExactWeakEquivalence_shift_iff C f n

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
