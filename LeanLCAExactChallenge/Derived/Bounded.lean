import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Localization.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
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
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- Bounded cochain complexes over an exact category. -/
def boundedCochainComplex : ObjectProperty (CochainComplex C ℤ) :=
  fun K => ∃ (a b : ℤ), K.IsStrictlyGE a ∧ K.IsStrictlyLE b

/-- The zero cochain complex is bounded. -/
instance boundedCochainComplex_containsZero [HasZeroObject C] :
    (boundedCochainComplex C).ContainsZero where
  exists_zero := ⟨(0 : CochainComplex C ℤ), isZero_zero _, by
    exact ⟨0, 0, inferInstance, inferInstance⟩⟩

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

omit [QuillenExactCategory C] in
/-- Mapping cones of morphisms between bounded cochain complexes are bounded. -/
theorem boundedCochainComplex_mappingCone [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : boundedCochainComplex C K) (hL : boundedCochainComplex C L) :
    boundedCochainComplex C (CochainComplex.mappingCone f) := by
  obtain ⟨aK, bK, hKge, hKle⟩ := hK
  obtain ⟨aL, bL, hLge, hLle⟩ := hL
  letI : K.IsStrictlyGE aK := hKge
  letI : K.IsStrictlyLE bK := hKle
  letI : L.IsStrictlyGE aL := hLge
  letI : L.IsStrictlyLE bL := hLle
  refine ⟨min (aK - 1) aL, max (bK - 1) bL, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · exact K.isZero_of_isStrictlyGE aK (i + 1) (by omega)
    · exact L.isZero_of_isStrictlyGE aL i (by omega)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · exact K.isZero_of_isStrictlyLE bK (i + 1) (by omega)
    · exact L.isZero_of_isStrictlyLE bL i (by omega)

omit [QuillenExactCategory C] in
/-- If a mapping cone is bounded, then its target complex is bounded. -/
theorem boundedCochainComplex_of_mappingCone_right [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedCochainComplex C L := by
  obtain ⟨a, b, hge, hle⟩ := hCone
  letI : (CochainComplex.mappingCone f).IsStrictlyGE a := hge
  letI : (CochainComplex.mappingCone f).IsStrictlyLE b := hle
  refine ⟨a, b, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact ((CochainComplex.mappingCone.isZero_X_iff f i).1
      ((CochainComplex.mappingCone f).isZero_of_isStrictlyGE a i hi)).2
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact ((CochainComplex.mappingCone.isZero_X_iff f i).1
      ((CochainComplex.mappingCone f).isZero_of_isStrictlyLE b i hi)).2

omit [QuillenExactCategory C] in
/-- If a mapping cone is bounded, then its source complex is bounded. -/
theorem boundedCochainComplex_of_mappingCone_left [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedCochainComplex C K := by
  obtain ⟨a, b, hge, hle⟩ := hCone
  letI : (CochainComplex.mappingCone f).IsStrictlyGE a := hge
  letI : (CochainComplex.mappingCone f).IsStrictlyLE b := hle
  refine ⟨a + 1, b + 1, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    have hConeZero : IsZero ((CochainComplex.mappingCone f).X (i - 1)) :=
      (CochainComplex.mappingCone f).isZero_of_isStrictlyGE a (i - 1) (by omega)
    have hK := ((CochainComplex.mappingCone.isZero_X_iff f (i - 1)).1 hConeZero).1
    simpa using hK
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    have hConeZero : IsZero ((CochainComplex.mappingCone f).X (i - 1)) :=
      (CochainComplex.mappingCone f).isZero_of_isStrictlyLE b (i - 1) (by omega)
    have hK := ((CochainComplex.mappingCone.isZero_X_iff f (i - 1)).1 hConeZero).1
    simpa using hK

/-- The full category of bounded cochain complexes before localization. -/
abbrev BoundedComplexCategory : Type (max u v) :=
  (boundedCochainComplex C).FullSubcategory

/-- The inclusion of bounded complexes into all cochain complexes. -/
abbrev BoundedComplexCategory.ι : BoundedComplexCategory C ⥤ CochainComplex C ℤ :=
  (boundedCochainComplex C).ι

/-- The category of bounded complexes has a zero object when the base category does. -/
instance boundedComplexCategory_hasZeroObject [HasZeroObject C] :
    HasZeroObject (BoundedComplexCategory C) := by
  infer_instance

/-- Exact complexes in the Quillen exact-category sense. -/
def exactAcyclic (K : CochainComplex C ℤ) : Prop :=
  ∀ i : ℤ, QuillenExactCategory.Conflation (K.sc i)

/-- Exact acyclicity is invariant under isomorphism of cochain complexes. -/
theorem exactAcyclic_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L)
    (hK : exactAcyclic C K) : exactAcyclic C L := by
  intro i
  exact QuillenExactCategory.conflation_iso
    ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) i).mapIso e) (hK i)

/-- A cochain complex whose degreewise short complexes are split is exact acyclic. -/
theorem exactAcyclic_of_splittings {K : CochainComplex C ℤ}
    (hK : ∀ i : ℤ, (K.sc i).Splitting) : exactAcyclic C K := by
  intro i
  exact QuillenExactCategory.split_conflation (K.sc i) (hK i)

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

/-- The zero complex is exact acyclic in any local Quillen exact category. -/
theorem exactAcyclic_zero [HasZeroObject C] :
    exactAcyclic C (0 : CochainComplex C ℤ) := by
  intro i
  apply QuillenExactCategory.split_conflation
  refine { r := 0, s := 0, f_r := ?_, s_g := ?_, id := ?_ }
  · apply (Functor.map_isZero
      (HomologicalComplex.eval C (ComplexShape.up ℤ) ((ComplexShape.up ℤ).prev i))
      (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))).eq_of_src
  · apply (Functor.map_isZero
      (HomologicalComplex.eval C (ComplexShape.up ℤ) ((ComplexShape.up ℤ).next i))
      (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))).eq_of_src
  · apply (Functor.map_isZero
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
      (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))).eq_of_src

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

/-- Exact acyclic complexes as an object predicate on the homotopy category.

This predicate records the exact-category analogue of mathlib's abelian
`HomotopyCategory.subcategoryAcyclic`. It is intentionally not marked as triangulated here:
that homotopy-invariance and closure result is the remaining Verdier-route proof obligation. -/
def exactAcyclicHomotopyObject :
    ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K => exactAcyclic C K.as

/-- On quotient objects, the homotopy-category exact-acyclic predicate is the original
degreewise exact-acyclic predicate. -/
theorem exactAcyclicHomotopyObject_quotient_obj_iff (K : CochainComplex C ℤ) :
    exactAcyclicHomotopyObject C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ↔
      exactAcyclic C K := by
  rfl

/-- Exact acyclic homotopy objects contain a zero object. -/
instance exactAcyclicHomotopyObject_containsZero [HasZeroObject C] :
    (exactAcyclicHomotopyObject C).ContainsZero where
  exists_zero := by
    refine ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (0 : CochainComplex C ℤ),
      ?_, ?_⟩
    · exact Functor.map_isZero (HomotopyCategory.quotient C (ComplexShape.up ℤ))
        (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))
    · exact exactAcyclic_zero C

/-- The isomorphism closure of exact acyclic homotopy objects. -/
abbrev exactAcyclicHomotopyIsoClosure :
    ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (exactAcyclicHomotopyObject C).isoClosure

/-- The isomorphism closure of exact acyclic homotopy objects is stable under cochain shifts. -/
noncomputable instance exactAcyclicHomotopyIsoClosure_isStableUnderShift :
    (exactAcyclicHomotopyIsoClosure C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := by
    refine ⟨?_⟩
    rintro K ⟨K', hK', ⟨e⟩⟩
    obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K'
    refine ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (K₀⟦n⟧),
      exactAcyclic_shift C K₀ n hK', ?_⟩
    exact ⟨(shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).mapIso e ≪≫
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app K₀).symm⟩

/-- The isomorphism closure is triangulated once the distinguished-triangle closure is supplied. -/
theorem exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulated where

/-- It is enough to prove distinguished-triangle closure for the underlying exact-acyclic
homotopy-object predicate: mathlib then transports that closure to its isomorphism
closure. -/
theorem exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ := by
  infer_instance

/-- Closing exact acyclic homotopy objects under isomorphism does not change `trW`. -/
theorem exactAcyclicHomotopyIsoClosure_trW [HasZeroObject C] [HasBinaryBiproducts C] :
    (exactAcyclicHomotopyIsoClosure C).trW =
      (exactAcyclicHomotopyObject C).trW := by
  exact ObjectProperty.trW_isoClosure (exactAcyclicHomotopyObject C)

/-- If exact acyclicity is homotopy-category isomorphism invariant, then the exact-acyclic
homotopy-object predicate is stable under the homotopy-category shift. -/
noncomputable instance exactAcyclicHomotopyObject_isStableUnderShift_of_isClosedUnderIsomorphisms
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    (exactAcyclicHomotopyObject C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := by
    refine ⟨?_⟩
    intro K hK
    obtain ⟨K₀, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    exact (exactAcyclicHomotopyObject C).prop_of_iso
      (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app K₀)
      (exactAcyclic_shift C K₀ n hK)

/-- With homotopy-category isomorphism invariance, the remaining triangulated-subcategory
obligation is the two-out-of-three distinguished-triangle closure. -/
theorem exactAcyclicHomotopyObject_isTriangulated_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyObject C).IsTriangulated where

/-- A morphism of complexes whose mapping cone is exact acyclic lies in the Verdier-style
`trW` class for the exact-acyclic homotopy-object predicate. -/
theorem exactAcyclicHomotopyObject_trW_quotient_map_of_exactAcyclic_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hf : exactAcyclic C (CochainComplex.mappingCone f)) :
    (exactAcyclicHomotopyObject C).trW
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := by
  exact ⟨_, _, _, HomotopyCategory.mappingCone_triangleh_distinguished f, hf⟩

/-- If exact acyclicity is homotopy-category isomorphism invariant, the `trW` condition on
the quotient of a cochain map is exactly exact acyclicity of its mapping cone. -/
theorem exactAcyclicHomotopyObject_trW_quotient_map_iff_exactAcyclic_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (exactAcyclicHomotopyObject C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ↔
      exactAcyclic C (CochainComplex.mappingCone f) := by
  constructor
  · intro hf
    exact ((exactAcyclicHomotopyObject C).trW_iff_of_distinguished
      (CochainComplex.mappingCone.triangleh f)
      (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hf
  · intro hf
    exact exactAcyclicHomotopyObject_trW_quotient_map_of_exactAcyclic_mappingCone C f hf

/-- Exact acyclic mapping cones also give `trW` morphisms for the isomorphism closure of
exact acyclic homotopy objects. -/
theorem exactAcyclicHomotopyIsoClosure_trW_quotient_map_of_exactAcyclic_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hf : exactAcyclic C (CochainComplex.mappingCone f)) :
    (exactAcyclicHomotopyIsoClosure C).trW
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := by
  rw [exactAcyclicHomotopyIsoClosure_trW C]
  exact exactAcyclicHomotopyObject_trW_quotient_map_of_exactAcyclic_mappingCone C f hf

/-- For the isomorphism-closed exact-acyclic predicate, the `trW` condition on a quotient
map is equivalent to the mapping cone object lying in that isomorphism closure. This does
not require exact acyclicity itself to be homotopy-category isomorphism invariant. -/
theorem exactAcyclicHomotopyIsoClosure_trW_quotient_map_iff_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (exactAcyclicHomotopyIsoClosure C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ↔
      exactAcyclicHomotopyIsoClosure C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone f)) := by
  exact ((exactAcyclicHomotopyIsoClosure C).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f))

/-- Under homotopy-category isomorphism invariance, the isomorphism-closed `trW` condition
on the quotient of a cochain map is still equivalent to exact acyclicity of its mapping
cone. -/
theorem exactAcyclicHomotopyIsoClosure_trW_quotient_map_iff_exactAcyclic_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    (exactAcyclicHomotopyIsoClosure C).trW
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) ↔
      exactAcyclic C (CochainComplex.mappingCone f) := by
  rw [exactAcyclicHomotopyIsoClosure_trW C]
  exact exactAcyclicHomotopyObject_trW_quotient_map_iff_exactAcyclic_mappingCone C f

/-- Exact quasi-isomorphisms between bounded complexes, detected by the mapping cone. -/
noncomputable def boundedExactWeakEquivalence [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  fun _ _ f => exactAcyclic C (CochainComplex.mappingCone ((boundedCochainComplex C).ι.map f))

/-- The bounded-complex inclusion followed by the homotopy-category quotient. -/
abbrev BoundedComplexCategory.homotopyQuotient [HasBinaryBiproducts C] :
    BoundedComplexCategory C ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  BoundedComplexCategory.ι C ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ)

omit [QuillenExactCategory C] in
/-- Bounded objects in the homotopy category, understood up to homotopy-category
isomorphism from a strictly bounded cochain complex. -/
def boundedHomotopyObject : ObjectProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
  fun K => ∃ K₀ : CochainComplex C ℤ, boundedCochainComplex C K₀ ∧
    Nonempty ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K₀ ≅ K)

omit [QuillenExactCategory C] in
/-- A strictly bounded cochain complex defines a bounded homotopy object. -/
theorem boundedHomotopyObject_quotient_obj {K : CochainComplex C ℤ}
    (hK : boundedCochainComplex C K) :
    boundedHomotopyObject C ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) :=
  ⟨K, hK, ⟨Iso.refl _⟩⟩

omit [QuillenExactCategory C] in
/-- Bounded homotopy objects are closed under isomorphism by definition. -/
instance boundedHomotopyObject_isClosedUnderIsomorphisms :
    (boundedHomotopyObject C).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro K L e ⟨K₀, hK₀, ⟨e₀⟩⟩
    exact ⟨K₀, hK₀, ⟨e₀ ≪≫ e⟩⟩

omit [QuillenExactCategory C] in
/-- Bounded homotopy objects contain a zero object. -/
instance boundedHomotopyObject_containsZero [HasZeroObject C] :
    (boundedHomotopyObject C).ContainsZero where
  exists_zero := by
    refine ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (0 : CochainComplex C ℤ),
      ?_, ?_⟩
    · exact Functor.map_isZero (HomotopyCategory.quotient C (ComplexShape.up ℤ))
        (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))
    · exact boundedHomotopyObject_quotient_obj C (by
        exact ⟨0, 0, inferInstance, inferInstance⟩)

omit [QuillenExactCategory C] in
/-- Bounded homotopy objects are stable under the homotopy-category shift. -/
noncomputable instance boundedHomotopyObject_isStableUnderShift :
    (boundedHomotopyObject C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := by
    refine ⟨?_⟩
    rintro K ⟨K₀, hK₀, ⟨e⟩⟩
    refine ⟨K₀⟦n⟧, ?_, ?_⟩
    · exact (boundedCochainComplex C).le_shift n K₀ hK₀
    · exact ⟨((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app K₀ ≪≫
        (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).mapIso e⟩

omit [QuillenExactCategory C] in
/-- The full homotopy-category subcategory of bounded objects. -/
abbrev BoundedHomotopyCategory : Type (max u v) :=
  (boundedHomotopyObject C).FullSubcategory

omit [QuillenExactCategory C] in
/-- The inclusion of bounded homotopy objects into the full homotopy category. -/
abbrev BoundedHomotopyCategory.ι :
    BoundedHomotopyCategory C ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  (boundedHomotopyObject C).ι

omit [QuillenExactCategory C] in
/-- The homotopy object represented by the mapping cone of a map between bounded complexes is
bounded. -/
theorem boundedHomotopyObject_mappingCone [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hK : boundedCochainComplex C K) (hL : boundedCochainComplex C L) :
    boundedHomotopyObject C
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone f)) :=
  boundedHomotopyObject_quotient_obj C (boundedCochainComplex_mappingCone C f hK hL)

omit [QuillenExactCategory C] in
/-- A bounded mapping cone represents a bounded target object in the homotopy category. -/
theorem boundedHomotopyObject_of_mappingCone_right [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) :=
  boundedHomotopyObject_quotient_obj C (boundedCochainComplex_of_mappingCone_right C f hCone)

omit [QuillenExactCategory C] in
/-- A bounded mapping cone represents a bounded source object in the homotopy category. -/
theorem boundedHomotopyObject_of_mappingCone_left [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (hCone : boundedCochainComplex C (CochainComplex.mappingCone f)) :
    boundedHomotopyObject C ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) :=
  boundedHomotopyObject_quotient_obj C (boundedCochainComplex_of_mappingCone_left C f hCone)

/-- The direct mapping-cone weak equivalences on bounded complexes map into the
homotopy-category `trW` class of exact-acyclic objects. -/
theorem boundedExactWeakEquivalence_le_exactAcyclicHomotopy_trW_inverseImage
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedExactWeakEquivalence C ≤
      (exactAcyclicHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotient C) := by
  intro K L f hf
  exact exactAcyclicHomotopyObject_trW_quotient_map_of_exactAcyclic_mappingCone C _ hf

/-- If exact acyclicity is invariant under isomorphisms in the homotopy category, then the
direct bounded mapping-cone weak equivalences are exactly the inverse image of the
Verdier-style `trW` class. -/
theorem boundedExactWeakEquivalence_eq_exactAcyclicHomotopy_trW_inverseImage
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    boundedExactWeakEquivalence C =
      (exactAcyclicHomotopyObject C).trW.inverseImage
        (BoundedComplexCategory.homotopyQuotient C) := by
  ext K L f
  constructor
  · intro hf
    exact boundedExactWeakEquivalence_le_exactAcyclicHomotopy_trW_inverseImage C f hf
  · intro hf
    exact ((exactAcyclicHomotopyObject C).trW_iff_of_distinguished
      (CochainComplex.mappingCone.triangleh ((BoundedComplexCategory.ι C).map f))
      (HomotopyCategory.mappingCone_triangleh_distinguished
        ((BoundedComplexCategory.ι C).map f))).1 hf

/-- Bounded morphisms whose image in the homotopy category lies in the Verdier-style weak
equivalence class attached to the isomorphism closure of exact acyclic homotopy objects. -/
abbrev boundedHomotopyExactWeakEquivalence [HasZeroObject C] [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  (exactAcyclicHomotopyIsoClosure C).trW.inverseImage
    (BoundedComplexCategory.homotopyQuotient C)

/-- Direct mapping-cone exact weak equivalences are homotopy/Verdier weak equivalences after
passing to the homotopy category and closing exact acyclic objects under isomorphism. -/
theorem boundedExactWeakEquivalence_le_boundedHomotopyExactWeakEquivalence
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedExactWeakEquivalence C ≤ boundedHomotopyExactWeakEquivalence C := by
  intro K L f hf
  dsimp [boundedHomotopyExactWeakEquivalence]
  rw [exactAcyclicHomotopyIsoClosure_trW C]
  exact boundedExactWeakEquivalence_le_exactAcyclicHomotopy_trW_inverseImage C f hf

/-- A bounded morphism with exact acyclic mapping cone is a homotopy/Verdier pullback weak
equivalence. -/
theorem boundedHomotopyExactWeakEquivalence_of_exactAcyclic_mappingCone
    [HasZeroObject C] [HasBinaryBiproducts C] {K L : BoundedComplexCategory C} (f : K ⟶ L)
    (hf : exactAcyclic C
      (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f))) :
    boundedHomotopyExactWeakEquivalence C f :=
  boundedExactWeakEquivalence_le_boundedHomotopyExactWeakEquivalence C f hf

/-- A bounded morphism is a homotopy/Verdier weak equivalence exactly when its mapping cone,
viewed in the homotopy category, lies in the isomorphism closure of the exact-acyclic
objects. -/
theorem boundedHomotopyExactWeakEquivalence_iff_mappingCone_isoClosure
    [HasZeroObject C] [HasBinaryBiproducts C] {K L : BoundedComplexCategory C} (f : K ⟶ L) :
    boundedHomotopyExactWeakEquivalence C f ↔
      exactAcyclicHomotopyIsoClosure C
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f))) := by
  dsimp [boundedHomotopyExactWeakEquivalence, BoundedComplexCategory.homotopyQuotient]
  exact exactAcyclicHomotopyIsoClosure_trW_quotient_map_iff_mappingCone C
    ((BoundedComplexCategory.ι C).map f)

/-- A bounded morphism whose mapping cone is degreewise split is a direct exact weak
equivalence. -/
theorem boundedExactWeakEquivalence_of_mappingCone_splittings
    [HasBinaryBiproducts C] {K L : BoundedComplexCategory C} (f : K ⟶ L)
    (hf : ∀ i : ℤ,
      ((CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f)).sc i).Splitting) :
    boundedExactWeakEquivalence C f :=
  exactAcyclic_of_splittings C hf

/-- A bounded morphism whose mapping cone is degreewise split maps to the homotopy/Verdier
pullback weak-equivalence class. -/
theorem boundedHomotopyExactWeakEquivalence_of_mappingCone_splittings
    [HasZeroObject C] [HasBinaryBiproducts C] {K L : BoundedComplexCategory C} (f : K ⟶ L)
    (hf : ∀ i : ℤ,
      ((CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f)).sc i).Splitting) :
    boundedHomotopyExactWeakEquivalence C f :=
  boundedExactWeakEquivalence_le_boundedHomotopyExactWeakEquivalence C f
    (boundedExactWeakEquivalence_of_mappingCone_splittings C f hf)

/-- If exact acyclicity is homotopy-category isomorphism invariant, the direct bounded weak
equivalences coincide with the homotopy/Verdier pullback weak equivalences. -/
theorem boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    boundedExactWeakEquivalence C = boundedHomotopyExactWeakEquivalence C := by
  dsimp [boundedHomotopyExactWeakEquivalence]
  rw [exactAcyclicHomotopyIsoClosure_trW C]
  exact boundedExactWeakEquivalence_eq_exactAcyclicHomotopy_trW_inverseImage C

/-- Under homotopy-category isomorphism invariance of exact acyclicity, the direct and
homotopy/Verdier bounded weak-equivalence predicates agree on each morphism. -/
theorem boundedExactWeakEquivalence_iff_boundedHomotopyExactWeakEquivalence_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    {K L : BoundedComplexCategory C} (f : K ⟶ L) :
    boundedExactWeakEquivalence C f ↔ boundedHomotopyExactWeakEquivalence C f := by
  rw [← boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed C]

/-- Once exact acyclicity is invariant under homotopy-category isomorphism, a left calculus
for the homotopy/Verdier pullback weak equivalences transfers to the direct bounded exact
weak equivalences by equality of localizers. -/
theorem boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions := by
  rw [boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed C]
  infer_instance

/-- Once exact acyclicity is invariant under homotopy-category isomorphism, a right calculus
for the homotopy/Verdier pullback weak equivalences transfers to the direct bounded exact
weak equivalences by equality of localizers. -/
theorem boundedExactWeakEquivalence_hasRightCalculusOfFractions_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasRightCalculusOfFractions] :
    (boundedExactWeakEquivalence C).HasRightCalculusOfFractions := by
  rw [boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed C]
  infer_instance

/-- Under homotopy-category isomorphism invariance of exact acyclicity, the
homotopy/Verdier bounded weak-equivalence predicate is exactly the mapping-cone exact
acyclicity condition. -/
theorem boundedHomotopyExactWeakEquivalence_iff_exactAcyclic_mappingCone_of_isoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    {K L : BoundedComplexCategory C} (f : K ⟶ L) :
    boundedHomotopyExactWeakEquivalence C f ↔
      exactAcyclic C (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f)) := by
  rw [← boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed C]
  rfl

/-- The homotopy/Verdier pullback weak equivalences on bounded complexes are compatible with
cochain shifts. -/
noncomputable instance boundedHomotopyExactWeakEquivalence_isCompatibleWithShift
    [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyExactWeakEquivalence C).IsCompatibleWithShift ℤ where
  condition n := by
    ext K L f
    let F : BoundedComplexCategory C ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
      BoundedComplexCategory.homotopyQuotient C
    let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
      (exactAcyclicHomotopyIsoClosure C).trW
    change W (F.map (f⟦n⟧')) ↔ W (F.map f)
    have hArrow : Arrow.mk (F.map (f⟦n⟧')) ≅ Arrow.mk ((F.map f)⟦n⟧') :=
      Arrow.isoOfNatIso (F.commShiftIso n) (Arrow.mk f)
    constructor
    · intro hf
      have hf' : W ((F.map f)⟦n⟧') := (W.arrow_mk_iso_iff hArrow).1 hf
      exact (MorphismProperty.IsCompatibleWithShift.iff W (F.map f) n).1 hf'
    · intro hf
      have hf' : W ((F.map f)⟦n⟧') :=
        (MorphismProperty.IsCompatibleWithShift.iff W (F.map f) n).2 hf
      exact (W.arrow_mk_iso_iff hArrow).2 hf'

/-- The identity functor sends direct bounded exact weak equivalences to the
homotopy/Verdier pullback weak equivalences. -/
abbrev boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence
    [HasZeroObject C] [HasBinaryBiproducts C] :
    LocalizerMorphism (boundedExactWeakEquivalence C)
      (boundedHomotopyExactWeakEquivalence C) where
  functor := 𝟭 _
  map := by
    intro K L f hf
    exact boundedExactWeakEquivalence_le_boundedHomotopyExactWeakEquivalence C f hf

/-- If exact acyclicity is invariant under homotopy-category isomorphism, the identity
localizer morphism from direct bounded exact weak equivalences to homotopy/Verdier pullback
weak equivalences is a morphism induced by equality of the two weak-equivalence classes. -/
abbrev boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    LocalizerMorphism (boundedExactWeakEquivalence C)
      (boundedHomotopyExactWeakEquivalence C) :=
  LocalizerMorphism.ofEq (F := 𝟭 (BoundedComplexCategory C)) (by
    ext K L f
    simp only [MorphismProperty.inverseImage, Functor.id_map]
    rw [boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed C]
    rfl)

instance boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed_localizedEquivalence
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    (boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed
      C).IsLocalizedEquivalence := by
  haveI :
      (boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed
        C).functor.IsEquivalence := by
    dsimp [boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed]
    infer_instance
  apply LocalizerMorphism.IsLocalizedEquivalence.of_equivalence
  intro K L f hf
  refine ⟨K, L, f, ?_, ?_⟩
  · rw [boundedExactWeakEquivalence_eq_boundedHomotopyExactWeakEquivalence_of_isoClosed C]
    exact hf
  · simpa [boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed]
      using (Nonempty.intro (Iso.refl (Arrow.mk f)))

/-- Once the exact-acyclic homotopy-object predicate is triangulated, mathlib supplies the
left calculus of fractions for its Verdier-style weak equivalences. -/
theorem exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulated] :
    (exactAcyclicHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  infer_instance

/-- Once the exact-acyclic homotopy-object predicate is triangulated, mathlib also supplies
the right calculus of fractions for its Verdier-style weak equivalences. -/
theorem exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulated] :
    (exactAcyclicHomotopyObject C).trW.HasRightCalculusOfFractions := by
  infer_instance

/-- A sharper conditional form: after isomorphism invariance and distinguished-triangle closure,
mathlib supplies the Verdier left calculus of fractions. -/
theorem exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyObject C).IsTriangulated :=
    exactAcyclicHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  exact exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated C

/-- A sharper conditional form: after isomorphism invariance and distinguished-triangle closure,
mathlib supplies the Verdier right calculus of fractions. -/
theorem exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyObject C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyObject C).IsTriangulated :=
    exactAcyclicHomotopyObject_isTriangulated_of_isTriangulatedClosed2 C
  exact exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated C

/-- It is enough to triangulate the isomorphism closure, because its `trW` is the same. -/
theorem exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isoClosureClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  rw [← exactAcyclicHomotopyIsoClosure_trW C]
  infer_instance

/-- It is enough to triangulate the isomorphism closure to get the right calculus as well,
because its `trW` is the same. -/
theorem exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isoClosureClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyObject C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  rw [← exactAcyclicHomotopyIsoClosure_trW C]
  infer_instance

/-- A non-closed distinguished-triangle closure proof for exact acyclic homotopy objects is
already enough for the original `trW`, because the `trW` class is unchanged by taking the
isomorphism closure. -/
theorem exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyObject C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  exact exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_isoClosureClosed2 C

/-- The same non-closed distinguished-triangle closure proof also supplies the original
`trW` right calculus via the isomorphism closure. -/
theorem exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyObject C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  exact exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_isoClosureClosed2 C

/-- Once the isomorphism closure is triangulated, mathlib supplies the Verdier left calculus
directly for the isomorphism-closed homotopy-category `trW` class. -/
theorem exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  infer_instance

/-- Once the isomorphism closure is triangulated, mathlib supplies the Verdier right calculus
directly for the isomorphism-closed homotopy-category `trW` class. -/
theorem exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  infer_instance

/-- The same reduction as
`exactAcyclicHomotopyObject_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2`,
but stated for the isomorphism-closed predicate itself. -/
theorem exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasLeftCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  exact exactAcyclicHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_isTriangulatedClosed2 C

/-- The same reduction as
`exactAcyclicHomotopyObject_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2`,
but stated for the isomorphism-closed predicate itself. -/
theorem exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.HasRightCalculusOfFractions := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  exact exactAcyclicHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_isTriangulatedClosed2 C

/-- Once the isomorphism closure is triangulated, its Verdier weak equivalences are compatible
with the homotopy-category triangulation. -/
theorem exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.IsCompatibleWithTriangulation := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  infer_instance

/-- A distinguished-triangle closure proof for exact acyclic homotopy objects also gives
triangulation compatibility for the isomorphism-closed Verdier weak equivalences. -/
theorem exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    (exactAcyclicHomotopyIsoClosure C).trW.IsCompatibleWithTriangulation := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  exact exactAcyclicHomotopyIsoClosure_trW_isCompatibleWithTriangulation_of_isTriangulatedClosed2 C

/-- The ordinary Verdier localization of the homotopy category at the `trW` class attached to
the isomorphism closure of exact acyclic homotopy objects. -/
abbrev ExactAcyclicHomotopyVerdierCategory [HasZeroObject C] [HasBinaryBiproducts C] :
    Type (max u v) :=
  (exactAcyclicHomotopyIsoClosure C).trW.Localization

/-- The ordinary nerve of the exact-acyclic homotopy Verdier localization. -/
noncomputable abbrev ExactAcyclicHomotopyVerdierQuasicategory
    [HasZeroObject C] [HasBinaryBiproducts C] : SSet.QCat :=
  ⟨CategoryTheory.nerve (ExactAcyclicHomotopyVerdierCategory C), inferInstance⟩

/-- The homotopy category of the ordinary nerve of the homotopy Verdier localization recovers
the localized category. -/
noncomputable def ExactAcyclicHomotopyVerdierQuasicategory.homotopyCategoryIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    SSet.hoFunctor.obj (ExactAcyclicHomotopyVerdierQuasicategory C).1 ≅
      Cat.of (ExactAcyclicHomotopyVerdierCategory C) :=
  CategoryTheory.nerveFunctorCompHoFunctorIso.app
    (Cat.of (ExactAcyclicHomotopyVerdierCategory C))

/-- The bounded homotopy/Verdier weak equivalences are the inverse image of the
exact-acyclic homotopy Verdier weak equivalences under the bounded homotopy quotient. -/
abbrev boundedHomotopyExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW
    [HasZeroObject C] [HasBinaryBiproducts C] :
    LocalizerMorphism (boundedHomotopyExactWeakEquivalence C)
      (exactAcyclicHomotopyIsoClosure C).trW where
  functor := BoundedComplexCategory.homotopyQuotient C
  map := by
    intro K L f hf
    exact hf

/-- The direct bounded exact weak equivalences also map to the ordinary homotopy Verdier
weak equivalences; this is the composite of the direct-to-homotopy comparison and the
homotopy-to-Verdier localizer morphism. -/
abbrev boundedExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW
    [HasZeroObject C] [HasBinaryBiproducts C] :
    LocalizerMorphism (boundedExactWeakEquivalence C)
      (exactAcyclicHomotopyIsoClosure C).trW :=
  (boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence C).comp
    (boundedHomotopyExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW C)

/-- The exact-acyclic homotopy Verdier localization is preadditive once the
isomorphism-closed exact-acyclic objects form a triangulated subcategory. -/
noncomputable instance exactAcyclicHomotopyVerdierCategory_preadditive_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Preadditive (ExactAcyclicHomotopyVerdierCategory C) := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  exact Localization.preadditive W.Q W

/-- Under the same triangulated-closure hypothesis, the homotopy Verdier localization functor
is additive. -/
instance exactAcyclicHomotopyVerdierCategory_localization_additive_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).Additive := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  exact Localization.functor_additive W.Q W

/-- Under the same triangulated-closure hypothesis, the homotopy Verdier localization has a
zero object. -/
instance exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasZeroObject (ExactAcyclicHomotopyVerdierCategory C) := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  change HasZeroObject W.Localization
  exact W.Q.hasZeroObject_of_additive

/-- Under the same triangulated-closure hypothesis, the homotopy Verdier localization inherits
the integer shift. -/
noncomputable instance exactAcyclicHomotopyVerdierCategory_hasShift_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    HasShift (ExactAcyclicHomotopyVerdierCategory C) ℤ := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  haveI : W.IsCompatibleWithShift ℤ := by
    dsimp [W]
    infer_instance
  exact HasShift.localized W.Q W ℤ

/-- Under the same triangulated-closure hypothesis, the homotopy Verdier localization functor
commutes with shifts. -/
noncomputable instance
    exactAcyclicHomotopyVerdierCategory_localization_commShift_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).CommShift ℤ := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  haveI : W.IsCompatibleWithShift ℤ := by
    dsimp [W]
    infer_instance
  exact Functor.CommShift.localized W.Q W ℤ

/-- Under the same triangulated-closure hypothesis, localized shifts are additive. -/
instance exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] (n : ℤ) :
    (shiftFunctor (ExactAcyclicHomotopyVerdierCategory C) n).Additive := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  change (shiftFunctor W.Localization n).Additive
  rw [Localization.functor_additive_iff W.Q W]
  exact Functor.additive_of_iso (W.Q.commShiftIso n)

/-- Under the same triangulated-closure hypothesis, the homotopy Verdier localization is
pretriangulated by mathlib's localization theorem. -/
noncomputable instance
    exactAcyclicHomotopyVerdierCategory_pretriangulated_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    Pretriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  haveI : W.IsCompatibleWithTriangulation := by
    dsimp [W]
    infer_instance
  exact Triangulated.Localization.pretriangulated W.Q W

/-- Under the same triangulated-closure hypothesis, the homotopy Verdier localization is an
ordinary triangulated category. -/
instance exactAcyclicHomotopyVerdierCategory_isTriangulated_of_isTriangulatedClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂] :
    IsTriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  let W : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) :=
    (exactAcyclicHomotopyIsoClosure C).trW
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulated :=
    exactAcyclicHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2 C
  haveI : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    infer_instance
  haveI : W.IsCompatibleWithTriangulation := by
    dsimp [W]
    infer_instance
  haveI : W.Q.IsTriangulated :=
    Triangulated.Localization.isTriangulated_functor W.Q W
  change IsTriangulated W.Localization
  exact Triangulated.Localization.isTriangulated W.Q W

/-- It is enough to prove distinguished-triangle closure for `exactAcyclicHomotopyObject` to
obtain preadditivity of the ordinary homotopy Verdier localization: the closure is first
transported to the isomorphism closure. -/
noncomputable abbrev exactAcyclicHomotopyVerdierCategory_preadditive_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    Preadditive (ExactAcyclicHomotopyVerdierCategory C) := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

/-- The localization functor for the homotopy Verdier quotient is additive under the same
homotopy-object distinguished-triangle closure hypothesis. -/
noncomputable abbrev
    exactAcyclicHomotopyVerdierCategory_localization_additive_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).Additive := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

/-- The homotopy Verdier quotient has a zero object once exact acyclic homotopy objects are
closed under distinguished triangles. -/
noncomputable abbrev exactAcyclicHomotopyVerdierCategory_hasZeroObject_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    HasZeroObject (ExactAcyclicHomotopyVerdierCategory C) := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

/-- The homotopy Verdier quotient inherits shifts once exact acyclic homotopy objects are
closed under distinguished triangles. -/
noncomputable abbrev exactAcyclicHomotopyVerdierCategory_hasShift_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    HasShift (ExactAcyclicHomotopyVerdierCategory C) ℤ := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

/-- The homotopy Verdier localization functor commutes with shifts under the homotopy-object
distinguished-triangle closure hypothesis. -/
noncomputable abbrev
    exactAcyclicHomotopyVerdierCategory_localization_commShift_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    ((exactAcyclicHomotopyIsoClosure C).trW.Q).CommShift ℤ := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

/-- Localized shifts are additive under the homotopy-object distinguished-triangle closure
hypothesis. -/
noncomputable abbrev
    exactAcyclicHomotopyVerdierCategory_shiftFunctor_additive_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] (n : ℤ) :
    (shiftFunctor (ExactAcyclicHomotopyVerdierCategory C) n).Additive := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

/-- The ordinary homotopy Verdier quotient is pretriangulated under the homotopy-object
distinguished-triangle closure hypothesis. -/
noncomputable abbrev exactAcyclicHomotopyVerdierCategory_pretriangulated_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    Pretriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

/-- The ordinary homotopy Verdier quotient is triangulated under the homotopy-object
distinguished-triangle closure hypothesis. -/
noncomputable abbrev exactAcyclicHomotopyVerdierCategory_isTriangulated_of_homotopyObjectClosed2
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsTriangulatedClosed₂] :
    IsTriangulated (ExactAcyclicHomotopyVerdierCategory C) := by
  haveI : (exactAcyclicHomotopyIsoClosure C).IsTriangulatedClosed₂ :=
    exactAcyclicHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject C
  infer_instance

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

/-- The ordinary localization at the homotopy/Verdier pullback weak equivalences. -/
abbrev BoundedHomotopyDerivedCategory [HasZeroObject C] [HasBinaryBiproducts C] :
    Type (max u v) :=
  (boundedHomotopyExactWeakEquivalence C).Localization

/-- The ordinary nerve of the homotopy/Verdier pullback localization. -/
noncomputable abbrev BoundedHomotopyDerivedQuasicategory
    [HasZeroObject C] [HasBinaryBiproducts C] : SSet.QCat :=
  ⟨CategoryTheory.nerve (BoundedHomotopyDerivedCategory C), inferInstance⟩

/-- The ordinary homotopy category of the homotopy/Verdier pullback nerve recovers its
localized category. -/
noncomputable def BoundedHomotopyDerivedQuasicategory.homotopyCategoryIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    SSet.hoFunctor.obj (BoundedHomotopyDerivedQuasicategory C).1 ≅
      Cat.of (BoundedHomotopyDerivedCategory C) :=
  CategoryTheory.nerveFunctorCompHoFunctorIso.app (Cat.of (BoundedHomotopyDerivedCategory C))

namespace BoundedHomotopyDerivedCategory

/-- If the homotopy/Verdier pullback weak equivalences have a left calculus of fractions,
mathlib's localization API equips their bounded localization with a preadditive structure. -/
noncomputable abbrev preadditiveOfHasLeftCalculusOfFractions
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (BoundedHomotopyDerivedCategory C) := by
  infer_instance

/-- Under the same left-calculus hypothesis, the homotopy/Verdier pullback localization
functor is additive. -/
theorem localization_additiveOfHasLeftCalculusOfFractions
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    ((boundedHomotopyExactWeakEquivalence C).Q).Additive := by
  infer_instance

/-- Under the homotopy/Verdier pullback left-calculus hypothesis, the bounded homotopy
localization has a zero object. -/
theorem hasZeroObjectOfHasLeftCalculusOfFractions
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (BoundedHomotopyDerivedCategory C) := by
  infer_instance

/-- Under the homotopy/Verdier pullback left-calculus hypothesis, localized shifts are
additive on the bounded homotopy derived category. -/
theorem shiftFunctor_additiveOfHasLeftCalculusOfFractions
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] (n : ℤ) :
    (shiftFunctor (BoundedHomotopyDerivedCategory C) n).Additive := by
  rw [Localization.functor_additive_iff (boundedHomotopyExactWeakEquivalence C).Q
    (boundedHomotopyExactWeakEquivalence C) (shiftFunctor (BoundedHomotopyDerivedCategory C) n)]
  exact Functor.additive_of_iso (((boundedHomotopyExactWeakEquivalence C).Q).commShiftIso n)

/-- The comparison from the bounded homotopy/Verdier pullback localization to the ordinary
homotopy Verdier quotient. -/
noncomputable abbrev verdierComparison [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedHomotopyDerivedCategory C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
  (boundedHomotopyExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW C).localizedFunctor
    (boundedHomotopyExactWeakEquivalence C).Q
    (exactAcyclicHomotopyIsoClosure C).trW.Q

/-- The bounded homotopy comparison functor is the functor induced by the Verdier localizer
morphism, so it commutes with the two localization functors up to the canonical
`CatCommSq` isomorphism. -/
noncomputable def verdierComparisonLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory.homotopyQuotient C ⋙
        (exactAcyclicHomotopyIsoClosure C).trW.Q ≅
      (boundedHomotopyExactWeakEquivalence C).Q ⋙
        BoundedHomotopyDerivedCategory.verdierComparison C :=
  let Φ := boundedHomotopyExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW C
  letI : CatCommSq Φ.functor (boundedHomotopyExactWeakEquivalence C).Q
      (exactAcyclicHomotopyIsoClosure C).trW.Q
      (Φ.localizedFunctor (boundedHomotopyExactWeakEquivalence C).Q
        (exactAcyclicHomotopyIsoClosure C).trW.Q) :=
    Φ.catCommSq (boundedHomotopyExactWeakEquivalence C).Q
      (exactAcyclicHomotopyIsoClosure C).trW.Q
  CatCommSq.iso Φ.functor (boundedHomotopyExactWeakEquivalence C).Q
    (exactAcyclicHomotopyIsoClosure C).trW.Q
    (Φ.localizedFunctor (boundedHomotopyExactWeakEquivalence C).Q
      (exactAcyclicHomotopyIsoClosure C).trW.Q)

end BoundedHomotopyDerivedCategory

namespace Dbounded

/-- The comparison from the direct bounded exact localization to the homotopy/Verdier pullback
localization induced by the inclusion of weak-equivalence classes. -/
noncomputable abbrev homotopyComparison [HasZeroObject C] [HasBinaryBiproducts C] :
    Dbounded C ⥤ BoundedHomotopyDerivedCategory C :=
  (boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence C).localizedFunctor
    (Dbounded.localization C) (boundedHomotopyExactWeakEquivalence C).Q

/-- The comparison from the direct bounded localization to the homotopy/Verdier pullback
localization is induced by the identity localizer morphism, so it commutes with the
localization functors by the canonical `CatCommSq` isomorphism. -/
noncomputable def homotopyComparisonLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    (boundedHomotopyExactWeakEquivalence C).Q ≅
      Dbounded.localization C ⋙ Dbounded.homotopyComparison C :=
  let Φ := boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence C
  letI : CatCommSq Φ.functor (Dbounded.localization C)
      (boundedHomotopyExactWeakEquivalence C).Q
      (Φ.localizedFunctor (Dbounded.localization C)
        (boundedHomotopyExactWeakEquivalence C).Q) :=
    Φ.catCommSq (Dbounded.localization C)
      (boundedHomotopyExactWeakEquivalence C).Q
  by
    simpa [boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence,
      Dbounded.homotopyComparison] using
      CatCommSq.iso Φ.functor (Dbounded.localization C)
        (boundedHomotopyExactWeakEquivalence C).Q
        (Φ.localizedFunctor (Dbounded.localization C)
          (boundedHomotopyExactWeakEquivalence C).Q)

/-- The comparison from the direct bounded exact localization to the ordinary homotopy
Verdier quotient, routed through the homotopy/Verdier pullback localization. -/
noncomputable abbrev verdierComparison [HasZeroObject C] [HasBinaryBiproducts C] :
    Dbounded C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
  Dbounded.homotopyComparison C ⋙ BoundedHomotopyDerivedCategory.verdierComparison C

/-- The routed bounded-to-Verdier comparison also commutes with the direct bounded
localization and the homotopy Verdier localization. -/
noncomputable def verdierComparisonLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory.homotopyQuotient C ⋙
        (exactAcyclicHomotopyIsoClosure C).trW.Q ≅
      Dbounded.localization C ⋙ Dbounded.verdierComparison C :=
  BoundedHomotopyDerivedCategory.verdierComparisonLocalizationIso C ≪≫
    Functor.isoWhiskerRight (Dbounded.homotopyComparisonLocalizationIso C)
      (BoundedHomotopyDerivedCategory.verdierComparison C) ≪≫
    Functor.associator _ _ _

/-- The comparison from the direct bounded exact localization to the ordinary homotopy
Verdier quotient, induced directly by the composite localizer morphism. -/
noncomputable abbrev verdierComparisonDirect [HasZeroObject C] [HasBinaryBiproducts C] :
    Dbounded C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
  (boundedExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW C).localizedFunctor
    (Dbounded.localization C) (exactAcyclicHomotopyIsoClosure C).trW.Q

/-- The direct bounded-to-Verdier comparison commutes with the direct bounded localization
and the homotopy Verdier localization by the canonical `CatCommSq` isomorphism. -/
noncomputable def verdierComparisonDirectLocalizationIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    BoundedComplexCategory.homotopyQuotient C ⋙
        (exactAcyclicHomotopyIsoClosure C).trW.Q ≅
      Dbounded.localization C ⋙ Dbounded.verdierComparisonDirect C :=
  let Φ := boundedExactWeakEquivalenceToExactAcyclicHomotopyIsoClosure_trW C
  letI : CatCommSq Φ.functor (Dbounded.localization C)
      (exactAcyclicHomotopyIsoClosure C).trW.Q
      (Φ.localizedFunctor (Dbounded.localization C)
        (exactAcyclicHomotopyIsoClosure C).trW.Q) :=
    Φ.catCommSq (Dbounded.localization C)
      (exactAcyclicHomotopyIsoClosure C).trW.Q
  CatCommSq.iso Φ.functor (Dbounded.localization C)
    (exactAcyclicHomotopyIsoClosure C).trW.Q
    (Φ.localizedFunctor (Dbounded.localization C)
      (exactAcyclicHomotopyIsoClosure C).trW.Q)

/-- The routed and direct comparisons from `Dbounded` to the ordinary homotopy Verdier
quotient are canonically isomorphic because they lift the same functor out of the direct
bounded localization. -/
noncomputable def verdierComparisonDirectIso
    [HasZeroObject C] [HasBinaryBiproducts C] :
    Dbounded.verdierComparison C ≅ Dbounded.verdierComparisonDirect C :=
  let source : BoundedComplexCategory C ⥤ ExactAcyclicHomotopyVerdierCategory C :=
    BoundedComplexCategory.homotopyQuotient C ⋙
      (exactAcyclicHomotopyIsoClosure C).trW.Q
  haveI : Localization.Lifting (Dbounded.localization C) (boundedExactWeakEquivalence C)
      source (Dbounded.verdierComparison C) :=
    ⟨(Dbounded.verdierComparisonLocalizationIso C).symm⟩
  haveI : Localization.Lifting (Dbounded.localization C) (boundedExactWeakEquivalence C)
      source (Dbounded.verdierComparisonDirect C) :=
    ⟨(Dbounded.verdierComparisonDirectLocalizationIso C).symm⟩
  Localization.liftNatIso (Dbounded.localization C) (boundedExactWeakEquivalence C)
    source source (Dbounded.verdierComparison C) (Dbounded.verdierComparisonDirect C)
    (Iso.refl source)

/-- If exact acyclicity is invariant under homotopy-category isomorphism, the direct bounded
localization and the homotopy/Verdier pullback localization are equivalent. -/
noncomputable def homotopyComparisonEquivalenceOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms] :
    Dbounded C ≌ BoundedHomotopyDerivedCategory C :=
  ((boundedExactWeakEquivalenceToHomotopyExactWeakEquivalenceOfIsoClosed C).localizedFunctor
    (Dbounded.localization C) (boundedHomotopyExactWeakEquivalence C).Q).asEquivalence

/-- If the exact weak equivalences have a left calculus of fractions, mathlib's localization
API equips `Dbounded` with a preadditive structure. -/
noncomputable abbrev preadditiveOfHasLeftCalculusOfFractions [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (Dbounded C) := by
  infer_instance

/-- Under the same left-calculus hypothesis, the localization functor is additive. -/
theorem localization_additiveOfHasLeftCalculusOfFractions [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    (Dbounded.localization C).Additive := by
  infer_instance

/-- Under a left-calculus hypothesis, the localized bounded derived category has a zero object
whenever the base category has one. -/
theorem hasZeroObjectOfHasLeftCalculusOfFractions [HasBinaryBiproducts C] [HasZeroObject C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (Dbounded C) := by
  infer_instance

/-- Under a left-calculus hypothesis, the localized shifts are additive. -/
theorem shiftFunctor_additiveOfHasLeftCalculusOfFractions [HasBinaryBiproducts C]
    [(boundedExactWeakEquivalence C).HasLeftCalculusOfFractions] (n : ℤ) :
    (shiftFunctor (Dbounded C) n).Additive := by
  rw [Localization.functor_additive_iff (Dbounded.localization C) (boundedExactWeakEquivalence C)
    (shiftFunctor (Dbounded C) n)]
  exact Functor.additive_of_iso ((Dbounded.localization C).commShiftIso n)

/-- If exact acyclicity is homotopy-isomorphism closed, a left calculus for the
homotopy/Verdier pullback localizer gives the direct bounded localization a preadditive
structure. -/
noncomputable abbrev preadditiveOfHomotopyLeftCalculusOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    Preadditive (Dbounded C) := by
  haveI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
    boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
  exact Dbounded.preadditiveOfHasLeftCalculusOfFractions C

/-- Under the same iso-closed and homotopy-left-calculus hypotheses, the direct bounded
localization functor is additive. -/
theorem localization_additiveOfHomotopyLeftCalculusOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
      boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
    (Dbounded.localization C).Additive := by
  letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
    boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
  change (Dbounded.localization C).Additive
  exact Dbounded.localization_additiveOfHasLeftCalculusOfFractions C

/-- Under the same iso-closed and homotopy-left-calculus hypotheses, `Dbounded` has a zero
object. -/
theorem hasZeroObjectOfHomotopyLeftCalculusOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] :
    HasZeroObject (Dbounded C) := by
  haveI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
    boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
  exact Dbounded.hasZeroObjectOfHasLeftCalculusOfFractions C

/-- Under the same iso-closed and homotopy-left-calculus hypotheses, localized shifts on
`Dbounded` are additive. -/
theorem shiftFunctor_additiveOfHomotopyLeftCalculusOfIsoClosed
    [HasZeroObject C] [HasBinaryBiproducts C]
    [(exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms]
    [(boundedHomotopyExactWeakEquivalence C).HasLeftCalculusOfFractions] (n : ℤ) :
    letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
      boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
    (shiftFunctor (Dbounded C) n).Additive := by
  letI : (boundedExactWeakEquivalence C).HasLeftCalculusOfFractions :=
    boundedExactWeakEquivalence_hasLeftCalculusOfFractions_of_isoClosed C
  change (shiftFunctor (Dbounded C) n).Additive
  exact Dbounded.shiftFunctor_additiveOfHasLeftCalculusOfFractions C n

end Dbounded

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
