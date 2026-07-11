import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence

/-!
# Mapping-cone objects in the bounded dg carrier

This file records the first object-level construction needed for a genuine stability proof of
the localized dg nerve.  It stays in the bounded dg carrier: the cone is not replaced by an
object of the ordinary derived category.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

/-- The zero bounded complex as an actual object of the direct simplicial dg category. -/
def directDGZeroObject : DirectDGSimplicialCategory :=
  directDGObject 0

/-- The direct simplicial dg category has a genuine zero object on its underlying category.
The proof transports uniqueness of arrows through the explicitly verified hom equivalence. -/
theorem directDGZeroObject_isZero : IsZero directDGZeroObject := by
  let h0 : IsZero (0 : ComplexCategory) := isZero_zero ComplexCategory
  constructor
  · intro Y
    let e := directDGToComplexHomEquiv directDGZeroObject Y
    exact ⟨
      { default := e.symm (h0.to_ (directDGToComplexFunctor.obj Y))
        uniq := fun f ↦ e.injective (h0.eq_of_src (e f) (e _)) }⟩
  · intro Y
    let e := directDGToComplexHomEquiv Y directDGZeroObject
    exact ⟨
      { default := e.symm (h0.from_ (directDGToComplexFunctor.obj Y))
        uniq := fun f ↦ e.injective (h0.eq_of_tgt (e f) (e _)) }⟩

/-- The cochain shift, retained as an actual object of the bounded dg carrier. -/
def dgShiftObject (K : ComplexCategory) (n : ℤ) : ComplexCategory :=
  (shiftFunctor ComplexCategory n).obj K

/-- Shifted objects also belong to the honest direct simplicial dg category. -/
def directDGShiftObject (K : ComplexCategory) (n : ℤ) :
    DirectDGSimplicialCategory :=
  directDGObject (dgShiftObject K n)

/-- The mapping cone of a morphism of bounded complexes, as an actual object of the bounded
dg carrier. -/
def dgMappingConeObject {K L : ComplexCategory} (f : K ⟶ L) : ComplexCategory :=
  ⟨CochainComplex.mappingCone ((boundedCochainComplex MetrizableLCA.{0}).ι.map f),
    boundedCochainComplex_mappingCone MetrizableLCA.{0}
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) K.property L.property⟩

@[simp]
theorem dgMappingConeObject_obj {K L : ComplexCategory} (f : K ⟶ L) :
    (dgMappingConeObject f).obj =
      CochainComplex.mappingCone ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) :=
  rfl

/-- The degree-zero inclusion of the target into the mapping cone, retained in the bounded
dg carrier. -/
def dgMappingConeInr {K L : ComplexCategory} (f : K ⟶ L) :
    L ⟶ dgMappingConeObject f :=
  (boundedCochainComplex MetrizableLCA.{0}).ι.preimage
    (CochainComplex.mappingCone.inr
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))

@[simp]
theorem boundedInclusion_map_dgMappingConeInr {K L : ComplexCategory} (f : K ⟶ L) :
    (boundedCochainComplex MetrizableLCA.{0}).ι.map (dgMappingConeInr f) =
      CochainComplex.mappingCone.inr
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) :=
  Functor.map_preimage _ _

/-- The degree `-1` left inclusion is the explicit nullhomotopy in the cone triangle. -/
def dgMappingConeInl {K L : ComplexCategory} (f : K ⟶ L) :
    CochainComplex.HomComplex.Cochain K.obj (dgMappingConeObject f).obj (-1) :=
  CochainComplex.mappingCone.inl
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)

/-- The cone triangle is genuinely nullhomotopic at chain level: the differential of its
degree `-1` left inclusion is the composite through the degree-zero right inclusion. -/
theorem dgMappingConeInl_delta {K L : ComplexCategory} (f : K ⟶ L) :
    CochainComplex.HomComplex.δ (-1) 0 (dgMappingConeInl f) =
      CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map
          (f ≫ dgMappingConeInr f)) := by
  convert CochainComplex.mappingCone.δ_inl
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) using 1 <;>
      first | rfl | simp only [Functor.map_comp,
        boundedInclusion_map_dgMappingConeInr]
  case e'_3 => exact HEq.rfl

/-- The same cone, regarded as an object of the honest direct simplicial dg category. -/
def directDGMappingConeObject {K L : ComplexCategory} (f : K ⟶ L) :
    DirectDGSimplicialCategory :=
  directDGObject (dgMappingConeObject f)

/-- Regard a bounded chain map as an ordinary morphism in the direct simplicial dg category,
using the explicitly verified enriched-vertex equivalence. -/
def directDGMorphism {K L : ComplexCategory} (f : K ⟶ L) :
    directDGObject K ⟶ directDGObject L :=
  (directDGToComplexHomEquiv (directDGObject K) (directDGObject L)).symm f

@[simp]
theorem directDGToComplexFunctor_map_directDGMorphism
    {K L : ComplexCategory} (f : K ⟶ L) :
    directDGToComplexFunctor.map (directDGMorphism f) = f :=
  Equiv.apply_symm_apply
    (directDGToComplexHomEquiv (directDGObject K) (directDGObject L)) f

/-- Postcomposition by the cone inclusion, as an explicit morphism of enriched mapping
simplicial sets. -/
def directDGMappingConePostcomposition (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGObject T ⟶[SSet] directDGObject L) ⟶
      (directDGObject T ⟶[SSet] directDGMappingConeObject f) :=
  eHomWhiskerLeft SSet (directDGObject T) (directDGMorphism (dgMappingConeInr f))

/-- Precomposition by the cone inclusion, as an explicit morphism of enriched mapping
simplicial sets. -/
def directDGMappingConePrecomposition (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeObject f ⟶[SSet] directDGObject T) ⟶
      (directDGObject L ⟶[SSet] directDGObject T) :=
  eHomWhiskerRight SSet (directDGMorphism (dgMappingConeInr f)) (directDGObject T)

@[simp]
theorem directDGObjectEquiv_symm_directDGMappingConeObject
    {K L : ComplexCategory} (f : K ⟶ L) :
    directDGObjectEquiv.symm (directDGMappingConeObject f) = dgMappingConeObject f :=
  rfl

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
