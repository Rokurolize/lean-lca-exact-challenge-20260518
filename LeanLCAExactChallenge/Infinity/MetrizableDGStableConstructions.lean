import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence

/-!
# Mapping-cone objects in the bounded dg carrier

This file records the first object-level construction needed for a genuine stability proof of
the localized dg nerve.  It stays in the bounded dg carrier: the cone is not replaced by an
object of the ordinary derived category.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

/-- The verified zero object supplies the ordinary zero-object structure underlying the direct
simplicial enrichment. -/
noncomputable instance directDGSimplicialCategory_hasZeroObject :
    HasZeroObject DirectDGSimplicialCategory :=
  directDGZeroObject_isZero.hasZeroObject

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

/-- Maps from a bounded test complex into a cone are detected by their two cone coordinates.
This is the chain-level representability identity underlying the cocartesian cone square. -/
theorem dgMappingConeCochain_ext_to_iff
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L)
    (i j : ℤ) (hij : i + 1 = j)
    {a b : CochainComplex.HomComplex.Cochain T.obj
      (CochainComplex.mappingCone
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) i} :
    a = b ↔
      a.comp (CochainComplex.mappingCone.fst
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1 hij =
        b.comp (CochainComplex.mappingCone.fst
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1 hij ∧
      a.comp (CochainComplex.mappingCone.snd
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) (add_zero i) =
        b.comp (CochainComplex.mappingCone.snd
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) (add_zero i) :=
  CochainComplex.mappingCone.ext_cochain_to_iff
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) i j hij

/-- Maps out of a cone are detected by restriction to its shifted-source and target
coordinates.  This is the dual chain-level identity underlying the cartesian cone square. -/
theorem dgMappingConeCochain_ext_from_iff
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L)
    (i j : ℤ) (hij : i + 1 = j)
    {a b : CochainComplex.HomComplex.Cochain
      (CochainComplex.mappingCone
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) T.obj j} :
    a = b ↔
      (CochainComplex.mappingCone.inl
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).comp a (show _ = i by omega) =
        (CochainComplex.mappingCone.inl
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).comp b (by omega) ∧
      (CochainComplex.HomComplex.Cochain.ofHom
          (CochainComplex.mappingCone.inr
            ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))).comp a (zero_add j) =
        (CochainComplex.HomComplex.Cochain.ofHom
          (CochainComplex.mappingCone.inr
            ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))).comp b (zero_add j) :=
  CochainComplex.mappingCone.ext_cochain_from_iff
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) i j hij

/-- Degreewise additive decomposition of maps into a cone into its shifted-source and target
coordinates.  Unlike mere extensionality, this is the actual representability isomorphism on
the graded Hom carrier. -/
def dgMappingConeCochainAddEquiv
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cochain T.obj
        (CochainComplex.mappingCone
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) n ≃+
      (CochainComplex.HomComplex.Cochain T.obj K.obj (n + 1) ×
        CochainComplex.HomComplex.Cochain T.obj L.obj n) where
  toFun γ :=
    (γ.comp (CochainComplex.mappingCone.fst
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1 rfl,
      γ.comp (CochainComplex.mappingCone.snd
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) (add_zero n))
  invFun γ :=
    CochainComplex.mappingCone.liftCochain
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) γ.1 γ.2 rfl
  left_inv γ := by
    rw [dgMappingConeCochain_ext_to_iff T f n (n + 1) rfl]
    exact ⟨CochainComplex.mappingCone.liftCochain_fst _ _ _ _,
      CochainComplex.mappingCone.liftCochain_snd _ _ _ _⟩
  right_inv γ := by
    exact Prod.ext
      (CochainComplex.mappingCone.liftCochain_fst _ _ _ _)
      (CochainComplex.mappingCone.liftCochain_snd _ _ _ _)
  map_add' γ γ' := by
    apply Prod.ext
    · exact CochainComplex.HomComplex.Cochain.add_comp _ _ _ rfl
    · exact CochainComplex.HomComplex.Cochain.add_comp _ _ _ (add_zero n)

/-- Differential compatibility of the cone decomposition.  In coordinates the cone Hom
differential is the standard upper-triangular matrix: the shifted-source differential carries
the minus sign, while the target coordinate receives postcomposition by `f`. -/
theorem dgMappingConeCochainAddEquiv_symm_delta
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ)
    (a : CochainComplex.HomComplex.Cochain T.obj K.obj (n + 1))
    (b : CochainComplex.HomComplex.Cochain T.obj L.obj n) :
    CochainComplex.HomComplex.δ n (n + 1)
        ((dgMappingConeCochainAddEquiv T f n).symm (a, b)) =
      -(CochainComplex.HomComplex.δ (n + 1) (n + 2) a).comp
          (CochainComplex.mappingCone.inl
            ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) (by omega) +
        (CochainComplex.HomComplex.δ n (n + 1) b +
            a.comp (CochainComplex.HomComplex.Cochain.ofHom
              f.hom) (add_zero (n + 1))).comp
          (CochainComplex.HomComplex.Cochain.ofHom
            (CochainComplex.mappingCone.inr
              ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))) (add_zero (n + 1)) := by
  exact CochainComplex.mappingCone.δ_liftCochain
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) a b rfl (n + 2) (by omega)

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
