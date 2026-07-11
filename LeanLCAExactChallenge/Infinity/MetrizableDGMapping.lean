import LeanLCAExactChallenge.Infinity.MetrizableRelative
import Mathlib.Algebra.Homology.Embedding.TruncLE
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
import Mathlib.AlgebraicTopology.DoldKan.Equivalence
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Dold--Kan mapping objects for bounded metrizable complexes

The cochain Hom complex is truncated along `embeddingDownNat`, so degree zero is replaced
by its cycle object and negative cochain degrees become nonnegative chain degrees.  Dold--Kan
then produces a simplicial abelian group, whose underlying simplicial set is the prospective
higher mapping object.

This file constructs the mapping carriers and their associative unital composition on
vertices.  It does not yet transport composition through all simplicial degrees of Dold--Kan
or claim that these carriers form a simplicial category.
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
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial

/-- At simplicial degree zero, the identity is the only Dold--Kan splitting index. -/
lemma doldKanIndexSet_zero_eq_id
    (A : SimplicialObject.Splitting.IndexSet (op ⦋0⦌)) :
    A = SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌) := by
  apply (SimplicialObject.Splitting.IndexSet.eqId_iff_len_eq A).2
  exact Nat.eq_zero_of_le_zero (SimplexCategory.len_le_of_epi A.e)

/-- The degree-zero object of a nonnegative chain complex agrees with simplicial degree zero
of its explicit Dold--Kan inverse. -/
def doldKanGammaZeroIso (T : ChainComplex AddCommGrpCat ℕ) :
    T.X 0 ≅ (AlgebraicTopology.DoldKan.Γ₀.obj T).obj (op ⦋0⦌) := by
  let s := AlgebraicTopology.DoldKan.Γ₀.splitting T
  let p : ∀ A : SimplicialObject.Splitting.IndexSet (op ⦋0⦌),
      s.N A.1.unop.len ⟶ T.X 0 := fun A =>
    eqToHom (by rw [doldKanIndexSet_zero_eq_id A]; rfl)
  refine
    { hom := s.ι 0
      inv := s.desc (op ⦋0⦌) p
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← s.cofan_inj_id 0]
    exact (s.ι_desc (op ⦋0⦌) p
      (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌))).trans (by
        dsimp only [p]
        apply eqToHom_refl)
  · apply s.hom_ext'
    intro A
    have hA := doldKanIndexSet_zero_eq_id A
    subst A
    have hdesc :
        (s.cofan (op ⦋0⦌)).inj
              (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫
            (s.desc (op ⦋0⦌) p ≫ s.ι 0) =
          p (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫ s.ι 0 :=
      s.ι_desc_assoc (op ⦋0⦌) p
        (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) (s.ι 0)
    refine hdesc.trans ?_
    have hp : p (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) = 𝟙 _ := by
      dsimp only [p]
      apply eqToHom_refl
    rw [hp]
    calc
      𝟙 _ ≫ s.ι 0 = s.ι 0 := Category.id_comp _
      _ = (s.cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) :=
        (s.cofan_inj_id 0).symm
      _ = (s.cofan (op ⦋0⦌)).inj
          (SimplicialObject.Splitting.IndexSet.id (op ⦋0⦌)) ≫ 𝟙 _ :=
        (Category.comp_id _).symm

/-- The abstract Dold--Kan inverse has the same degree-zero comparison as its explicit
construction. -/
def doldKanInverseZeroIso (T : ChainComplex AddCommGrpCat ℕ) :
    T.X 0 ≅ (CategoryTheory.Abelian.DoldKan.equivalence.inverse.obj T).obj (op ⦋0⦌) :=
  doldKanGammaZeroIso T

/-- The underlying cochain complex of a bounded metrizable complex. -/
abbrev underlyingComplex (K : ComplexCategory) :
    CochainComplex MetrizableLCA.{0} ℤ :=
  (BoundedComplexCategory.ι MetrizableLCA.{0}).obj K

/-- The nonnegative chain complex obtained from the nonpositive Hom cochain complex. -/
def dgMappingChainComplex (K L : ComplexCategory) :
    ChainComplex AddCommGrpCat.{0} ℕ :=
  HomologicalComplex.truncLE'
    (CochainComplex.HomComplex (underlyingComplex K) (underlyingComplex L))
    ComplexShape.embeddingDownNat

/-- Composition of homogeneous cochains is bilinear.  This is the chain-level input for a
future shuffle/lax-monoidal Dold--Kan composition map. -/
def dgCochainCompBilinear (K L M : ComplexCategory) {p q r : ℤ} (h : p + q = r) :
    CochainComplex.HomComplex.Cochain (underlyingComplex K) (underlyingComplex L) p →+
      CochainComplex.HomComplex.Cochain (underlyingComplex L) (underlyingComplex M) q →+
        CochainComplex.HomComplex.Cochain (underlyingComplex K) (underlyingComplex M) r where
  toFun x :=
    { toFun := fun y => x.comp y h
      map_zero' := CochainComplex.HomComplex.Cochain.comp_zero x h
      map_add' := fun y z => CochainComplex.HomComplex.Cochain.comp_add x y z h }
  map_zero' := AddMonoidHom.ext fun y =>
    CochainComplex.HomComplex.Cochain.zero_comp y h
  map_add' x y := AddMonoidHom.ext fun z =>
    CochainComplex.HomComplex.Cochain.add_comp x y z h

/-- The Dold--Kan simplicial abelian group attached to the nonpositive Hom complex. -/
def dgMappingSimplicialAbelianGroup (K L : ComplexCategory) :
    SimplicialObject AddCommGrpCat.{0} :=
  CategoryTheory.Abelian.DoldKan.equivalence.inverse.obj
    (dgMappingChainComplex K L)

/-- The underlying simplicial set of the Dold--Kan Hom mapping object. -/
def dgMappingSSet (K L : ComplexCategory) : SSet.{0} :=
  ((SimplicialObject.whiskering AddCommGrpCat.{0} (Type 0)).obj
    (forget AddCommGrpCat.{0})).obj (dgMappingSimplicialAbelianGroup K L)

/-- The concrete zero-cocycles of the Hom complex present its chosen cycle object. -/
def dgCocycleIsoCycles (K L : ComplexCategory) :
    AddCommGrpCat.of
      (CochainComplex.HomComplex.Cocycle (underlyingComplex K) (underlyingComplex L) 0) ≅
      (CochainComplex.HomComplex (underlyingComplex K) (underlyingComplex L)).cycles 0 :=
  IsLimit.conePointUniqueUpToIso
    (CochainComplex.HomComplex.Cocycle.isKernel
      (underlyingComplex K) (underlyingComplex L) 0 1 (by omega))
    (HomologicalComplex.cyclesIsKernel
      (CochainComplex.HomComplex (underlyingComplex K) (underlyingComplex L))
      0 1 (CochainComplex.next ℤ 0))

/-- Degree zero of the truncated Hom chain complex is the additive group of zero-cocycles,
and hence, via `Cocycle.equivHom`, the additive group of cochain maps. -/
def dgMappingChainComplexZeroIsoCocycle (K L : ComplexCategory) :
    (dgMappingChainComplex K L).X 0 ≅
      AddCommGrpCat.of
        (CochainComplex.HomComplex.Cocycle (underlyingComplex K) (underlyingComplex L) 0) :=
  HomologicalComplex.truncLE'XIsoCycles
      (CochainComplex.HomComplex (underlyingComplex K) (underlyingComplex L))
      ComplexShape.embeddingDownNat (by rfl) (by
        constructor
        · simp
        · intro k hk
          dsimp [ComplexShape.embeddingDownNat] at hk
          omega) ≪≫
    (dgCocycleIsoCycles K L).symm

/-- Degree-zero elements of the truncated Hom chain complex are additively equivalent to
cochain maps between the underlying bounded complexes. -/
def dgMappingChainComplexZeroEquivHom (K L : ComplexCategory) :
    (dgMappingChainComplex K L).X 0 ≃+
      (underlyingComplex K ⟶ underlyingComplex L) :=
  (dgMappingChainComplexZeroIsoCocycle K L).addCommGroupIsoToAddEquiv.trans
    (CochainComplex.HomComplex.Cocycle.equivHom
      (underlyingComplex K) (underlyingComplex L)).symm

/-- Degree-zero elements of the truncated Hom chain complex are exactly morphisms in the
bounded-complex category. -/
def dgMappingChainComplexZeroEquivBoundedHom (K L : ComplexCategory) :
    (dgMappingChainComplex K L).X 0 ≃ (K ⟶ L) :=
  (dgMappingChainComplexZeroEquivHom K L).toEquiv.trans
    ((boundedCochainComplex MetrizableLCA.{0}).fullyFaithfulι.homEquiv).symm

/-- The vertices of the Dold--Kan mapping object are the zero-cocycles of the Hom complex. -/
def dgMappingVerticesIsoCocycles (K L : ComplexCategory) :
    (dgMappingSimplicialAbelianGroup K L).obj (op ⦋0⦌) ≅
      AddCommGrpCat.of
        (CochainComplex.HomComplex.Cocycle (underlyingComplex K) (underlyingComplex L) 0) :=
  (doldKanInverseZeroIso (dgMappingChainComplex K L)).symm ≪≫
    dgMappingChainComplexZeroIsoCocycle K L

/-- Vertices of the prospective higher mapping object are exactly cochain maps. -/
def dgMappingVerticesEquivCochainMaps (K L : ComplexCategory) :
    dgMappingSSet K L _⦋0⦌ ≃
      (underlyingComplex K ⟶ underlyingComplex L) :=
  (dgMappingVerticesIsoCocycles K L).addCommGroupIsoToAddEquiv.toEquiv.trans
    (CochainComplex.HomComplex.Cocycle.equivHom
      (underlyingComplex K) (underlyingComplex L)).symm.toEquiv

/-- Vertices of the prospective higher mapping object are exactly bounded-complex
morphisms. -/
def dgMappingVerticesEquivBoundedMorphisms (K L : ComplexCategory) :
    dgMappingSSet K L _⦋0⦌ ≃ (K ⟶ L) :=
  (dgMappingVerticesEquivCochainMaps K L).trans
    ((boundedCochainComplex MetrizableLCA.{0}).fullyFaithfulι.homEquiv).symm

/-- The vertex representing the identity cochain map. -/
def dgMappingIdentityVertex (K : ComplexCategory) :
    dgMappingSSet K K _⦋0⦌ :=
  (dgMappingVerticesEquivBoundedMorphisms K K).symm (𝟙 K)

/-- The enriched unit candidate: the identity vertex, degenerately extended through every
simplicial degree from the monoidal unit of simplicial sets. -/
def dgMappingIdentitySSetMap (K : ComplexCategory) :
    (𝟙_ SSet) ⟶ dgMappingSSet K K :=
  (SSet.unitHomEquiv _).symm (dgMappingIdentityVertex K)

/-- The degenerate identity simplex in an arbitrary simplicial degree. -/
def dgMappingIdentitySimplex (K : ComplexCategory) (n : SimplexCategoryᵒᵖ) :
    (dgMappingSSet K K).obj n :=
  (dgMappingIdentitySSetMap K).app n PUnit.unit

@[simp]
theorem dgMappingIdentitySSetMap_vertex (K : ComplexCategory) :
    SSet.unitHomEquiv _ (dgMappingIdentitySSetMap K) = dgMappingIdentityVertex K := by
  exact Equiv.apply_symm_apply _ _

/-- Composition on vertices, transported from composition of bounded cochain maps. -/
def dgMappingVertexComp (K L M : ComplexCategory)
    (f : dgMappingSSet K L _⦋0⦌) (g : dgMappingSSet L M _⦋0⦌) :
    dgMappingSSet K M _⦋0⦌ :=
  (dgMappingVerticesEquivBoundedMorphisms K M).symm
    (dgMappingVerticesEquivBoundedMorphisms K L f ≫
      dgMappingVerticesEquivBoundedMorphisms L M g)

@[simp]
theorem dgMappingVerticesEquiv_identity (K : ComplexCategory) :
    dgMappingVerticesEquivBoundedMorphisms K K (dgMappingIdentityVertex K) = 𝟙 K := by
  simp [dgMappingIdentityVertex]

@[simp]
theorem dgMappingVerticesEquiv_comp (K L M : ComplexCategory)
    (f : dgMappingSSet K L _⦋0⦌) (g : dgMappingSSet L M _⦋0⦌) :
    dgMappingVerticesEquivBoundedMorphisms K M (dgMappingVertexComp K L M f g) =
      dgMappingVerticesEquivBoundedMorphisms K L f ≫
        dgMappingVerticesEquivBoundedMorphisms L M g := by
  simp [dgMappingVertexComp]

/-- Vertex composition is associative. -/
theorem dgMappingVertexComp_assoc (K L M N : ComplexCategory)
    (f : dgMappingSSet K L _⦋0⦌) (g : dgMappingSSet L M _⦋0⦌)
    (h : dgMappingSSet M N _⦋0⦌) :
    dgMappingVertexComp K M N (dgMappingVertexComp K L M f g) h =
      dgMappingVertexComp K L N f (dgMappingVertexComp L M N g h) := by
  apply (dgMappingVerticesEquivBoundedMorphisms K N).injective
  simp only [dgMappingVerticesEquiv_comp, Category.assoc]

/-- The identity vertex is a left unit for vertex composition. -/
theorem dgMappingVertexComp_identity_left (K L : ComplexCategory)
    (f : dgMappingSSet K L _⦋0⦌) :
    dgMappingVertexComp K K L (dgMappingIdentityVertex K) f = f := by
  apply (dgMappingVerticesEquivBoundedMorphisms K L).injective
  simp

/-- The identity vertex is a right unit for vertex composition. -/
theorem dgMappingVertexComp_identity_right (K L : ComplexCategory)
    (f : dgMappingSSet K L _⦋0⦌) :
    dgMappingVertexComp K L L f (dgMappingIdentityVertex L) = f := by
  apply (dgMappingVerticesEquivBoundedMorphisms K L).injective
  simp

/-- The exact type of a simplicial composition map between three Dold--Kan mapping
carriers. -/
abbrev DgMappingComposition (K L M : ComplexCategory) :=
  (dgMappingSSet K L ⊗ dgMappingSSet L M) ⟶ dgMappingSSet K M

/-- A simplicial composition map extends the already-checked category structure on vertices. -/
def DgMappingComposition.ExtendsVertices {K L M : ComplexCategory}
    (comp : DgMappingComposition K L M) : Prop :=
  ∀ (f : dgMappingSSet K L _⦋0⦌) (g : dgMappingSSet L M _⦋0⦌),
    comp.app _ (f, g) = dgMappingVertexComp K L M f g

/-- The remaining coherent enrichment data for the Dold--Kan mapping carriers.

An inhabitant supplies actual simplicial composition extending bounded cochain-map
composition.  No inhabitant is asserted until the Alexander--Whitney transport is built. -/
structure DgMappingEnrichment where
  comp : ∀ K L M : ComplexCategory, DgMappingComposition K L M
  comp_vertices : ∀ K L M, (comp K L M).ExtendsVertices
  comp_assoc : ∀ (K L M N : ComplexCategory) (n : SimplexCategoryᵒᵖ)
      (f : (dgMappingSSet K L).obj n) (g : (dgMappingSSet L M).obj n)
      (h : (dgMappingSSet M N).obj n),
    (comp K M N).app n ((comp K L M).app n (f, g), h) =
      (comp K L N).app n (f, (comp L M N).app n (g, h))
  comp_identity_left : ∀ (K L : ComplexCategory) (n : SimplexCategoryᵒᵖ)
      (f : (dgMappingSSet K L).obj n),
    (comp K K L).app n (dgMappingIdentitySimplex K n, f) = f
  comp_identity_right : ∀ (K L : ComplexCategory) (n : SimplexCategoryᵒᵖ)
      (f : (dgMappingSSet K L).obj n),
    (comp K L L).app n (f, dgMappingIdentitySimplex L n) = f

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
