import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence
import Mathlib.Algebra.Homology.HomotopyCofiber

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

/-- The genuine maps-out universal property of the project mapping cone. -/
noncomputable def dgMappingConeDescEquiv (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    (Σ (α : L.obj ⟶ T.obj),
      Homotopy (((boundedCochainComplex MetrizableLCA.{0}).ι.map f) ≫ α) 0) ≃
      ((dgMappingConeObject f).obj ⟶ T.obj) := by
  exact HomologicalComplex.homotopyCofiber.descEquiv
    (φ := (boundedCochainComplex MetrizableLCA.{0}).ι.map f) T.obj
    (fun j ↦ ⟨j - 1, by simp⟩)

@[simp]
theorem dgMappingConeDescEquiv_symm_fst (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L)
    (g : (dgMappingConeObject f).obj ⟶ T.obj) :
    ((dgMappingConeDescEquiv T f).symm g).1 =
      CochainComplex.mappingCone.inr
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) ≫ g :=
  rfl

/-- The nullhomotopy produced by the inverse maps-out equivalence is the
canonical homotopy-cofiber contraction, postcomposed with the given map. -/
theorem dgMappingConeDescEquiv_symm_snd (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L)
    (g : (dgMappingConeObject f).obj ⟶ T.obj) :
    ((dgMappingConeDescEquiv T f).symm g).2 =
      Homotopy.trans (Homotopy.ofEq (by
        rw [dgMappingConeDescEquiv_symm_fst]
        rfl))
        (((HomologicalComplex.homotopyCofiber.inrCompHomotopy
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)
          (fun j ↦ ⟨j - 1, by simp⟩)).compRight g).trans
            (Homotopy.ofEq (by simp))) :=
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

/-- The cone-coordinate equivalence is integer-linear, hence is an isomorphism of the
homogeneous modules used by the direct dg enrichment. -/
def dgMappingConeCochainLinearEquiv
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cochain T.obj
        (CochainComplex.mappingCone
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) n ≃ₗ[ℤ]
      (CochainComplex.HomComplex.Cochain T.obj K.obj (n + 1) ×
        CochainComplex.HomComplex.Cochain T.obj L.obj n) :=
  { dgMappingConeCochainAddEquiv T f n with
    map_smul' := by
      intro r γ
      apply Prod.ext
      · exact CochainComplex.HomComplex.Cochain.smul_comp r γ _ rfl
      · exact CochainComplex.HomComplex.Cochain.smul_comp r γ _ (add_zero n) }

private theorem transportedCochainDifferential_sq
    (C : CochainComplex (ModuleCat.{0} ℤ) ℤ) (n m k : ℤ)
    {Xn Xm Xk : ModuleCat.{0} ℤ}
    (en : C.X n ≅ Xn) (em : C.X m ≅ Xm) (ek : C.X k ≅ Xk) :
    (en.inv ≫ C.d n m ≫ em.hom) ≫ (em.inv ≫ C.d m k ≫ ek.hom) = 0 := by
  simp only [Category.assoc]
  rw [← Category.assoc em.hom em.inv]
  rw [Iso.hom_inv_id]
  simp only [Category.id_comp]
  rw [C.d_comp_d_assoc]
  simp

/-- The coordinate model for maps into a cone.  Its differential is transported from the
actual dg Hom complex through the degreewise linear equivalences above. -/
def dgMappingConeExplicitCoordinateCochainComplex
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    CochainComplex (ModuleCat.{0} ℤ) ℤ where
  X n := ModuleCat.of ℤ
    (CochainComplex.HomComplex.Cochain T.obj K.obj (n + 1) ×
      CochainComplex.HomComplex.Cochain T.obj L.obj n)
  d n m := (dgMappingConeCochainLinearEquiv T f n).toModuleIso.inv ≫
    (dgHomZModuleCochainComplex T (dgMappingConeObject f)).d n m ≫
      (dgMappingConeCochainLinearEquiv T f m).toModuleIso.hom
  shape n m h := by
    rw [(dgHomZModuleCochainComplex T (dgMappingConeObject f)).shape n m h]
    simp
  d_comp_d' n m k hnm hmk := by
    exact transportedCochainDifferential_sq
      (dgHomZModuleCochainComplex T (dgMappingConeObject f)) n m k
      (dgMappingConeCochainLinearEquiv T f n).toModuleIso
      (dgMappingConeCochainLinearEquiv T f m).toModuleIso
      (dgMappingConeCochainLinearEquiv T f k).toModuleIso

private theorem transportedCochainDifferential_comm
    (C : CochainComplex (ModuleCat.{0} ℤ) ℤ) (n m : ℤ)
    {Xn Xm : ModuleCat.{0} ℤ}
    (en : C.X n ≅ Xn) (em : C.X m ≅ Xm) :
    en.hom ≫ (en.inv ≫ C.d n m ≫ em.hom) = C.d n m ≫ em.hom := by
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The actual untruncated dg Hom complex into `Cone(f)` is isomorphic to its explicit
two-coordinate model. -/
def dgMappingConeExplicitCoordinateCochainIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex T (dgMappingConeObject f) ≅
      dgMappingConeExplicitCoordinateCochainComplex T f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (dgMappingConeCochainLinearEquiv T f n).toModuleIso) (by
      intro n m _
      dsimp [dgMappingConeExplicitCoordinateCochainComplex]
      exact transportedCochainDifferential_comm
        (dgHomZModuleCochainComplex T (dgMappingConeObject f)) n m
        (dgMappingConeCochainLinearEquiv T f n).toModuleIso
        (dgMappingConeCochainLinearEquiv T f m).toModuleIso)

/-- The cone Hom isomorphism survives the nonpositive truncation used by the direct dg
mapping object. -/
def dgMappingConeExplicitCoordinateChainIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleChainComplex T (dgMappingConeObject f) ≅
      HomologicalComplex.truncLE' (dgMappingConeExplicitCoordinateCochainComplex T f)
        ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{0} ℤ)).mapIso
    (dgMappingConeExplicitCoordinateCochainIso T f)

/-- Transport the truncated cone Hom isomorphism through the Dold--Kan inverse. -/
def dgMappingConeExplicitCoordinateSimplicialModuleIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleSimplicialModule T (dgMappingConeObject f) ≅
      DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
        (HomologicalComplex.truncLE'
          (dgMappingConeExplicitCoordinateCochainComplex T f)
          ComplexShape.embeddingDownNat) :=
  DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.mapIso
    (dgMappingConeExplicitCoordinateChainIso T f)

/-- Forgetting the module structure degreewise preserves the transported cone Hom
isomorphism. -/
def dgMappingConeExplicitCoordinateSSetIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleSSet T (dgMappingConeObject f) ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE'
            (dgMappingConeExplicitCoordinateCochainComplex T f)
            ComplexShape.embeddingDownNat)) :=
  zModuleSimplicialForget.mapIso
    (dgMappingConeExplicitCoordinateSimplicialModuleIso T f)

/-- The actual enriched Hom simplicial set into the cone is the Dold--Kan realization of the
explicit coordinate complex. -/
def directDGMappingConeEnrichedHomIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGObject T ⟶[SSet] directDGObject (dgMappingConeObject f)) ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE'
            (dgMappingConeExplicitCoordinateCochainComplex T f)
            ComplexShape.embeddingDownNat)) :=
  (eqToIso (directDG_enrichedHom_eq T (dgMappingConeObject f))).trans
    (dgMappingConeExplicitCoordinateSSetIso T f)

/-- Precomposition by `f` on untruncated dg Hom cochain complexes. -/
def dgHomZModulePrecomposition (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex L T ⟶ dgHomZModuleCochainComplex K T where
  f n := ModuleCat.ofHom
    { toFun := fun γ ↦ (CochainComplex.HomComplex.Cochain.ofHom f.hom).comp γ (zero_add n)
      map_add' := fun γ γ' ↦
        CochainComplex.HomComplex.Cochain.comp_add _ γ γ' (zero_add n)
      map_smul' := fun r γ ↦
        CochainComplex.HomComplex.Cochain.comp_smul _ r γ (zero_add n) }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro γ
    simp [dgHomZModuleCochainComplex,
      CochainComplex.HomComplex.δ_ofHom_comp]

/-- The standard chain-level path object of the target of precomposition. -/
abbrev dgHomPrecompositionPathObject (T K : ComplexCategory) :
    CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  HomologicalComplex.pathObject (dgHomZModuleCochainComplex K T)

/-- The endpoint map from the chain path object. -/
def dgHomPrecompositionPathEndpoints (T K : ComplexCategory) :
    dgHomPrecompositionPathObject T K ⟶
      (dgHomZModuleCochainComplex K T ⨯ dgHomZModuleCochainComplex K T) :=
  Limits.prod.lift
    (HomologicalComplex.pathObject.π₀ (dgHomZModuleCochainComplex K T))
    (HomologicalComplex.pathObject.π₁ (dgHomZModuleCochainComplex K T))

/-- Precomposition paired with the zero endpoint. -/
def dgHomPrecompositionZeroEndpoints (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex L T ⟶
      (dgHomZModuleCochainComplex K T ⨯ dgHomZModuleCochainComplex K T) :=
  Limits.prod.lift (dgHomZModulePrecomposition T f) 0

/-- The strict categorical path-object model of the homotopy fiber of precomposition. -/
abbrev dgHomPrecompositionPathFiber (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  Limits.pullback (dgHomPrecompositionZeroEndpoints T f)
    (dgHomPrecompositionPathEndpoints T K)

/-- By construction, the path-fiber square is a strict categorical pullback. -/
theorem dgHomPrecompositionPathFiber_isPullback (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    IsPullback
      (Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K))
      (Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K))
      (dgHomPrecompositionZeroEndpoints T f)
      (dgHomPrecompositionPathEndpoints T K) :=
  IsPullback.of_hasPullback _ _

/-- The cone triangle carries its genuine chain homotopy from the composite to zero. -/
def dgMappingConeTriangleHomotopy {K L : ComplexCategory} (f : K ⟶ L) :
    Homotopy
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map
        (f ≫ dgMappingConeInr f)) 0 :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨dgMappingConeInl f, by
      rw [dgMappingConeInl_delta]
      simp⟩

/-- A degree `-1` cochain induces the sign-corrected operation on contravariant dg Hom
complexes. -/
def dgHomPrecompositionHomotopyCochain (T : ComplexCategory)
    {X Y : ComplexCategory}
    (z : CochainComplex.HomComplex.Cochain
      (underlyingComplex X) (underlyingComplex Y) (-1)) :
    CochainComplex.HomComplex.Cochain
      (dgHomZModuleCochainComplex Y T) (dgHomZModuleCochainComplex X T) (-1) :=
  CochainComplex.HomComplex.Cochain.mk (fun p q hpq ↦ ModuleCat.ofHom
    { toFun := fun γ ↦ p.negOnePow • z.comp γ (by omega)
      map_add' := by intro γ γ'; rw [CochainComplex.HomComplex.Cochain.comp_add, smul_add]
      map_smul' := by
        intro r γ
        simp only [RingHom.id_apply]
        rw [CochainComplex.HomComplex.Cochain.comp_smul, smul_comm] })

theorem dgHomPrecompositionHomotopyCochain_delta
    (T : ComplexCategory) {X Y : ComplexCategory}
    (g₀ g₁ : X ⟶ Y)
    (z : CochainComplex.HomComplex.Cochain
      (underlyingComplex X) (underlyingComplex Y) (-1))
    (hz : CochainComplex.HomComplex.δ (-1) 0 z =
      CochainComplex.HomComplex.Cochain.ofHom g₀.hom -
        CochainComplex.HomComplex.Cochain.ofHom g₁.hom) :
    CochainComplex.HomComplex.δ (-1) 0
        (dgHomPrecompositionHomotopyCochain T z) =
      CochainComplex.HomComplex.Cochain.ofHom (dgHomZModulePrecomposition T g₀) -
        CochainComplex.HomComplex.Cochain.ofHom (dgHomZModulePrecomposition T g₁) := by
  ext p
  rename_i γ
  change _ = _
  rw [CochainComplex.HomComplex.δ_neg_one_cochain]
  simp only [CochainComplex.HomComplex.Cochain.ofHom_v]
  rw [Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (p - 1) p by simp)
    (show (ComplexShape.up ℤ).Rel p (p + 1) by simp)]
  simp only [dgHomPrecompositionHomotopyCochain,
    CochainComplex.HomComplex.Cochain.mk_v,
    CochainComplex.HomComplex.Cochain.sub_v,
    dgHomZModuleCochainComplex, dgHomZModulePrecomposition,
    ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_ofHom,
    LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    ConcreteCategory.comp_apply]
  simp only [CochainComplex.HomComplex.δ_hom_apply]
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [CochainComplex.HomComplex.δ_units_smul]
  have hz' := CochainComplex.HomComplex.Cochain.congr_v hz p p (add_zero p)
  simp only [CochainComplex.HomComplex.Cochain.sub_v,
    CochainComplex.HomComplex.Cochain.ofHom_v] at hz'
  rw [CochainComplex.HomComplex.δ_comp z γ (by omega) 0 (p + 1) p
    (by omega) (neg_add_cancel 1) rfl]
  rw [hz]
  simp only [hz', Int.negOnePow_succ, Units.neg_smul,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.sub_v,
    CochainComplex.HomComplex.Cochain.sub_comp,
    dgHomZModulePrecomposition, ModuleCat.hom_sub, ModuleCat.hom_ofHom,
    LinearMap.sub_apply, smul_add, smul_smul, Int.units_mul_self, one_smul]
  abel

/-- Chain homotopies act contravariantly on dg Hom cochain complexes. -/
def dgHomZModulePrecompositionHomotopy (T : ComplexCategory)
    {X Y : ComplexCategory} {g₀ g₁ : X ⟶ Y}
    (h : Homotopy g₀.hom g₁.hom) :
    Homotopy (dgHomZModulePrecomposition T g₀)
      (dgHomZModulePrecomposition T g₁) :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨dgHomPrecompositionHomotopyCochain T
        (CochainComplex.HomComplex.Cochain.ofHomotopy h), by
      rw [dgHomPrecompositionHomotopyCochain_delta T g₀ g₁ _
        (CochainComplex.HomComplex.δ_ofHomotopy h)]
      abel⟩

/-- The cone triangle nullhomotopy induces the homotopy required by the maps-out path
fiber. -/
def dgMappingConePrecompositionNullhomotopy (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    Homotopy (dgHomZModulePrecomposition T (f ≫ dgMappingConeInr f)) 0 := by
  convert dgHomZModulePrecompositionHomotopy T
    (dgMappingConeTriangleHomotopy f) using 1 <;>
      ext n γ <;> simp [dgHomZModulePrecomposition] <;> rfl

@[reassoc]
theorem dgHomZModulePrecomposition_comp (T : ComplexCategory)
    {X Y Z : ComplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dgHomZModulePrecomposition T g ≫ dgHomZModulePrecomposition T f =
      dgHomZModulePrecomposition T (f ≫ g) := by
  ext n γ
  change (CochainComplex.HomComplex.Cochain.ofHom f.hom).comp
      ((CochainComplex.HomComplex.Cochain.ofHom g.hom).comp γ (zero_add n))
        (zero_add n) =
    (CochainComplex.HomComplex.Cochain.ofHom (f.hom ≫ g.hom)).comp γ (zero_add n)
  rw [CochainComplex.HomComplex.Cochain.ofHom_comp]
  rw [CochainComplex.HomComplex.Cochain.comp_assoc]
  omega

/-- The cone nullhomotopy with its source written as a composite of precomposition maps. -/
def dgMappingConePrecompositionCompositeNullhomotopy (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    Homotopy
      (dgHomZModulePrecomposition T (dgMappingConeInr f) ≫
        dgHomZModulePrecomposition T f) 0 :=
  (Homotopy.ofEq (dgHomZModulePrecomposition_comp T f (dgMappingConeInr f))).trans
    (dgMappingConePrecompositionNullhomotopy T f)

/-- The cone nullhomotopy as a map into the standard chain path object. -/
def dgMappingConeHomToPathObject (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex (dgMappingConeObject f) T ⟶
      dgHomPrecompositionPathObject T K :=
  HomologicalComplex.pathObject.lift
    (dgHomZModulePrecomposition T (dgMappingConeInr f) ≫
      dgHomZModulePrecomposition T f) 0
    (dgMappingConePrecompositionCompositeNullhomotopy T f)

@[reassoc (attr := simp)]
theorem dgMappingConeHomToPathObject_π₀ (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingConeHomToPathObject T f ≫
        HomologicalComplex.pathObject.π₀ (dgHomZModuleCochainComplex K T) =
      dgHomZModulePrecomposition T (dgMappingConeInr f) ≫
        dgHomZModulePrecomposition T f :=
  HomologicalComplex.pathObject.lift_π₀ _ _ _

@[reassoc (attr := simp)]
theorem dgMappingConeHomToPathObject_π₁ (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingConeHomToPathObject T f ≫
        HomologicalComplex.pathObject.π₁ (dgHomZModuleCochainComplex K T) = 0 :=
  HomologicalComplex.pathObject.lift_π₁ _ _ _

/-- Endpoint commutativity needed for the canonical map to the strict pullback. -/
theorem dgMappingConeHom_pathFiber_condition (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModulePrecomposition T (dgMappingConeInr f) ≫
        dgHomPrecompositionZeroEndpoints T f =
      dgMappingConeHomToPathObject T f ≫
        dgHomPrecompositionPathEndpoints T K := by
  apply Limits.prod.hom_ext
  · simp [dgHomPrecompositionZeroEndpoints, dgHomPrecompositionPathEndpoints]
  · simp [dgHomPrecompositionZeroEndpoints, dgHomPrecompositionPathEndpoints]

/-- The canonical map from the actual cone Hom complex to the strict path-object
pullback. -/
def dgMappingConeHomToPathFiber (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex (dgMappingConeObject f) T ⟶
      dgHomPrecompositionPathFiber T f :=
  Limits.pullback.lift
    (dgHomZModulePrecomposition T (dgMappingConeInr f))
    (dgMappingConeHomToPathObject T f)
    (dgMappingConeHom_pathFiber_condition T f)

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
