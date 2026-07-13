import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence
import Mathlib.Algebra.Category.ModuleCat.Limits
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
    Homotopy (dgHomZModulePrecomposition T (f ≫ dgMappingConeInr f)) 0 :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨@dgHomPrecompositionHomotopyCochain T K (dgMappingConeObject f)
      (dgMappingConeInl f), by
      rw [dgHomPrecompositionHomotopyCochain_delta T
        (f ≫ dgMappingConeInr f) 0 (dgMappingConeInl f)]
      · have hzero : dgHomZModulePrecomposition T
            (0 : K ⟶ dgMappingConeObject f) = 0 := by
          ext n g
          simp [dgHomZModulePrecomposition]
          rfl
        rw [hzero]
        simp
      · rw [dgMappingConeInl_delta]
        simp⟩

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

def zModuleElementHom {M : ModuleCat.{0} ℤ} (x : M) :
    ModuleCat.of ℤ ℤ ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ M x)

@[reassoc]
theorem zModuleElementHom_comp {M N : ModuleCat.{0} ℤ}
    (x : M) (f : M ⟶ N) :
    zModuleElementHom x ≫ f = zModuleElementHom (f.hom x) := by
  apply ModuleCat.hom_ext
  exact LinearMap.comp_toSpanSingleton f.hom x

theorem zModuleElementHom_injective {M : ModuleCat.{0} ℤ} {x y : M}
    (h : zModuleElementHom x = zModuleElementHom y) : x = y := by
  apply LinearMap.toSpanSingleton_injective ℤ M
  exact congrArg ModuleCat.Hom.hom h

def dgMappingConeCochainFromLinearEquiv
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cochain (dgMappingConeObject f).obj T.obj n ≃ₗ[ℤ]
      (CochainComplex.HomComplex.Cochain K.obj T.obj (n - 1) ×
        CochainComplex.HomComplex.Cochain L.obj T.obj n) where
  toFun γ :=
    ((CochainComplex.mappingCone.inl
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).comp γ (by omega),
      (CochainComplex.HomComplex.Cochain.ofHom
        (CochainComplex.mappingCone.inr
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f))).comp γ (zero_add n))
  invFun γ := CochainComplex.mappingCone.descCochain
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) γ.1 γ.2 (by omega)
  left_inv γ := by
    rw [dgMappingConeCochain_ext_from_iff T f (n - 1) n (by omega)]
    exact ⟨CochainComplex.mappingCone.inl_descCochain _ _ _ _,
      CochainComplex.mappingCone.inr_descCochain _ _ _ _⟩
  right_inv γ := by
    exact Prod.ext
      (CochainComplex.mappingCone.inl_descCochain _ _ _ _)
      (CochainComplex.mappingCone.inr_descCochain _ _ _ _)
  map_add' γ γ' := by
    apply Prod.ext
    · exact CochainComplex.HomComplex.Cochain.comp_add _ γ γ' (by omega)
    · exact CochainComplex.HomComplex.Cochain.comp_add _ γ γ' (zero_add n)
  map_smul' r γ := by
    apply Prod.ext
    · exact CochainComplex.HomComplex.Cochain.comp_smul _ r γ (by omega)
    · exact CochainComplex.HomComplex.Cochain.comp_smul _ r γ (zero_add n)

def pathObjectHomotopyCoordinate
    (C : CochainComplex (ModuleCat.{0} ℤ) ℤ) (n : ℤ) :
    C.pathObject.X n ⟶ C.X (n - 1) := by
  letI : DecidableRel (ComplexShape.up ℤ).symm.Rel :=
    (ComplexShape.up ℤ).decidableRelSymm
  simpa [HomologicalComplex.pathObject] using
    (HomologicalComplex.cylinder.inlX C.op (n - 1) n (by simp)).unop

theorem pathObject_lift_homotopyCoordinate
    {A C : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    (f g : A ⟶ C) (h : Homotopy f g) (n : ℤ) :
    (HomologicalComplex.pathObject.lift f g h).f n ≫
        pathObjectHomotopyCoordinate C n =
      h.hom n (n - 1) := by
  letI : DecidableRel (ComplexShape.up ℤ).symm.Rel :=
    (ComplexShape.up ℤ).decidableRelSymm
  dsimp [HomologicalComplex.pathObject.lift, pathObjectHomotopyCoordinate,
    HomologicalComplex.pathObject]
  apply Quiver.Hom.op_inj
  have hn : (ComplexShape.up ℤ).symm.Rel n (n - 1) := by
    change n - 1 + 1 = n
    omega
  change (HomologicalComplex.cylinder.inlX
      ((HomologicalComplex.opFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).obj
        (Opposite.op C)) (n - 1) n hn) ≫
      (HomologicalComplex.cylinder.desc
        ((HomologicalComplex.opFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).map f.op)
        ((HomologicalComplex.opFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).map g.op)
        h.op).f n = h.op.hom (n - 1) n
  unfold HomologicalComplex.cylinder.inlX HomologicalComplex.cylinder.desc
  rw [HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp [Homotopy.trans, Homotopy.ofEq, Homotopy.equivSubZero]

theorem pathObject_X_hom_ext
    (C : CochainComplex (ModuleCat.{0} ℤ) ℤ) (n : ℤ)
    {A : ModuleCat.{0} ℤ} {x y : A ⟶ C.pathObject.X n}
    (hc : x ≫ pathObjectHomotopyCoordinate C n =
      y ≫ pathObjectHomotopyCoordinate C n)
    (h₀ : x ≫ (HomologicalComplex.pathObject.π₀ C).f n =
      y ≫ (HomologicalComplex.pathObject.π₀ C).f n)
    (h₁ : x ≫ (HomologicalComplex.pathObject.π₁ C).f n =
      y ≫ (HomologicalComplex.pathObject.π₁ C).f n) :
    x = y := by
  letI : DecidableRel (ComplexShape.up ℤ).symm.Rel :=
    (ComplexShape.up ℤ).decidableRelSymm
  apply Quiver.Hom.op_inj
  dsimp [HomologicalComplex.pathObject, pathObjectHomotopyCoordinate] at *
  apply HomologicalComplex.homotopyCofiber.ext_from_X
  · exact congrArg Quiver.Hom.op hc
  · rw [← cancel_epi
        (HomologicalComplex.biprodXIso C.op C.op n).inv]
    apply Limits.biprod.hom_ext'
    · simp only [HomologicalComplex.inl_biprodXIso_inv_assoc]
      simpa [HomologicalComplex.pathObject.π₀,
          HomologicalComplex.cylinder.ι₀, HomologicalComplex.homotopyCofiber.inr,
          HomologicalComplex.pathObject, Category.assoc] using
        congrArg Quiver.Hom.op h₀
    · simp only [HomologicalComplex.inr_biprodXIso_inv_assoc]
      simpa [HomologicalComplex.pathObject.π₁,
          HomologicalComplex.cylinder.ι₁, HomologicalComplex.homotopyCofiber.inr,
          HomologicalComplex.pathObject, Category.assoc] using
        congrArg Quiver.Hom.op h₁

theorem dgMappingConePrecompositionCompositeNullhomotopy_hom_apply
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ)
    (g : CochainComplex.HomComplex.Cochain (dgMappingConeObject f).obj T.obj n) :
    ((dgMappingConePrecompositionCompositeNullhomotopy T f).hom n (n - 1)).hom g =
      n.negOnePow •
        (CochainComplex.mappingCone.inl
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).comp g (by omega) := by
  unfold dgMappingConePrecompositionCompositeNullhomotopy
  dsimp [Homotopy.trans, Homotopy.ofEq]
  unfold dgMappingConePrecompositionNullhomotopy
  dsimp [CochainComplex.HomComplex.Cochain.equivHomotopy]
  rw [dif_pos (by omega)]
  simp only [zero_add]
  change n.negOnePow • (dgMappingConeInl f).comp g
    (show -1 + n = n - 1 by omega) = _
  rfl

@[reassoc]
theorem dgMappingConeHomToPathFiber_fst
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingConeHomToPathFiber T f ≫
        Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) =
      dgHomZModulePrecomposition T (dgMappingConeInr f) :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem dgMappingConeHomToPathFiber_snd
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingConeHomToPathFiber T f ≫
        Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) =
      dgMappingConeHomToPathObject T f :=
  Limits.pullback.lift_snd _ _ _

@[reassoc]
theorem dgMappingConeHomToPathFiber_snd_π₀
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingConeHomToPathFiber T f ≫
        Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) ≫
      HomologicalComplex.pathObject.π₀ (dgHomZModuleCochainComplex K T) =
    dgMappingConeHomToPathFiber T f ≫
        Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) ≫
      dgHomZModulePrecomposition T f := by
  rw [← Category.assoc, dgMappingConeHomToPathFiber_snd,
    dgMappingConeHomToPathObject_π₀]
  rw [← Category.assoc, dgMappingConeHomToPathFiber_fst]

@[reassoc]
theorem dgMappingConeHomToPathFiber_snd_π₁
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingConeHomToPathFiber T f ≫
        Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) ≫
      HomologicalComplex.pathObject.π₁ (dgHomZModuleCochainComplex K T) = 0 := by
  rw [← Category.assoc, dgMappingConeHomToPathFiber_snd,
    dgMappingConeHomToPathObject_π₁]

@[reassoc]
theorem dgHomPrecompositionPathFiber_fst_precomposition
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) ≫
        dgHomZModulePrecomposition T f =
      Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) ≫
        HomologicalComplex.pathObject.π₀ (dgHomZModuleCochainComplex K T) := by
  have h : Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K) ≫
      dgHomPrecompositionZeroEndpoints T f =
    Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K) ≫
      dgHomPrecompositionPathEndpoints T K := Limits.pullback.condition
  have h₀ := congrArg (fun z ↦ z ≫ Limits.prod.fst) h
  simpa [dgHomPrecompositionZeroEndpoints, dgHomPrecompositionPathEndpoints,
    Category.assoc] using h₀

@[reassoc]
theorem dgHomPrecompositionPathFiber_snd_π₁
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K) ≫
        HomologicalComplex.pathObject.π₁ (dgHomZModuleCochainComplex K T) = 0 := by
  have h : Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K) ≫
      dgHomPrecompositionZeroEndpoints T f =
    Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K) ≫
      dgHomPrecompositionPathEndpoints T K := Limits.pullback.condition
  have h₁ := congrArg (fun z ↦ z ≫ Limits.prod.snd) h
  simpa [dgHomPrecompositionZeroEndpoints, dgHomPrecompositionPathEndpoints,
    Category.assoc] using h₁.symm

def dgMappingConeHomToPathFiberLinearEquiv
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    (dgHomZModuleCochainComplex (dgMappingConeObject f) T).X n ≃ₗ[ℤ]
      (dgHomPrecompositionPathFiber T f).X n where
  toFun g := (dgMappingConeHomToPathFiber T f).f n g
  invFun x := CochainComplex.mappingCone.descCochain
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)
    (n.negOnePow • (((Limits.pullback.snd
      (dgHomPrecompositionZeroEndpoints T f)
      (dgHomPrecompositionPathEndpoints T K)).f n ≫
        pathObjectHomotopyCoordinate (dgHomZModuleCochainComplex K T) n).hom x))
    (((Limits.pullback.fst
      (dgHomPrecompositionZeroEndpoints T f)
      (dgHomPrecompositionPathEndpoints T K)).f n).hom x) (by omega)
  left_inv g := by
    rw [dgMappingConeCochain_ext_from_iff T f (n - 1) n (by omega)]
    constructor
    · rw [CochainComplex.mappingCone.inl_descCochain]
      have hs := congrArg (fun z ↦ z.f n)
        (dgMappingConeHomToPathFiber_snd T f)
      have hsc := congrArg (fun z ↦ z ≫
        pathObjectHomotopyCoordinate (dgHomZModuleCochainComplex K T) n) hs
      have hscg := congrArg (fun z ↦ z.hom g) hsc
      change n.negOnePow •
        (((dgMappingConeHomToPathFiber T f ≫
            Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
              (dgHomPrecompositionPathEndpoints T K)).f n ≫
          pathObjectHomotopyCoordinate
            (dgHomZModuleCochainComplex K T) n).hom g) = _
      rw [hscg]
      unfold dgMappingConeHomToPathObject
      rw [pathObject_lift_homotopyCoordinate]
      rw [dgMappingConePrecompositionCompositeNullhomotopy_hom_apply]
      simp [smul_smul]
    · rw [CochainComplex.mappingCone.inr_descCochain]
      have hf := congrArg (fun z ↦ z.f n)
        (dgMappingConeHomToPathFiber_fst T f)
      change (((dgMappingConeHomToPathFiber T f ≫
        Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K)).f n).hom g) = _
      rw [hf]
      change (CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map
          (dgMappingConeInr f))).comp g (zero_add n) = _
      rw [boundedInclusion_map_dgMappingConeInr]
  right_inv x := by
    let z := CochainComplex.mappingCone.descCochain
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)
      (n.negOnePow • (((Limits.pullback.snd
        (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K)).f n ≫
          pathObjectHomotopyCoordinate
            (dgHomZModuleCochainComplex K T) n).hom x))
      (((Limits.pullback.fst
        (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K)).f n).hom x) (by omega)
    change ((dgMappingConeHomToPathFiber T f).f n).hom z = x
    apply zModuleElementHom_injective
    let hpb := (dgHomPrecompositionPathFiber_isPullback T f).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) n)
    have hfst : ((Limits.pullback.fst
        (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K)).f n).hom
          (((dgMappingConeHomToPathFiber T f).f n).hom z) =
        ((Limits.pullback.fst
          (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K)).f n).hom x := by
      have hf := congrArg (fun q ↦ q.f n)
        (dgMappingConeHomToPathFiber_fst T f)
      change (((dgMappingConeHomToPathFiber T f ≫
        Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
          (dgHomPrecompositionPathEndpoints T K)).f n).hom z) = _
      rw [hf]
      change (CochainComplex.HomComplex.Cochain.ofHom
        ((boundedCochainComplex MetrizableLCA.{0}).ι.map
          (dgMappingConeInr f))).comp _ (zero_add n) = _
      rw [boundedInclusion_map_dgMappingConeInr]
      dsimp only [z]
      rw [CochainComplex.mappingCone.inr_descCochain]
    apply hpb.hom_ext
    · simp only [zModuleElementHom_comp]
      exact congrArg zModuleElementHom hfst
    · simp only [zModuleElementHom_comp]
      apply pathObject_X_hom_ext
      · rw [zModuleElementHom_comp, zModuleElementHom_comp]
        apply congrArg zModuleElementHom
        have hs := congrArg (fun z ↦ z.f n)
          (dgMappingConeHomToPathFiber_snd T f)
        have hsc := congrArg (fun z ↦ z ≫
          pathObjectHomotopyCoordinate (dgHomZModuleCochainComplex K T) n) hs
        have hscz := congrArg (fun q ↦ q.hom z) hsc
        change (((dgMappingConeHomToPathFiber T f ≫
            Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
              (dgHomPrecompositionPathEndpoints T K)).f n ≫
          pathObjectHomotopyCoordinate
            (dgHomZModuleCochainComplex K T) n).hom z) = _
        rw [hscz]
        unfold dgMappingConeHomToPathObject
        rw [pathObject_lift_homotopyCoordinate]
        rw [dgMappingConePrecompositionCompositeNullhomotopy_hom_apply]
        dsimp only [z]
        rw [CochainComplex.mappingCone.inl_descCochain]
        simp [smul_smul]
      · rw [zModuleElementHom_comp, zModuleElementHom_comp]
        apply congrArg zModuleElementHom
        have hy := congrArg (fun q ↦ q.f n)
          (dgMappingConeHomToPathFiber_snd_π₀ T f)
        have hyz := congrArg (fun q ↦ q.hom z) hy
        have hx := congrArg (fun q ↦ q.f n)
          (dgHomPrecompositionPathFiber_fst_precomposition T f)
        have hxx := congrArg (fun q ↦ q.hom x) hx
        calc
          _ = ((dgHomZModulePrecomposition T f).f n).hom
                (((Limits.pullback.fst
                  (dgHomPrecompositionZeroEndpoints T f)
                  (dgHomPrecompositionPathEndpoints T K)).f n).hom
                    (((dgMappingConeHomToPathFiber T f).f n).hom z)) := hyz
          _ = ((dgHomZModulePrecomposition T f).f n).hom
                (((Limits.pullback.fst
                  (dgHomPrecompositionZeroEndpoints T f)
                  (dgHomPrecompositionPathEndpoints T K)).f n).hom x) :=
            congrArg (fun q ↦ ((dgHomZModulePrecomposition T f).f n).hom q) hfst
          _ = _ := hxx
      · rw [zModuleElementHom_comp, zModuleElementHom_comp]
        apply congrArg zModuleElementHom
        have hy := congrArg (fun q ↦ q.f n)
          (dgMappingConeHomToPathFiber_snd_π₁ T f)
        have hyz := congrArg (fun q ↦ q.hom z) hy
        have hx := congrArg (fun q ↦ q.f n)
          (dgHomPrecompositionPathFiber_snd_π₁ T f)
        have hxx := congrArg (fun q ↦ q.hom x) hx
        exact hyz.trans hxx.symm
  map_add' g g' := by
    exact (dgMappingConeHomToPathFiber T f).f n |>.hom.map_add g g'
  map_smul' r g := by
    exact (dgMappingConeHomToPathFiber T f).f n |>.hom.map_smul r g

noncomputable instance dgMappingConeHomToPathFiber_isIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    IsIso (dgMappingConeHomToPathFiber T f) := by
  letI (n : ℤ) : IsIso ((dgMappingConeHomToPathFiber T f).f n) := by
    let e := (dgMappingConeHomToPathFiberLinearEquiv T f n).toModuleIso
    change IsIso e.hom
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

def dgMappingConeHomPathFiberIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex (dgMappingConeObject f) T ≅
      dgHomPrecompositionPathFiber T f :=
  asIso (dgMappingConeHomToPathFiber T f)

def dgMappingConeHomPathFiberChainIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleChainComplex (dgMappingConeObject f) T ≅
      HomologicalComplex.truncLE' (dgHomPrecompositionPathFiber T f)
        ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{0} ℤ)).mapIso
    (dgMappingConeHomPathFiberIso T f)

def dgMappingConeHomPathFiberSimplicialModuleIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleSimplicialModule (dgMappingConeObject f) T ≅
      DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
        (HomologicalComplex.truncLE' (dgHomPrecompositionPathFiber T f)
          ComplexShape.embeddingDownNat) :=
  DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.mapIso
    (dgMappingConeHomPathFiberChainIso T f)

def dgMappingConeHomPathFiberSSetIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleSSet (dgMappingConeObject f) T ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE' (dgHomPrecompositionPathFiber T f)
            ComplexShape.embeddingDownNat)) :=
  zModuleSimplicialForget.mapIso
    (dgMappingConeHomPathFiberSimplicialModuleIso T f)

def directDGMappingConePathFiberEnrichedHomIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeObject f ⟶[SSet] directDGObject T) ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE' (dgHomPrecompositionPathFiber T f)
            ComplexShape.embeddingDownNat)) :=
  (eqToIso (directDG_enrichedHom_eq (dgMappingConeObject f) T)).trans
    (dgMappingConeHomPathFiberSSetIso T f)

theorem cochainDegree_isPullback
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (n : ℤ) :
    IsPullback (fst.f n) (snd.f n) (f.f n) (g.f n) := by
  change IsPullback
    ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) n).map fst)
    ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) n).map snd)
    ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) n).map f)
    ((HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℤ) n).map g)
  exact h.map _

def cyclesPullbackLift
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (n : ℤ)
    (s : PullbackCone (HomologicalComplex.cyclesMap f n)
      (HomologicalComplex.cyclesMap g n)) :
    s.pt ⟶ P.cycles n := by
  have hw : (s.fst ≫ X.iCycles n) ≫ f.f n =
      (s.snd ≫ Y.iCycles n) ≫ g.f n := by
    simpa only [Category.assoc, HomologicalComplex.cyclesMap_i] using
      congrArg (fun q ↦ q ≫ Z.iCycles n) s.condition
  let k : s.pt ⟶ P.X n := (cochainDegree_isPullback h n).lift
    (s.fst ≫ X.iCycles n) (s.snd ≫ Y.iCycles n) hw
  exact P.liftCycles k (n + 1) (CochainComplex.next ℤ n) (by
    apply (cochainDegree_isPullback h (n + 1)).hom_ext
    · rw [Category.assoc, ← fst.comm, ← Category.assoc,
        (cochainDegree_isPullback h n).lift_fst,
        Category.assoc, HomologicalComplex.iCycles_d, comp_zero, zero_comp]
    · rw [Category.assoc, ← snd.comm, ← Category.assoc,
        (cochainDegree_isPullback h n).lift_snd,
        Category.assoc, HomologicalComplex.iCycles_d, comp_zero, zero_comp])

theorem cyclesPullbackLift_fst
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (n : ℤ)
    (s : PullbackCone (HomologicalComplex.cyclesMap f n)
      (HomologicalComplex.cyclesMap g n)) :
    cyclesPullbackLift h n s ≫ HomologicalComplex.cyclesMap fst n = s.fst := by
  apply (cancel_mono (X.iCycles n)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  change (cyclesPullbackLift h n s ≫ P.iCycles n) ≫ fst.f n = _
  rw [cyclesPullbackLift, HomologicalComplex.liftCycles_i,
    (cochainDegree_isPullback h n).lift_fst]

theorem cyclesPullbackLift_snd
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (n : ℤ)
    (s : PullbackCone (HomologicalComplex.cyclesMap f n)
      (HomologicalComplex.cyclesMap g n)) :
    cyclesPullbackLift h n s ≫ HomologicalComplex.cyclesMap snd n = s.snd := by
  apply (cancel_mono (Y.iCycles n)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  change (cyclesPullbackLift h n s ≫ P.iCycles n) ≫ snd.f n = _
  rw [cyclesPullbackLift, HomologicalComplex.liftCycles_i,
    (cochainDegree_isPullback h n).lift_snd]

theorem cyclesPullbackLift_unique
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (n : ℤ)
    (s : PullbackCone (HomologicalComplex.cyclesMap f n)
      (HomologicalComplex.cyclesMap g n))
    (m : s.pt ⟶ P.cycles n)
    (hm₁ : m ≫ HomologicalComplex.cyclesMap fst n = s.fst)
    (hm₂ : m ≫ HomologicalComplex.cyclesMap snd n = s.snd) :
    m = cyclesPullbackLift h n s := by
  apply (cancel_mono (P.iCycles n)).1
  apply (cochainDegree_isPullback h n).hom_ext
  · calc
      (m ≫ P.iCycles n) ≫ fst.f n =
          (m ≫ HomologicalComplex.cyclesMap fst n) ≫ X.iCycles n := by
            simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
      _ = s.fst ≫ X.iCycles n := congrArg (fun q ↦ q ≫ X.iCycles n) hm₁
      _ = (cyclesPullbackLift h n s ≫
          HomologicalComplex.cyclesMap fst n) ≫ X.iCycles n :=
        (congrArg (fun q ↦ q ≫ X.iCycles n)
          (cyclesPullbackLift_fst h n s)).symm
      _ = (cyclesPullbackLift h n s ≫ P.iCycles n) ≫ fst.f n := by
        simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  · calc
      (m ≫ P.iCycles n) ≫ snd.f n =
          (m ≫ HomologicalComplex.cyclesMap snd n) ≫ Y.iCycles n := by
            simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
      _ = s.snd ≫ Y.iCycles n := congrArg (fun q ↦ q ≫ Y.iCycles n) hm₂
      _ = (cyclesPullbackLift h n s ≫
          HomologicalComplex.cyclesMap snd n) ≫ Y.iCycles n :=
        (congrArg (fun q ↦ q ≫ Y.iCycles n)
          (cyclesPullbackLift_snd h n s)).symm
      _ = (cyclesPullbackLift h n s ≫ P.iCycles n) ≫ snd.f n := by
        simp only [Category.assoc, HomologicalComplex.cyclesMap_i]

theorem cyclesMap_isPullback
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (n : ℤ) :
    IsPullback
      (HomologicalComplex.cyclesMap fst n)
      (HomologicalComplex.cyclesMap snd n)
      (HomologicalComplex.cyclesMap f n)
      (HomologicalComplex.cyclesMap g n) := by
  refine IsPullback.of_isLimit'
    ⟨by rw [← HomologicalComplex.cyclesMap_comp,
      ← HomologicalComplex.cyclesMap_comp, h.w]⟩ ?_
  exact PullbackCone.IsLimit.mk _ (cyclesPullbackLift h n)
    (cyclesPullbackLift_fst h n) (cyclesPullbackLift_snd h n)
    (cyclesPullbackLift_unique h n)

theorem truncLE'_map_isPullback
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) :
    IsPullback
      (HomologicalComplex.truncLE'Map fst ComplexShape.embeddingDownNat)
      (HomologicalComplex.truncLE'Map snd ComplexShape.embeddingDownNat)
      (HomologicalComplex.truncLE'Map f ComplexShape.embeddingDownNat)
      (HomologicalComplex.truncLE'Map g ComplexShape.embeddingDownNat) := by
  refine IsPullback.of_isLimit'
    ⟨by rw [← HomologicalComplex.truncLE'Map_comp,
      ← HomologicalComplex.truncLE'Map_comp, h.w]⟩ ?_
  apply HomologicalComplex.isLimitOfEval
  intro i
  have hi : IsPullback
      ((HomologicalComplex.truncLE'Map fst ComplexShape.embeddingDownNat).f i)
      ((HomologicalComplex.truncLE'Map snd ComplexShape.embeddingDownNat).f i)
      ((HomologicalComplex.truncLE'Map f ComplexShape.embeddingDownNat).f i)
      ((HomologicalComplex.truncLE'Map g ComplexShape.embeddingDownNat).f i) := by
    by_cases hb : ComplexShape.embeddingDownNat.BoundaryLE i
    · apply (cyclesMap_isPullback h
          (ComplexShape.embeddingDownNat.f i)).of_iso'
        (P.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb)
        (X.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb)
        (Y.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb)
        (Z.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb)
      · rw [HomologicalComplex.truncLE'Map_f_eq_cyclesMap fst
          ComplexShape.embeddingDownNat hb rfl]
        simp
      · rw [HomologicalComplex.truncLE'Map_f_eq_cyclesMap snd
          ComplexShape.embeddingDownNat hb rfl]
        simp
      · rw [HomologicalComplex.truncLE'Map_f_eq_cyclesMap f
          ComplexShape.embeddingDownNat hb rfl]
        simp
      · rw [HomologicalComplex.truncLE'Map_f_eq_cyclesMap g
          ComplexShape.embeddingDownNat hb rfl]
        simp
    · apply (cochainDegree_isPullback h
          (ComplexShape.embeddingDownNat.f i)).of_iso'
        (P.truncLE'XIso ComplexShape.embeddingDownNat rfl hb)
        (X.truncLE'XIso ComplexShape.embeddingDownNat rfl hb)
        (Y.truncLE'XIso ComplexShape.embeddingDownNat rfl hb)
        (Z.truncLE'XIso ComplexShape.embeddingDownNat rfl hb)
      · rw [HomologicalComplex.truncLE'Map_f_eq fst
          ComplexShape.embeddingDownNat hb rfl]
        simp
      · rw [HomologicalComplex.truncLE'Map_f_eq snd
          ComplexShape.embeddingDownNat hb rfl]
        simp
      · rw [HomologicalComplex.truncLE'Map_f_eq f
          ComplexShape.embeddingDownNat hb rfl]
        simp
      · rw [HomologicalComplex.truncLE'Map_f_eq g
          ComplexShape.embeddingDownNat hb rfl]
        simp
  let E := HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) i
  refine (IsLimit.equivOfNatIsoOfIso
    (cospanCompIso E
      (HomologicalComplex.truncLE'Map f ComplexShape.embeddingDownNat)
      (HomologicalComplex.truncLE'Map g ComplexShape.embeddingDownNat)) _ _
      (WalkingCospan.ext ?_ ?_ ?_)).symm hi.isLimit
  · exact Iso.refl _
  · rfl
  · rfl

def dgNonpositiveDoldKanSSetFunctor :
    CochainComplex (ModuleCat.{0} ℤ) ℤ ⥤ SSet.{0} :=
  ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{0} ℤ) ⋙
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse ⋙
      zModuleSimplicialForget

noncomputable instance zModuleSimplicialForget_preservesLimits :
    PreservesLimits zModuleSimplicialForget :=
  preservesLimits_of_evaluation zModuleSimplicialForget (fun k ↦ by
    change PreservesLimits
      ((evaluation SimplexCategoryᵒᵖ (ModuleCat.{0} ℤ)).obj k ⋙
        forget (ModuleCat.{0} ℤ))
    infer_instance)

theorem dgNonpositiveDoldKanSSet_map_isPullback
    {P X Y Z : CochainComplex (ModuleCat.{0} ℤ) ℤ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) :
    IsPullback
      (dgNonpositiveDoldKanSSetFunctor.map fst)
      (dgNonpositiveDoldKanSSetFunctor.map snd)
      (dgNonpositiveDoldKanSSetFunctor.map f)
      (dgNonpositiveDoldKanSSetFunctor.map g) := by
  change IsPullback
    (zModuleSimplicialForget.map
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
        (HomologicalComplex.truncLE'Map fst ComplexShape.embeddingDownNat)))
    (zModuleSimplicialForget.map
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
        (HomologicalComplex.truncLE'Map snd ComplexShape.embeddingDownNat)))
    (zModuleSimplicialForget.map
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
        (HomologicalComplex.truncLE'Map f ComplexShape.embeddingDownNat)))
    (zModuleSimplicialForget.map
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
        (HomologicalComplex.truncLE'Map g ComplexShape.embeddingDownNat)))
  exact ((truncLE'_map_isPullback h).map
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse).map zModuleSimplicialForget

def directDGMappingConePathFiberFst
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeObject f ⟶[SSet] directDGObject T) ⟶
      dgNonpositiveDoldKanSSetFunctor.obj
        (dgHomZModuleCochainComplex L T) :=
  (directDGMappingConePathFiberEnrichedHomIso T f).hom ≫
    dgNonpositiveDoldKanSSetFunctor.map
      (Limits.pullback.fst (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K))

def directDGMappingConePathFiberSnd
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeObject f ⟶[SSet] directDGObject T) ⟶
      dgNonpositiveDoldKanSSetFunctor.obj
        (dgHomPrecompositionPathObject T K) :=
  (directDGMappingConePathFiberEnrichedHomIso T f).hom ≫
    dgNonpositiveDoldKanSSetFunctor.map
      (Limits.pullback.snd (dgHomPrecompositionZeroEndpoints T f)
        (dgHomPrecompositionPathEndpoints T K))

/-- The enriched mapping simplicial set out of a mapping cone is the strict pullback of the
transported cochain path-object diagram, giving the explicit simplicial homotopy-pullback model. -/
theorem directDGMappingConeEnrichedHom_isPullback
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    IsPullback
      (directDGMappingConePathFiberFst T f)
      (directDGMappingConePathFiberSnd T f)
      (dgNonpositiveDoldKanSSetFunctor.map
        (dgHomPrecompositionZeroEndpoints T f))
      (dgNonpositiveDoldKanSSetFunctor.map
        (dgHomPrecompositionPathEndpoints T K)) := by
  apply (dgNonpositiveDoldKanSSet_map_isPullback
    (dgHomPrecompositionPathFiber_isPullback T f)).of_iso'
    (directDGMappingConePathFiberEnrichedHomIso T f)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · rfl
  · rfl
  · simp
  · simp

/-- The degree-zero maps and degree-minus-one coherence of a square in the raw direct DG
homotopy-coherent nerve.  This is the two-dimensional DG input, before any localization or
quasicategorical Kan-extension construction. -/
structure RawDirectDGCoherentNerveSquare where
  obj00 : ComplexCategory
  obj10 : ComplexCategory
  obj01 : ComplexCategory
  obj11 : ComplexCategory
  top : obj00 ⟶ obj10
  left : obj00 ⟶ obj01
  right : obj10 ⟶ obj11
  bottom : obj01 ⟶ obj11
  coherenceCochain : CochainComplex.HomComplex.Cochain obj00.obj obj11.obj (-1)
  coherence_delta :
    CochainComplex.HomComplex.Cochain.ofHom (top ≫ right).hom =
      CochainComplex.HomComplex.δ (-1) 0 coherenceCochain +
        CochainComplex.HomComplex.Cochain.ofHom (left ≫ bottom).hom

/-- The coherence cochain of a raw DG square is equivalently a chain homotopy between its two
boundary composites. -/
def RawDirectDGCoherentNerveSquare.coherenceHomotopy
    (sq : RawDirectDGCoherentNerveSquare) :
    Homotopy (sq.top.hom ≫ sq.right.hom) (sq.left.hom ≫ sq.bottom.hom) :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨sq.coherenceCochain, sq.coherence_delta⟩

/-- The canonical raw coherent mapping-cone square
`K ⟶ L`, `K ⟶ 0`, `L ⟶ Cone(f)`, `0 ⟶ Cone(f)`.
Its nontrivial coherence is exactly the degree-minus-one cone inclusion. -/
def directDGMappingConeRawCoherentSquare
    {K L : ComplexCategory} (f : K ⟶ L) : RawDirectDGCoherentNerveSquare where
  obj00 := K
  obj10 := L
  obj01 := 0
  obj11 := dgMappingConeObject f
  top := f
  left := 0
  right := dgMappingConeInr f
  bottom := 0
  coherenceCochain := dgMappingConeInl f
  coherence_delta := by
    rw [dgMappingConeInl_delta]
    simp

@[simp]
theorem directDGMappingConeRawCoherentSquare_top
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeRawCoherentSquare f).top = f :=
  rfl

@[simp]
theorem directDGMappingConeRawCoherentSquare_left
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeRawCoherentSquare f).left = 0 :=
  rfl

@[simp]
theorem directDGMappingConeRawCoherentSquare_right
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeRawCoherentSquare f).right = dgMappingConeInr f :=
  rfl

@[simp]
theorem directDGMappingConeRawCoherentSquare_bottom
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeRawCoherentSquare f).bottom = 0 :=
  rfl

@[simp]
theorem directDGMappingConeRawCoherentSquare_coherenceCochain
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeRawCoherentSquare f).coherenceCochain = dgMappingConeInl f :=
  rfl

/-- Mapping-out detection of homotopy cocartesianness for the canonical raw mapping-cone
square.  The path-object leg retains the chosen `dgMappingConeInl` coherence; the statement is
entirely in simplicial mapping objects and does not assert a quasicategorical pushout. -/
def DirectDGMappingConeSquareDetectedHomotopyCocartesian
    {K L : ComplexCategory} (f : K ⟶ L) : Prop :=
  ∀ T : ComplexCategory,
    IsPullback
      (directDGMappingConePathFiberFst T f)
      (directDGMappingConePathFiberSnd T f)
      (dgNonpositiveDoldKanSSetFunctor.map
        (dgHomPrecompositionZeroEndpoints T f))
      (dgNonpositiveDoldKanSSetFunctor.map
        (dgHomPrecompositionPathEndpoints T K))

/-- Every enriched mapping object detects the canonical raw mapping-cone square as the
path-object homotopy pullback supplied by the cone coherence. -/
theorem directDGMappingConeRawCoherentSquare_detectedHomotopyCocartesian
    {K L : ComplexCategory} (f : K ⟶ L) :
    DirectDGMappingConeSquareDetectedHomotopyCocartesian f :=
  fun T ↦ directDGMappingConeEnrichedHom_isPullback T f

/-- A raw coherent square is certified as a mapping-cone homotopy pushout when it is the
canonical cone square and its mapping-out path-object squares are pullbacks for every test
object.  This predicate deliberately stops before quasicategorical pushout recognition. -/
def RawDirectDGCoherentNerveSquare.IsMappingConeHomotopyCocartesianDetected
    (sq : RawDirectDGCoherentNerveSquare) : Prop :=
  ∃ (K L : ComplexCategory) (f : K ⟶ L),
    sq = directDGMappingConeRawCoherentSquare f ∧
      DirectDGMappingConeSquareDetectedHomotopyCocartesian f

/-- The canonical raw coherent mapping-cone square has a mapping-out homotopy-pullback
certificate against every enriched test object. -/
theorem directDGMappingConeRawCoherentSquare_isMappingConeHomotopyCocartesianDetected
    {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeRawCoherentSquare f).IsMappingConeHomotopyCocartesianDetected :=
  ⟨K, L, f, rfl, directDGMappingConeRawCoherentSquare_detectedHomotopyCocartesian f⟩

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
