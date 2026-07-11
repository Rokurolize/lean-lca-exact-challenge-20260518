import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Mapping-cone objects in the bounded dg carrier

This file records the first object-level construction needed for a genuine stability proof of
the localized dg nerve.  It stays in the bounded dg carrier: the cone is not replaced by an
object of the ordinary derived category.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

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

/-- The cone triangle carries its genuine chain homotopy from the composite to zero. -/
def dgMappingConeTriangleHomotopy {K L : ComplexCategory} (f : K ⟶ L) :
    Homotopy
      ((boundedCochainComplex MetrizableLCA.{0}).ι.map
        (f ≫ dgMappingConeInr f)) 0 :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨dgMappingConeInl f, by
      rw [dgMappingConeInl_delta]
      simp⟩

/-- A degree `-1` cochain induces the sign-corrected degree `-1` operation on contravariant
dg Hom complexes. -/
def dgHomPrecompositionHomotopyCochain (T : ComplexCategory)
    {X Y : ComplexCategory}
    (z : CochainComplex.HomComplex.Cochain X.obj Y.obj (-1)) :
    CochainComplex.HomComplex.Cochain
      (dgHomZModuleCochainComplex Y T) (dgHomZModuleCochainComplex X T) (-1) where
  v p q hpq := ModuleCat.ofHom
    { toFun := fun γ ↦ p.negOnePow • z.comp γ (by omega)
      map_add' := by
        intro γ γ'
        rw [CochainComplex.HomComplex.Cochain.comp_add, smul_add]
      map_smul' := by
        intro r γ
        rw [CochainComplex.HomComplex.Cochain.comp_smul, smul_comm,
          smul_assoc] }

theorem dgHomPrecompositionHomotopyCochain_delta
    (T : ComplexCategory) {X Y : ComplexCategory}
    (g₀ g₁ : X ⟶ Y)
    (z : CochainComplex.HomComplex.Cochain X.obj Y.obj (-1))
    (hz : CochainComplex.HomComplex.δ (-1) 0 z =
      CochainComplex.HomComplex.Cochain.ofHom g₀.hom -
        CochainComplex.HomComplex.Cochain.ofHom g₁.hom) :
    CochainComplex.HomComplex.δ (-1) 0
        (dgHomPrecompositionHomotopyCochain T z) =
      CochainComplex.HomComplex.Cochain.ofHom (dgHomZModulePrecomposition T g₀) -
        CochainComplex.HomComplex.Cochain.ofHom (dgHomZModulePrecomposition T g₁) := by
  ext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro γ
  change _ = _
  simp only [CochainComplex.HomComplex.δ_zero_cochain_v,
    dgHomPrecompositionHomotopyCochain,
    CochainComplex.HomComplex.Cochain.ofHom_v,
    CochainComplex.HomComplex.Cochain.sub_v,
    dgHomZModuleCochainComplex, dgHomZModulePrecomposition,
    ConcreteCategory.comp_apply]
  have hz' := CochainComplex.HomComplex.Cochain.congr_v hz p p (add_zero p)
  simp only [CochainComplex.HomComplex.Cochain.sub_v,
    CochainComplex.HomComplex.Cochain.ofHom_v] at hz'
  rw [CochainComplex.HomComplex.δ_comp z γ (by omega) 0 (p + 1) p
    (by omega) (neg_add_cancel 1) rfl]
  simp only [hz', Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul,
    one_smul, smul_add, smul_smul]
  abel

/-- Chain homotopies act contravariantly on the dg Hom cochain complexes. -/
def dgHomZModulePrecompositionHomotopy (T : ComplexCategory)
    {X Y : ComplexCategory} {g₀ g₁ : X ⟶ Y}
    (h : Homotopy g₀.hom g₁.hom) :
    Homotopy (dgHomZModulePrecomposition T g₀)
      (dgHomZModulePrecomposition T g₁) :=
  (CochainComplex.HomComplex.Cochain.equivHomotopy _ _).symm
    ⟨dgHomPrecompositionHomotopyCochain T
        (CochainComplex.HomComplex.Cochain.ofHomotopy h), by
      apply dgHomPrecompositionHomotopyCochain_delta
      exact CochainComplex.HomComplex.Cochain.δ_ofHomotopy h⟩

/-- The cone triangle nullhomotopy induces the homotopy required by the maps-out path fiber. -/
def dgMappingConePrecompositionNullhomotopy (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    Homotopy
      (dgHomZModulePrecomposition T (f ≫ dgMappingConeInr f)) 0 := by
  simpa only [dgHomZModulePrecomposition, map_zero] using
    dgHomZModulePrecompositionHomotopy T (dgMappingConeTriangleHomotopy f)

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
  rw [CochainComplex.HomComplex.Cochain.ofHom_comp,
    CochainComplex.HomComplex.Cochain.comp_assoc]

/-- The nullhomotopy with its source written as the composite of the two precomposition maps. -/
def dgMappingConePrecompositionCompositeNullhomotopy (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    Homotopy
      (dgHomZModulePrecomposition T (dgMappingConeInr f) ≫
        dgHomZModulePrecomposition T f) 0 :=
  Homotopy.ofEq (dgHomZModulePrecomposition_comp T f (dgMappingConeInr f)) |>.trans
    (dgMappingConePrecompositionNullhomotopy T f)

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

/-- Postcomposition by a bounded chain map as a morphism of the untruncated dg Hom cochain
complexes. -/
def dgHomZModulePostcomposition (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex T K ⟶ dgHomZModuleCochainComplex T L where
  f n := ModuleCat.ofHom
    { toFun := fun γ ↦ γ.comp
        (CochainComplex.HomComplex.Cochain.ofHom f.hom) (add_zero n)
      map_add' := fun γ γ' ↦
        CochainComplex.HomComplex.Cochain.add_comp γ γ' _ (add_zero n)
      map_smul' := fun r γ ↦
        CochainComplex.HomComplex.Cochain.smul_comp r γ _ (add_zero n) }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro γ
    simp [dgHomZModuleCochainComplex,
      CochainComplex.HomComplex.δ_comp_ofHom]

/-- The coordinate complex for maps into `Cone(f)` is itself the ordinary mapping cone of
postcomposition by `f`. -/
abbrev dgMappingConeCoordinateCochainComplex (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) : CochainComplex (ModuleCat.{0} ℤ) ℤ :=
  CochainComplex.mappingCone (dgHomZModulePostcomposition T f)

/-- Degreewise module isomorphism from the actual Hom into `Cone(f)` to the packaged
coordinate cone complex. -/
def dgMappingConeCochainComponentIso (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    (dgHomZModuleCochainComplex T (dgMappingConeObject f)).X n ≅
      (dgMappingConeCoordinateCochainComplex T f).X n := by
  change ModuleCat.of ℤ
      (CochainComplex.HomComplex.Cochain T.obj
        (CochainComplex.mappingCone
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) n) ≅ _
  exact Iso.trans (dgMappingConeCochainLinearEquiv T f n).toModuleIso
    (Iso.trans
      (ModuleCat.biprodIsoProd
        ((dgHomZModuleCochainComplex T K).X (n + 1))
        ((dgHomZModuleCochainComplex T L).X n)).symm
      (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (dgHomZModulePostcomposition T f) n (n + 1) rfl).symm)

@[reassoc]
theorem dgMappingConeCochainComponentIso_hom_fst
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    (dgMappingConeCochainComponentIso T f n).hom ≫
        (CochainComplex.mappingCone.fst (dgHomZModulePostcomposition T f)).1.v
          n (n + 1) rfl =
      (dgMappingConeCochainLinearEquiv T f n).toModuleIso.hom ≫
        ModuleCat.ofHom (LinearMap.fst ℤ
          (CochainComplex.HomComplex.Cochain T.obj K.obj (n + 1))
          (CochainComplex.HomComplex.Cochain T.obj L.obj n)) := by
  simp [dgMappingConeCochainComponentIso, CochainComplex.mappingCone.fst,
    HomologicalComplex.homotopyCofiber.fstX, Category.assoc]
  rfl

/-- The explicit two-coordinate cochain complex for maps into a cone.  Its differential is
transported through the verified coordinate linear equivalence; the matrix formula is the
preceding theorem `dgMappingConeCochainAddEquiv_symm_delta`. -/
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
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (dgMappingConeCochainLinearEquiv T f k)
      ((dgHomZModuleCochainComplex T (dgMappingConeObject f)).d m k
        ((dgHomZModuleCochainComplex T (dgMappingConeObject f)).d n m
          ((dgMappingConeCochainLinearEquiv T f n).symm x))) = 0
    have hx := ConcreteCategory.congr_hom
      ((dgHomZModuleCochainComplex T (dgMappingConeObject f)).d_comp_d n m k)
      ((dgMappingConeCochainLinearEquiv T f n).symm x)
    simp only [ConcreteCategory.comp_apply, Zero.zero_apply] at hx
    rw [hx]
    exact map_zero _

/-- The actual untruncated Hom cochain complex into `Cone(f)` is isomorphic to the explicit
two-coordinate complex. -/
def dgMappingConeExplicitCoordinateCochainIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex T (dgMappingConeObject f) ≅
      dgMappingConeExplicitCoordinateCochainComplex T f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (dgMappingConeCochainLinearEquiv T f n).toModuleIso) (by
      intro n m _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (dgMappingConeCochainLinearEquiv T f m)
          ((dgMappingConeCochainLinearEquiv T f n).symm
            (dgMappingConeCochainLinearEquiv T f n x) |> fun y ↦
              (dgHomZModuleCochainComplex T (dgMappingConeObject f)).d n m y) =
        dgMappingConeCochainLinearEquiv T f m
          ((dgHomZModuleCochainComplex T (dgMappingConeObject f)).d n m x)
      rw [Equiv.symm_apply_apply])

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

/-- After forgetting module structure degreewise, maps into the dg cone are still isomorphic
to the Dold--Kan realization of the explicit coordinate complex. -/
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

/-- Enriched cone representability: the actual enriched mapping simplicial set into the cone
is the Dold--Kan realization of the verified two-coordinate fiber complex. -/
def directDGMappingConeEnrichedHomIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGObject T ⟶[SSet] directDGMappingConeObject f) ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE'
            (dgMappingConeExplicitCoordinateCochainComplex T f)
            ComplexShape.embeddingDownNat)) :=
  eqToIso (directDG_enrichedHom_eq T (dgMappingConeObject f)) ≪≋
    dgMappingConeExplicitCoordinateSSetIso T f

/-- The explicit enriched universal property supplied by the cone construction.  It records a
mapping-object isomorphism for every bounded dg test object, rather than only a bijection in the
ordinary homotopy category. -/
structure DirectDGMappingConeEnrichedUniversalProperty
    {K L : ComplexCategory} (f : K ⟶ L) : Type 1 where
  mappingIso : ∀ T : ComplexCategory,
    (directDGObject T ⟶[SSet] directDGMappingConeObject f) ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE'
            (dgMappingConeExplicitCoordinateCochainComplex T f)
            ComplexShape.embeddingDownNat))

/-- Every bounded dg mapping cone satisfies the explicit enriched universal property. -/
def directDGMappingConeEnrichedUniversalProperty
    {K L : ComplexCategory} (f : K ⟶ L) :
    DirectDGMappingConeEnrichedUniversalProperty f where
  mappingIso T := directDGMappingConeEnrichedHomIso T f

/-- Degreewise additive decomposition of maps out of a cone.  This is the dual coordinate
carrier needed for the cartesian half of the stable cone-square calculation. -/
def dgMappingConeCochainFromAddEquiv
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cochain
        (CochainComplex.mappingCone
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) T.obj n ≃+
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
    · exact CochainComplex.HomComplex.Cochain.comp_add _ _ _ (by omega)
    · exact CochainComplex.HomComplex.Cochain.comp_add _ _ _ (zero_add n)

/-- The maps-out coordinate equivalence is integer-linear. -/
def dgMappingConeCochainFromLinearEquiv
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cochain
        (CochainComplex.mappingCone
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)) T.obj n ≃ₗ[ℤ]
      (CochainComplex.HomComplex.Cochain K.obj T.obj (n - 1) ×
        CochainComplex.HomComplex.Cochain L.obj T.obj n) :=
  { dgMappingConeCochainFromAddEquiv T f n with
    map_smul' := by
      intro r γ
      apply Prod.ext
      · exact CochainComplex.HomComplex.Cochain.comp_smul _ r γ (by omega)
      · exact CochainComplex.HomComplex.Cochain.comp_smul _ r γ (zero_add n) }

/-- Differential compatibility of the maps-out coordinates. -/
theorem dgMappingConeCochainFromAddEquiv_symm_delta
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) (n : ℤ)
    (a : CochainComplex.HomComplex.Cochain K.obj T.obj (n - 1))
    (b : CochainComplex.HomComplex.Cochain L.obj T.obj n) :
    CochainComplex.HomComplex.δ n (n + 1)
        ((dgMappingConeCochainFromAddEquiv T f n).symm (a, b)) =
      (CochainComplex.mappingCone.fst
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).1.comp
        (CochainComplex.HomComplex.δ (n - 1) n a +
          (n + 1).negOnePow •
            (CochainComplex.HomComplex.Cochain.ofHom f.hom).comp b (zero_add n)) (by omega) +
      (CochainComplex.mappingCone.snd
          ((boundedCochainComplex MetrizableLCA.{0}).ι.map f)).comp
        (CochainComplex.HomComplex.δ n (n + 1) b) (zero_add (n + 1)) := by
  exact CochainComplex.mappingCone.δ_descCochain
    ((boundedCochainComplex MetrizableLCA.{0}).ι.map f) a b (by omega) (n + 1) rfl

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

theorem dgMappingConeHom_pathFiber_condition (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModulePrecomposition T (dgMappingConeInr f) ≫
        dgHomPrecompositionZeroEndpoints T f =
      dgMappingConeHomToPathObject T f ≫
        dgHomPrecompositionPathEndpoints T K := by
  apply Limits.prod.hom_ext
  · simp [dgHomPrecompositionZeroEndpoints, dgHomPrecompositionPathEndpoints]
  · simp [dgHomPrecompositionZeroEndpoints, dgHomPrecompositionPathEndpoints]

/-- The canonical map from the actual maps-out cone Hom complex to the strict path-fiber
pullback. -/
def dgMappingConeHomToPathFiber (T : ComplexCategory)
    {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex (dgMappingConeObject f) T ⟶
      dgHomPrecompositionPathFiber T f :=
  Limits.pullback.lift
    (dgHomZModulePrecomposition T (dgMappingConeInr f))
    (dgMappingConeHomToPathObject T f)
    (dgMappingConeHom_pathFiber_condition T f)

/-- Explicit two-coordinate complex for maps out of a cone. -/
def dgMappingConeExplicitFromCoordinateCochainComplex
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    CochainComplex (ModuleCat.{0} ℤ) ℤ where
  X n := ModuleCat.of ℤ
    (CochainComplex.HomComplex.Cochain K.obj T.obj (n - 1) ×
      CochainComplex.HomComplex.Cochain L.obj T.obj n)
  d n m := (dgMappingConeCochainFromLinearEquiv T f n).toModuleIso.inv ≫
    (dgHomZModuleCochainComplex (dgMappingConeObject f) T).d n m ≫
      (dgMappingConeCochainFromLinearEquiv T f m).toModuleIso.hom
  shape n m h := by
    rw [(dgHomZModuleCochainComplex (dgMappingConeObject f) T).shape n m h]
    simp
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (dgMappingConeCochainFromLinearEquiv T f k)
      ((dgHomZModuleCochainComplex (dgMappingConeObject f) T).d m k
        ((dgHomZModuleCochainComplex (dgMappingConeObject f) T).d n m
          ((dgMappingConeCochainFromLinearEquiv T f n).symm x))) = 0
    have hx := ConcreteCategory.congr_hom
      ((dgHomZModuleCochainComplex (dgMappingConeObject f) T).d_comp_d n m k)
      ((dgMappingConeCochainFromLinearEquiv T f n).symm x)
    simp only [ConcreteCategory.comp_apply, Zero.zero_apply] at hx
    rw [hx]
    exact map_zero _

/-- Actual maps out of the dg cone form the explicit dual coordinate cochain complex. -/
def dgMappingConeExplicitFromCoordinateCochainIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgHomZModuleCochainComplex (dgMappingConeObject f) T ≅
      dgMappingConeExplicitFromCoordinateCochainComplex T f :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (dgMappingConeCochainFromLinearEquiv T f n).toModuleIso) (by
      intro n m _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (dgMappingConeCochainFromLinearEquiv T f m)
          ((dgMappingConeCochainFromLinearEquiv T f n).symm
            (dgMappingConeCochainFromLinearEquiv T f n x) |> fun y ↦
              (dgHomZModuleCochainComplex (dgMappingConeObject f) T).d n m y) =
        dgMappingConeCochainFromLinearEquiv T f m
          ((dgHomZModuleCochainComplex (dgMappingConeObject f) T).d n m x)
      rw [Equiv.symm_apply_apply])

/-- Transport the dual cone coordinate isomorphism through truncation. -/
def dgMappingConeExplicitFromCoordinateChainIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleChainComplex (dgMappingConeObject f) T ≅
      HomologicalComplex.truncLE'
        (dgMappingConeExplicitFromCoordinateCochainComplex T f)
        ComplexShape.embeddingDownNat :=
  (ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{0} ℤ)).mapIso
    (dgMappingConeExplicitFromCoordinateCochainIso T f)

/-- Transport the dual cone coordinate isomorphism through Dold--Kan and forgetting. -/
def dgMappingConeExplicitFromCoordinateSSetIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    dgMappingDirectZModuleSSet (dgMappingConeObject f) T ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE'
            (dgMappingConeExplicitFromCoordinateCochainComplex T f)
            ComplexShape.embeddingDownNat)) :=
  zModuleSimplicialForget.mapIso
    (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.mapIso
      (dgMappingConeExplicitFromCoordinateChainIso T f))

/-- Enriched maps out of a cone are represented by the dual coordinate fiber complex. -/
def directDGMappingConeEnrichedHomFromIso
    (T : ComplexCategory) {K L : ComplexCategory} (f : K ⟶ L) :
    (directDGMappingConeObject f ⟶[SSet] directDGObject T) ≅
      zModuleSimplicialForget.obj
        (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
          (HomologicalComplex.truncLE'
            (dgMappingConeExplicitFromCoordinateCochainComplex T f)
            ComplexShape.embeddingDownNat)) :=
  eqToIso (directDG_enrichedHom_eq (dgMappingConeObject f) T) ≪≋
    dgMappingConeExplicitFromCoordinateSSetIso T f

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
