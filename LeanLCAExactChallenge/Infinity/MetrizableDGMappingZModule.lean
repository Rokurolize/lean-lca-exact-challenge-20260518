import LeanLCAExactChallenge.Infinity.DoldKanMonoidal
import LeanLCAExactChallenge.Infinity.MetrizableDGMapping
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Homology.Additive

/-!
# Integer-module Dold--Kan mapping carriers

The existing additive-group mapping chain complex is transported through the equivalence
between additive commutative groups and integer modules.  The resulting Dold--Kan carrier
lives in the algebraic tensor category needed by Alexander--Whitney.
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

/-- The equivalence between integer modules and additive commutative groups. -/
abbrev zModuleAddCommGrpEquivalence :
    ModuleCat.{0} ℤ ≌ AddCommGrpCat.{0} :=
  (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}).asEquivalence

/-- The inverse functor, equipping an additive commutative group with its integer-module
structure. -/
abbrev addCommGrpToZModule : AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℤ :=
  zModuleAddCommGrpEquivalence.inverse

/-- The truncated Hom chain complex transported to integer modules. -/
def dgMappingZModuleChainComplex (K L : ComplexCategory) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  (addCommGrpToZModule.mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (dgMappingChainComplex K L)

/-- The Hom cochain complex constructed directly in integer modules. -/
def dgHomZModuleCochainComplex (K L : ComplexCategory) :
    CochainComplex (ModuleCat.{0} ℤ) ℤ where
  X n := ModuleCat.of ℤ
    (CochainComplex.HomComplex.Cochain (underlyingComplex K) (underlyingComplex L) n)
  d n m := ModuleCat.ofHom
    (CochainComplex.HomComplex.δ_hom ℤ (underlyingComplex K) (underlyingComplex L) n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact CochainComplex.HomComplex.δ_shape n m h z
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact CochainComplex.HomComplex.δ_δ n m k z

/-- The direct integer-module Hom complex after nonpositive truncation. -/
def dgMappingDirectZModuleChainComplex (K L : ComplexCategory) :
    ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  HomologicalComplex.truncLE' (dgHomZModuleCochainComplex K L)
    ComplexShape.embeddingDownNat

/-- The transported integer-module structure is canonically the usual one. -/
def transportedToCanonicalZModuleIso (A : AddCommGrpCat.{0}) :
    addCommGrpToZModule.obj A ≅ ModuleCat.of ℤ A :=
  zModuleAddCommGrpEquivalence.functor.preimageIso
    (zModuleAddCommGrpEquivalence.counitIso.app A)

/-- Equip an additive commutative group with its canonical integer-module structure. -/
def canonicalZModuleFunctor : AddCommGrpCat.{0} ⥤ ModuleCat.{0} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id A := by
    apply ModuleCat.hom_ext
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    rfl

instance : canonicalZModuleFunctor.PreservesZeroMorphisms where
  map_zero := by
    intro X Y
    apply ModuleCat.hom_ext
    rfl

/-- Transport through the equivalence agrees naturally with the canonical structure. -/
def transportedToCanonicalZModuleNatIso :
    addCommGrpToZModule ≅ canonicalZModuleFunctor :=
  NatIso.ofComponents transportedToCanonicalZModuleIso fun f => by
    apply zModuleAddCommGrpEquivalence.functor.map_injective
    dsimp only [transportedToCanonicalZModuleIso,
      Functor.FullyFaithful.preimageIso_hom, canonicalZModuleFunctor]
    rw [Functor.map_comp, Functor.map_comp,
      Functor.preimageIso_hom, Functor.preimageIso_hom, Functor.map_preimage,
      Functor.map_preimage]
    exact zModuleAddCommGrpEquivalence.counitIso.hom.naturality f

/-- Mapping the additive Hom complex canonically agrees with the direct module Hom complex. -/
def canonicalMappedHomIsoDirect (K L : ComplexCategory) :
    (canonicalZModuleFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.HomComplex K.obj L.obj) ≅
      dgHomZModuleCochainComplex K L :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    apply ModuleCat.hom_ext
    rfl)

/-- The transported untruncated Hom complex agrees with the direct module construction. -/
def transportedHomIsoDirect (K L : ComplexCategory) :
    (addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.HomComplex K.obj L.obj) ≅
      dgHomZModuleCochainComplex K L :=
  (NatIso.mapHomologicalComplex transportedToCanonicalZModuleNatIso
      (ComplexShape.up ℤ)).app _ ≪≫
    canonicalMappedHomIsoDirect K L

private lemma boundaryLE_embeddingDownNat_iff (n : ℕ) :
    ComplexShape.embeddingDownNat.BoundaryLE n ↔ n = 0 := by
  simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
    ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 n

private def mapTruncHomComponentIso (K L : ComplexCategory) (n : ℕ) :
    ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (HomologicalComplex.truncLE'
            (CochainComplex.HomComplex K.obj L.obj)
            ComplexShape.embeddingDownNat)).X n ≅
      (HomologicalComplex.truncLE'
          ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (CochainComplex.HomComplex K.obj L.obj))
          ComplexShape.embeddingDownNat).X n := by
  let H := CochainComplex.HomComplex K.obj L.obj
  let FH := (addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj H
  obtain rfl | n := n
  · have hn : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
      (boundaryLE_embeddingDownNat_iff 0).2 rfl
    exact
      addCommGrpToZModule.mapIso
          (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hn) ≪≫
      ((H.sc 0).mapCyclesIso addCommGrpToZModule).symm ≪≫
      (FH.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hn).symm
  · have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE (n + 1) := fun h =>
      Nat.succ_ne_zero n ((boundaryLE_embeddingDownNat_iff (n + 1)).1 h)
    exact
      addCommGrpToZModule.mapIso
          (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn) ≪≫
      (FH.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).symm

@[reassoc]
private lemma mapHomologicalComplex_toCycles_comp_mapCyclesIso_inv
    (H : CochainComplex AddCommGrpCat ℤ) (i j : ℤ) :
    addCommGrpToZModule.map (H.toCycles i j) ≫
        ((H.sc j).mapCyclesIso addCommGrpToZModule).inv =
      ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj H).toCycles i j := by
  apply (cancel_mono
    (((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj H).iCycles j)).1
  change (addCommGrpToZModule.map (H.toCycles i j) ≫
      ((H.sc j).mapCyclesIso addCommGrpToZModule).inv) ≫
        ((H.sc j).map addCommGrpToZModule).iCycles = _
  have hcycles : ((H.sc j).mapCyclesIso addCommGrpToZModule).inv ≫
        ((H.sc j).map addCommGrpToZModule).iCycles =
      addCommGrpToZModule.map (H.sc j).iCycles := by
    rw [← (H.sc j).mapCyclesIso_hom_iCycles addCommGrpToZModule]
    exact Iso.inv_hom_id_assoc _ _
  rw [Category.assoc]
  dsimp only [HomologicalComplex.cycles, HomologicalComplex.iCycles] at hcycles ⊢
  slice_lhs 2 3 => rw [hcycles]
  change addCommGrpToZModule.map (H.toCycles i j) ≫
      addCommGrpToZModule.map (H.iCycles j) =
    ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj H).toCycles i j ≫
      ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj H).iCycles j
  rw [← Functor.map_comp, HomologicalComplex.toCycles_i]
  rw [HomologicalComplex.toCycles_i, Functor.mapHomologicalComplex_obj_d]

@[reassoc]
private lemma mapHomologicalComplex_toCycles_zero_comp_mapCyclesIso_inv
    (H : CochainComplex AddCommGrpCat ℤ) (i : ℤ) :
    addCommGrpToZModule.map
          (H.toCycles i (ComplexShape.embeddingDownNat.f 0)) ≫
        ((H.sc 0).mapCyclesIso addCommGrpToZModule).inv =
      ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj H).toCycles
        i (ComplexShape.embeddingDownNat.f 0) := by
  simpa using mapHomologicalComplex_toCycles_comp_mapCyclesIso_inv H i 0

@[reassoc]
private lemma truncLE'XIso_inv_hom_of_proofs
    (H : CochainComplex (ModuleCat ℤ) ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ¬ ComplexShape.embeddingDownNat.BoundaryLE n) :
    (H.truncLE'XIso ComplexShape.embeddingDownNat hi₁ hn₁).inv ≫
        (H.truncLE'XIso ComplexShape.embeddingDownNat hi₂ hn₂).hom = 𝟙 _ := by
  have hhi : hi₁ = hi₂ := Subsingleton.elim _ _
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hi₂
  subst hn₂
  exact Iso.inv_hom_id _

@[reassoc]
private lemma truncLE'XIsoCycles_inv_hom_of_proofs
    (H : CochainComplex (ModuleCat ℤ) ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ComplexShape.embeddingDownNat.BoundaryLE n) :
    (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₁ hn₁).inv ≫
        (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₂ hn₂).hom = 𝟙 _ := by
  have hhi : hi₁ = hi₂ := Subsingleton.elim _ _
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hi₂
  subst hn₂
  exact Iso.inv_hom_id _

@[reassoc]
private lemma map_comp_truncLE'XIso_inv_hom_of_proofs
    (H : CochainComplex AddCommGrpCat ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ¬ ComplexShape.embeddingDownNat.BoundaryLE n)
    {X : AddCommGrpCat} (f : X ⟶ H.X i) :
    addCommGrpToZModule.map
          (f ≫ (H.truncLE'XIso ComplexShape.embeddingDownNat hi₁ hn₁).inv) ≫
        addCommGrpToZModule.map
          (H.truncLE'XIso ComplexShape.embeddingDownNat hi₂ hn₂).hom =
      addCommGrpToZModule.map f := by
  have hhi : hi₁ = hi₂ := Subsingleton.elim _ _
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hi₂
  subst hn₂
  rw [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id, Category.comp_id]

@[reassoc]
private lemma map_comp_truncLE'XIsoCycles_inv_hom_of_proofs
    (H : CochainComplex AddCommGrpCat ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ComplexShape.embeddingDownNat.BoundaryLE n)
    {X : AddCommGrpCat} (f : X ⟶ H.cycles i) :
    addCommGrpToZModule.map
          (f ≫ (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₁ hn₁).inv) ≫
        addCommGrpToZModule.map
          (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₂ hn₂).hom =
      addCommGrpToZModule.map f := by
  have hhi : hi₁ = hi₂ := Subsingleton.elim _ _
  have hhn : hn₁ = hn₂ := Subsingleton.elim _ _
  subst hi₂
  subst hn₂
  rw [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id, Category.comp_id]

@[reassoc]
private lemma map_comp_comp_truncLE'XIso_inv_hom_of_proofs
    (H : CochainComplex AddCommGrpCat ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ¬ ComplexShape.embeddingDownNat.BoundaryLE n)
    {X Y : AddCommGrpCat} (f : X ⟶ Y) (g : Y ⟶ H.X i) :
    addCommGrpToZModule.map
          (f ≫ g ≫ (H.truncLE'XIso ComplexShape.embeddingDownNat hi₁ hn₁).inv) ≫
        addCommGrpToZModule.map
          (H.truncLE'XIso ComplexShape.embeddingDownNat hi₂ hn₂).hom =
      addCommGrpToZModule.map (f ≫ g) := by
  rw [Functor.map_comp, Category.assoc,
    map_comp_truncLE'XIso_inv_hom_of_proofs, Functor.map_comp]

@[reassoc]
private lemma map_comp_comp_truncLE'XIsoCycles_inv_hom_of_proofs
    (H : CochainComplex AddCommGrpCat ℤ) (n : ℕ) (i : ℤ)
    (hi₁ hi₂ : ComplexShape.embeddingDownNat.f n = i)
    (hn₁ hn₂ : ComplexShape.embeddingDownNat.BoundaryLE n)
    {X Y : AddCommGrpCat} (f : X ⟶ Y) (g : Y ⟶ H.cycles i) :
    addCommGrpToZModule.map
          (f ≫ g ≫
            (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₁ hn₁).inv) ≫
        addCommGrpToZModule.map
          (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat hi₂ hn₂).hom =
      addCommGrpToZModule.map (f ≫ g) := by
  rw [Functor.map_comp, Category.assoc,
    map_comp_truncLE'XIsoCycles_inv_hom_of_proofs, Functor.map_comp]

/-- Mapping the truncated additive Hom complex agrees with truncating after mapping. -/
def mapTruncHomIso (K L : ComplexCategory) :
    (addCommGrpToZModule.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (HomologicalComplex.truncLE'
          (CochainComplex.HomComplex K.obj L.obj)
          ComplexShape.embeddingDownNat) ≅
      HomologicalComplex.truncLE'
        ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplex K.obj L.obj))
        ComplexShape.embeddingDownNat :=
  HomologicalComplex.Hom.isoOfComponents (mapTruncHomComponentIso K L) (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    obtain rfl | j := j
    · have hj : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
        (boundaryLE_embeddingDownNat_iff 0).2 rfl
      dsimp [mapTruncHomComponentIso]
      erw [HomologicalComplex.truncLE'_d_eq_toCycles
        ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplex K.obj L.obj))
        ComplexShape.embeddingDownNat
        (show (ComplexShape.down ℕ).Rel 1 0 by simp) rfl rfl hj]
      erw [HomologicalComplex.truncLE'_d_eq_toCycles
        (CochainComplex.HomComplex K.obj L.obj)
        ComplexShape.embeddingDownNat
        (show (ComplexShape.down ℕ).Rel 1 0 by simp) rfl rfl hj]
      dsimp only [HomologicalComplex.cycles, HomologicalComplex.iCycles]
      slice_lhs 2 3 => erw [truncLE'XIso_inv_hom_of_proofs
        ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplex K.obj L.obj)) 1
        (ComplexShape.embeddingDownNat.f 1)]
      erw [map_comp_comp_truncLE'XIsoCycles_inv_hom_of_proofs_assoc
        (CochainComplex.HomComplex K.obj L.obj) 0
        (ComplexShape.embeddingDownNat.f 0) rfl rfl hj hj]
      slice_rhs 1 1 => rw [Functor.map_comp]
      simp only [Category.assoc]
      dsimp only [HomologicalComplex.cycles]
      erw [mapHomologicalComplex_toCycles_zero_comp_mapCyclesIso_inv_assoc
        (CochainComplex.HomComplex K.obj L.obj)
        (ComplexShape.embeddingDownNat.f 1)]
      rfl
    · have hj : ¬ ComplexShape.embeddingDownNat.BoundaryLE (j + 1) := fun h =>
        Nat.succ_ne_zero j ((boundaryLE_embeddingDownNat_iff (j + 1)).1 h)
      dsimp [mapTruncHomComponentIso]
      erw [HomologicalComplex.truncLE'_d_eq
        ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplex K.obj L.obj))
        ComplexShape.embeddingDownNat
        (show (ComplexShape.down ℕ).Rel (j + 1 + 1) (j + 1) by simp) rfl rfl hj]
      erw [HomologicalComplex.truncLE'_d_eq
        (CochainComplex.HomComplex K.obj L.obj)
        ComplexShape.embeddingDownNat
        (show (ComplexShape.down ℕ).Rel (j + 1 + 1) (j + 1) by simp) rfl rfl hj]
      slice_lhs 2 3 => erw [truncLE'XIso_inv_hom_of_proofs
        ((addCommGrpToZModule.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.HomComplex K.obj L.obj)) (j + 1 + 1)
        (ComplexShape.embeddingDownNat.f (j + 1 + 1))]
      rw [Functor.mapHomologicalComplex_obj_d]
      erw [map_comp_comp_truncLE'XIso_inv_hom_of_proofs_assoc
        (CochainComplex.HomComplex K.obj L.obj) (j + 1)
        (ComplexShape.embeddingDownNat.f (j + 1)) rfl rfl hj hj]
      slice_rhs 1 1 => rw [Functor.map_comp]
      rfl)

/-- The transported and direct integer-module mapping chain complexes are isomorphic. -/
def dgMappingZModuleChainComplexIsoDirect (K L : ComplexCategory) :
    dgMappingZModuleChainComplex K L ≅ dgMappingDirectZModuleChainComplex K L :=
  mapTruncHomIso K L ≪≫
    (ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat ℤ)).mapIso
      (transportedHomIsoDirect K L)

/-- Homogeneous cochain composition as a linear map into linear maps over `ℤ`. -/
def dgCochainCompLinear (K L M : ComplexCategory) {p q r : ℤ} (h : p + q = r) :
    ModuleCat.of ℤ
        (CochainComplex.HomComplex.Cochain (underlyingComplex K) (underlyingComplex L) p) ⟶
      ModuleCat.of ℤ
        (CochainComplex.HomComplex.Cochain (underlyingComplex L) (underlyingComplex M) q) ⟶[
          ModuleCat ℤ]
        ModuleCat.of ℤ
          (CochainComplex.HomComplex.Cochain
            (underlyingComplex K) (underlyingComplex M) r) :=
  ModuleCat.ofHom₂ (LinearMap.mk₂ ℤ (fun x y => x.comp y h)
    (fun x₁ x₂ y => CochainComplex.HomComplex.Cochain.add_comp x₁ x₂ y h)
    (fun n x y => CochainComplex.HomComplex.Cochain.smul_comp n x y h)
    (fun x y₁ y₂ => CochainComplex.HomComplex.Cochain.comp_add x y₁ y₂ h)
    (fun n x y => CochainComplex.HomComplex.Cochain.comp_smul x n y h))

/-- Homogeneous cochain composition descends from the algebraic tensor product over `ℤ`. -/
def dgCochainCompTensor (K L M : ComplexCategory) {p q r : ℤ} (h : p + q = r) :
    ModuleCat.of ℤ
          (CochainComplex.HomComplex.Cochain
            (underlyingComplex K) (underlyingComplex L) p) ⊗
        ModuleCat.of ℤ
          (CochainComplex.HomComplex.Cochain
            (underlyingComplex L) (underlyingComplex M) q) ⟶
      ModuleCat.of ℤ
        (CochainComplex.HomComplex.Cochain
          (underlyingComplex K) (underlyingComplex M) r) :=
  ModuleCat.ofHom (TensorProduct.lift (dgCochainCompLinear K L M h).hom₂)

@[simp]
theorem dgCochainCompTensor_tmul (K L M : ComplexCategory) {p q r : ℤ}
    (h : p + q = r)
    (x : CochainComplex.HomComplex.Cochain
      (underlyingComplex K) (underlyingComplex L) p)
    (y : CochainComplex.HomComplex.Cochain
      (underlyingComplex L) (underlyingComplex M) q) :
    dgCochainCompTensor K L M h (x ⊗ₜ[ℤ] y) = x.comp y h := by
  rfl

/-- The reversed homogeneous pairing used by the total-complex sign convention. -/
def dgCochainCompTensorReversed (K L M : ComplexCategory) {p q r : ℤ}
    (h : p + q = r) :
    ModuleCat.of ℤ
          (CochainComplex.HomComplex.Cochain
            (underlyingComplex L) (underlyingComplex M) p) ⊗
        ModuleCat.of ℤ
          (CochainComplex.HomComplex.Cochain
            (underlyingComplex K) (underlyingComplex L) q) ⟶
      ModuleCat.of ℤ
        (CochainComplex.HomComplex.Cochain
          (underlyingComplex K) (underlyingComplex M) r) :=
  (β_ _ _).hom ≫ dgCochainCompTensor K L M (by omega)

@[simp]
theorem dgCochainCompTensorReversed_tmul (K L M : ComplexCategory) {p q r : ℤ}
    (h : p + q = r)
    (y : CochainComplex.HomComplex.Cochain
      (underlyingComplex L) (underlyingComplex M) p)
    (x : CochainComplex.HomComplex.Cochain
      (underlyingComplex K) (underlyingComplex L) q) :
    dgCochainCompTensorReversed K L M h (y ⊗ₜ[ℤ] x) =
      x.comp y (by omega) := by
  rfl

/-- Composition is a chain map on the direct integer-module Hom cochain complexes.

The factors are reversed because mathlib's total-complex differential signs the second
factor by the degree of the first.  This order agrees exactly with `HomComplex.δ_comp`.
-/
def dgHomZModuleCompositionReversed (K L M : ComplexCategory) :
    HomologicalComplex.tensorObj
        (dgHomZModuleCochainComplex L M) (dgHomZModuleCochainComplex K L) ⟶
      dgHomZModuleCochainComplex K M where
  f n := HomologicalComplex.mapBifunctorDesc fun p q h =>
    dgCochainCompTensorReversed K L M h
  comm' n m hnm := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [HomologicalComplex.mapBifunctor.d_eq, ← Category.assoc, Preadditive.comp_add,
      Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
    change p + q = n at hpq
    change n + 1 = m at hnm
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show p + 1 = p + 1 by rfl) q m (by change p + 1 + q = m; omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
      (show q + 1 = q + 1 by rfl) m (by change p + (q + 1) = m; omega)]
    simp only [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [Units.smul_def, Units.smul_def]
    change _ = (1 : ℤ) • _ + (p.negOnePow : ℤ) • _
    rw [one_smul]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext y x
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
    dsimp [dgHomZModuleCochainComplex, dgCochainCompTensorReversed,
      dgCochainCompTensor, dgCochainCompLinear]
    simp only [ObjectProperty.ι_obj]
    have hqp : q + p = n := by omega
    have hqpm : q + (p + 1) = m := by omega
    have hqmp : (q + 1) + p = m := by omega
    change CochainComplex.HomComplex.δ n m (x.comp y hqp) = _
    change _ =
      x.comp (CochainComplex.HomComplex.δ p (p + 1) y) hqpm +
        p.negOnePow •
          (CochainComplex.HomComplex.δ q (q + 1) x).comp y hqmp
    exact CochainComplex.HomComplex.δ_comp x y hqp (q + 1) (p + 1) m
      hnm rfl rfl

private lemma truncLE'ToRestriction_f_zero
    (H : CochainComplex (ModuleCat ℤ) ℤ)
    (hb : ComplexShape.embeddingDownNat.BoundaryLE 0) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 =
      (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫
        H.iCycles 0 := by
  dsimp [HomologicalComplex.truncLE'ToRestriction]
  have h0 : ComplexShape.embeddingDownNat.op.f 0 = (0 : ℤ) := rfl
  have hb' : ComplexShape.embeddingDownNat.op.BoundaryGE 0 := by
    simpa [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE] using
      (ComplexShape.boundaryLE_embeddingUpIntLE_iff 0 0).2 rfl
  rw [(H.op).restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv
    ComplexShape.embeddingDownNat.op h0 hb']
  dsimp [HomologicalComplex.restrictionXIso]
  simp only [Category.comp_id]
  dsimp [HomologicalComplex.truncLE'XIsoCycles, HomologicalComplex.iCycles,
    HomologicalComplex.pOpcycles]
  rw [Category.assoc]
  congr 1
  dsimp only [HomologicalComplex.cycles]
  have hp : (H.opcyclesOpIso 0).hom.unop ≫ ((H.op).pOpcycles 0).unop =
      H.iCycles 0 := by
    dsimp [HomologicalComplex.opcyclesOpIso, HomologicalComplex.pOpcycles,
      HomologicalComplex.iCycles]
    exact congrArg Quiver.Hom.unop
      (H.sc 0).op_pOpcycles_opcyclesOpIso_hom
  have hcancel : (H.opcyclesOpIso 0).hom.unop ≫
      (H.opcyclesOpIso 0).inv.unop = 𝟙 _ :=
    (H.opcyclesOpIso 0).unop.hom_inv_id
  apply (cancel_epi ((H.opcyclesOpIso 0).hom.unop)).1
  calc
    (H.opcyclesOpIso 0).hom.unop ≫ ((H.op).pOpcycles 0).unop =
        H.iCycles 0 := hp
    _ = ((H.opcyclesOpIso 0).hom.unop ≫
          (H.opcyclesOpIso 0).inv.unop) ≫ H.iCycles 0 := by
      rw [hcancel, Category.id_comp]
    _ = (H.opcyclesOpIso 0).hom.unop ≫
        ((H.opcyclesOpIso 0).inv.unop ≫ H.iCycles 0) :=
      Category.assoc _ _ _

private lemma truncLE'ToRestriction_f_zero_d
    (H : CochainComplex (ModuleCat ℤ) ℤ) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f 0 ≫ H.d 0 1 = 0 := by
  have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
    (boundaryLE_embeddingDownNat_iff 0).2 rfl
  rw [truncLE'ToRestriction_f_zero H hb]
  calc
    ((H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫
          H.iCycles 0) ≫ H.d 0 1 =
        (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫
          (H.iCycles 0 ≫ H.d 0 1) := Category.assoc _ _ _
    _ = (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫ 0 := by
      exact congrArg
        (fun t => (H.truncLE'XIsoCycles ComplexShape.embeddingDownNat rfl hb).hom ≫ t)
        (H.iCycles_d 0 1)
    _ = 0 := rfl

private lemma truncLE'ToRestriction_f_succ
    (H : CochainComplex (ModuleCat ℤ) ℤ) (n : ℕ)
    (hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE (n + 1)) :
    (H.truncLE'ToRestriction ComplexShape.embeddingDownNat).f (n + 1) =
      (H.truncLE'XIso ComplexShape.embeddingDownNat rfl hn).hom := by
  dsimp [HomologicalComplex.truncLE'ToRestriction]
  have hn' : ¬ ComplexShape.embeddingDownNat.op.BoundaryGE (n + 1) := by
    simpa using hn
  rw [(H.op).restrictionToTruncGE'_f_eq_iso_hom_iso_inv
    ComplexShape.embeddingDownNat.op rfl hn']
  dsimp [HomologicalComplex.restrictionXIso,
    HomologicalComplex.truncLE'XIso]
  simp

/-- Compose two truncated cochains and retain the resulting untruncated cochain. -/
def dgTruncatedCompositionToCochain (K L M : ComplexCategory)
    {p q n : ℕ} (h : p + q = n) :
    (dgMappingDirectZModuleChainComplex L M).X p ⊗
        (dgMappingDirectZModuleChainComplex K L).X q ⟶
      (dgHomZModuleCochainComplex K M).X (ComplexShape.embeddingDownNat.f n) :=
  (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p ⊗ₘ
      ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q) ≫
    dgCochainCompTensorReversed K L M (by
      dsimp [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE]
      omega)

@[simp]
lemma dgTruncatedCompositionToCochain_tmul (K L M : ComplexCategory)
    {p q n : ℕ} (h : p + q = n)
    (y : (dgMappingDirectZModuleChainComplex L M).X p)
    (x : (dgMappingDirectZModuleChainComplex K L).X q) :
    dgTruncatedCompositionToCochain K L M h (y ⊗ₜ[ℤ] x) =
      (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q x).comp
        (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p y) (by
            dsimp [ComplexShape.embeddingDownNat, ComplexShape.embeddingUpIntLE]
            omega) := by
  rfl

/-- The composition of two boundary-degree truncated cochains is a zero cocycle. -/
lemma dgTruncatedCompositionToCochain_zero_d (K L M : ComplexCategory) :
    dgTruncatedCompositionToCochain K L M (show 0 + 0 = 0 by rfl) ≫
        (dgHomZModuleCochainComplex K M).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext y x
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  dsimp only [ModuleCat.Hom.hom, Zero.zero]
  change (dgHomZModuleCochainComplex K M).d 0 1
      (dgTruncatedCompositionToCochain K L M rfl (y ⊗ₜ[ℤ] x)) = 0
  rw [show dgTruncatedCompositionToCochain K L M rfl (y ⊗ₜ[ℤ] x) =
      (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 x).comp
        (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f 0 y) rfl by rfl]
  let x' : CochainComplex.HomComplex.Cochain K.obj L.obj 0 :=
    ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0 x
  let y' : CochainComplex.HomComplex.Cochain L.obj M.obj 0 :=
    ((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
      ComplexShape.embeddingDownNat).f 0 y
  change CochainComplex.HomComplex.δ (0 + 0) 1 (x'.comp y' rfl) = 0
  rw [CochainComplex.HomComplex.δ_comp x' y' rfl 1 1 1 rfl rfl rfl]
  have hx : CochainComplex.HomComplex.δ 0 1 x' = 0 := by
    change (dgHomZModuleCochainComplex K L).d 0 1
      (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0 x) = 0
    simpa using ConcreteCategory.congr_hom
      (truncLE'ToRestriction_f_zero_d (dgHomZModuleCochainComplex K L)) x
  have hy : CochainComplex.HomComplex.δ 0 1 y' = 0 := by
    change (dgHomZModuleCochainComplex L M).d 0 1
      (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0 y) = 0
    simpa using ConcreteCategory.congr_hom
      (truncLE'ToRestriction_f_zero_d (dgHomZModuleCochainComplex L M)) y
  rw [hx, hy]
  simp

/-- Composition on each summand of the tensor product of the truncated Hom complexes. -/
def dgTruncatedCompositionComponentReversed (K L M : ComplexCategory)
    {p q n : ℕ} (h : p + q = n) :
    (dgMappingDirectZModuleChainComplex L M).X p ⊗
        (dgMappingDirectZModuleChainComplex K L).X q ⟶
      (dgMappingDirectZModuleChainComplex K M).X n := by
  obtain rfl | n := n
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
      (boundaryLE_embeddingDownNat_iff 0).2 rfl
    exact
      (dgHomZModuleCochainComplex K M).liftCycles'
          (dgTruncatedCompositionToCochain K L M rfl) 1 (by simp)
          (dgTruncatedCompositionToCochain_zero_d K L M) ≫
        ((dgHomZModuleCochainComplex K M).truncLE'XIsoCycles
          ComplexShape.embeddingDownNat rfl hb).inv
  · have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE (n + 1) := fun hn =>
      Nat.succ_ne_zero n ((boundaryLE_embeddingDownNat_iff (n + 1)).1 hn)
    exact dgTruncatedCompositionToCochain K L M h ≫
      ((dgHomZModuleCochainComplex K M).truncLE'XIso
        ComplexShape.embeddingDownNat rfl hn).inv

@[reassoc]
lemma dgTruncatedCompositionComponentReversed_toRestriction
    (K L M : ComplexCategory) {p q n : ℕ} (h : p + q = n) :
    dgTruncatedCompositionComponentReversed K L M h ≫
        ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      dgTruncatedCompositionToCochain K L M h := by
  obtain rfl | n := n
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p
    subst q
    have hb : ComplexShape.embeddingDownNat.BoundaryLE 0 :=
      (boundaryLE_embeddingDownNat_iff 0).2 rfl
    dsimp [dgTruncatedCompositionComponentReversed]
    rw [truncLE'ToRestriction_f_zero _ hb]
    simp only [Category.assoc]
    erw [truncLE'XIsoCycles_inv_hom_of_proofs_assoc
      (dgHomZModuleCochainComplex K M) 0 0 rfl rfl hb hb]
    simp
  · have hn : ¬ ComplexShape.embeddingDownNat.BoundaryLE (n + 1) := fun hn =>
      Nat.succ_ne_zero n ((boundaryLE_embeddingDownNat_iff (n + 1)).1 hn)
    rw [truncLE'ToRestriction_f_succ _ n hn]
    change (dgTruncatedCompositionToCochain K L M h ≫
        ((dgHomZModuleCochainComplex K M).truncLE'XIso
          ComplexShape.embeddingDownNat rfl hn).inv) ≫
      ((dgHomZModuleCochainComplex K M).truncLE'XIso
        ComplexShape.embeddingDownNat rfl hn).hom =
      dgTruncatedCompositionToCochain K L M h
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The degreewise map induced by composition on the tensor of truncated Hom complexes. -/
def dgTruncatedCompositionDegreeReversed (K L M : ComplexCategory) (n : ℕ) :
    (HomologicalComplex.tensorObj
        (dgMappingDirectZModuleChainComplex L M)
        (dgMappingDirectZModuleChainComplex K L)).X n ⟶
      (dgMappingDirectZModuleChainComplex K M).X n :=
  HomologicalComplex.mapBifunctorDesc fun _ _ h =>
    dgTruncatedCompositionComponentReversed K L M h

/-- The degreewise truncated composition viewed in the unrestricted output complex. -/
def dgTruncatedCompositionToRestrictionDegree
    (K L M : ComplexCategory) (n : ℕ) :
    (HomologicalComplex.tensorObj
        (dgMappingDirectZModuleChainComplex L M)
        (dgMappingDirectZModuleChainComplex K L)).X n ⟶
      ((dgHomZModuleCochainComplex K M).restriction
        ComplexShape.embeddingDownNat).X n :=
  HomologicalComplex.mapBifunctorDesc fun _ _ h =>
    dgTruncatedCompositionToCochain K L M h

@[reassoc (attr := simp)]
lemma ιTensorObj_dgTruncatedCompositionDegreeReversed
    (K L M : ComplexCategory) {p q n : ℕ} (h : p + q = n) :
    HomologicalComplex.ιTensorObj
          (dgMappingDirectZModuleChainComplex L M)
          (dgMappingDirectZModuleChainComplex K L) p q n h ≫
        dgTruncatedCompositionDegreeReversed K L M n =
      dgTruncatedCompositionComponentReversed K L M h := by
  apply HomologicalComplex.ι_mapBifunctorDesc

@[reassoc]
lemma dgTruncatedCompositionDegreeReversed_toRestriction
    (K L M : ComplexCategory) (n : ℕ) :
    dgTruncatedCompositionDegreeReversed K L M n ≫
        ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n =
      dgTruncatedCompositionToRestrictionDegree K L M n := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hleft := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := dgMappingDirectZModuleChainComplex L M)
    (K₂ := dgMappingDirectZModuleChainComplex K L)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (fun _ _ h => dgTruncatedCompositionComponentReversed K L M h) p q h
  have hright := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := dgMappingDirectZModuleChainComplex L M)
    (K₂ := dgMappingDirectZModuleChainComplex K L)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (fun _ _ h => dgTruncatedCompositionToCochain K L M h) p q h
  rw [← Category.assoc]
  dsimp [dgTruncatedCompositionDegreeReversed,
    dgTruncatedCompositionToRestrictionDegree]
  exact (congrArg (fun t => t ≫
        ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f n) hleft).trans
    ((dgTruncatedCompositionComponentReversed_toRestriction K L M h).trans
      hright.symm)

lemma dgTruncatedCompositionToRestrictionDegree_comm
    (K L M : ComplexCategory) {n m : ℕ} (hnm : (ComplexShape.down ℕ).Rel n m) :
    dgTruncatedCompositionToRestrictionDegree K L M n ≫
        ((dgHomZModuleCochainComplex K M).restriction
          ComplexShape.embeddingDownNat).d n m =
      (HomologicalComplex.tensorObj
        (dgMappingDirectZModuleChainComplex L M)
        (dgMappingDirectZModuleChainComplex K L)).d n m ≫
          dgTruncatedCompositionToRestrictionDegree K L M m := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hraw := HomologicalComplex.ι_mapBifunctorDesc
    (K₁ := dgMappingDirectZModuleChainComplex L M)
    (K₂ := dgMappingDirectZModuleChainComplex K L)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    (fun _ _ h => dgTruncatedCompositionToCochain K L M h) p q hpq
  rw [← Category.assoc]
  dsimp [dgTruncatedCompositionToRestrictionDegree]
  refine (congrArg (fun t => t ≫
    (dgHomZModuleCochainComplex K M).d (-n) (-m)) hraw).trans ?_
  have hD₁ := HomologicalComplex.mapBifunctor.ι_D₁
    (K₁ := dgMappingDirectZModuleChainComplex L M)
    (K₂ := dgMappingDirectZModuleChainComplex K L)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    n m p q hpq
  have hD₂ := HomologicalComplex.mapBifunctor.ι_D₂
    (K₁ := dgMappingDirectZModuleChainComplex L M)
    (K₂ := dgMappingDirectZModuleChainComplex K L)
    (F := curriedTensor (ModuleCat ℤ)) (c := ComplexShape.down ℕ)
    n m p q hpq
  have hD₁assoc := congrArg (fun t => t ≫
    HomologicalComplex.mapBifunctorDesc
      (fun _ _ h => dgTruncatedCompositionToCochain K L M h)) hD₁
  have hD₂assoc := congrArg (fun t => t ≫
    HomologicalComplex.mapBifunctorDesc
      (fun _ _ h => dgTruncatedCompositionToCochain K L M h)) hD₂
  rw [HomologicalComplex.mapBifunctor.d_eq, ← Category.assoc,
    Preadditive.comp_add, Preadditive.add_comp]
  refine Eq.trans ?_ (congrArg₂ (fun a b => a + b) hD₁assoc hD₂assoc).symm
  change p + q = n at hpq
  change m + 1 = n at hnm
  obtain rfl | p := p <;> obtain rfl | q := q
  · omega
  · rw [HomologicalComplex.mapBifunctor.d₁_eq_zero _ _ _ _ 0 (q + 1) m
      (by simp [ComplexShape.down])]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0
      (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down]) m
      (by change 0 + q = m; omega)]
    simp only [zero_comp, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    have heps : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (0, q + 1) = 1 := rfl
    simp only [heps, one_smul]
    refine Eq.trans ?_ (zero_add _).symm
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext y x
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
    change (dgHomZModuleCochainComplex K M).d (-n) (-m)
        (dgTruncatedCompositionToCochain K L M hpq (y ⊗ₜ[ℤ] x)) =
      dgTruncatedCompositionToCochain K L M (show 0 + q = m by omega)
        (y ⊗ₜ[ℤ]
          (dgMappingDirectZModuleChainComplex K L).d (q + 1) q x)
    rw [dgTruncatedCompositionToCochain_tmul,
      dgTruncatedCompositionToCochain_tmul]
    let x' : CochainComplex.HomComplex.Cochain K.obj L.obj (-(q + 1 : ℕ) : ℤ) :=
      ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f (q + 1) x
    let y' : CochainComplex.HomComplex.Cochain L.obj M.obj 0 :=
      ((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0 y
    change CochainComplex.HomComplex.δ (-n) (-m)
      (x'.comp y' (by dsimp [x', y']; omega)) = _
    rw [CochainComplex.HomComplex.δ_comp x' y'
      (by dsimp [x', y']; omega) (-q) 1 (-m) (by omega) (by omega) rfl]
    have hx : CochainComplex.HomComplex.δ (-(q + 1 : ℕ) : ℤ) (-q) x' =
        ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q
            ((dgMappingDirectZModuleChainComplex K L).d (q + 1) q x) := by
      exact ConcreteCategory.congr_hom
        (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).comm (q + 1) q) x
    have hy : CochainComplex.HomComplex.δ 0 1 y' = 0 := by
      exact ConcreteCategory.congr_hom
        (truncLE'ToRestriction_f_zero_d (dgHomZModuleCochainComplex L M)) y
    rw [hx, hy]
    simp [y']
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
      0 m (by change p + 0 = m; omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ (p + 1) 0 m
      (by simp [ComplexShape.down])]
    simp only [zero_comp, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    have heps : ComplexShape.ε₁ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p + 1, 0) = 1 := rfl
    simp only [heps, one_smul]
    refine Eq.trans ?_ (add_zero _).symm
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext y x
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
    change (dgHomZModuleCochainComplex K M).d (-n) (-m)
        (dgTruncatedCompositionToCochain K L M hpq (y ⊗ₜ[ℤ] x)) =
      dgTruncatedCompositionToCochain K L M (show p + 0 = m by omega)
        ((dgMappingDirectZModuleChainComplex L M).d (p + 1) p y ⊗ₜ[ℤ] x)
    rw [dgTruncatedCompositionToCochain_tmul,
      dgTruncatedCompositionToCochain_tmul]
    let x' : CochainComplex.HomComplex.Cochain K.obj L.obj 0 :=
      ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f 0 x
    let y' : CochainComplex.HomComplex.Cochain L.obj M.obj (-(p + 1 : ℕ) : ℤ) :=
      ((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f (p + 1) y
    change CochainComplex.HomComplex.δ (-n) (-m)
      (x'.comp y' (by dsimp [x', y']; omega)) = _
    rw [CochainComplex.HomComplex.δ_comp x' y'
      (by dsimp [x', y']; omega) 1 (-p) (-m) (by omega) rfl (by omega)]
    have hx : CochainComplex.HomComplex.δ 0 1 x' = 0 := by
      exact ConcreteCategory.congr_hom
        (truncLE'ToRestriction_f_zero_d (dgHomZModuleCochainComplex K L)) x
    have hy : CochainComplex.HomComplex.δ (-(p + 1 : ℕ) : ℤ) (-p) y' =
        ((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p
            ((dgMappingDirectZModuleChainComplex L M).d (p + 1) p y) := by
      exact ConcreteCategory.congr_hom
        (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).comm (p + 1) p) y
    rw [hx, hy]
    simp [x']
  · rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
      (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down])
      (q + 1) m (by change p + (q + 1) = m; omega)]
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ (p + 1)
      (show (ComplexShape.down ℕ).Rel (q + 1) q by simp [ComplexShape.down])
      m (by change p + 1 + q = m; omega)]
    simp only [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [Units.smul_def, Units.smul_def]
    change _ = (1 : ℤ) • _ + ((-1 : ℤ) ^ (p + 1)) • _
    rw [one_smul]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext y x
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
    change (dgHomZModuleCochainComplex K M).d (-n) (-m)
        (dgTruncatedCompositionToCochain K L M hpq (y ⊗ₜ[ℤ] x)) =
      dgTruncatedCompositionToCochain K L M
          (show p + (q + 1) = m by omega)
          ((dgMappingDirectZModuleChainComplex L M).d (p + 1) p y ⊗ₜ[ℤ] x) +
        ((-1 : ℤ) ^ (p + 1)) •
          dgTruncatedCompositionToCochain K L M
            (show p + 1 + q = m by omega)
            (y ⊗ₜ[ℤ]
              (dgMappingDirectZModuleChainComplex K L).d (q + 1) q x)
    rw [dgTruncatedCompositionToCochain_tmul,
      dgTruncatedCompositionToCochain_tmul,
      dgTruncatedCompositionToCochain_tmul]
    let x' : CochainComplex.HomComplex.Cochain K.obj L.obj (-(q + 1 : ℕ) : ℤ) :=
      ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f (q + 1) x
    let y' : CochainComplex.HomComplex.Cochain L.obj M.obj (-(p + 1 : ℕ) : ℤ) :=
      ((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f (p + 1) y
    change CochainComplex.HomComplex.δ (-n) (-m)
      (x'.comp y' (by dsimp [x', y']; omega)) = _
    rw [CochainComplex.HomComplex.δ_comp x' y'
      (by dsimp [x', y']; omega) (-q) (-p) (-m) (by omega) (by omega) (by omega)]
    have hx : CochainComplex.HomComplex.δ (-(q + 1 : ℕ) : ℤ) (-q) x' =
        ((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f q
            ((dgMappingDirectZModuleChainComplex K L).d (q + 1) q x) := by
      exact ConcreteCategory.congr_hom
        (((dgHomZModuleCochainComplex K L).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).comm (q + 1) q) x
    have hy : CochainComplex.HomComplex.δ (-(p + 1 : ℕ) : ℤ) (-p) y' =
        ((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).f p
            ((dgMappingDirectZModuleChainComplex L M).d (p + 1) p y) := by
      exact ConcreteCategory.congr_hom
        (((dgHomZModuleCochainComplex L M).truncLE'ToRestriction
          ComplexShape.embeddingDownNat).comm (p + 1) p) y
    rw [hx, hy]
    have hsign : ((-(p + 1 : ℕ) : ℤ).negOnePow : ℤ) =
        (-1 : ℤ) ^ (p + 1) := by
      rw [Int.negOnePow_neg]
      exact Int.coe_negOnePow_natCast (p + 1)
    rw [Units.smul_def, hsign]

/-- Composition is a chain map on the directly truncated integer-module Hom complexes. -/
def dgTruncatedCompositionReversed (K L M : ComplexCategory) :
    HomologicalComplex.tensorObj
        (dgMappingDirectZModuleChainComplex L M)
        (dgMappingDirectZModuleChainComplex K L) ⟶
      dgMappingDirectZModuleChainComplex K M where
  f n := dgTruncatedCompositionDegreeReversed K L M n
  comm' n m hnm := by
    apply (cancel_mono
      (((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
        ComplexShape.embeddingDownNat).f m)).1
    calc
      (dgTruncatedCompositionDegreeReversed K L M n ≫
            (dgMappingDirectZModuleChainComplex K M).d n m) ≫
          ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f m =
        dgTruncatedCompositionDegreeReversed K L M n ≫
          ((dgMappingDirectZModuleChainComplex K M).d n m ≫
            ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
              ComplexShape.embeddingDownNat).f m) := Category.assoc _ _ _
      _ = dgTruncatedCompositionDegreeReversed K L M n ≫
          (((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
              ComplexShape.embeddingDownNat).f n ≫
            ((dgHomZModuleCochainComplex K M).restriction
              ComplexShape.embeddingDownNat).d n m) := by
        exact congrArg (fun t =>
          dgTruncatedCompositionDegreeReversed K L M n ≫ t)
            (((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
              ComplexShape.embeddingDownNat).comm n m).symm
      _ = (dgTruncatedCompositionDegreeReversed K L M n ≫
            ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
              ComplexShape.embeddingDownNat).f n) ≫
          ((dgHomZModuleCochainComplex K M).restriction
            ComplexShape.embeddingDownNat).d n m := (Category.assoc _ _ _).symm
      _ = dgTruncatedCompositionToRestrictionDegree K L M n ≫
          ((dgHomZModuleCochainComplex K M).restriction
            ComplexShape.embeddingDownNat).d n m := by
        rw [dgTruncatedCompositionDegreeReversed_toRestriction]
      _ = (HomologicalComplex.tensorObj
            (dgMappingDirectZModuleChainComplex L M)
            (dgMappingDirectZModuleChainComplex K L)).d n m ≫
          dgTruncatedCompositionToRestrictionDegree K L M m :=
        dgTruncatedCompositionToRestrictionDegree_comm K L M hnm
      _ = (HomologicalComplex.tensorObj
            (dgMappingDirectZModuleChainComplex L M)
            (dgMappingDirectZModuleChainComplex K L)).d n m ≫
          (dgTruncatedCompositionDegreeReversed K L M m ≫
            ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
              ComplexShape.embeddingDownNat).f m) := by
        rw [dgTruncatedCompositionDegreeReversed_toRestriction]
      _ = ((HomologicalComplex.tensorObj
              (dgMappingDirectZModuleChainComplex L M)
              (dgMappingDirectZModuleChainComplex K L)).d n m ≫
            dgTruncatedCompositionDegreeReversed K L M m) ≫
          ((dgHomZModuleCochainComplex K M).truncLE'ToRestriction
            ComplexShape.embeddingDownNat).f m := (Category.assoc _ _ _).symm

/-- The integer-module Dold--Kan mapping simplicial object. -/
def dgMappingZModuleSimplicialModule (K L : ComplexCategory) :
    SimplicialObject (ModuleCat.{0} ℤ) :=
  DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj
    (dgMappingZModuleChainComplex K L)

/-- The underlying simplicial set of the integer-module Dold--Kan mapping object. -/
def dgMappingZModuleSSet (K L : ComplexCategory) : SSet.{0} :=
  ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (Type 0)).obj
    (forget (ModuleCat.{0} ℤ))).obj (dgMappingZModuleSimplicialModule K L)

/-- Degree zero of the Dold--Kan inverse agrees with degree zero of the integer-module chain
complex. -/
def zModuleDoldKanInverseZeroIso (T : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    T.X 0 ≅
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.obj T).obj (op ⦋0⦌) := by
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

/-- Degree zero of the integer-module mapping chain complex is the bounded morphism type. -/
def dgMappingZModuleChainComplexZeroEquivBoundedHom (K L : ComplexCategory) :
    (dgMappingZModuleChainComplex K L).X 0 ≃ (K ⟶ L) :=
  (zModuleAddCommGrpEquivalence.counitIso.app
      ((dgMappingChainComplex K L).X 0)).addCommGroupIsoToAddEquiv.toEquiv.trans
    (dgMappingChainComplexZeroEquivBoundedHom K L)

/-- Vertices of the integer-module Dold--Kan carrier are bounded-complex morphisms. -/
def dgMappingZModuleVerticesEquivBoundedMorphisms (K L : ComplexCategory) :
    dgMappingZModuleSSet K L _⦋0⦌ ≃ (K ⟶ L) :=
  (zModuleDoldKanInverseZeroIso
      (dgMappingZModuleChainComplex K L)).symm.toLinearEquiv.toEquiv.trans
    (dgMappingZModuleChainComplexZeroEquivBoundedHom K L)

/-- The identity vertex in the integer-module Dold--Kan carrier. -/
def dgMappingZModuleIdentityVertex (K : ComplexCategory) :
    dgMappingZModuleSSet K K _⦋0⦌ :=
  (dgMappingZModuleVerticesEquivBoundedMorphisms K K).symm (𝟙 K)

/-- The identity vertex degenerately extended through every simplicial degree. -/
def dgMappingZModuleIdentitySSetMap (K : ComplexCategory) :
    (𝟙_ SSet) ⟶ dgMappingZModuleSSet K K :=
  (SSet.unitHomEquiv _).symm (dgMappingZModuleIdentityVertex K)

/-- The identity simplex in an arbitrary degree. -/
def dgMappingZModuleIdentitySimplex (K : ComplexCategory) (n : SimplexCategoryᵒᵖ) :
    (dgMappingZModuleSSet K K).obj n :=
  (dgMappingZModuleIdentitySSetMap K).app n PUnit.unit

@[simp]
theorem dgMappingZModuleIdentitySSetMap_vertex (K : ComplexCategory) :
    SSet.unitHomEquiv _ (dgMappingZModuleIdentitySSetMap K) =
      dgMappingZModuleIdentityVertex K := by
  exact Equiv.apply_symm_apply _ _

/-- Composition on the transported integer-module chain carriers. -/
def dgMappingZModuleChainComposition (K L M : ComplexCategory) :
    HomologicalComplex.tensorObj
        (dgMappingZModuleChainComplex L M)
        (dgMappingZModuleChainComplex K L) ⟶
      dgMappingZModuleChainComplex K M :=
  HomologicalComplex.tensorHom
      (dgMappingZModuleChainComplexIsoDirect L M).hom
      (dgMappingZModuleChainComplexIsoDirect K L).hom ≫
    dgTruncatedCompositionReversed K L M ≫
    (dgMappingZModuleChainComplexIsoDirect K M).inv

/-- Dold--Kan transports chain composition to simplicial integer modules once an
Alexander--Whitney oplax structure is supplied. -/
def dgMappingZModuleSimplicialComposition
    (h : DoldKanMonoidal.NormalizedMooreOplaxMonoidal)
    (K L M : ComplexCategory) :
    dgMappingZModuleSimplicialModule K L ⊗
      dgMappingZModuleSimplicialModule L M ⟶
      dgMappingZModuleSimplicialModule K M :=
  (β_ (dgMappingZModuleSimplicialModule K L)
      (dgMappingZModuleSimplicialModule L M)).hom ≫
    DoldKanMonoidal.inverseTensorator h
      (dgMappingZModuleChainComplex L M)
      (dgMappingZModuleChainComplex K L) ≫
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgMappingZModuleChainComposition K L M)

/-- Pure tensors give the canonical pairing from the cartesian product of the underlying
simplicial sets to the underlying simplicial set of a tensor product. -/
def simplicialZModuleTensorPairing
    (X Y : SimplicialObject (ModuleCat.{0} ℤ)) :
    ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (Type 0)).obj
          (forget (ModuleCat.{0} ℤ))).obj X ⊗
        ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (Type 0)).obj
          (forget (ModuleCat.{0} ℤ))).obj Y ⟶
      ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (Type 0)).obj
        (forget (ModuleCat.{0} ℤ))).obj (X ⊗ Y) where
  app n := ↾fun xy : (forget (ModuleCat ℤ)).obj (X.obj n) ×
    (forget (ModuleCat ℤ)).obj (Y.obj n) ↦ xy.1 ⊗ₜ[ℤ] xy.2
  naturality _ _ f := by
    ext xy
    obtain ⟨x, y⟩ := xy
    exact ModuleCat.MonoidalCategory.tensorHom_tmul (X.map f) (Y.map f) x y

/-- The underlying simplicial-set composition induced by a normalized Alexander--Whitney
oplax structure. -/
def dgMappingZModuleSSetComposition
    (h : DoldKanMonoidal.NormalizedMooreOplaxMonoidal)
    (K L M : ComplexCategory) :
    (dgMappingZModuleSSet K L ⊗ dgMappingZModuleSSet L M) ⟶
      dgMappingZModuleSSet K M :=
  simplicialZModuleTensorPairing
      (dgMappingZModuleSimplicialModule K L)
      (dgMappingZModuleSimplicialModule L M) ≫
    ((SimplicialObject.whiskering (ModuleCat.{0} ℤ) (Type 0)).obj
      (forget (ModuleCat.{0} ℤ))).map
        (dgMappingZModuleSimplicialComposition h K L M)

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
