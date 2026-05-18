import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import LeanLCAExactChallenge.LCA.ExactCategory

/-!
Yoneda extension groups for the local Quillen exact-category interface.

Positive-degree generators are finite chains of conflations. Degree zero is the
hom group, so the usual `Ext⁰(X,Y) ≃ Hom(X,Y)` comparison is definitional.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/-- A one-fold extension of `X` by `Y`, represented by a conflation
`0 ⟶ Y ⟶ middle ⟶ X ⟶ 0`. -/
structure ShortExactExtension (X Y : C) where
  middle : C
  i : Y ⟶ middle
  p : middle ⟶ X
  zero : i ≫ p = 0
  conflation : QuillenExactCategory.Conflation (ShortComplex.mk i p zero)

namespace ShortExactExtension

/-- The short complex underlying a one-fold extension. -/
def shortComplex {X Y : C} (e : ShortExactExtension X Y) : ShortComplex C :=
  ShortComplex.mk e.i e.p e.zero

@[simp]
lemma conflation_shortComplex {X Y : C} (e : ShortExactExtension X Y) :
    QuillenExactCategory.Conflation e.shortComplex :=
  e.conflation

/-- An isomorphism of one-fold extensions with fixed endpoints. -/
structure Iso {X Y : C} (e e' : ShortExactExtension X Y) where
  middleIso : e.middle ≅ e'.middle
  i_hom : e.i ≫ middleIso.hom = e'.i
  hom_p : middleIso.hom ≫ e'.p = e.p

namespace Iso

/-- Reflexivity for isomorphism of one-fold extensions. -/
def refl {X Y : C} (e : ShortExactExtension X Y) : Iso e e where
  middleIso := CategoryTheory.Iso.refl e.middle
  i_hom := by simp
  hom_p := by simp

end Iso

/-- An isomorphism of one-fold extensions over chosen endpoint isomorphisms. -/
structure IsoBetween {X X' Y Y' : C} (α : X ≅ X') (β : Y ≅ Y')
    (e : ShortExactExtension X Y) (e' : ShortExactExtension X' Y') where
  middleIso : e.middle ≅ e'.middle
  i_hom : e.i ≫ middleIso.hom = β.hom ≫ e'.i
  hom_p : middleIso.hom ≫ e'.p = e.p ≫ α.hom

namespace IsoBetween

/-- Reflexivity for isomorphism of one-fold extensions over endpoint identities. -/
def refl {X Y : C} (e : ShortExactExtension X Y) :
    IsoBetween (CategoryTheory.Iso.refl X) (CategoryTheory.Iso.refl Y) e e where
  middleIso := CategoryTheory.Iso.refl e.middle
  i_hom := by simp
  hom_p := by simp

end IsoBetween

/-- Diagrammatic data identifying a one-fold extension as a Baer sum.

The data records the standard route: product extension, pullback along the
diagonal, pushout along the codiagonal, and an isomorphism to the chosen sum.
-/
structure BaerSumData {X Y : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    (e₁ e₂ sum : ShortExactExtension X Y) where
  productExtension : ShortExactExtension (X ⊞ X) (Y ⊞ Y)
  productFst : productExtension.middle ⟶ e₁.middle
  productSnd : productExtension.middle ⟶ e₂.middle
  product_i_fst : productExtension.i ≫ productFst = biprod.fst ≫ e₁.i
  product_i_snd : productExtension.i ≫ productSnd = biprod.snd ≫ e₂.i
  product_p_fst : productFst ≫ e₁.p = productExtension.p ≫ biprod.fst
  product_p_snd : productSnd ≫ e₂.p = productExtension.p ≫ biprod.snd
  pullbackExtension : ShortExactExtension X (Y ⊞ Y)
  pullbackMap : pullbackExtension.middle ⟶ productExtension.middle
  pullback_i : pullbackExtension.i ≫ pullbackMap = productExtension.i
  pullback_p :
    pullbackMap ≫ productExtension.p =
      pullbackExtension.p ≫ biprod.lift (𝟙 X) (𝟙 X)
  pushoutExtension : ShortExactExtension X Y
  pushoutMap : pullbackExtension.middle ⟶ pushoutExtension.middle
  pushout_i :
    biprod.desc (𝟙 Y) (𝟙 Y) ≫ pushoutExtension.i =
      pullbackExtension.i ≫ pushoutMap
  pushout_p : pushoutMap ≫ pushoutExtension.p = pullbackExtension.p
  sumIso : Iso pushoutExtension sum

end ShortExactExtension

namespace MetrizableLCA

/-- Coordinatewise product of one-fold short exact extensions in `MetrizableLCA`. -/
noncomputable def shortExactExtensionBiprod
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    ShortExactExtension (C := MetrizableLCA.{u}) (biprodObj X₁ X₂) (biprodObj Y₁ Y₂) where
  middle := biprodObj e₁.middle e₂.middle
  i := biprodMap e₁.i e₂.i
  p := biprodMap e₁.p e₂.p
  zero := by
    ext p
    · exact congrArg (fun h : Y₁ ⟶ X₁ => h p.1) e₁.zero
    · exact congrArg (fun h : Y₂ ⟶ X₂ => h p.2) e₂.zero
  conflation := by
    simpa [ShortExactExtension.shortComplex, strictShortExactBiprodComplex]
      using strictShortExact_biprod e₁.conflation e₂.conflation

@[simp]
lemma shortExactExtensionBiprod_i_fst
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    (shortExactExtensionBiprod e₁ e₂).i ≫ biprodFst e₁.middle e₂.middle =
      biprodFst Y₁ Y₂ ≫ e₁.i := by
  ext p
  rfl

@[simp]
lemma shortExactExtensionBiprod_i_snd
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    (shortExactExtensionBiprod e₁ e₂).i ≫ biprodSnd e₁.middle e₂.middle =
      biprodSnd Y₁ Y₂ ≫ e₂.i := by
  ext p
  rfl

@[simp]
lemma shortExactExtensionBiprod_p_fst
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    biprodFst e₁.middle e₂.middle ≫ e₁.p =
      (shortExactExtensionBiprod e₁ e₂).p ≫ biprodFst X₁ X₂ := by
  ext p
  rfl

@[simp]
lemma shortExactExtensionBiprod_p_snd
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    biprodSnd e₁.middle e₂.middle ≫ e₂.p =
      (shortExactExtensionBiprod e₁ e₂).p ≫ biprodSnd X₁ X₂ := by
  ext p
  rfl

/-- Product of one-fold extensions, transported to mathlib's chosen binary biproduct endpoints. -/
noncomputable def shortExactExtensionBinaryBiproduct
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    ShortExactExtension (C := MetrizableLCA.{u}) (X₁ ⊞ X₂) (Y₁ ⊞ Y₂) where
  middle := biprodObj e₁.middle e₂.middle
  i := (biprodObjIsoBiprod Y₁ Y₂).inv ≫ (shortExactExtensionBiprod e₁ e₂).i
  p := (shortExactExtensionBiprod e₁ e₂).p ≫ (biprodObjIsoBiprod X₁ X₂).hom
  zero := by
    change (biprodObjIsoBiprod Y₁ Y₂).inv ≫
        ((shortExactExtensionBiprod e₁ e₂).i ≫ (shortExactExtensionBiprod e₁ e₂).p) ≫
          (biprodObjIsoBiprod X₁ X₂).hom = 0
    rw [(shortExactExtensionBiprod e₁ e₂).zero]
    simp
  conflation := by
    let prod := shortExactExtensionBiprod e₁ e₂
    let αY := biprodObjIsoBiprod Y₁ Y₂
    let αX := biprodObjIsoBiprod X₁ X₂
    let T : ShortComplex MetrizableLCA.{u} :=
      ShortComplex.mk (αY.inv ≫ prod.i) (prod.p ≫ αX.hom) (by
        change αY.inv ≫ (prod.i ≫ prod.p) ≫ αX.hom = 0
        rw [prod.zero]
        simp)
    have hIso : prod.shortComplex ≅ T :=
      ShortComplex.isoMk αY (Iso.refl prod.middle) αX (by
        simp [T, ShortExactExtension.shortComplex]) (by
        simp [T, ShortExactExtension.shortComplex])
    simpa [prod, T, ShortExactExtension.shortComplex] using
      strictShortExact_iso hIso prod.conflation

@[simp]
lemma shortExactExtensionBinaryBiproduct_i_fst
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    (shortExactExtensionBinaryBiproduct e₁ e₂).i ≫ biprodFst e₁.middle e₂.middle =
      biprod.fst ≫ e₁.i := by
  change ((biprodObjIsoBiprod Y₁ Y₂).inv ≫ (shortExactExtensionBiprod e₁ e₂).i) ≫
      biprodFst e₁.middle e₂.middle = biprod.fst ≫ e₁.i
  rw [Category.assoc, shortExactExtensionBiprod_i_fst]
  rw [← Category.assoc, biprodObjIsoBiprod_inv_fst]

@[simp]
lemma shortExactExtensionBinaryBiproduct_i_snd
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    (shortExactExtensionBinaryBiproduct e₁ e₂).i ≫ biprodSnd e₁.middle e₂.middle =
      biprod.snd ≫ e₂.i := by
  change ((biprodObjIsoBiprod Y₁ Y₂).inv ≫ (shortExactExtensionBiprod e₁ e₂).i) ≫
      biprodSnd e₁.middle e₂.middle = biprod.snd ≫ e₂.i
  rw [Category.assoc, shortExactExtensionBiprod_i_snd]
  rw [← Category.assoc, biprodObjIsoBiprod_inv_snd]

@[simp]
lemma shortExactExtensionBinaryBiproduct_p_fst
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    biprodFst e₁.middle e₂.middle ≫ e₁.p =
      (shortExactExtensionBinaryBiproduct e₁ e₂).p ≫ biprod.fst := by
  change biprodFst e₁.middle e₂.middle ≫ e₁.p =
      ((shortExactExtensionBiprod e₁ e₂).p ≫ (biprodObjIsoBiprod X₁ X₂).hom) ≫ biprod.fst
  rw [Category.assoc, biprodObjIsoBiprod_hom_fst]
  exact shortExactExtensionBiprod_p_fst e₁ e₂

@[simp]
lemma shortExactExtensionBinaryBiproduct_p_snd
    {X₁ Y₁ X₂ Y₂ : MetrizableLCA.{u}}
    (e₁ : ShortExactExtension (C := MetrizableLCA.{u}) X₁ Y₁)
    (e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X₂ Y₂) :
    biprodSnd e₁.middle e₂.middle ≫ e₂.p =
      (shortExactExtensionBinaryBiproduct e₁ e₂).p ≫ biprod.snd := by
  change biprodSnd e₁.middle e₂.middle ≫ e₂.p =
      ((shortExactExtensionBiprod e₁ e₂).p ≫ (biprodObjIsoBiprod X₁ X₂).hom) ≫ biprod.snd
  rw [Category.assoc, biprodObjIsoBiprod_hom_snd]
  exact shortExactExtensionBiprod_p_snd e₁ e₂

/-- Pull back a one-fold extension along a map on the quotient endpoint. -/
noncomputable def shortExactExtensionPullback
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : X' ⟶ X) :
    ShortExactExtension (C := MetrizableLCA.{u}) X' Y where
  middle := pullbackObj a e.p
  i := pullbackKernelMap a e.p e.i e.zero
  p := pullbackFst a e.p
  zero := pullbackKernelMap_fst a e.p e.i e.zero
  conflation := strictShortExact_pullback e.conflation a

@[simp]
lemma shortExactExtensionPullback_i_map
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : X' ⟶ X) :
    (shortExactExtensionPullback e a).i ≫ pullbackSnd a e.p = e.i :=
  pullbackKernelMap_snd a e.p e.i e.zero

@[simp]
lemma shortExactExtensionPullback_map_p
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : X' ⟶ X) :
    pullbackSnd a e.p ≫ e.p = (shortExactExtensionPullback e a).p ≫ a :=
  (pullback_condition a e.p).symm

/-- Push out a one-fold extension along a map on the kernel endpoint. -/
noncomputable def shortExactExtensionPushout
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y') :
    ShortExactExtension (C := MetrizableLCA.{u}) X Y' where
  middle := pushoutObj (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)
  i := pushoutInr (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)
  p := pushoutCokernelMap (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)
  zero := pushoutInr_cokernel (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)
  conflation := by
    simpa [ShortExactExtension.shortComplex] using
      strictShortExact_pushout (S := e.shortComplex) e.conflation a

@[simp]
lemma shortExactExtensionPushout_i
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y') :
    a ≫ (shortExactExtensionPushout e a).i =
      e.i ≫ pushoutInl (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a) :=
  (pushout_condition (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)).symm

@[simp]
lemma shortExactExtensionPushout_map_p
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y') :
    pushoutInl (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a) ≫
        (shortExactExtensionPushout e a).p = e.p :=
  pushoutInl_cokernel (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)

/-- The canonical Baer sum extension built by product, diagonal pullback, and codiagonal pushout. -/
noncomputable def shortExactExtensionBaerSum
    {X Y : MetrizableLCA.{u}}
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    ShortExactExtension (C := MetrizableLCA.{u}) X Y :=
  shortExactExtensionPushout
    (shortExactExtensionPullback (shortExactExtensionBinaryBiproduct e₁ e₂) (biprodDiag X))
    (biprodCodiag Y)

/-- Diagrammatic Baer-sum witness for the canonical MetrizableLCA Baer sum extension. -/
noncomputable def shortExactExtensionBaerSumData
    {X Y : MetrizableLCA.{u}}
    (e₁ e₂ : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    ShortExactExtension.BaerSumData e₁ e₂ (shortExactExtensionBaerSum e₁ e₂) where
  productExtension := shortExactExtensionBinaryBiproduct e₁ e₂
  productFst := biprodFst e₁.middle e₂.middle
  productSnd := biprodSnd e₁.middle e₂.middle
  product_i_fst := shortExactExtensionBinaryBiproduct_i_fst e₁ e₂
  product_i_snd := shortExactExtensionBinaryBiproduct_i_snd e₁ e₂
  product_p_fst := shortExactExtensionBinaryBiproduct_p_fst e₁ e₂
  product_p_snd := shortExactExtensionBinaryBiproduct_p_snd e₁ e₂
  pullbackExtension :=
    shortExactExtensionPullback (shortExactExtensionBinaryBiproduct e₁ e₂) (biprodDiag X)
  pullbackMap := pullbackSnd (biprodDiag X) (shortExactExtensionBinaryBiproduct e₁ e₂).p
  pullback_i :=
    shortExactExtensionPullback_i_map (shortExactExtensionBinaryBiproduct e₁ e₂) (biprodDiag X)
  pullback_p :=
    shortExactExtensionPullback_map_p (shortExactExtensionBinaryBiproduct e₁ e₂) (biprodDiag X)
  pushoutExtension := shortExactExtensionBaerSum e₁ e₂
  pushoutMap :=
    pushoutInl
      (S := (shortExactExtensionPullback (shortExactExtensionBinaryBiproduct e₁ e₂)
        (biprodDiag X)).shortComplex)
      (biprodCodiag Y)
      (pushoutSubgroup_closed
        (shortExactExtensionPullback (shortExactExtensionBinaryBiproduct e₁ e₂)
          (biprodDiag X)).conflation
        (biprodCodiag Y))
  pushout_i :=
    shortExactExtensionPushout_i
      (shortExactExtensionPullback (shortExactExtensionBinaryBiproduct e₁ e₂) (biprodDiag X))
      (biprodCodiag Y)
  pushout_p :=
    shortExactExtensionPushout_map_p
      (shortExactExtensionPullback (shortExactExtensionBinaryBiproduct e₁ e₂) (biprodDiag X))
      (biprodCodiag Y)
  sumIso := ShortExactExtension.Iso.refl (shortExactExtensionBaerSum e₁ e₂)

end MetrizableLCA

/-- A finite Yoneda extension chain from `X` to `Y`.

The successor constructor prepends a one-fold extension
`0 ⟶ Z ⟶ E ⟶ X ⟶ 0` to an `n`-fold extension from `Z` to `Y`.
-/
inductive YonedaExtension : C → C → ℕ → Type (max u v)
  | ofHom {X Y : C} (f : X ⟶ Y) : YonedaExtension X Y 0
| cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      (tail : YonedaExtension Z Y n) : YonedaExtension X Y (n + 1)

namespace ShortExactExtension

/-- The one-fold Yoneda extension chain represented by a short exact extension. -/
def toYonedaExtension {X Y : C} (e : ShortExactExtension X Y) : YonedaExtension X Y 1 :=
  YonedaExtension.cons e (YonedaExtension.ofHom (𝟙 Y))

end ShortExactExtension

namespace YonedaExtension

/-- Splice a one-fold extension on the left of a positive-degree Yoneda chain. -/
def consLeftMap {X Y Z : C} (e : ShortExactExtension X Y) (n : ℕ) :
    YonedaExtension Y Z (n + 1) → YonedaExtension X Z ((n + 1) + 1) :=
  fun a => YonedaExtension.cons e a

/-- The chain relation generated by hom equality and termwise isomorphism of extensions. -/
inductive Rel :
    {X Y : C} → {n : ℕ} → YonedaExtension X Y n → YonedaExtension X Y n → Prop
  | ofHom {X Y : C} {f g : X ⟶ Y} (h : f = g) :
      Rel (YonedaExtension.ofHom f) (YonedaExtension.ofHom g)
  | cons {X Y Z : C} {n : ℕ} {e e' : ShortExactExtension X Z}
      {tail tail' : YonedaExtension Z Y n}
      (he : ShortExactExtension.Iso e e') (ht : Rel tail tail') :
      Rel (YonedaExtension.cons e tail) (YonedaExtension.cons e' tail')

/-- Recursive isomorphism of extension chains, allowing isomorphic intermediate objects. -/
inductive RelIso :
    {X X' Y : C} → (α : X ≅ X') → {n : ℕ} →
      YonedaExtension X Y n → YonedaExtension X' Y n → Prop
  | ofHom {X X' Y : C} (α : X ≅ X') {f : X ⟶ Y} {g : X' ⟶ Y}
      (h : f = α.hom ≫ g) :
      RelIso α (YonedaExtension.ofHom f) (YonedaExtension.ofHom g)
  | cons {X X' Y Z Z' : C} {n : ℕ} {α : X ≅ X'} {β : Z ≅ Z'}
      {e : ShortExactExtension X Z} {e' : ShortExactExtension X' Z'}
      {tail : YonedaExtension Z Y n} {tail' : YonedaExtension Z' Y n}
      (he : ShortExactExtension.IsoBetween α β e e') (ht : RelIso β tail tail') :
      RelIso α (YonedaExtension.cons e tail) (YonedaExtension.cons e' tail')

/-- Witnessed Baer sums of positive-degree extension chains. -/
inductive BaerSumData :
    {X Y : C} → {n : ℕ} →
      YonedaExtension X Y (n + 1) →
      YonedaExtension X Y (n + 1) →
      YonedaExtension X Y (n + 1) → Type (max u v)
  | one {X Y : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
      {e₁ e₂ sum : ShortExactExtension X Y}
      (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
      BaerSumData e₁.toYonedaExtension e₂.toYonedaExtension sum.toYonedaExtension
  | cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      {a b sum : YonedaExtension Z Y (n + 1)}
      (h : BaerSumData a b sum) :
      BaerSumData (YonedaExtension.cons e a) (YonedaExtension.cons e b)
        (YonedaExtension.cons e sum)

/-- Positive-degree extension chains whose rightmost one-fold extension is split. -/
inductive RightSplitData :
    {X Y : C} → {n : ℕ} → YonedaExtension X Y (n + 1) → Type (max u v)
  | one {X Y : C} (e : ShortExactExtension X Y) (s : e.shortComplex.Splitting) :
      RightSplitData e.toYonedaExtension
  | cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      {tail : YonedaExtension Z Y (n + 1)}
      (h : RightSplitData tail) :
      RightSplitData (YonedaExtension.cons e tail)

/-- Positive-degree extension chains containing a split one-fold factor. -/
inductive SplitFactorData :
    {X Y : C} → {n : ℕ} → YonedaExtension X Y (n + 1) → Type (max u v)
  | head {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      (s : e.shortComplex.Splitting) (tail : YonedaExtension Z Y n) :
      SplitFactorData (YonedaExtension.cons e tail)
  | cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      {tail : YonedaExtension Z Y (n + 1)}
      (h : SplitFactorData tail) :
      SplitFactorData (YonedaExtension.cons e tail)

/-- Positive chains whose factors are all one-fold extensions. -/
inductive PositiveChain : C → C → ℕ → Type (max u v)
  | one {X Y : C} (e : ShortExactExtension X Y) : PositiveChain X Y 0
  | cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      (tail : PositiveChain Z Y n) : PositiveChain X Y (n + 1)

namespace PositiveChain

/-- View a positive one-fold chain as a Yoneda extension chain. -/
def toYonedaExtension :
    {X Y : C} → {n : ℕ} → PositiveChain X Y n → YonedaExtension X Y (n + 1)
  | _, _, 0, one e => e.toYonedaExtension
  | _, _, _ + 1, cons e tail => YonedaExtension.cons e (toYonedaExtension tail)

/-- Splice a positive one-fold chain on the left of a positive Yoneda chain. -/
def consLeftMap :
    {X Y Z : C} → {m n : ℕ} →
      PositiveChain X Y m → YonedaExtension Y Z (n + 1) →
        YonedaExtension X Z ((n + (m + 1)) + 1)
  | _, _, _, 0, _, one e, a => YonedaExtension.cons e a
  | _, _, _, m + 1, n, cons e tail, a => by
      simpa [Nat.add_assoc] using
        YonedaExtension.cons e (consLeftMap (m := m) (n := n) tail a)

/-- Positive one-fold chains containing a split factor. -/
inductive SplitFactorData :
    {X Y : C} → {n : ℕ} → PositiveChain X Y n → Type (max u v)
  | one {X Y : C} (e : ShortExactExtension X Y) (s : e.shortComplex.Splitting) :
      SplitFactorData (one e)
  | head {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      (s : e.shortComplex.Splitting) (tail : PositiveChain Z Y n) :
      SplitFactorData (cons e tail)
  | cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      {tail : PositiveChain Z Y n} (h : SplitFactorData tail) :
      SplitFactorData (cons e tail)

/-- A split factor in a positive one-fold chain gives a split factor in its Yoneda chain. -/
def SplitFactorData.toYonedaExtension :
    {X Y : C} → {n : ℕ} → {p : PositiveChain X Y n} →
      SplitFactorData p → YonedaExtension.SplitFactorData p.toYonedaExtension
  | _, _, 0, _, one e s =>
      YonedaExtension.SplitFactorData.head e s (YonedaExtension.ofHom (𝟙 _))
  | _, _, _ + 1, _, head e s tail =>
      YonedaExtension.SplitFactorData.head e s tail.toYonedaExtension
  | _, _, _ + 1, _, cons e h =>
      YonedaExtension.SplitFactorData.cons e h.toYonedaExtension

/-- A split factor in a positive one-fold chain remains after left splicing. -/
def SplitFactorData.consLeftMap :
    {X Y Z : C} → {m n : ℕ} → {p : PositiveChain X Y m} →
      SplitFactorData p → (a : YonedaExtension Y Z (n + 1)) →
        YonedaExtension.SplitFactorData (p.consLeftMap a)
  | _, _, _, 0, _, _, one e s, a =>
      YonedaExtension.SplitFactorData.head e s a
  | _, _, _, _ + 1, _, _, head e s tail, a =>
      YonedaExtension.SplitFactorData.head e s (tail.consLeftMap a)
  | _, _, _, _ + 1, _, _, cons e h, a =>
      YonedaExtension.SplitFactorData.cons e (h.consLeftMap a)

end PositiveChain

end YonedaExtension

/-- The positive-degree free abelian group generated by `n + 1`-fold Yoneda extensions. -/
abbrev PositiveYonedaExtFree (X Y : C) (n : ℕ) : Type (max u v) :=
  FreeAbelianGroup (YonedaExtension X Y (n + 1))

/-- Relation generators imposed on positive-degree Yoneda extension chains. -/
inductive YonedaRelGenerator (X Y : C) :
    (n : ℕ) → PositiveYonedaExtFree X Y n → Prop
  | iso {n : ℕ} {a b : YonedaExtension X Y (n + 1)}
      (h : YonedaExtension.Rel a b) :
      YonedaRelGenerator X Y n (FreeAbelianGroup.of a - FreeAbelianGroup.of b)
  | chainIso {n : ℕ} {a b : YonedaExtension X Y (n + 1)}
      (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) :
      YonedaRelGenerator X Y n (FreeAbelianGroup.of a - FreeAbelianGroup.of b)
  | split (e : ShortExactExtension X Y) (s : e.shortComplex.Splitting) :
      YonedaRelGenerator X Y 0 (FreeAbelianGroup.of e.toYonedaExtension)
  | baer [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
      {e₁ e₂ sum : ShortExactExtension X Y}
      (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
      YonedaRelGenerator X Y 0
        (FreeAbelianGroup.of sum.toYonedaExtension -
          FreeAbelianGroup.of e₁.toYonedaExtension -
          FreeAbelianGroup.of e₂.toYonedaExtension)
  | baerChain {n : ℕ} {a b sum : YonedaExtension X Y (n + 1)}
      (h : YonedaExtension.BaerSumData a b sum) :
      YonedaRelGenerator X Y n
        (FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b)
  | leftSplit {Z : C} (e : ShortExactExtension X Z) (f : ShortExactExtension Z Y)
      (s : f.shortComplex.Splitting) :
      YonedaRelGenerator X Y 1
        (FreeAbelianGroup.of (YonedaExtension.cons e f.toYonedaExtension))
  | rightSplit {n : ℕ} {a : YonedaExtension X Y (n + 1)}
      (h : YonedaExtension.RightSplitData a) :
      YonedaRelGenerator X Y n (FreeAbelianGroup.of a)
  | splitFactor {n : ℕ} {a : YonedaExtension X Y (n + 1)}
      (h : YonedaExtension.SplitFactorData a) :
      YonedaRelGenerator X Y n (FreeAbelianGroup.of a)

/-- The subgroup generated by the local Yoneda relation generators. -/
def yonedaRelationSubgroup (X Y : C) (n : ℕ) : AddSubgroup (PositiveYonedaExtFree X Y n) :=
  AddSubgroup.closure {z | YonedaRelGenerator X Y n z}

/--
The positive-degree Yoneda Ext group obtained by quotienting formal extension
chains by the local relation generators.
-/
abbrev PositiveYonedaExt (X Y : C) (n : ℕ) : Type (max u v) :=
  PositiveYonedaExtFree X Y n ⧸ yonedaRelationSubgroup X Y n

/-- Exact-category Yoneda Ext groups for the local Quillen exact-category interface. -/
def YonedaExt (X Y : C) : ℕ → Type (max u v)
  | 0 => ULift.{max u v, v} (X ⟶ Y)
  | n + 1 => PositiveYonedaExt X Y n

namespace YonedaExt

variable {X Y : C} {n : ℕ}

/-- Degree-zero Yoneda Ext is the hom group. -/
noncomputable def zero_equiv_hom : YonedaExt X Y 0 ≃ (X ⟶ Y) :=
  Equiv.ulift

/-- The generator associated to a positive-degree extension chain. -/
def ofExtension (e : YonedaExtension X Y (n + 1)) : YonedaExt X Y (n + 1) :=
  QuotientAddGroup.mk' (yonedaRelationSubgroup X Y n) (FreeAbelianGroup.of e)

/-- The additive group structure on exact-category Yoneda Ext. -/
noncomputable instance instAddCommGroup : AddCommGroup (YonedaExt X Y n) := by
  cases n with
  | zero =>
      dsimp [YonedaExt]
      infer_instance
  | succ n =>
      dsimp [YonedaExt, PositiveYonedaExt]
      infer_instance

/-- Termwise-related extension chains define equal classes in positive-degree Ext. -/
theorem ofExtension_eq_ofExtension_of_rel {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.Rel a b) :
    ofExtension (X := X) (Y := Y) (n := n) a =
      ofExtension (X := X) (Y := Y) (n := n) b := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of a : PositiveYonedaExtFree X Y n) : PositiveYonedaExt X Y n) =
    ((FreeAbelianGroup.of b : PositiveYonedaExtFree X Y n) : PositiveYonedaExt X Y n)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure (YonedaRelGenerator.iso (X := X) (Y := Y) h)

/-- Isomorphic extension chains define equal classes in positive-degree Ext. -/
theorem ofExtension_eq_ofExtension_of_relIso {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) :
    ofExtension (X := X) (Y := Y) (n := n) a =
      ofExtension (X := X) (Y := Y) (n := n) b := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of a : PositiveYonedaExtFree X Y n) : PositiveYonedaExt X Y n) =
    ((FreeAbelianGroup.of b : PositiveYonedaExtFree X Y n) : PositiveYonedaExt X Y n)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure (YonedaRelGenerator.chainIso (X := X) (Y := Y) h)

/-- A split one-fold extension represents zero in local Yoneda Ext. -/
theorem ofExtension_eq_zero_of_split (e : ShortExactExtension X Y)
    (s : e.shortComplex.Splitting) :
    ofExtension (X := X) (Y := Y) (n := 0) e.toYonedaExtension =
      (0 : YonedaExt X Y 1) := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of e.toYonedaExtension : PositiveYonedaExtFree X Y 0) :
    PositiveYonedaExt X Y 0) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (YonedaRelGenerator.split e s)

/-- Splicing a split right-hand one-fold extension after another one-fold extension is zero. -/
theorem ofExtension_cons_eq_zero_of_right_split {Z : C}
    (e : ShortExactExtension X Z) (f : ShortExactExtension Z Y)
    (s : f.shortComplex.Splitting) :
    ofExtension (X := X) (Y := Y) (n := 1)
        (YonedaExtension.cons e f.toYonedaExtension) =
      (0 : YonedaExt X Y 2) := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of (YonedaExtension.cons e f.toYonedaExtension) :
    PositiveYonedaExtFree X Y 1) : PositiveYonedaExt X Y 1) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (YonedaRelGenerator.leftSplit e f s)

/-- An extension chain whose rightmost one-fold extension is split represents zero. -/
theorem ofExtension_eq_zero_of_rightSplitData {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) :
    ofExtension (X := X) (Y := Y) (n := n) a =
      (0 : YonedaExt X Y (n + 1)) := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of a : PositiveYonedaExtFree X Y n) :
    PositiveYonedaExt X Y n) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (YonedaRelGenerator.rightSplit h)

/-- An extension chain containing a split one-fold factor represents zero. -/
theorem ofExtension_eq_zero_of_splitFactorData {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) :
    ofExtension (X := X) (Y := Y) (n := n) a =
      (0 : YonedaExt X Y (n + 1)) := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of a : PositiveYonedaExtFree X Y n) :
    PositiveYonedaExt X Y n) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact AddSubgroup.subset_closure (YonedaRelGenerator.splitFactor h)

/-- A positive-degree relation of the form `sum - a - b` gives addition in local Yoneda Ext. -/
theorem ofExtension_eq_add_of_relation_mem {a b sum : YonedaExtension X Y (n + 1)}
    (h : FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b ∈
      yonedaRelationSubgroup X Y n) :
    ofExtension (X := X) (Y := Y) (n := n) sum =
      ofExtension (X := X) (Y := Y) (n := n) a +
        ofExtension (X := X) (Y := Y) (n := n) b := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of sum : PositiveYonedaExtFree X Y n) :
    PositiveYonedaExt X Y n) =
      ((FreeAbelianGroup.of a + FreeAbelianGroup.of b : PositiveYonedaExtFree X Y n) :
        PositiveYonedaExt X Y n)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- A witnessed Baer sum is addition in local one-fold Yoneda Ext. -/
theorem ofExtension_eq_add_of_baer [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
    ofExtension (X := X) (Y := Y) (n := 0) sum.toYonedaExtension =
      ofExtension (X := X) (Y := Y) (n := 0) e₁.toYonedaExtension +
        ofExtension (X := X) (Y := Y) (n := 0) e₂.toYonedaExtension := by
  exact ofExtension_eq_add_of_relation_mem (X := X) (Y := Y) (n := 0)
    (a := e₁.toYonedaExtension) (b := e₂.toYonedaExtension) (sum := sum.toYonedaExtension) <|
    AddSubgroup.subset_closure (YonedaRelGenerator.baer (X := X) (Y := Y) h)

/-- A witnessed positive-degree Baer sum is addition in local Yoneda Ext. -/
theorem ofExtension_eq_add_of_baerChain {a b sum : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) :
    ofExtension (X := X) (Y := Y) (n := n) sum =
      ofExtension (X := X) (Y := Y) (n := n) a +
        ofExtension (X := X) (Y := Y) (n := n) b := by
  exact ofExtension_eq_add_of_relation_mem (X := X) (Y := Y) (n := n) (a := a) (b := b)
    (sum := sum) <|
    AddSubgroup.subset_closure (YonedaRelGenerator.baerChain (X := X) (Y := Y) h)

/-- Baer addition, represented by the additive group operation on the local Ext group. -/
noncomputable def baer_sum (a b : YonedaExt X Y n) : YonedaExt X Y n :=
  a + b

/-- A relation of the form `sum - a - b` computes the `baer_sum` operation. -/
theorem baer_sum_ofExtension_eq_of_relation_mem {a b sum : YonedaExtension X Y (n + 1)}
    (h : FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b ∈
      yonedaRelationSubgroup X Y n) :
    baer_sum
        (ofExtension (X := X) (Y := Y) (n := n) a)
        (ofExtension (X := X) (Y := Y) (n := n) b) =
      ofExtension (X := X) (Y := Y) (n := n) sum := by
  dsimp [baer_sum]
  exact (ofExtension_eq_add_of_relation_mem h).symm

/-- A witnessed Baer sum computes the `baer_sum` operation on one-fold extensions. -/
theorem baer_sum_ofExtension_eq_of_baer [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
    baer_sum
        (ofExtension (X := X) (Y := Y) (n := 0) e₁.toYonedaExtension)
        (ofExtension (X := X) (Y := Y) (n := 0) e₂.toYonedaExtension) =
      ofExtension (X := X) (Y := Y) (n := 0) sum.toYonedaExtension := by
  dsimp [baer_sum]
  exact (ofExtension_eq_add_of_baer h).symm

/-- A witnessed positive-degree Baer sum computes the `baer_sum` operation. -/
theorem baer_sum_ofExtension_eq_of_baerChain
    {a b sum : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) :
    baer_sum
        (ofExtension (X := X) (Y := Y) (n := n) a)
        (ofExtension (X := X) (Y := Y) (n := n) b) =
      ofExtension (X := X) (Y := Y) (n := n) sum := by
  dsimp [baer_sum]
  exact (ofExtension_eq_add_of_baerChain h).symm

section LeftProduct

variable {Z : C}

/-- The free abelian group map induced by splicing a one-fold extension on the left. -/
def consLeftFreeHom (e : ShortExactExtension X Y) (n : ℕ) :
    PositiveYonedaExtFree Y Z n →+ PositiveYonedaExtFree X Z (n + 1) :=
  FreeAbelianGroup.map (YonedaExtension.consLeftMap e n)

/-- Left splicing by a fixed one-fold extension preserves the local Yoneda relations. -/
theorem consLeft_relationSubgroup_le (e : ShortExactExtension X Y) (n : ℕ) :
    yonedaRelationSubgroup Y Z n ≤
      (yonedaRelationSubgroup X Z (n + 1)).comap
        (consLeftFreeHom (X := X) (Y := Y) (Z := Z) e n) := by
  rw [yonedaRelationSubgroup]
  refine (AddSubgroup.closure_le _).mpr ?_
  intro z hz
  change consLeftFreeHom (X := X) (Y := Y) (Z := Z) e n z ∈
    yonedaRelationSubgroup X Z (n + 1)
  cases hz with
  | iso h =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap, map_sub] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.iso (X := X) (Y := Z)
            (YonedaExtension.Rel.cons (ShortExactExtension.Iso.refl e) h))
  | chainIso h =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap, map_sub] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.chainIso (X := X) (Y := Z)
            (YonedaExtension.RelIso.cons (ShortExactExtension.IsoBetween.refl e) h))
  | split f s =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap] using
        AddSubgroup.subset_closure (YonedaRelGenerator.leftSplit e f s)
  | leftSplit g f s =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.rightSplit (X := X) (Y := Z)
            (YonedaExtension.RightSplitData.cons e
              (YonedaExtension.RightSplitData.cons g
                (YonedaExtension.RightSplitData.one f s))))
  | rightSplit h =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.rightSplit (X := X) (Y := Z)
            (YonedaExtension.RightSplitData.cons e h))
  | splitFactor h =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.splitFactor (X := X) (Y := Z)
            (YonedaExtension.SplitFactorData.cons e h))
  | baer h =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap, map_sub] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.baerChain (X := X) (Y := Z)
            (YonedaExtension.BaerSumData.cons e (YonedaExtension.BaerSumData.one h)))
  | baerChain h =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap, map_sub] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.baerChain (X := X) (Y := Z)
            (YonedaExtension.BaerSumData.cons e h))

/-- Left Yoneda product by a fixed one-fold extension, descended to the quotient group. -/
noncomputable def leftProductByExtension (e : ShortExactExtension X Y) (n : ℕ) :
    YonedaExt Y Z (n + 1) →+ YonedaExt X Z ((n + 1) + 1) :=
  QuotientAddGroup.map (yonedaRelationSubgroup Y Z n) (yonedaRelationSubgroup X Z (n + 1))
    (consLeftFreeHom (X := X) (Y := Y) (Z := Z) e n)
    (consLeft_relationSubgroup_le (X := X) (Y := Y) (Z := Z) e n)

@[simp]
theorem leftProductByExtension_ofExtension (e : ShortExactExtension X Y)
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      ofExtension (X := X) (Y := Z) (n := n + 1)
        (YonedaExtension.consLeftMap e n a) := by
  rfl

/-- A split left one-fold factor gives zero after left splicing. -/
theorem leftProductByExtension_ofExtension_eq_zero_of_split
    (e : ShortExactExtension X Y) (s : e.shortComplex.Splitting)
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      (0 : YonedaExt X Z ((n + 1) + 1)) := by
  rw [leftProductByExtension_ofExtension]
  exact ofExtension_eq_zero_of_splitFactorData
    (YonedaExtension.SplitFactorData.head e s a)

/-- The free abelian group map induced by splicing a positive one-fold chain on the left. -/
def positiveChainLeftFreeHom :
    {X Y Z : C} → {m : ℕ} →
      YonedaExtension.PositiveChain X Y m → (n : ℕ) →
        PositiveYonedaExtFree Y Z n →+ PositiveYonedaExtFree X Z (n + (m + 1))
  | _, _, _, 0, YonedaExtension.PositiveChain.one e, n => consLeftFreeHom e n
  | _, _, _, m + 1, YonedaExtension.PositiveChain.cons e tail, n => by
      simpa [Nat.add_assoc] using
        (consLeftFreeHom e (n + (m + 1))).comp
          (positiveChainLeftFreeHom tail n)

/--
Splicing by a fixed positive one-fold chain preserves the local Yoneda
relations in the right variable.
-/
theorem positiveChainLeft_relationSubgroup_le :
    {X Y Z : C} → {m : ℕ} →
      (p : YonedaExtension.PositiveChain X Y m) → (n : ℕ) →
        yonedaRelationSubgroup Y Z n ≤
          (yonedaRelationSubgroup X Z (n + (m + 1))).comap
            (positiveChainLeftFreeHom p n)
  | X, Y, Z, 0, YonedaExtension.PositiveChain.one e, n => by
      simpa [positiveChainLeftFreeHom] using
        consLeft_relationSubgroup_le (X := X) (Y := Y) (Z := Z) e n
  | _, _, Z, m + 1, YonedaExtension.PositiveChain.cons e tail, n => by
      intro z hz
      have htail := positiveChainLeft_relationSubgroup_le (Z := Z) tail n hz
      have hhead := consLeft_relationSubgroup_le e (n + (m + 1)) htail
      simpa [positiveChainLeftFreeHom, Nat.add_assoc] using hhead

/-- A fixed positive one-fold chain acts on the right by Yoneda splicing. -/
noncomputable def leftProductByPositiveChain {m : ℕ}
    (p : YonedaExtension.PositiveChain X Y m) (n : ℕ) :
    YonedaExt Y Z (n + 1) →+ YonedaExt X Z ((n + (m + 1)) + 1) :=
  QuotientAddGroup.map (yonedaRelationSubgroup Y Z n)
    (yonedaRelationSubgroup X Z (n + (m + 1)))
    (positiveChainLeftFreeHom (Z := Z) p n)
    (positiveChainLeft_relationSubgroup_le (Z := Z) p n)

@[simp]
theorem positiveChainLeftFreeHom_of {m : ℕ}
    (p : YonedaExtension.PositiveChain X Y m)
    (a : YonedaExtension Y Z (n + 1)) :
    positiveChainLeftFreeHom (Z := Z) p n (FreeAbelianGroup.of a) =
      FreeAbelianGroup.of (YonedaExtension.PositiveChain.consLeftMap p a) := by
  induction p with
  | one e =>
      rfl
  | cons e tail ih =>
      simp [positiveChainLeftFreeHom, YonedaExtension.PositiveChain.consLeftMap,
        consLeftFreeHom, YonedaExtension.consLeftMap, ih]

@[simp]
theorem leftProductByPositiveChain_ofExtension {m : ℕ}
    (p : YonedaExtension.PositiveChain X Y m)
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      ofExtension (X := X) (Y := Z) (n := n + (m + 1))
        (YonedaExtension.PositiveChain.consLeftMap p a) := by
  dsimp [leftProductByPositiveChain, ofExtension]
  calc
    (QuotientAddGroup.map (yonedaRelationSubgroup Y Z n)
          (yonedaRelationSubgroup X Z (n + (m + 1)))
          (positiveChainLeftFreeHom (Z := Z) p n)
          (positiveChainLeft_relationSubgroup_le (Z := Z) p n))
        ((FreeAbelianGroup.of a : PositiveYonedaExtFree Y Z n) :
          PositiveYonedaExt Y Z n) =
        ((positiveChainLeftFreeHom (Z := Z) p n (FreeAbelianGroup.of a) :
          PositiveYonedaExtFree X Z (n + (m + 1))) :
          PositiveYonedaExt X Z (n + (m + 1))) := by
          simp
    _ = ((FreeAbelianGroup.of (YonedaExtension.PositiveChain.consLeftMap p a) :
          PositiveYonedaExtFree X Z (n + (m + 1))) :
          PositiveYonedaExt X Z (n + (m + 1))) := by
          rw [positiveChainLeftFreeHom_of]

/-- A fixed positive left chain with a split factor gives zero after splicing. -/
theorem leftProductByPositiveChain_ofExtension_eq_zero_of_splitFactor {m : ℕ}
    {p : YonedaExtension.PositiveChain X Y m}
    (h : YonedaExtension.PositiveChain.SplitFactorData p)
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      (0 : YonedaExt X Z ((n + (m + 1)) + 1)) := by
  rw [leftProductByPositiveChain_ofExtension]
  exact ofExtension_eq_zero_of_splitFactorData (h.consLeftMap a)

end LeftProduct

end YonedaExt

end LeanLCAExactChallenge
