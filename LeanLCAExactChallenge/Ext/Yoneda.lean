import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.DepRewrite
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

/-- The kernel map in a one-fold Yoneda extension is an inflation in the ambient exact category. -/
theorem inflation_i {X Y : C} (e : ShortExactExtension X Y) :
    QuillenExactCategory.inflation e.i :=
  QuillenExactCategory.inflation_of_conflation e.conflation

/-- The quotient map in a one-fold Yoneda extension is a deflation in the ambient exact category. -/
theorem deflation_p {X Y : C} (e : ShortExactExtension X Y) :
    QuillenExactCategory.deflation e.p :=
  QuillenExactCategory.deflation_of_conflation e.conflation

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

/-- Symmetry for isomorphism of one-fold extensions. -/
def symm {X Y : C} {e e' : ShortExactExtension X Y} (h : Iso e e') : Iso e' e where
  middleIso := h.middleIso.symm
  i_hom := by
    rw [← h.i_hom]
    simp [Category.assoc]
  hom_p := by
    rw [← h.hom_p]
    simp

/-- Transitivity for isomorphism of one-fold extensions. -/
def trans {X Y : C} {e₁ e₂ e₃ : ShortExactExtension X Y}
    (h₁₂ : Iso e₁ e₂) (h₂₃ : Iso e₂ e₃) : Iso e₁ e₃ where
  middleIso := h₁₂.middleIso.trans h₂₃.middleIso
  i_hom := by
    change e₁.i ≫ h₁₂.middleIso.hom ≫ h₂₃.middleIso.hom = e₃.i
    rw [← Category.assoc, h₁₂.i_hom, h₂₃.i_hom]
  hom_p := by
    simp [CategoryTheory.Iso.trans_hom, h₂₃.hom_p, h₁₂.hom_p]

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

namespace BaerSumData

/-- Replace the chosen representative of a Baer sum by an isomorphic extension. -/
def isoSum {X Y : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum sum' : ShortExactExtension X Y}
    (h : BaerSumData e₁ e₂ sum) (hsum : Iso sum sum') :
    BaerSumData e₁ e₂ sum' where
  productExtension := h.productExtension
  productFst := h.productFst
  productSnd := h.productSnd
  product_i_fst := h.product_i_fst
  product_i_snd := h.product_i_snd
  product_p_fst := h.product_p_fst
  product_p_snd := h.product_p_snd
  pullbackExtension := h.pullbackExtension
  pullbackMap := h.pullbackMap
  pullback_i := h.pullback_i
  pullback_p := h.pullback_p
  pushoutExtension := h.pushoutExtension
  pushoutMap := h.pushoutMap
  pushout_i := h.pushout_i
  pushout_p := h.pushout_p
  sumIso := h.sumIso.trans hsum

end BaerSumData

/-- Diagrammatic data identifying an extension pulled back along a quotient-endpoint map. -/
structure PullbackData {X X' Y : C}
    (e : ShortExactExtension X Y) (a : X' ⟶ X) (out : ShortExactExtension X' Y) where
  middleMap : out.middle ⟶ e.middle
  i_map : out.i ≫ middleMap = e.i
  map_p : middleMap ≫ e.p = out.p ≫ a
  isPullback : IsPullback middleMap out.p e.p a

namespace PullbackData

/-- Pullback data transports an isomorphism of input one-fold extensions. -/
noncomputable def iso {X X' Y : C} {e e' : ShortExactExtension X Y}
    {a : X' ⟶ X} {out out' : ShortExactExtension X' Y}
    (d : PullbackData e a out) (d' : PullbackData e' a out') (h : Iso e e') :
    Iso out out' := by
  have h_hom_comm : (d.middleMap ≫ h.middleIso.hom) ≫ e'.p = out.p ≫ a := by
    rw [Category.assoc, h.hom_p, d.map_p]
  have h_inv_p : h.middleIso.inv ≫ e.p = e'.p := by
    rw [← h.hom_p]
    simp
  have h_inv_comm : (d'.middleMap ≫ h.middleIso.inv) ≫ e.p = out'.p ≫ a := by
    rw [Category.assoc, h_inv_p, d'.map_p]
  let homMap : out.middle ⟶ out'.middle :=
    d'.isPullback.lift (d.middleMap ≫ h.middleIso.hom) out.p h_hom_comm
  let invMap : out'.middle ⟶ out.middle :=
    d.isPullback.lift (d'.middleMap ≫ h.middleIso.inv) out'.p h_inv_comm
  have hom_fst : homMap ≫ d'.middleMap = d.middleMap ≫ h.middleIso.hom := by
    change d'.isPullback.lift (d.middleMap ≫ h.middleIso.hom) out.p h_hom_comm ≫
        d'.middleMap =
      d.middleMap ≫ h.middleIso.hom
    exact d'.isPullback.lift_fst (d.middleMap ≫ h.middleIso.hom) out.p h_hom_comm
  have hom_snd : homMap ≫ out'.p = out.p := by
    change d'.isPullback.lift (d.middleMap ≫ h.middleIso.hom) out.p h_hom_comm ≫
        out'.p =
      out.p
    exact d'.isPullback.lift_snd (d.middleMap ≫ h.middleIso.hom) out.p h_hom_comm
  have inv_fst : invMap ≫ d.middleMap = d'.middleMap ≫ h.middleIso.inv := by
    change d.isPullback.lift (d'.middleMap ≫ h.middleIso.inv) out'.p h_inv_comm ≫
        d.middleMap =
      d'.middleMap ≫ h.middleIso.inv
    exact d.isPullback.lift_fst (d'.middleMap ≫ h.middleIso.inv) out'.p h_inv_comm
  have inv_snd : invMap ≫ out.p = out'.p := by
    change d.isPullback.lift (d'.middleMap ≫ h.middleIso.inv) out'.p h_inv_comm ≫
        out.p =
      out'.p
    exact d.isPullback.lift_snd (d'.middleMap ≫ h.middleIso.inv) out'.p h_inv_comm
  refine
    { middleIso :=
        { hom := homMap
          inv := invMap
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      i_hom := ?_
      hom_p := hom_snd }
  · apply d.isPullback.hom_ext
    · rw [Category.assoc, inv_fst, ← Category.assoc, hom_fst, Category.assoc,
        h.middleIso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, inv_snd, hom_snd, Category.id_comp]
  · apply d'.isPullback.hom_ext
    · rw [Category.assoc, hom_fst, ← Category.assoc, inv_fst, Category.assoc,
        h.middleIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hom_snd, inv_snd, Category.id_comp]
  · apply d'.isPullback.hom_ext
    · rw [Category.assoc, hom_fst, ← Category.assoc, d.i_map, h.i_hom, d'.i_map]
    · rw [Category.assoc, hom_snd, out.zero, out'.zero]

/-- Pullback data transports an isomorphism of output one-fold extensions. -/
noncomputable def isoOut {X X' Y : C} {e : ShortExactExtension X Y}
    {a : X' ⟶ X} {out out' : ShortExactExtension X' Y}
    (d : PullbackData e a out) (h : Iso out out') : PullbackData e a out' where
  middleMap := h.middleIso.inv ≫ d.middleMap
  i_map := by
    have hi : out'.i ≫ h.middleIso.inv = out.i := by
      rw [← h.i_hom, Category.assoc, h.middleIso.hom_inv_id, Category.comp_id]
    calc
      out'.i ≫ (h.middleIso.inv ≫ d.middleMap) =
          (out'.i ≫ h.middleIso.inv) ≫ d.middleMap := by rw [Category.assoc]
      _ = out.i ≫ d.middleMap := by rw [hi]
      _ = e.i := d.i_map
  map_p := by
    have hp : h.middleIso.inv ≫ out.p = out'.p := by
      rw [← h.hom_p, ← Category.assoc, h.middleIso.inv_hom_id, Category.id_comp]
    rw [Category.assoc, d.map_p, ← Category.assoc, hp]
  isPullback := by
    refine d.isPullback.of_iso' h.middleIso.symm (CategoryTheory.Iso.refl _)
      (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · have hp : h.middleIso.inv ≫ out.p = out'.p := by
        rw [← h.hom_p, ← Category.assoc, h.middleIso.inv_hom_id, Category.id_comp]
      simpa using hp
    · simp
    · simp

end PullbackData

/-- Diagrammatic data identifying an extension pushed out along a kernel-endpoint map. -/
structure PushoutData {X Y Y' : C}
    (e : ShortExactExtension X Y) (a : Y ⟶ Y') (out : ShortExactExtension X Y') where
  middleMap : e.middle ⟶ out.middle
  i_map : a ≫ out.i = e.i ≫ middleMap
  map_p : middleMap ≫ out.p = e.p
  isPushout : IsPushout e.i a middleMap out.i

namespace PushoutData

/-- Pushout data transports an isomorphism of input one-fold extensions. -/
noncomputable def iso {X Y Y' : C} {e e' : ShortExactExtension X Y}
    {a : Y ⟶ Y'} {out out' : ShortExactExtension X Y'}
    (d : PushoutData e a out) (d' : PushoutData e' a out') (h : Iso e e') :
    Iso out out' := by
  have h_hom_comm : e.i ≫ h.middleIso.hom ≫ d'.middleMap = a ≫ out'.i := by
    rw [← Category.assoc, h.i_hom, ← d'.i_map]
  have h_inv_i : e'.i ≫ h.middleIso.inv = e.i := by
    rw [← h.i_hom]
    simp [Category.assoc]
  have h_inv_comm : e'.i ≫ h.middleIso.inv ≫ d.middleMap = a ≫ out.i := by
    rw [← Category.assoc, h_inv_i, ← d.i_map]
  let homMap : out.middle ⟶ out'.middle :=
    d.isPushout.desc (h.middleIso.hom ≫ d'.middleMap) out'.i h_hom_comm
  let invMap : out'.middle ⟶ out.middle :=
    d'.isPushout.desc (h.middleIso.inv ≫ d.middleMap) out.i h_inv_comm
  have hom_inl : d.middleMap ≫ homMap = h.middleIso.hom ≫ d'.middleMap := by
    change d.middleMap ≫
        d.isPushout.desc (h.middleIso.hom ≫ d'.middleMap) out'.i h_hom_comm =
      h.middleIso.hom ≫ d'.middleMap
    exact d.isPushout.inl_desc (h.middleIso.hom ≫ d'.middleMap) out'.i h_hom_comm
  have hom_inr : out.i ≫ homMap = out'.i := by
    change out.i ≫
        d.isPushout.desc (h.middleIso.hom ≫ d'.middleMap) out'.i h_hom_comm =
      out'.i
    exact d.isPushout.inr_desc (h.middleIso.hom ≫ d'.middleMap) out'.i h_hom_comm
  have inv_inl : d'.middleMap ≫ invMap = h.middleIso.inv ≫ d.middleMap := by
    change d'.middleMap ≫
        d'.isPushout.desc (h.middleIso.inv ≫ d.middleMap) out.i h_inv_comm =
      h.middleIso.inv ≫ d.middleMap
    exact d'.isPushout.inl_desc (h.middleIso.inv ≫ d.middleMap) out.i h_inv_comm
  have inv_inr : out'.i ≫ invMap = out.i := by
    change out'.i ≫
        d'.isPushout.desc (h.middleIso.inv ≫ d.middleMap) out.i h_inv_comm =
      out.i
    exact d'.isPushout.inr_desc (h.middleIso.inv ≫ d.middleMap) out.i h_inv_comm
  refine
    { middleIso :=
        { hom := homMap
          inv := invMap
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      i_hom := hom_inr
      hom_p := ?_ }
  · apply d.isPushout.hom_ext
    · rw [Category.comp_id, ← Category.assoc, hom_inl, Category.assoc, inv_inl,
        ← Category.assoc, h.middleIso.hom_inv_id, Category.id_comp]
    · rw [Category.comp_id, ← Category.assoc, hom_inr, inv_inr]
  · apply d'.isPushout.hom_ext
    · rw [Category.comp_id, ← Category.assoc, inv_inl, Category.assoc, hom_inl,
        ← Category.assoc, h.middleIso.inv_hom_id, Category.id_comp]
    · rw [Category.comp_id, ← Category.assoc, inv_inr, hom_inr]
  · apply d.isPushout.hom_ext
    · rw [← Category.assoc, hom_inl, Category.assoc, d'.map_p, h.hom_p, d.map_p]
    · rw [← Category.assoc, hom_inr, out'.zero, out.zero]

/-- Pushout data transports an isomorphism of output one-fold extensions. -/
noncomputable def isoOut {X Y Y' : C} {e : ShortExactExtension X Y}
    {a : Y ⟶ Y'} {out out' : ShortExactExtension X Y'}
    (d : PushoutData e a out) (h : Iso out out') : PushoutData e a out' where
  middleMap := d.middleMap ≫ h.middleIso.hom
  i_map := by
    calc
      a ≫ out'.i = a ≫ (out.i ≫ h.middleIso.hom) := by rw [h.i_hom]
      _ = (a ≫ out.i) ≫ h.middleIso.hom := by rw [Category.assoc]
      _ = (e.i ≫ d.middleMap) ≫ h.middleIso.hom := by rw [d.i_map]
      _ = e.i ≫ d.middleMap ≫ h.middleIso.hom := by rw [Category.assoc]
  map_p := by
    rw [Category.assoc, h.hom_p, d.map_p]
  isPushout := by
    refine d.isPushout.of_iso (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
      (CategoryTheory.Iso.refl _) h.middleIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simpa using h.i_hom

end PushoutData

end ShortExactExtension

namespace MetrizableLCA

/--
Build a one-fold exact-category extension from a strict short exact sequence in
the canonical metrizable LCA exact category.
-/
def shortExactExtensionOfStrictShortExact
    {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0) (h : strictShortExact (ShortComplex.mk i p zero)) :
    ShortExactExtension (C := MetrizableLCA.{u}) X Y where
  middle := M
  i := i
  p := p
  zero := zero
  conflation := quillenConflation_of_strictShortExact h

@[simp]
lemma shortExactExtensionOfStrictShortExact_shortComplex
    {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0) (h : strictShortExact (ShortComplex.mk i p zero)) :
    (shortExactExtensionOfStrictShortExact i p zero h).shortComplex =
      ShortComplex.mk i p zero :=
  rfl

/-- A one-fold extension over `MetrizableLCA` recovers a strict short exact sequence. -/
theorem strictShortExact_of_shortExactExtension
    {X Y : MetrizableLCA.{u}} (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    strictShortExact e.shortComplex :=
  strictShortExact_of_quillenConflation e.conflation

/-- The strict sequence used to build the one-fold extension is recovered immediately. -/
theorem strictShortExact_shortExactExtensionOfStrictShortExact
    {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0) (h : strictShortExact (ShortComplex.mk i p zero)) :
    strictShortExact (shortExactExtensionOfStrictShortExact i p zero h).shortComplex := by
  simpa using h

/-- The strict short exact sequence extension has an inflation as its left map. -/
theorem shortExactExtensionOfStrictShortExact_inflation_i
    {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0) (h : strictShortExact (ShortComplex.mk i p zero)) :
    QuillenExactCategory.inflation i :=
  (shortExactExtensionOfStrictShortExact i p zero h).inflation_i

/-- The strict short exact sequence extension has a deflation as its right map. -/
theorem shortExactExtensionOfStrictShortExact_deflation_p
    {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0) (h : strictShortExact (ShortComplex.mk i p zero)) :
    QuillenExactCategory.deflation p :=
  (shortExactExtensionOfStrictShortExact i p zero h).deflation_p

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

/-- Diagrammatic witness for the canonical pullback of a one-fold extension. -/
noncomputable def shortExactExtensionPullbackData
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : X' ⟶ X) :
    ShortExactExtension.PullbackData e a (shortExactExtensionPullback e a) where
  middleMap := pullbackSnd a e.p
  i_map := shortExactExtensionPullback_i_map e a
  map_p := shortExactExtensionPullback_map_p e a
  isPullback := (IsPullback.of_isLimit (pullbackIsLimit a e.p)).flip

/-- The identity pullback square of a one-fold extension. -/
noncomputable def shortExactExtensionPullbackIdData
    {X Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    ShortExactExtension.PullbackData e (𝟙 X) e where
  middleMap := 𝟙 e.middle
  i_map := by simp
  map_p := by simp
  isPullback := by
    simpa using (IsPullback.of_id_fst (f := e.p))

/-- Canonical pullback along the identity is isomorphic to the original one-fold extension. -/
noncomputable def shortExactExtensionPullbackIdIso
    {X Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    ShortExactExtension.Iso (shortExactExtensionPullback e (𝟙 X)) e :=
  ShortExactExtension.PullbackData.iso
    (shortExactExtensionPullbackData e (𝟙 X))
    (shortExactExtensionPullbackIdData e)
    (ShortExactExtension.Iso.refl e)

/-- Canonical pullback preserves isomorphism of one-fold extensions. -/
noncomputable def shortExactExtensionPullbackIso
    {X X' Y : MetrizableLCA.{u}}
    {e e' : ShortExactExtension (C := MetrizableLCA.{u}) X Y}
    (a : X' ⟶ X) (h : ShortExactExtension.Iso e e') :
    ShortExactExtension.Iso (shortExactExtensionPullback e a)
      (shortExactExtensionPullback e' a) := by
  let homMap : pullbackObj a e.p ⟶ pullbackObj a e'.p :=
    pullbackLift a e'.p (pullbackFst a e.p) (pullbackSnd a e.p ≫ h.middleIso.hom) (by
      rw [Category.assoc, h.hom_p]
      exact pullback_condition a e.p)
  have h_inv_p : h.middleIso.inv ≫ e.p = e'.p := by
    rw [← h.hom_p, ← Category.assoc, h.middleIso.inv_hom_id, Category.id_comp]
  let invMap : pullbackObj a e'.p ⟶ pullbackObj a e.p :=
    pullbackLift a e.p (pullbackFst a e'.p) (pullbackSnd a e'.p ≫ h.middleIso.inv) (by
      rw [Category.assoc, h_inv_p]
      exact pullback_condition a e'.p)
  have hom_fst : homMap ≫ pullbackFst a e'.p = pullbackFst a e.p := by
    dsimp [homMap]
    rw [pullbackLift_fst]
  have hom_snd : homMap ≫ pullbackSnd a e'.p = pullbackSnd a e.p ≫ h.middleIso.hom := by
    dsimp [homMap]
    rw [pullbackLift_snd]
  have inv_fst : invMap ≫ pullbackFst a e.p = pullbackFst a e'.p := by
    dsimp [invMap]
    rw [pullbackLift_fst]
  have inv_snd : invMap ≫ pullbackSnd a e.p = pullbackSnd a e'.p ≫ h.middleIso.inv := by
    dsimp [invMap]
    rw [pullbackLift_snd]
  refine
    { middleIso :=
        { hom := homMap
          inv := invMap
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      i_hom := ?_
      hom_p := ?_ }
  · apply pullback_hom_ext a e.p
    · change homMap ≫ (invMap ≫ pullbackFst a e.p) = pullbackFst a e.p
      rw [inv_fst, hom_fst]
    · change homMap ≫ (invMap ≫ pullbackSnd a e.p) = pullbackSnd a e.p
      rw [inv_snd]
      change (homMap ≫ pullbackSnd a e'.p) ≫ h.middleIso.inv = pullbackSnd a e.p
      rw [hom_snd]
      simp [Category.assoc]
  · apply pullback_hom_ext a e'.p
    · change invMap ≫ (homMap ≫ pullbackFst a e'.p) = pullbackFst a e'.p
      rw [hom_fst, inv_fst]
    · change invMap ≫ (homMap ≫ pullbackSnd a e'.p) = pullbackSnd a e'.p
      rw [hom_snd]
      change (invMap ≫ pullbackSnd a e.p) ≫ h.middleIso.hom = pullbackSnd a e'.p
      rw [inv_snd]
      simp [Category.assoc]
  · apply pullback_hom_ext a e'.p
    · calc
        ((shortExactExtensionPullback e a).i ≫ homMap) ≫ pullbackFst a e'.p =
            (shortExactExtensionPullback e a).i ≫ (homMap ≫ pullbackFst a e'.p) :=
              Category.assoc _ _ _
        _ = (shortExactExtensionPullback e a).i ≫ pullbackFst a e.p := by
              exact congrArg (fun k => (shortExactExtensionPullback e a).i ≫ k) hom_fst
        _ = 0 :=
              (shortExactExtensionPullback e a).zero
        _ = (shortExactExtensionPullback e' a).i ≫ pullbackFst a e'.p :=
              ((shortExactExtensionPullback e' a).zero).symm
    · calc
        ((shortExactExtensionPullback e a).i ≫ homMap) ≫ pullbackSnd a e'.p =
            (shortExactExtensionPullback e a).i ≫ (homMap ≫ pullbackSnd a e'.p) :=
              Category.assoc _ _ _
        _ = (shortExactExtensionPullback e a).i ≫
              (pullbackSnd a e.p ≫ h.middleIso.hom) := by
              exact congrArg (fun k => (shortExactExtensionPullback e a).i ≫ k) hom_snd
        _ = ((shortExactExtensionPullback e a).i ≫ pullbackSnd a e.p) ≫
              h.middleIso.hom :=
              (Category.assoc _ _ _).symm
        _ = e.i ≫ h.middleIso.hom := by
              exact congrArg (fun k => k ≫ h.middleIso.hom)
                (shortExactExtensionPullback_i_map e a)
        _ = e'.i := h.i_hom
        _ = (shortExactExtensionPullback e' a).i ≫ pullbackSnd a e'.p :=
              (shortExactExtensionPullback_i_map e' a).symm
  · exact hom_fst

/-- Canonical pullback preserves isomorphism of one-fold extensions over endpoint isomorphisms. -/
noncomputable def shortExactExtensionPullbackIsoBetween
    {X X' Y Y' : MetrizableLCA.{u}} {β : Y ≅ Y'}
    {e : ShortExactExtension (C := MetrizableLCA.{u}) X Y}
    {e' : ShortExactExtension (C := MetrizableLCA.{u}) X Y'}
    (a : X' ⟶ X)
    (h : ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X) β e e') :
    ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X') β
      (shortExactExtensionPullback e a) (shortExactExtensionPullback e' a) := by
  have h_hom_p : h.middleIso.hom ≫ e'.p = e.p := by
    simpa using h.hom_p
  let homMap : pullbackObj a e.p ⟶ pullbackObj a e'.p :=
    pullbackLift a e'.p (pullbackFst a e.p) (pullbackSnd a e.p ≫ h.middleIso.hom) (by
      rw [Category.assoc, h_hom_p]
      exact pullback_condition a e.p)
  have h_inv_p : h.middleIso.inv ≫ e.p = e'.p := by
    rw [← h_hom_p, ← Category.assoc, h.middleIso.inv_hom_id, Category.id_comp]
  let invMap : pullbackObj a e'.p ⟶ pullbackObj a e.p :=
    pullbackLift a e.p (pullbackFst a e'.p) (pullbackSnd a e'.p ≫ h.middleIso.inv) (by
      rw [Category.assoc, h_inv_p]
      exact pullback_condition a e'.p)
  have hom_fst : homMap ≫ pullbackFst a e'.p = pullbackFst a e.p := by
    dsimp [homMap]
    rw [pullbackLift_fst]
  have hom_snd : homMap ≫ pullbackSnd a e'.p = pullbackSnd a e.p ≫ h.middleIso.hom := by
    dsimp [homMap]
    rw [pullbackLift_snd]
  have inv_fst : invMap ≫ pullbackFst a e.p = pullbackFst a e'.p := by
    dsimp [invMap]
    rw [pullbackLift_fst]
  have inv_snd : invMap ≫ pullbackSnd a e.p = pullbackSnd a e'.p ≫ h.middleIso.inv := by
    dsimp [invMap]
    rw [pullbackLift_snd]
  refine
    { middleIso :=
        { hom := homMap
          inv := invMap
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      i_hom := ?_
      hom_p := ?_ }
  · apply pullback_hom_ext a e.p
    · change homMap ≫ (invMap ≫ pullbackFst a e.p) = pullbackFst a e.p
      rw [inv_fst, hom_fst]
    · change homMap ≫ (invMap ≫ pullbackSnd a e.p) = pullbackSnd a e.p
      rw [inv_snd]
      change (homMap ≫ pullbackSnd a e'.p) ≫ h.middleIso.inv = pullbackSnd a e.p
      rw [hom_snd]
      simp [Category.assoc]
  · apply pullback_hom_ext a e'.p
    · change invMap ≫ (homMap ≫ pullbackFst a e'.p) = pullbackFst a e'.p
      rw [hom_fst, inv_fst]
    · change invMap ≫ (homMap ≫ pullbackSnd a e'.p) = pullbackSnd a e'.p
      rw [hom_snd]
      change (invMap ≫ pullbackSnd a e.p) ≫ h.middleIso.hom = pullbackSnd a e'.p
      rw [inv_snd]
      simp [Category.assoc]
  · apply pullback_hom_ext a e'.p
    · calc
        ((shortExactExtensionPullback e a).i ≫ homMap) ≫ pullbackFst a e'.p =
            (shortExactExtensionPullback e a).i ≫ (homMap ≫ pullbackFst a e'.p) :=
              Category.assoc _ _ _
        _ = (shortExactExtensionPullback e a).i ≫ pullbackFst a e.p := by
              exact congrArg (fun k => (shortExactExtensionPullback e a).i ≫ k) hom_fst
        _ = 0 :=
              (shortExactExtensionPullback e a).zero
        _ = β.hom ≫ 0 := by
              rw [comp_zero]
        _ = β.hom ≫ ((shortExactExtensionPullback e' a).i ≫ pullbackFst a e'.p) := by
              exact congrArg (fun k => β.hom ≫ k)
                ((shortExactExtensionPullback e' a).zero).symm
        _ = (β.hom ≫ (shortExactExtensionPullback e' a).i) ≫ pullbackFst a e'.p :=
              (Category.assoc _ _ _).symm
    · calc
        ((shortExactExtensionPullback e a).i ≫ homMap) ≫ pullbackSnd a e'.p =
            (shortExactExtensionPullback e a).i ≫ (homMap ≫ pullbackSnd a e'.p) :=
              Category.assoc _ _ _
        _ = (shortExactExtensionPullback e a).i ≫
              (pullbackSnd a e.p ≫ h.middleIso.hom) := by
              exact congrArg (fun k => (shortExactExtensionPullback e a).i ≫ k) hom_snd
        _ = ((shortExactExtensionPullback e a).i ≫ pullbackSnd a e.p) ≫
              h.middleIso.hom :=
              (Category.assoc _ _ _).symm
        _ = e.i ≫ h.middleIso.hom := by
              exact congrArg (fun k => k ≫ h.middleIso.hom)
                (shortExactExtensionPullback_i_map e a)
        _ = β.hom ≫ e'.i := h.i_hom
        _ = β.hom ≫ ((shortExactExtensionPullback e' a).i ≫ pullbackSnd a e'.p) := by
              rw [shortExactExtensionPullback_i_map]
  · simpa using hom_fst

/--
Canonical pullbacks along maps related by a quotient-endpoint isomorphism are
isomorphic over that endpoint isomorphism.
-/
noncomputable def shortExactExtensionPullbackDomainIsoBetween
    {X X' Y W : MetrizableLCA.{u}} (α : X ≅ X')
    (e : ShortExactExtension (C := MetrizableLCA.{u}) Y W)
    (f : X ⟶ Y) (g : X' ⟶ Y) (hfg : f = α.hom ≫ g) :
    ShortExactExtension.IsoBetween α (CategoryTheory.Iso.refl W)
      (shortExactExtensionPullback e f) (shortExactExtensionPullback e g) := by
  have hgf : α.inv ≫ f = g := by
    rw [hfg]
    simp
  let homMap : pullbackObj f e.p ⟶ pullbackObj g e.p :=
    pullbackLift g e.p (pullbackFst f e.p ≫ α.hom) (pullbackSnd f e.p) (by
      rw [Category.assoc, ← hfg]
      exact pullback_condition f e.p)
  let invMap : pullbackObj g e.p ⟶ pullbackObj f e.p :=
    pullbackLift f e.p (pullbackFst g e.p ≫ α.inv) (pullbackSnd g e.p) (by
      rw [Category.assoc, hgf]
      exact pullback_condition g e.p)
  have hom_fst : homMap ≫ pullbackFst g e.p = pullbackFst f e.p ≫ α.hom := by
    dsimp [homMap]
    rw [pullbackLift_fst]
  have hom_snd : homMap ≫ pullbackSnd g e.p = pullbackSnd f e.p := by
    dsimp [homMap]
    rw [pullbackLift_snd]
  have inv_fst : invMap ≫ pullbackFst f e.p = pullbackFst g e.p ≫ α.inv := by
    dsimp [invMap]
    rw [pullbackLift_fst]
  have inv_snd : invMap ≫ pullbackSnd f e.p = pullbackSnd g e.p := by
    dsimp [invMap]
    rw [pullbackLift_snd]
  refine
    { middleIso :=
        { hom := homMap
          inv := invMap
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      i_hom := ?_
      hom_p := ?_ }
  · apply pullback_hom_ext f e.p
    · change homMap ≫ (invMap ≫ pullbackFst f e.p) = pullbackFst f e.p
      rw [inv_fst]
      simpa [Category.assoc] using congrArg (fun q => q ≫ α.inv) hom_fst
    · change homMap ≫ (invMap ≫ pullbackSnd f e.p) = pullbackSnd f e.p
      rw [inv_snd, hom_snd]
  · apply pullback_hom_ext g e.p
    · change invMap ≫ (homMap ≫ pullbackFst g e.p) = pullbackFst g e.p
      rw [hom_fst]
      simpa [Category.assoc] using congrArg (fun q => q ≫ α.hom) inv_fst
    · change invMap ≫ (homMap ≫ pullbackSnd g e.p) = pullbackSnd g e.p
      rw [hom_snd, inv_snd]
  · apply pullback_hom_ext g e.p
    · simpa [Category.assoc, hom_fst, shortExactExtensionPullback] using
        congrArg (fun q => q ≫ α.hom) (shortExactExtensionPullback e f).zero
    · calc
        ((shortExactExtensionPullback e f).i ≫ homMap) ≫ pullbackSnd g e.p =
            (shortExactExtensionPullback e f).i ≫ pullbackSnd f e.p := by
              simpa [Category.assoc] using
                congrArg (fun q => (shortExactExtensionPullback e f).i ≫ q) hom_snd
        _ = e.i := shortExactExtensionPullback_i_map e f
        _ = (shortExactExtensionPullback e g).i ≫ pullbackSnd g e.p :=
              (shortExactExtensionPullback_i_map e g).symm
        _ = ((CategoryTheory.Iso.refl W).hom ≫ (shortExactExtensionPullback e g).i) ≫
              pullbackSnd g e.p := by simp
  · exact hom_fst

/-- The explicit pullback of a split short complex is split. -/
noncomputable def pullbackSplitting
    {S : ShortComplex MetrizableLCA.{u}} {Y : MetrizableLCA.{u}}
    (a : Y ⟶ S.X₃) (s : S.Splitting) :
    (ShortComplex.mk (pullbackKernelMap a S.g S.f S.zero) (pullbackFst a S.g)
      (pullbackKernelMap_fst a S.g S.f S.zero)).Splitting := by
  let r : pullbackObj a S.g ⟶ S.X₁ :=
    pullbackSnd a S.g ≫ s.r
  let sec : Y ⟶ pullbackObj a S.g :=
    pullbackLift a S.g (𝟙 Y) (a ≫ s.s) (by
      rw [Category.id_comp, Category.assoc, s.s_g, Category.comp_id])
  refine
    { r := r
      s := sec
      f_r := ?_
      s_g := ?_
      id := ?_ }
  · dsimp [r]
    rw [← Category.assoc, pullbackKernelMap_snd, s.f_r]
  · dsimp [sec]
    rw [pullbackLift_fst]
  · dsimp [r, sec]
    apply pullback_hom_ext a S.g
    · rw [CategoryTheory.Preadditive.add_comp (C := MetrizableLCA.{u})]
      rw [Category.assoc, pullbackKernelMap_fst]
      rw [comp_zero, zero_add]
      simp [Category.assoc, pullbackLift_fst]
    · rw [CategoryTheory.Preadditive.add_comp (C := MetrizableLCA.{u})]
      rw [Category.assoc, pullbackKernelMap_snd]
      simp only [Category.assoc, pullbackLift_snd]
      change (pullbackSnd a S.g ≫ s.r) ≫ S.f + (pullbackFst a S.g ≫ a) ≫ s.s =
        𝟙 (pullbackObj a S.g) ≫ pullbackSnd a S.g
      rw [pullback_condition]
      rw [Category.assoc, Category.assoc]
      rw [← CategoryTheory.Preadditive.comp_add (C := MetrizableLCA.{u})
        (pullbackObj a S.g) S.X₂ S.X₂ (pullbackSnd a S.g)
        (s.r ≫ S.f) (S.g ≫ s.s)]
      rw [s.id]
      simp

/-- The canonical pullback of a split one-fold extension is split. -/
noncomputable def shortExactExtensionPullbackSplitting
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : X' ⟶ X)
    (s : e.shortComplex.Splitting) :
    (shortExactExtensionPullback e a).shortComplex.Splitting := by
  simpa [shortExactExtensionPullback, ShortExactExtension.shortComplex] using
    pullbackSplitting (S := e.shortComplex) a s

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

@[simp]
lemma shortExactExtensionPushout_inr_p
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y') :
    pushoutInr (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a) ≫
        (shortExactExtensionPushout e a).p = 0 :=
  pushoutInr_cokernel (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)

/-- The pushed-out one-fold extension has kernel of `p` equal to range of `i`. -/
theorem shortExactExtensionPushout_kernel_iff_range_i
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y')
    (q : (shortExactExtensionPushout e a).middle) :
    (shortExactExtensionPushout e a).p q = 0 ↔
      ∃ y : Y', (shortExactExtensionPushout e a).i y = q := by
  change
    pushoutCokernelMap (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a) q = 0 ↔
      ∃ y : Y',
        pushoutInr (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a) y = q
  exact pushoutCokernelMap_kernel_iff_range_inr (S := e.shortComplex) e.conflation a
    (pushoutSubgroup_closed e.conflation a) q

/-- Diagrammatic witness for the canonical pushout of a one-fold extension. -/
noncomputable def shortExactExtensionPushoutData
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y') :
    ShortExactExtension.PushoutData e a (shortExactExtensionPushout e a) where
  middleMap :=
    pushoutInl (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a)
  i_map := shortExactExtensionPushout_i e a
  map_p := shortExactExtensionPushout_map_p e a
  isPushout :=
    IsPushout.of_isColimit
      (pushoutIsColimit (S := e.shortComplex) a
        (pushoutSubgroup_closed e.conflation a))

/-- Canonical pushout along the identity is the original one-fold extension. -/
noncomputable def shortExactExtensionPushoutIdData
    {X Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    ShortExactExtension.PushoutData e (𝟙 Y) e where
  middleMap := 𝟙 e.middle
  i_map := by simp
  map_p := by simp
  isPushout := by
    simpa using (IsPushout.of_id_snd (f := e.i))

/-- Canonical pushout along the identity is isomorphic to the original one-fold extension. -/
noncomputable def shortExactExtensionPushoutIdIso
    {X Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    ShortExactExtension.Iso (shortExactExtensionPushout e (𝟙 Y)) e :=
  ShortExactExtension.PushoutData.iso
    (shortExactExtensionPushoutData e (𝟙 Y))
    (shortExactExtensionPushoutIdData e)
    (ShortExactExtension.Iso.refl e)

/-- Pullback preserves the canonical identity-tail pushout up to the existing input isomorphism. -/
noncomputable def shortExactExtensionPullbackPushoutIdIso
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) :
    ShortExactExtension.Iso
      (shortExactExtensionPullback (shortExactExtensionPushout e (𝟙 Y)) f)
      (shortExactExtensionPullback e f) :=
  shortExactExtensionPullbackIso f (shortExactExtensionPushoutIdIso e)

/-- Pulling back an identity-tail pushout supplies the expected identity pushout data. -/
noncomputable def shortExactExtensionPullbackPushoutIdData
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) :
    ShortExactExtension.PushoutData
      (shortExactExtensionPullback e f) (𝟙 Y)
      (shortExactExtensionPullback (shortExactExtensionPushout e (𝟙 Y)) f) :=
  ShortExactExtension.PushoutData.isoOut
    (shortExactExtensionPushoutIdData (shortExactExtensionPullback e f))
    (shortExactExtensionPullbackPushoutIdIso e f).symm

/-- The canonical comparison map from pulling back before a tail pushout
to pulling back after it. -/
noncomputable def shortExactExtensionPullbackPushoutMiddleMap
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    (shortExactExtensionPullback e f).middle ⟶
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle :=
  let q : e.middle ⟶ (shortExactExtensionPushout e g).middle :=
    pushoutInl (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)
  pullbackLift f (shortExactExtensionPushout e g).p
    (pullbackFst f e.p)
    (pullbackSnd f e.p ≫ q)
    (by
      have hp : q ≫ (shortExactExtensionPushout e g).p = e.p :=
        shortExactExtensionPushout_map_p e g
      exact (pullback_condition f e.p).trans
        ((congrArg (fun k => pullbackSnd f e.p ≫ k) hp.symm).trans
          (Category.assoc (pullbackSnd f e.p) q (shortExactExtensionPushout e g).p).symm))

@[simp]
lemma shortExactExtensionPullbackPushoutMiddleMap_fst
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    shortExactExtensionPullbackPushoutMiddleMap e f g ≫
        pullbackFst f (shortExactExtensionPushout e g).p =
      pullbackFst f e.p := by
  dsimp [shortExactExtensionPullbackPushoutMiddleMap]
  exact pullbackLift_fst f (shortExactExtensionPushout e g).p (pullbackFst f e.p)
    (pullbackSnd f e.p ≫ pushoutInl (S := e.shortComplex) g
      (pushoutSubgroup_closed e.conflation g)) _

@[simp]
lemma shortExactExtensionPullbackPushoutMiddleMap_snd
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    shortExactExtensionPullbackPushoutMiddleMap e f g ≫
        pullbackSnd f (shortExactExtensionPushout e g).p =
      pullbackSnd f e.p ≫
        pushoutInl (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) := by
  dsimp [shortExactExtensionPullbackPushoutMiddleMap]
  exact pullbackLift_snd f (shortExactExtensionPushout e g).p (pullbackFst f e.p)
    (pullbackSnd f e.p ≫ pushoutInl (S := e.shortComplex) g
      (pushoutSubgroup_closed e.conflation g)) _

@[simp]
lemma shortExactExtensionPullbackPushoutMiddleMap_p
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    shortExactExtensionPullbackPushoutMiddleMap e f g ≫
        (shortExactExtensionPullback (shortExactExtensionPushout e g) f).p =
      (shortExactExtensionPullback e f).p := by
  exact shortExactExtensionPullbackPushoutMiddleMap_fst e f g

@[simp]
lemma shortExactExtensionPullbackPushoutMiddleMap_i
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    g ≫ (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i =
      (shortExactExtensionPullback e f).i ≫
        shortExactExtensionPullbackPushoutMiddleMap e f g := by
  apply pullback_hom_ext f (shortExactExtensionPushout e g).p
  · ext y
    rfl
  · let q : e.middle ⟶ (shortExactExtensionPushout e g).middle :=
      pushoutInl (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)
    calc
      (g ≫ (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) ≫
          pullbackSnd f (shortExactExtensionPushout e g).p =
          g ≫ ((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
            pullbackSnd f (shortExactExtensionPushout e g).p) :=
        Category.assoc _ _ _
      _ = g ≫ (shortExactExtensionPushout e g).i := by
        exact congrArg (fun k => g ≫ k)
          (shortExactExtensionPullback_i_map (shortExactExtensionPushout e g) f)
      _ = e.i ≫ q := shortExactExtensionPushout_i e g
      _ = ((shortExactExtensionPullback e f).i ≫ pullbackSnd f e.p) ≫ q := by
        exact congrArg (fun k => k ≫ q) (shortExactExtensionPullback_i_map e f).symm
      _ = (shortExactExtensionPullback e f).i ≫ (pullbackSnd f e.p ≫ q) :=
        Category.assoc _ _ _
      _ = (shortExactExtensionPullback e f).i ≫
            (shortExactExtensionPullbackPushoutMiddleMap e f g ≫
              pullbackSnd f (shortExactExtensionPushout e g).p) := by
        exact congrArg (fun k => (shortExactExtensionPullback e f).i ≫ k)
          (shortExactExtensionPullbackPushoutMiddleMap_snd e f g).symm
      _ = ((shortExactExtensionPullback e f).i ≫
              shortExactExtensionPullbackPushoutMiddleMap e f g) ≫
            pullbackSnd f (shortExactExtensionPushout e g).p :=
        (Category.assoc _ _ _).symm

/-- Reassociate the product of a pulled-back middle term with the pullback of
the pushout quotient product map. -/
noncomputable def shortExactExtensionPullbackPushoutProductHomeomorph
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y' ≃ₜ
      pullbackObj f
        (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) ≫
          pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)) where
  toEquiv :=
    { toFun := fun p => ⟨(p.1.1.1, (p.1.1.2, p.2)), by
        change f p.1.1.1 =
          (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) ≫
            pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g))
              (p.1.1.2, p.2)
        rw [pushoutQuotientMap_cokernel]
        change f p.1.1.1 = e.p p.1.1.2
        exact p.1.2⟩
      invFun := fun z => (⟨(z.1.1, z.1.2.1), by
        change f z.1.1 = e.p z.1.2.1
        rw [z.2]
        change (pushoutProductToCokernel e.shortComplex Y') z.1.2 = e.p z.1.2.1
        rfl⟩, z.1.2.2)
      left_inv := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          apply Prod.ext <;> rfl
        · rfl
      right_inv := by
        intro z
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Prod.ext <;> rfl }
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((pullbackFst f e.p).hom.continuous.comp continuous_fst).prodMk
      (((pullbackSnd f e.p).hom.continuous.comp continuous_fst).prodMk continuous_snd)
  continuous_invFun := by
    have hfirst : Continuous (fun z : pullbackObj f
        (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) ≫
          pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)) =>
        (⟨(z.1.1, z.1.2.1), by
          change f z.1.1 = e.p z.1.2.1
          rw [z.2]
          change (pushoutProductToCokernel e.shortComplex Y') z.1.2 = e.p z.1.2.1
          rfl⟩ : pullbackObj f e.p)) := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.fst.prodMk (continuous_fst.comp continuous_subtype_val.snd)
    exact hfirst.prodMk (continuous_snd.comp continuous_subtype_val.snd)

/-- The induced map from the canonical pushout of the pulled-back extension
to the pullback of the canonical pushout. -/
noncomputable def shortExactExtensionPullbackPushoutComparisonMap
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    (shortExactExtensionPushout (shortExactExtensionPullback e f) g).middle ⟶
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle :=
  pushoutDesc (S := (shortExactExtensionPullback e f).shortComplex) g
    (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g)
    (shortExactExtensionPullbackPushoutMiddleMap e f g)
    (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i
    (shortExactExtensionPullbackPushoutMiddleMap_i e f g).symm

@[simp]
lemma shortExactExtensionPullbackPushoutComparisonMap_inl
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    pushoutInl (S := (shortExactExtensionPullback e f).shortComplex) g
        (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g) ≫
        shortExactExtensionPullbackPushoutComparisonMap e f g =
      shortExactExtensionPullbackPushoutMiddleMap e f g := by
  dsimp [shortExactExtensionPullbackPushoutComparisonMap]
  exact pushoutInl_desc (S := (shortExactExtensionPullback e f).shortComplex) g
    (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g)
    (shortExactExtensionPullbackPushoutMiddleMap e f g)
    (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i _

@[simp]
lemma shortExactExtensionPullbackPushoutComparisonMap_inr
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    pushoutInr (S := (shortExactExtensionPullback e f).shortComplex) g
        (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g) ≫
        shortExactExtensionPullbackPushoutComparisonMap e f g =
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i := by
  dsimp [shortExactExtensionPullbackPushoutComparisonMap]
  exact pushoutInr_desc (S := (shortExactExtensionPullback e f).shortComplex) g
    (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g)
    (shortExactExtensionPullbackPushoutMiddleMap e f g)
    (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i _

@[simp]
lemma shortExactExtensionPullbackPushoutComparisonMap_i
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    (shortExactExtensionPushout (shortExactExtensionPullback e f) g).i ≫
        shortExactExtensionPullbackPushoutComparisonMap e f g =
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i :=
  shortExactExtensionPullbackPushoutComparisonMap_inr e f g

@[simp]
lemma shortExactExtensionPullbackPushoutComparisonMap_p
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    shortExactExtensionPullbackPushoutComparisonMap e f g ≫
        (shortExactExtensionPullback (shortExactExtensionPushout e g) f).p =
      (shortExactExtensionPushout (shortExactExtensionPullback e f) g).p := by
  apply pushout_hom_ext (S := (shortExactExtensionPullback e f).shortComplex) g
    (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g)
  · let inl := pushoutInl (S := (shortExactExtensionPullback e f).shortComplex) g
      (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g)
    let cmp := shortExactExtensionPullbackPushoutComparisonMap e f g
    let tp := (shortExactExtensionPullback (shortExactExtensionPushout e g) f).p
    have hassoc : inl ≫ (cmp ≫ tp) = (inl ≫ cmp) ≫ tp :=
      (Category.assoc inl cmp tp).symm
    have hinl : (inl ≫ cmp) ≫ tp =
        shortExactExtensionPullbackPushoutMiddleMap e f g ≫ tp := by
      exact congrArg (fun k => k ≫ tp)
        (shortExactExtensionPullbackPushoutComparisonMap_inl e f g)
    have hp : shortExactExtensionPullbackPushoutMiddleMap e f g ≫ tp =
        (shortExactExtensionPullback e f).p :=
      shortExactExtensionPullbackPushoutMiddleMap_p e f g
    have hpush : (shortExactExtensionPullback e f).p =
        pushoutInl (S := (shortExactExtensionPullback e f).shortComplex) g
          (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g) ≫
        (shortExactExtensionPushout (shortExactExtensionPullback e f) g).p :=
      (shortExactExtensionPushout_map_p (shortExactExtensionPullback e f) g).symm
    exact hassoc.trans (hinl.trans (hp.trans hpush))
  · let inr := pushoutInr (S := (shortExactExtensionPullback e f).shortComplex) g
      (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g)
    let cmp := shortExactExtensionPullbackPushoutComparisonMap e f g
    let tp := (shortExactExtensionPullback (shortExactExtensionPushout e g) f).p
    have hassoc : inr ≫ (cmp ≫ tp) = (inr ≫ cmp) ≫ tp :=
      (Category.assoc inr cmp tp).symm
    have hinr : (inr ≫ cmp) ≫ tp =
        (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫ tp := by
      exact congrArg (fun k => k ≫ tp)
        (shortExactExtensionPullbackPushoutComparisonMap_inr e f g)
    have hp : (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
        tp = 0 :=
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f).zero
    have hpush : 0 =
        pushoutInr (S := (shortExactExtensionPullback e f).shortComplex) g
          (pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g) ≫
        (shortExactExtensionPushout (shortExactExtensionPullback e f) g).p :=
      (shortExactExtensionPushout_inr_p (shortExactExtensionPullback e f) g).symm
    exact hassoc.trans (hinr.trans (hp.trans hpush))

/-- The product map inducing the comparison map is open. -/
lemma shortExactExtensionPullbackPushoutProductDesc_openMap
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    IsOpenMap
      (pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
        (shortExactExtensionPullbackPushoutMiddleMap e f g)
        (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i :
          pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y' →
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle) := by
  have hqopen : IsOpenMap
      (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) :
        pushoutProductObj e.shortComplex Y' → (shortExactExtensionPushout e g).middle) := by
    exact quotientMap_openMap (pushoutProductObj e.shortComplex Y')
      (pushoutSubgroup (S := e.shortComplex) g) (pushoutSubgroup_closed e.conflation g)
  have hpb : IsOpenMap
      (pullbackMapSnd f
        (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g))
        (pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)) :
          pullbackObj f
            (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) ≫
              pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)) →
            pullbackObj f
              (pushoutCokernelMap (S := e.shortComplex) g
                (pushoutSubgroup_closed e.conflation g))) :=
    pullbackMapSnd_openMap_of_openMap f
      (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g))
      (pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g))
      hqopen
  have hcomp : IsOpenMap (fun p : pushoutProductObj
        (shortExactExtensionPullback e f).shortComplex Y' =>
      (pullbackMapSnd f
        (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g))
        (pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)))
        ((shortExactExtensionPullbackPushoutProductHomeomorph e f g) p)) := by
    simpa [Function.comp_def] using
      hpb.comp (shortExactExtensionPullbackPushoutProductHomeomorph e f g).isOpenMap
  have hfun :
      (fun p : pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y' =>
        (pullbackMapSnd f
          (pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g))
          (pushoutCokernelMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)))
          ((shortExactExtensionPullbackPushoutProductHomeomorph e f g) p)) =
      (fun p : pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y' =>
        (pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
          (shortExactExtensionPullbackPushoutMiddleMap e f g)
          (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) p) := by
    funext p
    apply Subtype.ext
    apply Prod.ext
    · change p.1.1.1 =
        (pullbackFst f (shortExactExtensionPushout e g).p)
          ((shortExactExtensionPullbackPushoutMiddleMap e f g) p.1 +
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i p.2)
      have hfstadd := map_add (pullbackFst f (shortExactExtensionPushout e g).p).hom
        ((shortExactExtensionPullbackPushoutMiddleMap e f g) p.1)
        ((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i p.2)
      have hsum : p.1.1.1 =
          (pullbackFst f (shortExactExtensionPushout e g).p)
              ((shortExactExtensionPullbackPushoutMiddleMap e f g) p.1) +
            (pullbackFst f (shortExactExtensionPushout e g).p)
              ((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i p.2) := by
        change p.1.1.1 =
          ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
              pullbackFst f (shortExactExtensionPushout e g).p) p.1) +
            (((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
              pullbackFst f (shortExactExtensionPushout e g).p) p.2)
        have hizero : (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
            pullbackFst f (shortExactExtensionPushout e g).p = 0 :=
          (shortExactExtensionPullback (shortExactExtensionPushout e g) f).zero
        rw [shortExactExtensionPullbackPushoutMiddleMap_fst, hizero]
        change p.1.1.1 = (pullbackFst f e.p) p.1 + (0 : X')
        rw [add_zero]
        rfl
      exact hsum.trans hfstadd.symm
    · change pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)
          (p.1.1.2, p.2) =
        (pullbackSnd f (shortExactExtensionPushout e g).p)
          ((shortExactExtensionPullbackPushoutMiddleMap e f g) p.1 +
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i p.2)
      have hsndadd := map_add (pullbackSnd f (shortExactExtensionPushout e g).p).hom
        ((shortExactExtensionPullbackPushoutMiddleMap e f g) p.1)
        ((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i p.2)
      have hsum : pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)
            (p.1.1.2, p.2) =
          (pullbackSnd f (shortExactExtensionPushout e g).p)
              ((shortExactExtensionPullbackPushoutMiddleMap e f g) p.1) +
            (pullbackSnd f (shortExactExtensionPushout e g).p)
              ((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i p.2) := by
        change pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)
            (p.1.1.2, p.2) =
          ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
              pullbackSnd f (shortExactExtensionPushout e g).p) p.1) +
            (((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
              pullbackSnd f (shortExactExtensionPushout e g).p) p.2)
        rw [shortExactExtensionPullbackPushoutMiddleMap_snd, shortExactExtensionPullback_i_map]
        change pushoutQuotientMap (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g)
            (p.1.1.2, p.2) =
          pushoutInl (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) p.1.1.2 +
            pushoutInr (S := e.shortComplex) g (pushoutSubgroup_closed e.conflation g) p.2
        rw [pushoutQuotientMap_eq_inl_add_inr]
      exact hsum.trans hsndadd.symm
  rw [hfun] at hcomp
  simpa using hcomp

/-- The canonical comparison map is open on the underlying carrier. -/
theorem shortExactExtensionPullbackPushoutComparisonMap_openMap
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    IsOpenMap
      (shortExactExtensionPullbackPushoutComparisonMap e f g :
        (shortExactExtensionPushout (shortExactExtensionPullback e f) g).middle →
          (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle) := by
  let hNsrc := pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g
  let qsrc : pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y' ⟶
      (shortExactExtensionPushout (shortExactExtensionPullback e f) g).middle :=
    pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex) g hNsrc
  let cmp := shortExactExtensionPullbackPushoutComparisonMap e f g
  refine isOpenMap_of_comp_surjective qsrc cmp ?_ ?_
  · dsimp [qsrc]
    exact quotientMap_surjective
      (pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y')
      (pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g) hNsrc
  · have hdesc : qsrc ≫ cmp =
        pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
          (shortExactExtensionPullbackPushoutMiddleMap e f g)
          (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i := by
      dsimp [qsrc, cmp, shortExactExtensionPullbackPushoutComparisonMap, pushoutDesc,
        pushoutQuotientMap]
      exact quotientLift_quotientMap
          (pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y')
          (pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g)
          hNsrc
          (pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
            (shortExactExtensionPullbackPushoutMiddleMap e f g)
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i)
          (pushoutProductDesc_relation_le_ker
            (S := (shortExactExtensionPullback e f).shortComplex)
            g (shortExactExtensionPullbackPushoutMiddleMap_i e f g).symm)
    change IsOpenMap ((qsrc ≫ cmp : pushoutProductObj
      (shortExactExtensionPullback e f).shortComplex Y' ⟶
        (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle) :
          pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y' →
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle)
    rw [hdesc]
    exact shortExactExtensionPullbackPushoutProductDesc_openMap e f g

/-- The canonical comparison map is surjective on the underlying carrier.  This
is the representative-lifting half of the eventual inverse construction. -/
theorem shortExactExtensionPullbackPushoutComparisonMap_surjective
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    Function.Surjective
      (shortExactExtensionPullbackPushoutComparisonMap e f g :
        (shortExactExtensionPushout (shortExactExtensionPullback e f) g).middle →
          (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle) := by
  intro t
  let hNg := pushoutSubgroup_closed e.conflation g
  rcases quotientMap_surjective (pushoutProductObj e.shortComplex Y')
      (pushoutSubgroup (S := e.shortComplex) g) hNg
      ((pullbackSnd f (shortExactExtensionPushout e g).p) t) with ⟨p, hp⟩
  let m : (shortExactExtensionPullback e f).middle :=
    ⟨((pullbackFst f (shortExactExtensionPushout e g).p t), p.1), by
      have ht : f (pullbackFst f (shortExactExtensionPushout e g).p t) =
          (shortExactExtensionPushout e g).p
            (pullbackSnd f (shortExactExtensionPushout e g).p t) := by
        exact t.2
      have hpq : (shortExactExtensionPushout e g).p
            (pullbackSnd f (shortExactExtensionPushout e g).p t) = e.p p.1 := by
        rw [← hp]
        change (pushoutQuotientMap (S := e.shortComplex) g hNg ≫
            pushoutCokernelMap (S := e.shortComplex) g hNg) p = e.p p.1
        rw [pushoutQuotientMap_cokernel]
        rfl
      exact ht.trans hpq⟩
  let hNsrc := pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g
  let s : (shortExactExtensionPushout (shortExactExtensionPullback e f) g).middle :=
    pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex) g hNsrc
      (m, p.2)
  refine ⟨s, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (shortExactExtensionPullbackPushoutComparisonMap e f g ≫
        (shortExactExtensionPullback (shortExactExtensionPushout e g) f).p) s =
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f).p t
    rw [shortExactExtensionPullbackPushoutComparisonMap_p]
    dsimp [s]
    change (pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex)
        g hNsrc ≫
        pushoutCokernelMap (S := (shortExactExtensionPullback e f).shortComplex) g hNsrc)
        (m, p.2) = (shortExactExtensionPullback (shortExactExtensionPushout e g) f).p t
    rw [pushoutQuotientMap_cokernel]
    rfl
  · have hdesc :
        pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex)
            g hNsrc ≫ shortExactExtensionPullbackPushoutComparisonMap e f g =
          pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
            (shortExactExtensionPullbackPushoutMiddleMap e f g)
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i := by
      dsimp [shortExactExtensionPullbackPushoutComparisonMap, pushoutDesc,
        pushoutQuotientMap]
      exact quotientLift_quotientMap
          (pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y')
          (pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g)
          hNsrc
          (pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
            (shortExactExtensionPullbackPushoutMiddleMap e f g)
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i)
          (pushoutProductDesc_relation_le_ker
            (S := (shortExactExtensionPullback e f).shortComplex)
            g (shortExactExtensionPullbackPushoutMiddleMap_i e f g).symm)
    change (((pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex)
            g hNsrc ≫ shortExactExtensionPullbackPushoutComparisonMap e f g) ≫
            pullbackSnd f (shortExactExtensionPushout e g).p) (m, p.2)) =
      (pullbackSnd f (shortExactExtensionPushout e g).p) t
    rw [hdesc]
    change ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
            pullbackSnd f (shortExactExtensionPushout e g).p) m +
          ((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
            pullbackSnd f (shortExactExtensionPushout e g).p) p.2) = _
    have hleft : ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
            pullbackSnd f (shortExactExtensionPushout e g).p) m) =
          (pushoutInl (S := e.shortComplex) g hNg p.1 :
            (shortExactExtensionPushout e g).middle) := by
      have h := congrArg
        (fun h : (shortExactExtensionPullback e f).middle ⟶
            (shortExactExtensionPushout e g).middle => h m)
        (shortExactExtensionPullbackPushoutMiddleMap_snd e f g)
      exact h
    have hright : (((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
            pullbackSnd f (shortExactExtensionPushout e g).p) p.2) =
          (pushoutInr (S := e.shortComplex) g hNg p.2 :
            (shortExactExtensionPushout e g).middle) := by
      have h := congrArg
        (fun h : Y' ⟶ (shortExactExtensionPushout e g).middle => h p.2)
        (shortExactExtensionPullback_i_map (shortExactExtensionPushout e g) f)
      exact h
    rw [hleft, hright]
    rw [← hp]
    change (pushoutInl (S := e.shortComplex) g hNg p.1 +
        pushoutInr (S := e.shortComplex) g hNg p.2) =
      pushoutQuotientMap (S := e.shortComplex) g hNg p
    rw [pushoutQuotientMap_eq_inl_add_inr]

/-- The canonical comparison map is injective on the underlying carrier.  This
uses equality in the target pushout quotient to show that the source
representatives differ by the pulled-back pushout relation. -/
theorem shortExactExtensionPullbackPushoutComparisonMap_injective
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    Function.Injective
      (shortExactExtensionPullbackPushoutComparisonMap e f g :
        (shortExactExtensionPushout (shortExactExtensionPullback e f) g).middle →
          (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle) := by
  intro s t h
  let hNsrc := pushoutSubgroup_closed (shortExactExtensionPullback e f).conflation g
  let hNg := pushoutSubgroup_closed e.conflation g
  haveI hNsrcNormal :
      (pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g).Normal :=
    AddSubgroup.normal_of_isAddCommutative _
  haveI hNgNormal : (pushoutSubgroup (S := e.shortComplex) g).Normal :=
    AddSubgroup.normal_of_isAddCommutative _
  rcases quotientMap_surjective
      (pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y')
      (pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g)
      hNsrc s with ⟨p, rfl⟩
  rcases quotientMap_surjective
      (pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y')
      (pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g)
      hNsrc t with ⟨q, rfl⟩
  have hdesc :
        pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex)
            g hNsrc ≫ shortExactExtensionPullbackPushoutComparisonMap e f g =
          pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
            (shortExactExtensionPullbackPushoutMiddleMap e f g)
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i := by
      dsimp [shortExactExtensionPullbackPushoutComparisonMap, pushoutDesc,
        pushoutQuotientMap]
      exact quotientLift_quotientMap
          (pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y')
          (pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g)
          hNsrc
          (pushoutProductDesc (S := (shortExactExtensionPullback e f).shortComplex)
            (shortExactExtensionPullbackPushoutMiddleMap e f g)
            (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i)
          (pushoutProductDesc_relation_le_ker
            (S := (shortExactExtensionPullback e f).shortComplex)
            g (shortExactExtensionPullbackPushoutMiddleMap_i e f g).symm)
  change ((pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex)
      g hNsrc ≫ shortExactExtensionPullbackPushoutComparisonMap e f g) p) =
    ((pushoutQuotientMap (S := (shortExactExtensionPullback e f).shortComplex)
      g hNsrc ≫ shortExactExtensionPullbackPushoutComparisonMap e f g) q) at h
  rw [hdesc] at h
  have hfst0 := congrArg (fun z => pullbackFst f (shortExactExtensionPushout e g).p z) h
  change (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) p.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) p.2) =
    (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) q.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) q.2) at hfst0
  have hpadd : (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) p.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) p.2) =
      (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) p.1) +
      (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) p.2) := by
    exact map_add (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p)) _ _
  have hqadd : (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) q.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) q.2) =
      (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) q.1) +
      (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) q.2) := by
    exact map_add (Hom.hom (pullbackFst f (shortExactExtensionPushout e g).p)) _ _
  rw [hpadd, hqadd] at hfst0
  have hfst : (shortExactExtensionPullback e f).p p.1 =
      (shortExactExtensionPullback e f).p q.1 := by
    change ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
          pullbackFst f (shortExactExtensionPushout e g).p) p.1 +
        (((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
          pullbackFst f (shortExactExtensionPushout e g).p) p.2)) =
      ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
          pullbackFst f (shortExactExtensionPushout e g).p) q.1 +
        (((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
          pullbackFst f (shortExactExtensionPushout e g).p) q.2)) at hfst0
    have hizero : (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
        pullbackFst f (shortExactExtensionPushout e g).p = 0 := by
      exact (shortExactExtensionPullback (shortExactExtensionPushout e g) f).zero
    rw [shortExactExtensionPullbackPushoutMiddleMap_fst, hizero] at hfst0
    simpa using hfst0
  have hsnd0 := congrArg (fun z => pullbackSnd f (shortExactExtensionPushout e g).p z) h
  change (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) p.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) p.2) =
    (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) q.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) q.2) at hsnd0
  have hpadd' : (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) p.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) p.2) =
      (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) p.1) +
      (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) p.2) := by
    exact map_add (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p)) _ _
  have hqadd' : (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
      ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) q.1 +
        (Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) q.2) =
      (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullbackPushoutMiddleMap e f g)) q.1) +
      (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p))
        ((Hom.hom (shortExactExtensionPullback (shortExactExtensionPushout e g) f).i) q.2) := by
    exact map_add (Hom.hom (pullbackSnd f (shortExactExtensionPushout e g).p)) _ _
  rw [hpadd', hqadd'] at hsnd0
  have hsnd :
      pushoutInl (S := e.shortComplex) g hNg (pullbackSnd f e.p p.1) +
        pushoutInr (S := e.shortComplex) g hNg p.2 =
      pushoutInl (S := e.shortComplex) g hNg (pullbackSnd f e.p q.1) +
        pushoutInr (S := e.shortComplex) g hNg q.2 := by
    change ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
          pullbackSnd f (shortExactExtensionPushout e g).p) p.1 +
        (((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
          pullbackSnd f (shortExactExtensionPushout e g).p) p.2)) =
      ((shortExactExtensionPullbackPushoutMiddleMap e f g ≫
          pullbackSnd f (shortExactExtensionPushout e g).p) q.1 +
        (((shortExactExtensionPullback (shortExactExtensionPushout e g) f).i ≫
          pullbackSnd f (shortExactExtensionPushout e g).p) q.2)) at hsnd0
    rw [shortExactExtensionPullbackPushoutMiddleMap_snd,
      shortExactExtensionPullback_i_map] at hsnd0
    simpa using hsnd0
  have hquot : pushoutQuotientMap (S := e.shortComplex) g hNg
        (pullbackSnd f e.p p.1, p.2) =
      pushoutQuotientMap (S := e.shortComplex) g hNg
        (pullbackSnd f e.p q.1, q.2) := by
    rw [pushoutQuotientMap_eq_inl_add_inr, pushoutQuotientMap_eq_inl_add_inr]
    exact hsnd
  have hrel : (((pullbackSnd f e.p p.1, p.2) : e.middle × Y') -
      ((pullbackSnd f e.p q.1, q.2) : e.middle × Y')) ∈
      pushoutSubgroup (S := e.shortComplex) g := by
    exact (QuotientAddGroup.eq_iff_sub_mem (N := pushoutSubgroup (S := e.shortComplex) g)).mp (by
      change pushoutQuotientMap (S := e.shortComplex) g hNg
          (pullbackSnd f e.p p.1, p.2) =
        pushoutQuotientMap (S := e.shortComplex) g hNg
          (pullbackSnd f e.p q.1, q.2)
      exact hquot)
  rcases hrel with ⟨y, hy⟩
  change (p : (pushoutProductObj (shortExactExtensionPullback e f).shortComplex Y').carrier ⧸
      pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g) = q
  apply (QuotientAddGroup.eq_iff_sub_mem
    (N := pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g)).mpr
  change (p - q) ∈ pushoutSubgroup (S := (shortExactExtensionPullback e f).shortComplex) g
  refine ⟨y, ?_⟩
  ext
  · apply Subtype.ext
    ext
    · change (0 : X') = (shortExactExtensionPullback e f).p p.1 -
        (shortExactExtensionPullback e f).p q.1
      rw [hfst]
      simp
    · have hyfst := congrArg Prod.fst hy
      simpa using hyfst
  · have hysnd := congrArg Prod.snd hy
    simpa using hysnd

/-- The canonical comparison map is bijective on the underlying carrier.  This
is still weaker than an isomorphism in `MetrizableLCA`, because the continuous
inverse has not yet been constructed. -/
theorem shortExactExtensionPullbackPushoutComparisonMap_bijective
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    Function.Bijective
      (shortExactExtensionPullbackPushoutComparisonMap e f g :
        (shortExactExtensionPushout (shortExactExtensionPullback e f) g).middle →
          (shortExactExtensionPullback (shortExactExtensionPushout e g) f).middle) :=
  ⟨shortExactExtensionPullbackPushoutComparisonMap_injective e f g,
    shortExactExtensionPullbackPushoutComparisonMap_surjective e f g⟩

/-- The canonical comparison map is an isomorphism in `MetrizableLCA`. -/
theorem shortExactExtensionPullbackPushoutComparisonMap_isIso
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    IsIso (shortExactExtensionPullbackPushoutComparisonMap e f g) :=
  isIso_of_bijective_openMap (shortExactExtensionPullbackPushoutComparisonMap e f g)
    (shortExactExtensionPullbackPushoutComparisonMap_bijective e f g)
    (shortExactExtensionPullbackPushoutComparisonMap_openMap e f g)

/-- If the canonical comparison map is an isomorphism, it identifies the two
candidate one-fold extensions. -/
noncomputable def shortExactExtensionPullbackPushoutComparisonIsoOfIsIso
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y')
    [IsIso (shortExactExtensionPullbackPushoutComparisonMap e f g)] :
    ShortExactExtension.Iso
      (shortExactExtensionPushout (shortExactExtensionPullback e f) g)
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f) where
  middleIso := asIso (shortExactExtensionPullbackPushoutComparisonMap e f g)
  i_hom := by
    simp
  hom_p := by
    simp

/-- If the canonical comparison map is an isomorphism, the pulled-back pushout
is the expected pushout extension. -/
noncomputable def shortExactExtensionPullbackPushoutDataOfIsIsoComparison
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y')
    [IsIso (shortExactExtensionPullbackPushoutComparisonMap e f g)] :
    ShortExactExtension.PushoutData
      (shortExactExtensionPullback e f) g
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f) :=
  ShortExactExtension.PushoutData.isoOut
    (shortExactExtensionPushoutData (shortExactExtensionPullback e f) g)
    (shortExactExtensionPullbackPushoutComparisonIsoOfIsIso e f g)

/-- The pullback of a canonical pushout is the expected pushout of the pulled-back extension. -/
noncomputable def shortExactExtensionPullbackPushoutData
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y') :
    ShortExactExtension.PushoutData
      (shortExactExtensionPullback e f) g
      (shortExactExtensionPullback (shortExactExtensionPushout e g) f) := by
  haveI : IsIso (shortExactExtensionPullbackPushoutComparisonMap e f g) :=
    shortExactExtensionPullbackPushoutComparisonMap_isIso e f g
  exact shortExactExtensionPullbackPushoutDataOfIsIsoComparison e f g

/-- Pullback preserves any pushout square of one-fold extensions, by comparing
the chosen output with the canonical pushout. -/
noncomputable def shortExactExtensionPullbackPushoutDataOfPushoutData
    {X X' Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) (g : Y ⟶ Y')
    {out : ShortExactExtension (C := MetrizableLCA.{u}) X Y'}
    (h : ShortExactExtension.PushoutData e g out) :
    ShortExactExtension.PushoutData
      (shortExactExtensionPullback e f) g
      (shortExactExtensionPullback out f) :=
  ShortExactExtension.PushoutData.isoOut
    (shortExactExtensionPullbackPushoutData e f g)
    (shortExactExtensionPullbackIso f
      (ShortExactExtension.PushoutData.iso (shortExactExtensionPushoutData e g) h
        (ShortExactExtension.Iso.refl e)))

/-- Canonical pushout of one-fold extensions preserves isomorphism of the input extension. -/
noncomputable def shortExactExtensionPushoutIso
    {X Y Y' : MetrizableLCA.{u}} (a : Y ⟶ Y')
    {e e' : ShortExactExtension (C := MetrizableLCA.{u}) X Y}
    (h : ShortExactExtension.Iso e e') :
    ShortExactExtension.Iso
      (shortExactExtensionPushout e a) (shortExactExtensionPushout e' a) :=
  ShortExactExtension.PushoutData.iso
    (shortExactExtensionPushoutData e a) (shortExactExtensionPushoutData e' a) h

/-- Successive pushouts of a one-fold extension agree with the direct pushout. -/
noncomputable def shortExactExtensionPushoutAssocIso
    {X Y Y' Y'' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y)
    (g : Y ⟶ Y') (f : Y' ⟶ Y'')
    {out : ShortExactExtension (C := MetrizableLCA.{u}) X Y'}
    (h : ShortExactExtension.PushoutData e g out) :
    ShortExactExtension.Iso (shortExactExtensionPushout e (g ≫ f))
      (shortExactExtensionPushout out f) := by
  let direct := shortExactExtensionPushoutData e (g ≫ f)
  let second := shortExactExtensionPushoutData out f
  let pastedCocone := h.isPushout.cocone.pasteHoriz second.isPushout.cocone rfl
  have hpasted : IsColimit pastedCocone := by
    dsimp [pastedCocone]
    exact pasteHorizIsPushout rfl h.isPushout.isColimit second.isPushout.isColimit
  let middleIso :
      (shortExactExtensionPushout e (g ≫ f)).middle ≅
        (shortExactExtensionPushout out f).middle :=
    IsColimit.coconePointUniqueUpToIso direct.isPushout.isColimit hpasted
  refine
    { middleIso := middleIso
      i_hom := ?_
      hom_p := ?_ }
  · simpa [middleIso, direct, pastedCocone] using
      IsColimit.comp_coconePointUniqueUpToIso_hom direct.isPushout.isColimit
        hpasted WalkingSpan.right
  · apply direct.isPushout.hom_ext
    · have hinl :
          direct.middleMap ≫ middleIso.hom = h.middleMap ≫ second.middleMap := by
        simpa [middleIso, direct, pastedCocone] using
          IsColimit.comp_coconePointUniqueUpToIso_hom direct.isPushout.isColimit
            hpasted WalkingSpan.left
      rw [← Category.assoc, hinl, Category.assoc, second.map_p, h.map_p, direct.map_p]
    · have hinr :
          (shortExactExtensionPushout e (g ≫ f)).i ≫ middleIso.hom =
            (shortExactExtensionPushout out f).i := by
        simpa [middleIso, direct, pastedCocone] using
          IsColimit.comp_coconePointUniqueUpToIso_hom direct.isPushout.isColimit
            hpasted WalkingSpan.right
      rw [← Category.assoc, hinr, (shortExactExtensionPushout out f).zero,
        (shortExactExtensionPushout e (g ≫ f)).zero]

/-- The explicit pushout of a split short complex is split. -/
noncomputable def pushoutSplitting
    {S : ShortComplex MetrizableLCA.{u}} {Y : MetrizableLCA.{u}}
    (a : S.X₁ ⟶ Y) (hN : IsClosed (pushoutSubgroup a : Set (S.X₂ × Y)))
    (s : S.Splitting) :
    (ShortComplex.mk (pushoutInr a hN) (pushoutCokernelMap a hN)
      (pushoutInr_cokernel a hN)).Splitting := by
  let r : pushoutObj a hN ⟶ Y :=
    pushoutDesc (S := S) a hN (s.r ≫ a) (𝟙 Y) (by
      rw [← Category.assoc, s.f_r, Category.id_comp, Category.comp_id])
  let sec : S.X₃ ⟶ pushoutObj a hN :=
    s.s ≫ pushoutInl a hN
  refine
    { r := r
      s := sec
      f_r := ?_
      s_g := ?_
      id := ?_ }
  · dsimp [r]
    rw [pushoutInr_desc]
  · dsimp [sec]
    rw [Category.assoc, pushoutInl_cokernel]
    exact s.s_g
  · dsimp [r, sec]
    apply pushout_hom_ext (S := S) a hN
    · have hcomp :
          pushoutInl a hN ≫
              (pushoutDesc a hN (s.r ≫ a) (𝟙 Y) (by
                  rw [← Category.assoc, s.f_r, Category.id_comp, Category.comp_id]) ≫
                pushoutInr a hN +
                pushoutCokernelMap a hN ≫ s.s ≫ pushoutInl a hN) =
            pushoutInl a hN ≫
                (pushoutDesc a hN (s.r ≫ a) (𝟙 Y) (by
                    rw [← Category.assoc, s.f_r, Category.id_comp, Category.comp_id]) ≫
                  pushoutInr a hN) +
              pushoutInl a hN ≫
                (pushoutCokernelMap a hN ≫ s.s ≫ pushoutInl a hN) :=
        CategoryTheory.Preadditive.comp_add (C := MetrizableLCA.{u}) S.X₂
          (pushoutObj a hN) (pushoutObj a hN) (pushoutInl a hN)
          (pushoutDesc a hN (s.r ≫ a) (𝟙 Y) (by
            rw [← Category.assoc, s.f_r, Category.id_comp, Category.comp_id]) ≫
            pushoutInr a hN)
          (pushoutCokernelMap a hN ≫ s.s ≫ pushoutInl a hN)
      rw [hcomp]
      rw [← Category.assoc, pushoutInl_desc]
      rw [← Category.assoc, pushoutInl_cokernel]
      rw [Category.assoc, ← pushout_condition]
      rw [← Category.assoc, ← Category.assoc]
      rw [← CategoryTheory.Preadditive.add_comp (C := MetrizableLCA.{u}) S.X₂ S.X₂
        (pushoutObj a hN) (s.r ≫ S.f) (S.g ≫ s.s) (pushoutInl a hN)]
      rw [s.id]
      simp
    · have hcomp :
          pushoutInr a hN ≫
              (pushoutDesc a hN (s.r ≫ a) (𝟙 Y) (by
                  rw [← Category.assoc, s.f_r, Category.id_comp, Category.comp_id]) ≫
                pushoutInr a hN +
                pushoutCokernelMap a hN ≫ s.s ≫ pushoutInl a hN) =
            pushoutInr a hN ≫
                (pushoutDesc a hN (s.r ≫ a) (𝟙 Y) (by
                    rw [← Category.assoc, s.f_r, Category.id_comp, Category.comp_id]) ≫
                  pushoutInr a hN) +
              pushoutInr a hN ≫
                (pushoutCokernelMap a hN ≫ s.s ≫ pushoutInl a hN) :=
        CategoryTheory.Preadditive.comp_add (C := MetrizableLCA.{u}) Y
          (pushoutObj a hN) (pushoutObj a hN) (pushoutInr a hN)
          (pushoutDesc a hN (s.r ≫ a) (𝟙 Y) (by
            rw [← Category.assoc, s.f_r, Category.id_comp, Category.comp_id]) ≫
            pushoutInr a hN)
          (pushoutCokernelMap a hN ≫ s.s ≫ pushoutInl a hN)
      rw [hcomp]
      rw [← Category.assoc, pushoutInr_desc]
      rw [← Category.assoc, pushoutInr_cokernel]
      simp

/-- The canonical pushout of a split one-fold extension is split. -/
noncomputable def shortExactExtensionPushoutSplitting
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (a : Y ⟶ Y')
    (s : e.shortComplex.Splitting) :
    (shortExactExtensionPushout e a).shortComplex.Splitting := by
  simpa [shortExactExtensionPushout, ShortExactExtension.shortComplex] using
    pushoutSplitting (S := e.shortComplex) a (pushoutSubgroup_closed e.conflation a) s

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

/-- Pushing out a one-fold Baer-sum diagram preserves the Baer-sum diagram. -/
noncomputable def shortExactExtensionPushoutBaerSumData
    {X Y Y' : MetrizableLCA.{u}}
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y] [HasBinaryBiproduct Y' Y']
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA.{u}) X Y}
    (f : Y ⟶ Y') (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
    ShortExactExtension.BaerSumData
      (shortExactExtensionPushout e₁ f)
      (shortExactExtensionPushout e₂ f)
      (shortExactExtensionPushout sum f) := by
  let ff : Y ⊞ Y ⟶ Y' ⊞ Y' := biprod.map f f
  let productPush := shortExactExtensionPushout h.productExtension ff
  let productPushData := shortExactExtensionPushoutData h.productExtension ff
  let e₁PushData := shortExactExtensionPushoutData e₁ f
  let e₂PushData := shortExactExtensionPushoutData e₂ f
  let pullPush := shortExactExtensionPushout h.pullbackExtension ff
  let pullPushData := shortExactExtensionPushoutData h.pullbackExtension ff
  let finalPush := shortExactExtensionPushout h.pushoutExtension f
  let finalPushData := shortExactExtensionPushoutData h.pushoutExtension f
  have h_codiag_map : ff ≫ biprodCodiag Y' = biprodCodiag Y ≫ f := by
    apply biprod.hom_ext'
    · simp [ff, biprodCodiag]
    · simp [ff, biprodCodiag]
  have productFst_condition :
      h.productExtension.i ≫ (h.productFst ≫ e₁PushData.middleMap) =
        ff ≫ (biprod.fst ≫ (shortExactExtensionPushout e₁ f).i) := by
    calc
      h.productExtension.i ≫ (h.productFst ≫ e₁PushData.middleMap) =
          (h.productExtension.i ≫ h.productFst) ≫ e₁PushData.middleMap := by
            rw [Category.assoc]
      _ = (biprod.fst ≫ e₁.i) ≫ e₁PushData.middleMap := by
            rw [h.product_i_fst]
      _ = biprod.fst ≫ (e₁.i ≫ e₁PushData.middleMap) := by
            rw [Category.assoc]
      _ = biprod.fst ≫ (f ≫ (shortExactExtensionPushout e₁ f).i) := by
            rw [← e₁PushData.i_map]
      _ = (biprod.fst ≫ f) ≫ (shortExactExtensionPushout e₁ f).i := by
            rw [Category.assoc]
      _ = (ff ≫ biprod.fst) ≫ (shortExactExtensionPushout e₁ f).i := by
            rw [biprod.map_fst]
      _ = ff ≫ (biprod.fst ≫ (shortExactExtensionPushout e₁ f).i) := by
            rw [Category.assoc]
  have productSnd_condition :
      h.productExtension.i ≫ (h.productSnd ≫ e₂PushData.middleMap) =
        ff ≫ (biprod.snd ≫ (shortExactExtensionPushout e₂ f).i) := by
    calc
      h.productExtension.i ≫ (h.productSnd ≫ e₂PushData.middleMap) =
          (h.productExtension.i ≫ h.productSnd) ≫ e₂PushData.middleMap := by
            rw [Category.assoc]
      _ = (biprod.snd ≫ e₂.i) ≫ e₂PushData.middleMap := by
            rw [h.product_i_snd]
      _ = biprod.snd ≫ (e₂.i ≫ e₂PushData.middleMap) := by
            rw [Category.assoc]
      _ = biprod.snd ≫ (f ≫ (shortExactExtensionPushout e₂ f).i) := by
            rw [← e₂PushData.i_map]
      _ = (biprod.snd ≫ f) ≫ (shortExactExtensionPushout e₂ f).i := by
            rw [Category.assoc]
      _ = (ff ≫ biprod.snd) ≫ (shortExactExtensionPushout e₂ f).i := by
            rw [biprod.map_snd]
      _ = ff ≫ (biprod.snd ≫ (shortExactExtensionPushout e₂ f).i) := by
            rw [Category.assoc]
  let productFst : productPush.middle ⟶ (shortExactExtensionPushout e₁ f).middle :=
    productPushData.isPushout.desc
      (h.productFst ≫ e₁PushData.middleMap)
      (biprod.fst ≫ (shortExactExtensionPushout e₁ f).i)
      productFst_condition
  let productSnd : productPush.middle ⟶ (shortExactExtensionPushout e₂ f).middle :=
    productPushData.isPushout.desc
      (h.productSnd ≫ e₂PushData.middleMap)
      (biprod.snd ≫ (shortExactExtensionPushout e₂ f).i)
      productSnd_condition
  have productFst_inl :
      productPushData.middleMap ≫ productFst =
        h.productFst ≫ e₁PushData.middleMap := by
    simp [productFst]
  have productFst_inr :
      productPush.i ≫ productFst =
        biprod.fst ≫ (shortExactExtensionPushout e₁ f).i := by
    simp [productFst]
  have productSnd_inl :
      productPushData.middleMap ≫ productSnd =
        h.productSnd ≫ e₂PushData.middleMap := by
    simp [productSnd]
  have productSnd_inr :
      productPush.i ≫ productSnd =
        biprod.snd ≫ (shortExactExtensionPushout e₂ f).i := by
    simp [productSnd]
  have pullbackMap_condition :
      h.pullbackExtension.i ≫ (h.pullbackMap ≫ productPushData.middleMap) =
        ff ≫ productPush.i := by
    rw [← Category.assoc, h.pullback_i, ← productPushData.i_map]
  let pullbackMap : pullPush.middle ⟶ productPush.middle :=
    pullPushData.isPushout.desc
      (h.pullbackMap ≫ productPushData.middleMap)
      productPush.i
      pullbackMap_condition
  have pullbackMap_inl :
      pullPushData.middleMap ≫ pullbackMap =
        h.pullbackMap ≫ productPushData.middleMap := by
    simp [pullbackMap]
  have pullbackMap_inr : pullPush.i ≫ pullbackMap = productPush.i := by
    simp [pullbackMap]
  have pushoutMap_condition :
      h.pullbackExtension.i ≫ (h.pushoutMap ≫ finalPushData.middleMap) =
        ff ≫ (biprodCodiag Y' ≫ finalPush.i) := by
    calc
      h.pullbackExtension.i ≫ (h.pushoutMap ≫ finalPushData.middleMap) =
          (h.pullbackExtension.i ≫ h.pushoutMap) ≫ finalPushData.middleMap := by
            rw [Category.assoc]
      _ = (biprodCodiag Y ≫ h.pushoutExtension.i) ≫
            finalPushData.middleMap := by
            rw [← h.pushout_i]
      _ = biprodCodiag Y ≫
            (h.pushoutExtension.i ≫ finalPushData.middleMap) := by
            rw [Category.assoc]
      _ = biprodCodiag Y ≫ (f ≫ finalPush.i) := by
            rw [← finalPushData.i_map]
      _ = (biprodCodiag Y ≫ f) ≫ finalPush.i := by
            rw [Category.assoc]
      _ = (ff ≫ biprodCodiag Y') ≫ finalPush.i := by
            rw [h_codiag_map]
      _ = ff ≫ (biprodCodiag Y' ≫ finalPush.i) := by
            rw [Category.assoc]
  let pushoutMap : pullPush.middle ⟶ finalPush.middle :=
    pullPushData.isPushout.desc
      (h.pushoutMap ≫ finalPushData.middleMap)
      (biprodCodiag Y' ≫ finalPush.i)
      pushoutMap_condition
  have pushoutMap_inl :
      pullPushData.middleMap ≫ pushoutMap =
        h.pushoutMap ≫ finalPushData.middleMap := by
    simp [pushoutMap]
  have pushoutMap_inr : pullPush.i ≫ pushoutMap = biprodCodiag Y' ≫ finalPush.i := by
    simp [pushoutMap]
  refine
    { productExtension := productPush
      productFst := productFst
      productSnd := productSnd
      product_i_fst := productFst_inr
      product_i_snd := productSnd_inr
      product_p_fst := ?_
      product_p_snd := ?_
      pullbackExtension := pullPush
      pullbackMap := pullbackMap
      pullback_i := pullbackMap_inr
      pullback_p := ?_
      pushoutExtension := finalPush
      pushoutMap := pushoutMap
      pushout_i := pushoutMap_inr.symm
      pushout_p := ?_
      sumIso := shortExactExtensionPushoutIso f h.sumIso }
  · apply productPushData.isPushout.hom_ext
    · calc
        productPushData.middleMap ≫
            (productFst ≫ (shortExactExtensionPushout e₁ f).p) =
            (productPushData.middleMap ≫ productFst) ≫
              (shortExactExtensionPushout e₁ f).p := by
              rw [Category.assoc]
        _ = (h.productFst ≫ e₁PushData.middleMap) ≫
              (shortExactExtensionPushout e₁ f).p := by
              rw [productFst_inl]
        _ = h.productFst ≫
              (e₁PushData.middleMap ≫ (shortExactExtensionPushout e₁ f).p) := by
              rw [Category.assoc]
        _ = h.productFst ≫ e₁.p := by
              rw [e₁PushData.map_p]
        _ = h.productExtension.p ≫ biprod.fst := h.product_p_fst
        _ = (productPushData.middleMap ≫ productPush.p) ≫ biprod.fst := by
              rw [productPushData.map_p]
        _ = productPushData.middleMap ≫ (productPush.p ≫ biprod.fst) := by
              rw [Category.assoc]
    · calc
        productPush.i ≫ (productFst ≫ (shortExactExtensionPushout e₁ f).p) =
            (productPush.i ≫ productFst) ≫
              (shortExactExtensionPushout e₁ f).p := by
              rw [Category.assoc]
        _ = (biprod.fst ≫ (shortExactExtensionPushout e₁ f).i) ≫
              (shortExactExtensionPushout e₁ f).p := by
              rw [productFst_inr]
        _ = biprod.fst ≫
              ((shortExactExtensionPushout e₁ f).i ≫
                (shortExactExtensionPushout e₁ f).p) := by
              rw [Category.assoc]
        _ = 0 := by
              rw [(shortExactExtensionPushout e₁ f).zero, comp_zero]
        _ = productPush.i ≫ (productPush.p ≫ biprod.fst) := by
              rw [← Category.assoc, productPush.zero, zero_comp]
  · apply productPushData.isPushout.hom_ext
    · calc
        productPushData.middleMap ≫
            (productSnd ≫ (shortExactExtensionPushout e₂ f).p) =
            (productPushData.middleMap ≫ productSnd) ≫
              (shortExactExtensionPushout e₂ f).p := by
              rw [Category.assoc]
        _ = (h.productSnd ≫ e₂PushData.middleMap) ≫
              (shortExactExtensionPushout e₂ f).p := by
              rw [productSnd_inl]
        _ = h.productSnd ≫
              (e₂PushData.middleMap ≫ (shortExactExtensionPushout e₂ f).p) := by
              rw [Category.assoc]
        _ = h.productSnd ≫ e₂.p := by
              rw [e₂PushData.map_p]
        _ = h.productExtension.p ≫ biprod.snd := h.product_p_snd
        _ = (productPushData.middleMap ≫ productPush.p) ≫ biprod.snd := by
              rw [productPushData.map_p]
        _ = productPushData.middleMap ≫ (productPush.p ≫ biprod.snd) := by
              rw [Category.assoc]
    · calc
        productPush.i ≫ (productSnd ≫ (shortExactExtensionPushout e₂ f).p) =
            (productPush.i ≫ productSnd) ≫
              (shortExactExtensionPushout e₂ f).p := by
              rw [Category.assoc]
        _ = (biprod.snd ≫ (shortExactExtensionPushout e₂ f).i) ≫
              (shortExactExtensionPushout e₂ f).p := by
              rw [productSnd_inr]
        _ = biprod.snd ≫
              ((shortExactExtensionPushout e₂ f).i ≫
                (shortExactExtensionPushout e₂ f).p) := by
              rw [Category.assoc]
        _ = 0 := by
              rw [(shortExactExtensionPushout e₂ f).zero, comp_zero]
        _ = productPush.i ≫ (productPush.p ≫ biprod.snd) := by
              rw [← Category.assoc, productPush.zero, zero_comp]
  · apply pullPushData.isPushout.hom_ext
    · calc
        pullPushData.middleMap ≫ (pullbackMap ≫ productPush.p) =
            (pullPushData.middleMap ≫ pullbackMap) ≫ productPush.p := by
              rw [Category.assoc]
        _ = (h.pullbackMap ≫ productPushData.middleMap) ≫ productPush.p := by
              rw [pullbackMap_inl]
        _ = h.pullbackMap ≫ (productPushData.middleMap ≫ productPush.p) := by
              rw [Category.assoc]
        _ = h.pullbackMap ≫ h.productExtension.p := by
              rw [productPushData.map_p]
        _ = h.pullbackExtension.p ≫ biprodDiag X := h.pullback_p
        _ = (pullPushData.middleMap ≫ pullPush.p) ≫ biprodDiag X := by
              rw [pullPushData.map_p]
        _ = pullPushData.middleMap ≫ (pullPush.p ≫ biprodDiag X) := by
              rw [Category.assoc]
    · calc
        pullPush.i ≫ (pullbackMap ≫ productPush.p) =
            (pullPush.i ≫ pullbackMap) ≫ productPush.p := by
              rw [Category.assoc]
        _ = productPush.i ≫ productPush.p := by
              rw [pullbackMap_inr]
        _ = 0 := productPush.zero
        _ = pullPush.i ≫ (pullPush.p ≫ biprodDiag X) := by
              rw [← Category.assoc, pullPush.zero, zero_comp]
  · apply pullPushData.isPushout.hom_ext
    · calc
        pullPushData.middleMap ≫ (pushoutMap ≫ finalPush.p) =
            (pullPushData.middleMap ≫ pushoutMap) ≫ finalPush.p := by
              rw [Category.assoc]
        _ = (h.pushoutMap ≫ finalPushData.middleMap) ≫ finalPush.p := by
              rw [pushoutMap_inl]
        _ = h.pushoutMap ≫ (finalPushData.middleMap ≫ finalPush.p) := by
              rw [Category.assoc]
        _ = h.pushoutMap ≫ h.pushoutExtension.p := by
              rw [finalPushData.map_p]
        _ = h.pullbackExtension.p := h.pushout_p
        _ = pullPushData.middleMap ≫ pullPush.p := by
              rw [pullPushData.map_p]
    · calc
        pullPush.i ≫ (pushoutMap ≫ finalPush.p) =
            (pullPush.i ≫ pushoutMap) ≫ finalPush.p := by
              rw [Category.assoc]
        _ = (biprodCodiag Y' ≫ finalPush.i) ≫ finalPush.p := by
              rw [pushoutMap_inr]
        _ = biprodCodiag Y' ≫ (finalPush.i ≫ finalPush.p) := by
              rw [Category.assoc]
        _ = 0 := by
              rw [finalPush.zero, comp_zero]
        _ = pullPush.i ≫ pullPush.p := by
              rw [pullPush.zero]

/-- Pulling back a one-fold Baer-sum diagram preserves the Baer-sum diagram. -/
noncomputable def shortExactExtensionPullbackBaerSumData
    {X X' Y : MetrizableLCA.{u}}
    [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X'] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA.{u}) X Y}
    (f : X' ⟶ X) (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
    ShortExactExtension.BaerSumData
      (shortExactExtensionPullback e₁ f)
      (shortExactExtensionPullback e₂ f)
      (shortExactExtensionPullback sum f) := by
  let ff : X' ⊞ X' ⟶ X ⊞ X := biprod.map f f
  let productPull := shortExactExtensionPullback h.productExtension ff
  let productPullData := shortExactExtensionPullbackData h.productExtension ff
  let e₁PullData := shortExactExtensionPullbackData e₁ f
  let e₂PullData := shortExactExtensionPullbackData e₂ f
  let stagePull := shortExactExtensionPullback h.pullbackExtension f
  let stagePullData := shortExactExtensionPullbackData h.pullbackExtension f
  let finalPull := shortExactExtensionPullback h.pushoutExtension f
  let finalPullData := shortExactExtensionPullbackData h.pushoutExtension f
  have h_diag_map : biprodDiag X' ≫ ff = f ≫ biprodDiag X := by
    apply biprod.hom_ext
    · simp [ff, biprodDiag, Category.assoc]
    · simp [ff, biprodDiag, Category.assoc]
  have productFst_condition :
      (productPullData.middleMap ≫ h.productFst) ≫ e₁.p =
        (productPull.p ≫ biprod.fst) ≫ f := by
    calc
      (productPullData.middleMap ≫ h.productFst) ≫ e₁.p =
          productPullData.middleMap ≫ (h.productFst ≫ e₁.p) := by
            rw [Category.assoc]
      _ = productPullData.middleMap ≫ (h.productExtension.p ≫ biprod.fst) := by
            rw [h.product_p_fst]
      _ = (productPullData.middleMap ≫ h.productExtension.p) ≫ biprod.fst := by
            rw [Category.assoc]
      _ = (productPull.p ≫ ff) ≫ biprod.fst := by
            rw [productPullData.map_p]
      _ = productPull.p ≫ (ff ≫ biprod.fst) := by
            rw [Category.assoc]
      _ = productPull.p ≫ (biprod.fst ≫ f) := by
            rw [biprod.map_fst]
      _ = (productPull.p ≫ biprod.fst) ≫ f := by
            rw [Category.assoc]
  have productSnd_condition :
      (productPullData.middleMap ≫ h.productSnd) ≫ e₂.p =
        (productPull.p ≫ biprod.snd) ≫ f := by
    calc
      (productPullData.middleMap ≫ h.productSnd) ≫ e₂.p =
          productPullData.middleMap ≫ (h.productSnd ≫ e₂.p) := by
            rw [Category.assoc]
      _ = productPullData.middleMap ≫ (h.productExtension.p ≫ biprod.snd) := by
            rw [h.product_p_snd]
      _ = (productPullData.middleMap ≫ h.productExtension.p) ≫ biprod.snd := by
            rw [Category.assoc]
      _ = (productPull.p ≫ ff) ≫ biprod.snd := by
            rw [productPullData.map_p]
      _ = productPull.p ≫ (ff ≫ biprod.snd) := by
            rw [Category.assoc]
      _ = productPull.p ≫ (biprod.snd ≫ f) := by
            rw [biprod.map_snd]
      _ = (productPull.p ≫ biprod.snd) ≫ f := by
            rw [Category.assoc]
  let productFst : productPull.middle ⟶ (shortExactExtensionPullback e₁ f).middle :=
    e₁PullData.isPullback.lift
      (productPullData.middleMap ≫ h.productFst)
      (productPull.p ≫ biprod.fst)
      productFst_condition
  let productSnd : productPull.middle ⟶ (shortExactExtensionPullback e₂ f).middle :=
    e₂PullData.isPullback.lift
      (productPullData.middleMap ≫ h.productSnd)
      (productPull.p ≫ biprod.snd)
      productSnd_condition
  have productFst_middle :
      productFst ≫ e₁PullData.middleMap =
        productPullData.middleMap ≫ h.productFst := by
    simp [productFst]
  have productFst_p :
      productFst ≫ (shortExactExtensionPullback e₁ f).p =
        productPull.p ≫ biprod.fst := by
    simp [productFst]
  have productSnd_middle :
      productSnd ≫ e₂PullData.middleMap =
        productPullData.middleMap ≫ h.productSnd := by
    simp [productSnd]
  have productSnd_p :
      productSnd ≫ (shortExactExtensionPullback e₂ f).p =
        productPull.p ≫ biprod.snd := by
    simp [productSnd]
  have productFst_i :
      productPull.i ≫ productFst =
        biprod.fst ≫ (shortExactExtensionPullback e₁ f).i := by
    apply e₁PullData.isPullback.hom_ext
    · calc
        (productPull.i ≫ productFst) ≫ e₁PullData.middleMap =
            productPull.i ≫ (productFst ≫ e₁PullData.middleMap) := by
              rw [Category.assoc]
        _ = productPull.i ≫ (productPullData.middleMap ≫ h.productFst) := by
              rw [productFst_middle]
        _ = (productPull.i ≫ productPullData.middleMap) ≫ h.productFst := by
              rw [Category.assoc]
        _ = h.productExtension.i ≫ h.productFst := by
              rw [productPullData.i_map]
        _ = biprod.fst ≫ e₁.i := h.product_i_fst
        _ = biprod.fst ≫
              ((shortExactExtensionPullback e₁ f).i ≫ e₁PullData.middleMap) := by
              rw [← e₁PullData.i_map]
        _ = (biprod.fst ≫ (shortExactExtensionPullback e₁ f).i) ≫
              e₁PullData.middleMap := by
              rw [Category.assoc]
    · calc
        (productPull.i ≫ productFst) ≫ (shortExactExtensionPullback e₁ f).p =
            productPull.i ≫
              (productFst ≫ (shortExactExtensionPullback e₁ f).p) := by
              rw [Category.assoc]
        _ = productPull.i ≫ (productPull.p ≫ biprod.fst) := by
              rw [productFst_p]
        _ = 0 := by
              rw [← Category.assoc, productPull.zero, zero_comp]
        _ = (biprod.fst ≫ (shortExactExtensionPullback e₁ f).i) ≫
              (shortExactExtensionPullback e₁ f).p := by
              rw [Category.assoc, (shortExactExtensionPullback e₁ f).zero, comp_zero]
  have productSnd_i :
      productPull.i ≫ productSnd =
        biprod.snd ≫ (shortExactExtensionPullback e₂ f).i := by
    apply e₂PullData.isPullback.hom_ext
    · calc
        (productPull.i ≫ productSnd) ≫ e₂PullData.middleMap =
            productPull.i ≫ (productSnd ≫ e₂PullData.middleMap) := by
              rw [Category.assoc]
        _ = productPull.i ≫ (productPullData.middleMap ≫ h.productSnd) := by
              rw [productSnd_middle]
        _ = (productPull.i ≫ productPullData.middleMap) ≫ h.productSnd := by
              rw [Category.assoc]
        _ = h.productExtension.i ≫ h.productSnd := by
              rw [productPullData.i_map]
        _ = biprod.snd ≫ e₂.i := h.product_i_snd
        _ = biprod.snd ≫
              ((shortExactExtensionPullback e₂ f).i ≫ e₂PullData.middleMap) := by
              rw [← e₂PullData.i_map]
        _ = (biprod.snd ≫ (shortExactExtensionPullback e₂ f).i) ≫
              e₂PullData.middleMap := by
              rw [Category.assoc]
    · calc
        (productPull.i ≫ productSnd) ≫ (shortExactExtensionPullback e₂ f).p =
            productPull.i ≫
              (productSnd ≫ (shortExactExtensionPullback e₂ f).p) := by
              rw [Category.assoc]
        _ = productPull.i ≫ (productPull.p ≫ biprod.snd) := by
              rw [productSnd_p]
        _ = 0 := by
              rw [← Category.assoc, productPull.zero, zero_comp]
        _ = (biprod.snd ≫ (shortExactExtensionPullback e₂ f).i) ≫
              (shortExactExtensionPullback e₂ f).p := by
              rw [Category.assoc, (shortExactExtensionPullback e₂ f).zero, comp_zero]
  have pullbackMap_condition :
      (stagePullData.middleMap ≫ h.pullbackMap) ≫ h.productExtension.p =
        (stagePull.p ≫ biprodDiag X') ≫ ff := by
    calc
      (stagePullData.middleMap ≫ h.pullbackMap) ≫ h.productExtension.p =
          stagePullData.middleMap ≫ (h.pullbackMap ≫ h.productExtension.p) := by
            rw [Category.assoc]
      _ = stagePullData.middleMap ≫ (h.pullbackExtension.p ≫ biprodDiag X) := by
            rw [h.pullback_p]
      _ = (stagePullData.middleMap ≫ h.pullbackExtension.p) ≫ biprodDiag X := by
            rw [Category.assoc]
      _ = (stagePull.p ≫ f) ≫ biprodDiag X := by
            rw [stagePullData.map_p]
      _ = stagePull.p ≫ (f ≫ biprodDiag X) := by
            rw [Category.assoc]
      _ = stagePull.p ≫ (biprodDiag X' ≫ ff) := by
            rw [h_diag_map]
      _ = (stagePull.p ≫ biprodDiag X') ≫ ff := by
            rw [Category.assoc]
  let pullbackMap : stagePull.middle ⟶ productPull.middle :=
    productPullData.isPullback.lift
      (stagePullData.middleMap ≫ h.pullbackMap)
      (stagePull.p ≫ biprodDiag X')
      pullbackMap_condition
  have pullbackMap_middle :
      pullbackMap ≫ productPullData.middleMap =
        stagePullData.middleMap ≫ h.pullbackMap := by
    simp [pullbackMap]
  have pullbackMap_p :
      pullbackMap ≫ productPull.p = stagePull.p ≫ biprodDiag X' := by
    change productPullData.isPullback.lift
        (stagePullData.middleMap ≫ h.pullbackMap)
        (stagePull.p ≫ biprodDiag X') pullbackMap_condition ≫
        productPull.p =
      stagePull.p ≫ biprodDiag X'
    exact productPullData.isPullback.lift_snd
      (stagePullData.middleMap ≫ h.pullbackMap)
      (stagePull.p ≫ biprodDiag X') pullbackMap_condition
  have pullbackMap_i : stagePull.i ≫ pullbackMap = productPull.i := by
    apply productPullData.isPullback.hom_ext
    · calc
        (stagePull.i ≫ pullbackMap) ≫ productPullData.middleMap =
            stagePull.i ≫ (pullbackMap ≫ productPullData.middleMap) := by
              rw [Category.assoc]
        _ = stagePull.i ≫ (stagePullData.middleMap ≫ h.pullbackMap) := by
              rw [pullbackMap_middle]
        _ = (stagePull.i ≫ stagePullData.middleMap) ≫ h.pullbackMap := by
              rw [Category.assoc]
        _ = h.pullbackExtension.i ≫ h.pullbackMap := by
              rw [stagePullData.i_map]
        _ = h.productExtension.i := h.pullback_i
        _ = productPull.i ≫ productPullData.middleMap := by
              rw [productPullData.i_map]
    · calc
        (stagePull.i ≫ pullbackMap) ≫ productPull.p =
            stagePull.i ≫ (pullbackMap ≫ productPull.p) := by
              rw [Category.assoc]
        _ = stagePull.i ≫ (stagePull.p ≫ biprodDiag X') := by
              rw [pullbackMap_p]
        _ = 0 := by
              rw [← Category.assoc, stagePull.zero, zero_comp]
        _ = productPull.i ≫ productPull.p := productPull.zero.symm
  have pushoutMap_condition :
      (stagePullData.middleMap ≫ h.pushoutMap) ≫ h.pushoutExtension.p =
        stagePull.p ≫ f := by
    calc
      (stagePullData.middleMap ≫ h.pushoutMap) ≫ h.pushoutExtension.p =
          stagePullData.middleMap ≫ (h.pushoutMap ≫ h.pushoutExtension.p) := by
            rw [Category.assoc]
      _ = stagePullData.middleMap ≫ h.pullbackExtension.p := by
            rw [h.pushout_p]
      _ = stagePull.p ≫ f := stagePullData.map_p
  let pushoutMap : stagePull.middle ⟶ finalPull.middle :=
    finalPullData.isPullback.lift
      (stagePullData.middleMap ≫ h.pushoutMap)
      stagePull.p
      pushoutMap_condition
  have pushoutMap_middle :
      pushoutMap ≫ finalPullData.middleMap =
        stagePullData.middleMap ≫ h.pushoutMap := by
    simp [pushoutMap]
  have pushoutMap_p : pushoutMap ≫ finalPull.p = stagePull.p := by
    change finalPullData.isPullback.lift
        (stagePullData.middleMap ≫ h.pushoutMap)
        stagePull.p pushoutMap_condition ≫ finalPull.p =
      stagePull.p
    exact finalPullData.isPullback.lift_snd
      (stagePullData.middleMap ≫ h.pushoutMap)
      stagePull.p pushoutMap_condition
  have pushoutMap_i : biprodCodiag Y ≫ finalPull.i = stagePull.i ≫ pushoutMap := by
    apply finalPullData.isPullback.hom_ext
    · calc
        (biprodCodiag Y ≫ finalPull.i) ≫ finalPullData.middleMap =
            biprodCodiag Y ≫ (finalPull.i ≫ finalPullData.middleMap) := by
              rw [Category.assoc]
        _ = biprodCodiag Y ≫ h.pushoutExtension.i := by
              rw [finalPullData.i_map]
        _ = h.pullbackExtension.i ≫ h.pushoutMap := h.pushout_i
        _ = (stagePull.i ≫ stagePullData.middleMap) ≫ h.pushoutMap := by
              rw [stagePullData.i_map]
        _ = stagePull.i ≫ (stagePullData.middleMap ≫ h.pushoutMap) := by
              rw [Category.assoc]
        _ = stagePull.i ≫ (pushoutMap ≫ finalPullData.middleMap) := by
              rw [pushoutMap_middle]
        _ = (stagePull.i ≫ pushoutMap) ≫ finalPullData.middleMap := by
              rw [Category.assoc]
    · calc
        (biprodCodiag Y ≫ finalPull.i) ≫ finalPull.p =
            biprodCodiag Y ≫ (finalPull.i ≫ finalPull.p) := by
              rw [Category.assoc]
        _ = 0 := by
              rw [finalPull.zero, comp_zero]
        _ = stagePull.i ≫ stagePull.p := stagePull.zero.symm
        _ = (stagePull.i ≫ pushoutMap) ≫ finalPull.p := by
              rw [Category.assoc, pushoutMap_p]
  refine
    { productExtension := productPull
      productFst := productFst
      productSnd := productSnd
      product_i_fst := productFst_i
      product_i_snd := productSnd_i
      product_p_fst := productFst_p
      product_p_snd := productSnd_p
      pullbackExtension := stagePull
      pullbackMap := pullbackMap
      pullback_i := pullbackMap_i
      pullback_p := pullbackMap_p
      pushoutExtension := finalPull
      pushoutMap := pushoutMap
      pushout_i := pushoutMap_i
      pushout_p := pushoutMap_p
      sumIso := shortExactExtensionPullbackIso f h.sumIso }

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

/-- The head one-fold extension of a positive-degree Yoneda chain. -/
def headExtension :
    {X Y : C} → {n : ℕ} → YonedaExtension X Y (n + 1) →
      Σ Z : C, ShortExactExtension X Z
  | _, _, _, YonedaExtension.cons e _ => ⟨_, e⟩

/-- The head left map of a positive-degree Yoneda chain is an inflation. -/
theorem head_inflation_i {X Y : C} {n : ℕ} (a : YonedaExtension X Y (n + 1)) :
    QuillenExactCategory.inflation (headExtension a).2.i :=
  (headExtension a).2.inflation_i

/-- The head right map of a positive-degree Yoneda chain is a deflation. -/
theorem head_deflation_p {X Y : C} {n : ℕ} (a : YonedaExtension X Y (n + 1)) :
    QuillenExactCategory.deflation (headExtension a).2.p :=
  (headExtension a).2.deflation_p

/-- Pull back the head one-fold extension using a supplied pullback operation. -/
def pullbackHeadWith {X X' Y : C} (_f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z) :
    {n : ℕ} → YonedaExtension X Y (n + 1) → YonedaExtension X' Y (n + 1)
  | _, YonedaExtension.cons e tail => YonedaExtension.cons (pull e) tail

/-- Compose a degree-zero hom onto the right end of a positive Yoneda chain. -/
def composeTailHom {X Y Y' : C} (f : Y ⟶ Y') :
    {n : ℕ} → YonedaExtension X Y (n + 1) → YonedaExtension X Y' (n + 1)
  | 0, YonedaExtension.cons e (YonedaExtension.ofHom g) =>
      YonedaExtension.cons e (YonedaExtension.ofHom (g ≫ f))
  | n + 1, YonedaExtension.cons e tail =>
      YonedaExtension.cons e (composeTailHom f tail)

/-- Normalize right composition by recursively pushing out the tail extension. -/
def pushoutTailWith {X Y Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y') :
    {n : ℕ} → YonedaExtension X Y (n + 1) → YonedaExtension X Y' (n + 1)
  | 0, YonedaExtension.cons e (YonedaExtension.ofHom g) =>
      (push e (g ≫ f)).toYonedaExtension
  | n + 1, YonedaExtension.cons e tail =>
      YonedaExtension.cons e (pushoutTailWith f push tail)

/-- The chain relation generated by hom equality and termwise isomorphism of extensions. -/
inductive Rel :
    {X Y : C} → {n : ℕ} → YonedaExtension X Y n → YonedaExtension X Y n → Prop
  | ofHom {X Y : C} {f g : X ⟶ Y} (h : f = g) :
      Rel (YonedaExtension.ofHom f) (YonedaExtension.ofHom g)
  | cons {X Y Z : C} {n : ℕ} {e e' : ShortExactExtension X Z}
      {tail tail' : YonedaExtension Z Y n}
      (he : ShortExactExtension.Iso e e') (ht : Rel tail tail') :
      Rel (YonedaExtension.cons e tail) (YonedaExtension.cons e' tail')

/-- Reflexivity for the termwise Yoneda-chain relation. -/
def Rel.refl : {X Y : C} → {n : ℕ} → (a : YonedaExtension X Y n) → Rel a a
  | _, _, 0, YonedaExtension.ofHom _ => Rel.ofHom rfl
  | _, _, _ + 1, YonedaExtension.cons e tail =>
      Rel.cons (ShortExactExtension.Iso.refl e) (Rel.refl tail)

/-- Tail hom composition preserves termwise relations of positive chains. -/
def Rel.composeTailHom {X Y Y' : C} (f : Y ⟶ Y') :
    {n : ℕ} → {a b : YonedaExtension X Y (n + 1)} → Rel a b →
      Rel (YonedaExtension.composeTailHom f a) (YonedaExtension.composeTailHom f b)
  | 0, YonedaExtension.cons e (YonedaExtension.ofHom g),
      YonedaExtension.cons e' (YonedaExtension.ofHom g'), Rel.cons he (Rel.ofHom h) => by
      refine Rel.cons he (Rel.ofHom ?_)
      rw [h]
  | n + 1, YonedaExtension.cons e tail, YonedaExtension.cons e' tail',
      Rel.cons he htail =>
      Rel.cons he (Rel.composeTailHom f htail)

/-- Head pullback preserves termwise relations when one-fold pullback preserves isomorphisms. -/
def Rel.pullbackHeadWith {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → (e : ShortExactExtension X Z) → ShortExactExtension X' Z)
    (pullIso : ∀ {Z : C} {e e' : ShortExactExtension X Z},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull e) (pull e')) :
    {n : ℕ} → {a b : YonedaExtension X Y (n + 1)} → Rel a b →
      Rel (YonedaExtension.pullbackHeadWith f pull a)
        (YonedaExtension.pullbackHeadWith f pull b)
  | _, _, _, Rel.cons he htail =>
      Rel.cons (pullIso he) htail

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

/-- Reflexivity for recursive chain isomorphism. -/
def RelIso.refl : {X Y : C} → {n : ℕ} → (a : YonedaExtension X Y n) →
    RelIso (CategoryTheory.Iso.refl X) a a
  | _, _, 0, YonedaExtension.ofHom _ => RelIso.ofHom _ (by simp)
  | _, _, _ + 1, YonedaExtension.cons e tail =>
      RelIso.cons (ShortExactExtension.IsoBetween.refl e) (RelIso.refl tail)

/-- Tail hom composition preserves recursive isomorphism of positive chains. -/
def RelIso.composeTailHom {X X' Y Y' : C} {α : X ≅ X'} (f : Y ⟶ Y') :
    {n : ℕ} → {a : YonedaExtension X Y (n + 1)} →
      {b : YonedaExtension X' Y (n + 1)} → RelIso α a b →
        RelIso α (YonedaExtension.composeTailHom f a) (YonedaExtension.composeTailHom f b)
  | 0, YonedaExtension.cons e (YonedaExtension.ofHom g),
      YonedaExtension.cons e' (YonedaExtension.ofHom g'), RelIso.cons he htail => by
      cases htail with
      | ofHom β h =>
          refine RelIso.cons he (RelIso.ofHom _ ?_)
          rw [h, Category.assoc]
  | n + 1, YonedaExtension.cons e tail, YonedaExtension.cons e' tail',
      RelIso.cons he htail =>
      RelIso.cons he (RelIso.composeTailHom f htail)

/--
Head pullback preserves recursive chain isomorphisms when one-fold pullback
preserves `IsoBetween` over identity quotient endpoints.
-/
def RelIso.pullbackHeadWith {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → (e : ShortExactExtension X Z) → ShortExactExtension X' Z)
    (pullIsoBetween :
      ∀ {Z Z' : C} {β : Z ≅ Z'} {e : ShortExactExtension X Z}
        {e' : ShortExactExtension X Z'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X') β (pull e) (pull e')) :
    {n : ℕ} → {a b : YonedaExtension X Y (n + 1)} →
      RelIso (CategoryTheory.Iso.refl X) a b →
        RelIso (CategoryTheory.Iso.refl X')
          (YonedaExtension.pullbackHeadWith f pull a)
          (YonedaExtension.pullbackHeadWith f pull b)
  | _, _, _, RelIso.cons he htail =>
      RelIso.cons (pullIsoBetween he) htail

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
  | head {X Y Z : C} {n : ℕ} [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
      {e₁ e₂ sum : ShortExactExtension X Y}
      (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
      (tail : YonedaExtension Y Z (n + 1)) :
      BaerSumData (YonedaExtension.cons e₁ tail) (YonedaExtension.cons e₂ tail)
        (YonedaExtension.cons sum tail)
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

/-- A chain whose rightmost factor is split also contains a split factor. -/
def RightSplitData.toSplitFactorData :
    {X Y : C} → {n : ℕ} → {a : YonedaExtension X Y (n + 1)} →
      RightSplitData a → SplitFactorData a
  | _, _, 0, _, RightSplitData.one e s =>
      SplitFactorData.head e s (YonedaExtension.ofHom (𝟙 _))
  | _, _, _ + 1, _, RightSplitData.cons e h =>
      SplitFactorData.cons e h.toSplitFactorData

/-- Data reducing a degree-zero hom tail by pushing out the preceding extension. -/
inductive HomTailData :
    {X Y : C} → {n : ℕ} →
      YonedaExtension X Y (n + 1) →
      YonedaExtension X Y (n + 1) → Type (max u v)
  | one {X Y Y' : C} (e : ShortExactExtension X Y) (f : Y ⟶ Y')
      {out : ShortExactExtension X Y'}
      (h : ShortExactExtension.PushoutData e f out) :
      HomTailData (YonedaExtension.cons e (YonedaExtension.ofHom f)) out.toYonedaExtension
  | cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      {tail tail' : YonedaExtension Z Y (n + 1)}
      (h : HomTailData tail tail') :
      HomTailData (YonedaExtension.cons e tail) (YonedaExtension.cons e tail')

/-- Data describing the action of a degree-zero hom on the head of a positive chain. -/
inductive HomHeadData {X X' : C} (f : X' ⟶ X) :
    {Y : C} → {n : ℕ} →
      YonedaExtension X Y (n + 1) →
      YonedaExtension X' Y (n + 1) → Type (max u v)
  | cons {Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      {out : ShortExactExtension X' Z}
      (h : ShortExactExtension.PullbackData e f out)
      (tail : YonedaExtension Z Y n) :
      HomHeadData f (YonedaExtension.cons e tail) (YonedaExtension.cons out tail)

/-- Supplied pullback data witnesses the induced head action on a positive chain. -/
def pullbackHeadWithData {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → (e : ShortExactExtension X Z) → ShortExactExtension X' Z)
    (h : ∀ {Z : C} (e : ShortExactExtension X Z),
      ShortExactExtension.PullbackData e f (pull e)) :
    {n : ℕ} → (a : YonedaExtension X Y (n + 1)) →
      HomHeadData f a (pullbackHeadWith f pull a)
  | _, YonedaExtension.cons e tail => HomHeadData.cons e (h e) tail

/-- Pulling back the head of a chain preserves hom-tail data, provided
one-fold pullbacks preserve the supplied pushout data. -/
def HomTailData.pullbackHeadWith {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullPushoutData :
      ∀ {Z W : C} (e : ShortExactExtension X Z) (g : Z ⟶ W)
        {out : ShortExactExtension X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull e) g (pull out)) :
    {n : ℕ} → {a b : YonedaExtension X Y (n + 1)} →
      HomTailData a b →
        HomTailData (YonedaExtension.pullbackHeadWith f pull a)
          (YonedaExtension.pullbackHeadWith f pull b)
  | _, _, _, HomTailData.one e g h =>
      HomTailData.one (pull e) g (pullPushoutData e g h)
  | _, _, _, HomTailData.cons e h =>
      HomTailData.cons (pull e) h

/--
Pulling back the head of a chain preserves the right-split marker, provided
one-fold pullbacks preserve the chosen splitting.
-/
def RightSplitData.pullbackHeadWith {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → (e : ShortExactExtension X Z) → ShortExactExtension X' Z)
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting) :
    {n : ℕ} → {a : YonedaExtension X Y (n + 1)} →
      RightSplitData a → RightSplitData (YonedaExtension.pullbackHeadWith f pull a)
  | 0, _, RightSplitData.one e s => by
      simpa [ShortExactExtension.toYonedaExtension, YonedaExtension.pullbackHeadWith] using
        RightSplitData.one (pull e) (pullSplit e s)
  | n + 1, _, RightSplitData.cons e h => by
      simpa [YonedaExtension.pullbackHeadWith] using
        RightSplitData.cons (pull e) h

/--
Pulling back the head of a chain preserves the existence of a split factor,
provided one-fold pullbacks preserve the chosen splitting.
-/
def SplitFactorData.pullbackHeadWith {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → (e : ShortExactExtension X Z) → ShortExactExtension X' Z)
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting) :
    {n : ℕ} → {a : YonedaExtension X Y (n + 1)} →
      SplitFactorData a → SplitFactorData (YonedaExtension.pullbackHeadWith f pull a)
  | _, _, SplitFactorData.head e s tail => by
      simpa [YonedaExtension.pullbackHeadWith] using
        SplitFactorData.head (pull e) (pullSplit e s) tail
  | _, _, SplitFactorData.cons e h => by
      simpa [YonedaExtension.pullbackHeadWith] using
        SplitFactorData.cons (pull e) h

/-- Recursive pushout data identifies tail-hom composition with its pushout normal form. -/
def pushoutTailWithData {X Y Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (h : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g)) :
    {n : ℕ} → (a : YonedaExtension X Y (n + 1)) →
      HomTailData (composeTailHom f a) (pushoutTailWith f push a)
  | 0, YonedaExtension.cons e (YonedaExtension.ofHom g) =>
      HomTailData.one e (g ≫ f) (h e (g ≫ f))
  | n + 1, YonedaExtension.cons e tail =>
      HomTailData.cons e (pushoutTailWithData f push h tail)

/--
Pushing out the right end of a chain preserves the right-split marker, provided
one-fold pushouts preserve the chosen splitting.
-/
def RightSplitData.pushoutTailWith {X Y Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting) :
    {n : ℕ} → {a : YonedaExtension X Y (n + 1)} →
      RightSplitData a → RightSplitData (YonedaExtension.pushoutTailWith f push a)
  | 0, _, RightSplitData.one e s => by
      simpa [ShortExactExtension.toYonedaExtension, YonedaExtension.pushoutTailWith,
        Category.id_comp] using
        RightSplitData.one (push e f) (pushSplit e f s)
  | n + 1, _, RightSplitData.cons e h => by
      simpa [YonedaExtension.pushoutTailWith] using
        RightSplitData.cons e (RightSplitData.pushoutTailWith f push pushSplit h)

/--
Pushing out the right end of a chain preserves the existence of a split factor,
provided one-fold pushouts preserve the chosen splitting.
-/
def SplitFactorData.pushoutTailWith {X Y Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting) :
    {n : ℕ} → {a : YonedaExtension X Y (n + 1)} →
      SplitFactorData a → SplitFactorData (YonedaExtension.pushoutTailWith f push a)
  | 0, _, SplitFactorData.head e s (YonedaExtension.ofHom g) => by
      simpa [ShortExactExtension.toYonedaExtension, YonedaExtension.pushoutTailWith] using
        SplitFactorData.head (push e (g ≫ f)) (pushSplit e (g ≫ f) s)
          (YonedaExtension.ofHom (𝟙 Y'))
  | n + 1, _, SplitFactorData.head e s tail => by
      simpa [YonedaExtension.pushoutTailWith] using
        SplitFactorData.head e s (YonedaExtension.pushoutTailWith f push tail)
  | n + 1, _, SplitFactorData.cons e h => by
      simpa [YonedaExtension.pushoutTailWith] using
        SplitFactorData.cons e (SplitFactorData.pushoutTailWith f push pushSplit h)

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

/-- The head one-fold extension of a positive chain. -/
def headExtension :
    {X Y : C} → {n : ℕ} → PositiveChain X Y n → Σ Z : C, ShortExactExtension X Z
  | _, _, 0, one e => ⟨_, e⟩
  | _, _, _ + 1, cons e _ => ⟨_, e⟩

/-- The head left map of a positive chain is an inflation. -/
theorem head_inflation_i {X Y : C} {n : ℕ} (p : PositiveChain X Y n) :
    QuillenExactCategory.inflation (headExtension p).2.i :=
  (headExtension p).2.inflation_i

/-- The head right map of a positive chain is a deflation. -/
theorem head_deflation_p {X Y : C} {n : ℕ} (p : PositiveChain X Y n) :
    QuillenExactCategory.deflation (headExtension p).2.p :=
  (headExtension p).2.deflation_p

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

/-- Termwise isomorphism relation for positive chains. -/
inductive Rel :
    {X Y : C} → {n : ℕ} → PositiveChain X Y n → PositiveChain X Y n → Prop
  | one {X Y : C} {e e' : ShortExactExtension X Y}
      (h : ShortExactExtension.Iso e e') :
      Rel (one e) (one e')
  | cons {X Y Z : C} {n : ℕ} {e e' : ShortExactExtension X Z}
      {tail tail' : PositiveChain Z Y n}
      (he : ShortExactExtension.Iso e e') (ht : Rel tail tail') :
      Rel (cons e tail) (cons e' tail')

/-- Termwise-related positive chains give termwise-related Yoneda chains. -/
def Rel.toYonedaExtension :
    {X Y : C} → {n : ℕ} → {p q : PositiveChain X Y n} →
      Rel p q → YonedaExtension.Rel p.toYonedaExtension q.toYonedaExtension
  | _, _, 0, _, _, Rel.one h => by
      simpa [PositiveChain.toYonedaExtension, ShortExactExtension.toYonedaExtension] using
        YonedaExtension.Rel.cons h (YonedaExtension.Rel.ofHom rfl)
  | _, _, _ + 1, _, _, Rel.cons he ht => by
      simpa [PositiveChain.toYonedaExtension] using
        YonedaExtension.Rel.cons he ht.toYonedaExtension

/-- Termwise-related positive chains remain related after left splicing. -/
def Rel.consLeftMap :
    {X Y Z : C} → {m n : ℕ} → {p q : PositiveChain X Y m} →
      Rel p q → (a : YonedaExtension Y Z (n + 1)) →
        YonedaExtension.Rel (p.consLeftMap a) (q.consLeftMap a)
  | _, _, _, 0, _, _, _, Rel.one h, a => by
      simpa [PositiveChain.consLeftMap] using
        YonedaExtension.Rel.cons h (YonedaExtension.Rel.refl a)
  | _, _, _, _ + 1, _, _, _, Rel.cons he ht, a => by
      simpa [PositiveChain.consLeftMap, Nat.add_assoc] using
        YonedaExtension.Rel.cons he (ht.consLeftMap a)

/-- Witnessed Baer sums of positive chains. -/
inductive BaerSumData :
    {X Y : C} → {n : ℕ} →
      PositiveChain X Y n →
      PositiveChain X Y n →
      PositiveChain X Y n → Type (max u v)
  | one {X Y : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
      {e₁ e₂ sum : ShortExactExtension X Y}
      (h : ShortExactExtension.BaerSumData e₁ e₂ sum) :
      BaerSumData (one e₁) (one e₂) (one sum)
  | head {X Y Z : C} {n : ℕ} [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
      {e₁ e₂ sum : ShortExactExtension X Y}
      (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
      (tail : PositiveChain Y Z n) :
      BaerSumData (cons e₁ tail) (cons e₂ tail) (cons sum tail)
  | cons {X Y Z : C} {n : ℕ} (e : ShortExactExtension X Z)
      {a b sum : PositiveChain Z Y n}
      (h : BaerSumData a b sum) :
      BaerSumData (cons e a) (cons e b) (cons e sum)

/-- Positive-chain Baer sums give Yoneda-chain Baer sums. -/
def BaerSumData.toYonedaExtension :
    {X Y : C} → {n : ℕ} → {a b sum : PositiveChain X Y n} →
      BaerSumData a b sum →
        YonedaExtension.BaerSumData a.toYonedaExtension b.toYonedaExtension
          sum.toYonedaExtension
  | _, _, _, _, _, _, BaerSumData.one h => by
      simpa [PositiveChain.toYonedaExtension, ShortExactExtension.toYonedaExtension] using
        YonedaExtension.BaerSumData.one h
  | _, _, _, _, _, _, BaerSumData.head h tail => by
      simpa [PositiveChain.toYonedaExtension] using
        YonedaExtension.BaerSumData.head h tail.toYonedaExtension
  | _, _, _, _, _, _, BaerSumData.cons e h => by
      simpa [PositiveChain.toYonedaExtension] using
        YonedaExtension.BaerSumData.cons e h.toYonedaExtension

/-- Positive-chain Baer sums remain Baer sums after left splicing. -/
def BaerSumData.consLeftMap :
    {X Y Z : C} → {m n : ℕ} → {a b sum : PositiveChain X Y m} →
      BaerSumData a b sum → (tail : YonedaExtension Y Z (n + 1)) →
        YonedaExtension.BaerSumData (a.consLeftMap tail) (b.consLeftMap tail)
          (sum.consLeftMap tail)
  | _, _, _, 0, _, _, _, _, BaerSumData.one h, tail => by
      simpa [PositiveChain.consLeftMap] using
        YonedaExtension.BaerSumData.head h tail
  | _, _, _, _ + 1, _, _, _, _, BaerSumData.head h p, tail => by
      simpa [PositiveChain.consLeftMap, Nat.add_assoc] using
        YonedaExtension.BaerSumData.head h (p.consLeftMap tail)
  | _, _, _, _ + 1, _, _, _, _, BaerSumData.cons e h, tail => by
      simpa [PositiveChain.consLeftMap, Nat.add_assoc] using
        YonedaExtension.BaerSumData.cons e (h.consLeftMap tail)

end PositiveChain

/--
Splice an arbitrary left Yoneda chain against a positive right chain.

When the left chain ends in a degree-zero morphism, the head one-fold extension
of the right chain is pulled back along that morphism using the supplied
one-fold pullback operation.
-/
def spliceLeftWith
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W) :
    {X Y Z : C} → {m n : ℕ} →
      YonedaExtension X Y m → YonedaExtension Y Z (n + 1) →
        YonedaExtension X Z (n + m + 1)
  | _, _, _, 0, _, YonedaExtension.ofHom f, right =>
      YonedaExtension.pullbackHeadWith f (fun {_} e => pull f e) right
  | _, _, _, m + 1, n, YonedaExtension.cons e tail, right => by
      simpa [Nat.add_assoc] using
        YonedaExtension.cons e (spliceLeftWith pull (m := m) (n := n) tail right)

@[simp]
theorem spliceLeftWith_ofHom
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {X Y Z : C} {n : ℕ} (f : X ⟶ Y) (right : YonedaExtension Y Z (n + 1)) :
    spliceLeftWith pull (YonedaExtension.ofHom f) right =
      YonedaExtension.pullbackHeadWith f (fun {_} e => pull f e) right :=
  rfl

@[simp]
theorem spliceLeftWith_cons
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {X Y W Z : C} {m n : ℕ} (e : ShortExactExtension X W)
    (tail : YonedaExtension W Y m) (right : YonedaExtension Y Z (n + 1)) :
    spliceLeftWith pull (YonedaExtension.cons e tail) right =
      YonedaExtension.cons e (spliceLeftWith pull tail right) := by
  simp [spliceLeftWith]

@[simp]
theorem pullbackHeadWith_spliceLeftWith
    (pullLeft : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {X X' Y Z : C} {m n : ℕ} (f : X' ⟶ X)
    (pullHead : {W : C} → ShortExactExtension X W → ShortExactExtension X' W)
    (left : YonedaExtension X Y (m + 1))
    (right : YonedaExtension Y Z (n + 1)) :
    YonedaExtension.pullbackHeadWith f pullHead
        (YonedaExtension.spliceLeftWith pullLeft left right) =
      YonedaExtension.spliceLeftWith pullLeft
        (YonedaExtension.pullbackHeadWith f pullHead left) right := by
  cases left with
  | cons e tail =>
      simp [YonedaExtension.pullbackHeadWith]

@[simp]
theorem composeTailHom_pullbackHeadWith
    {X X' Y Y' : C} {n : ℕ} (f : X' ⟶ X) (g : Y ⟶ Y')
    (pull : {W : C} → ShortExactExtension X W → ShortExactExtension X' W)
    (right : YonedaExtension X Y (n + 1)) :
    YonedaExtension.composeTailHom g (YonedaExtension.pullbackHeadWith f pull right) =
      YonedaExtension.pullbackHeadWith f pull (YonedaExtension.composeTailHom g right) := by
  cases right with
  | cons e tail =>
      cases tail with
      | ofHom h => rfl
      | cons e' tail' => rfl

@[simp]
theorem composeTailHom_spliceLeftWith
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {X Y Z Z' : C} {m n : ℕ}
    (left : YonedaExtension X Y m) (right : YonedaExtension Y Z (n + 1))
    (f : Z ⟶ Z') :
    YonedaExtension.composeTailHom f (YonedaExtension.spliceLeftWith pull left right) =
      YonedaExtension.spliceLeftWith pull left (YonedaExtension.composeTailHom f right) := by
  induction left with
  | ofHom g =>
      exact composeTailHom_pullbackHeadWith g f (fun {_} e => pull g e) right
  | cons e tail ih =>
      simp [YonedaExtension.composeTailHom, ih]

/-- Two successive left splices are heterogeneously equal after reassociating their degree. -/
theorem spliceLeftWith_assoc_heq
    (pull₁ pull₂ : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {X W Y Z : C} {m n l : ℕ}
    (a : YonedaExtension X W (m + 1))
    (b : YonedaExtension W Y (n + 1))
    (c : YonedaExtension Y Z (l + 1)) :
    HEq
      (YonedaExtension.spliceLeftWith pull₂
        (YonedaExtension.spliceLeftWith pull₁ a b) c)
      (YonedaExtension.spliceLeftWith pull₁ a
        (YonedaExtension.spliceLeftWith pull₂ b c)) := by
  cases a with
  | cons e tail =>
      induction tail generalizing X with
      | ofHom f =>
          simp [YonedaExtension.spliceLeftWith]
      | cons e' tail' ih =>
          simp only [spliceLeftWith_cons]
          congr! 1
          · omega
          · exact ih (X := _) b e'

/-- Termwise-related arbitrary left chains remain related after splicing. -/
def Rel.spliceLeftWith
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W) :
    {X Y Z : C} → {m n : ℕ} → {a b : YonedaExtension X Y m} →
      Rel a b → (right : YonedaExtension Y Z (n + 1)) →
        Rel (spliceLeftWith pull a right) (spliceLeftWith pull b right)
  | _, _, _, 0, _, YonedaExtension.ofHom f, YonedaExtension.ofHom _, Rel.ofHom h, right => by
      cases h
      exact Rel.refl (YonedaExtension.spliceLeftWith pull (YonedaExtension.ofHom f) right)
  | _, _, _, m + 1, n, _, _, Rel.cons he ht, right => by
      simpa [spliceLeftWith, Nat.add_assoc] using
        Rel.cons he (Rel.spliceLeftWith pull ht right)

/-- Arbitrary left Baer relations remain Baer relations after splicing. -/
def BaerSumData.spliceLeftWith
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W) :
    {X Y Z : C} → {m n : ℕ} →
      {a b sum : YonedaExtension X Y (m + 1)} →
        BaerSumData a b sum → (right : YonedaExtension Y Z (n + 1)) →
          BaerSumData (spliceLeftWith pull a right) (spliceLeftWith pull b right)
            (spliceLeftWith pull sum right)
  | _, _, _, 0, _, _, _, _, BaerSumData.one h, right => by
      simpa [ShortExactExtension.toYonedaExtension, YonedaExtension.spliceLeftWith] using
        BaerSumData.head h
          (YonedaExtension.spliceLeftWith pull (YonedaExtension.ofHom (𝟙 _)) right)
  | _, _, _, _ + 1, _, _, _, _, BaerSumData.head h tail, right => by
      simpa [YonedaExtension.spliceLeftWith, Nat.add_assoc] using
        BaerSumData.head h (YonedaExtension.spliceLeftWith pull tail right)
  | _, _, _, _ + 1, _, _, _, _, BaerSumData.cons e h, right => by
      simpa [YonedaExtension.spliceLeftWith, Nat.add_assoc] using
        BaerSumData.cons e (BaerSumData.spliceLeftWith pull h right)

/-- Arbitrary left chains with a split factor still have one after splicing. -/
def SplitFactorData.spliceLeftWith
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W) :
    {X Y Z : C} → {m n : ℕ} → {a : YonedaExtension X Y (m + 1)} →
      SplitFactorData a → (right : YonedaExtension Y Z (n + 1)) →
        SplitFactorData (spliceLeftWith pull a right)
  | _, _, _, _, _, _, SplitFactorData.head e s tail, right => by
      simpa [YonedaExtension.spliceLeftWith, Nat.add_assoc] using
        SplitFactorData.head e s (YonedaExtension.spliceLeftWith pull tail right)
  | _, _, _, _, _, _, SplitFactorData.cons e h, right => by
      simpa [YonedaExtension.spliceLeftWith, Nat.add_assoc] using
        SplitFactorData.cons e (SplitFactorData.spliceLeftWith pull h right)

end YonedaExtension

namespace MetrizableLCA

/-- Pull back the head one-fold extension of a positive Yoneda chain in `MetrizableLCA`. -/
noncomputable def yonedaExtensionPullbackHead
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) {n : ℕ} :
    YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1) →
      YonedaExtension (C := MetrizableLCA.{u}) X' Y (n + 1) :=
  YonedaExtension.pullbackHeadWith (C := MetrizableLCA.{u}) f
    (fun {_} e => shortExactExtensionPullback e f)

/-- The canonical MetrizableLCA head pullback carries diagrammatic pullback data. -/
noncomputable def yonedaExtensionPullbackHeadData
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) {n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)) :
    YonedaExtension.HomHeadData (C := MetrizableLCA.{u}) f a
      (yonedaExtensionPullbackHead f a) :=
  YonedaExtension.pullbackHeadWithData (C := MetrizableLCA.{u}) f
    (fun {_} e => shortExactExtensionPullback e f)
    (fun {_} e => shortExactExtensionPullbackData e f)
    a

/-- Canonical MetrizableLCA head pullback preserves a right-split marker. -/
noncomputable def yonedaExtensionPullbackHeadRightSplitData
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData (C := MetrizableLCA.{u}) a) :
    YonedaExtension.RightSplitData (C := MetrizableLCA.{u})
      (yonedaExtensionPullbackHead f a) :=
  YonedaExtension.RightSplitData.pullbackHeadWith (C := MetrizableLCA.{u}) f
    (fun {_} e => shortExactExtensionPullback e f)
    (fun {_} e s => shortExactExtensionPullbackSplitting e f s)
    h

/-- Canonical MetrizableLCA head pullback preserves a split-factor marker. -/
noncomputable def yonedaExtensionPullbackHeadSplitFactorData
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData (C := MetrizableLCA.{u}) a) :
    YonedaExtension.SplitFactorData (C := MetrizableLCA.{u})
      (yonedaExtensionPullbackHead f a) :=
  YonedaExtension.SplitFactorData.pullbackHeadWith (C := MetrizableLCA.{u}) f
    (fun {_} e => shortExactExtensionPullback e f)
    (fun {_} e s => shortExactExtensionPullbackSplitting e f s)
    h

/-- Canonical MetrizableLCA head pullback preserves termwise chain relations. -/
noncomputable def yonedaExtensionPullbackHeadRel
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)}
    (h : YonedaExtension.Rel a b) :
    YonedaExtension.Rel (C := MetrizableLCA.{u})
      (yonedaExtensionPullbackHead f a) (yonedaExtensionPullbackHead f b) :=
  YonedaExtension.Rel.pullbackHeadWith (C := MetrizableLCA.{u}) f
    (fun {_} e => shortExactExtensionPullback e f)
    (fun {_} {_ _} h => shortExactExtensionPullbackIso f h)
    h

/-- Canonical MetrizableLCA head pullback preserves recursive chain isomorphisms. -/
noncomputable def yonedaExtensionPullbackHeadRelIso
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) {n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) :
    YonedaExtension.RelIso (C := MetrizableLCA.{u}) (CategoryTheory.Iso.refl X')
      (yonedaExtensionPullbackHead f a) (yonedaExtensionPullbackHead f b) :=
  YonedaExtension.RelIso.pullbackHeadWith (C := MetrizableLCA.{u}) f
    (fun {_} e => shortExactExtensionPullback e f)
    (fun {_ _} {_} {_ _} h => shortExactExtensionPullbackIsoBetween f h)
    h

/-- Pulling back a positive MetrizableLCA chain along the identity is termwise related to it. -/
noncomputable def yonedaExtensionPullbackHeadIdRel
    {X Y : MetrizableLCA.{u}} :
    {n : ℕ} → (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)) →
      YonedaExtension.Rel (C := MetrizableLCA.{u})
        (YonedaExtension.pullbackHeadWith (C := MetrizableLCA.{u}) (𝟙 X)
          (fun {_} e => shortExactExtensionPullback e (𝟙 X)) a)
        a
  | _, YonedaExtension.cons e tail =>
      YonedaExtension.Rel.cons (shortExactExtensionPullbackIdIso e)
        (YonedaExtension.Rel.refl tail)

/-- Push out the tail of a positive Yoneda chain in `MetrizableLCA`. -/
noncomputable def yonedaExtensionPushoutTail
    {X Y Y' : MetrizableLCA.{u}} (f : Y ⟶ Y') {n : ℕ} :
    YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1) →
      YonedaExtension (C := MetrizableLCA.{u}) X Y' (n + 1) :=
  YonedaExtension.pushoutTailWith (C := MetrizableLCA.{u}) f
    (fun {_ _} e g => shortExactExtensionPushout e g)

/-- The canonical MetrizableLCA tail pushout carries recursive hom-tail data. -/
noncomputable def yonedaExtensionPushoutTailData
    {X Y Y' : MetrizableLCA.{u}} (f : Y ⟶ Y') {n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)) :
    YonedaExtension.HomTailData (C := MetrizableLCA.{u})
      (YonedaExtension.composeTailHom f a) (yonedaExtensionPushoutTail f a) :=
  YonedaExtension.pushoutTailWithData (C := MetrizableLCA.{u}) f
    (fun {_ _} e g => shortExactExtensionPushout e g)
    (fun {_ _} e g => shortExactExtensionPushoutData e g)
    a

/-- Pushing out a one-fold MetrizableLCA extension along the identity does not change it. -/
noncomputable def yonedaExtensionPushoutTailIdRel
    {X Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    YonedaExtension.Rel (C := MetrizableLCA.{u})
      (shortExactExtensionPushout e (𝟙 Y)).toYonedaExtension e.toYonedaExtension :=
  YonedaExtension.Rel.cons (shortExactExtensionPushoutIdIso e)
    (YonedaExtension.Rel.ofHom rfl)

/-- Pulling back an identity-tail pushout does not change the pulled-back one-fold chain. -/
noncomputable def yonedaExtensionPullbackPushoutTailIdRel
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) :
    YonedaExtension.Rel (C := MetrizableLCA.{u})
      (shortExactExtensionPullback (shortExactExtensionPushout e (𝟙 Y)) f).toYonedaExtension
      (shortExactExtensionPullback e f).toYonedaExtension :=
  YonedaExtension.Rel.cons (shortExactExtensionPullbackPushoutIdIso e f)
    (YonedaExtension.Rel.ofHom rfl)

/-- Canonical MetrizableLCA tail pushout preserves a right-split marker. -/
noncomputable def yonedaExtensionPushoutTailRightSplitData
    {X Y Y' : MetrizableLCA.{u}} (f : Y ⟶ Y') {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)}
    (h : YonedaExtension.RightSplitData (C := MetrizableLCA.{u}) a) :
    YonedaExtension.RightSplitData (C := MetrizableLCA.{u})
      (yonedaExtensionPushoutTail f a) :=
  YonedaExtension.RightSplitData.pushoutTailWith (C := MetrizableLCA.{u}) f
    (fun {_ _} e g => shortExactExtensionPushout e g)
    (fun {_ _} e g s => shortExactExtensionPushoutSplitting e g s)
    h

/-- Canonical MetrizableLCA tail pushout preserves a split-factor marker. -/
noncomputable def yonedaExtensionPushoutTailSplitFactorData
    {X Y Y' : MetrizableLCA.{u}} (f : Y ⟶ Y') {n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData (C := MetrizableLCA.{u}) a) :
    YonedaExtension.SplitFactorData (C := MetrizableLCA.{u})
      (yonedaExtensionPushoutTail f a) :=
  YonedaExtension.SplitFactorData.pushoutTailWith (C := MetrizableLCA.{u}) f
    (fun {_ _} e g => shortExactExtensionPushout e g)
    (fun {_ _} e g s => shortExactExtensionPushoutSplitting e g s)
    h

end MetrizableLCA

namespace YonedaExtension

/--
Canonical MetrizableLCA head pullbacks along isomorphic quotient-endpoint maps
produce recursively isomorphic pulled-back chains.
-/
noncomputable def RelIso.pullbackHeadDomain_metrizable
    {X X' Y Z : MetrizableLCA.{u}} {α : X ≅ X'}
    {f : X ⟶ Y} {g : X' ⟶ Y} (hfg : f = α.hom ≫ g) :
    {n : ℕ} → (right : YonedaExtension (C := MetrizableLCA.{u}) Y Z (n + 1)) →
      RelIso (C := MetrizableLCA.{u}) α
        (YonedaExtension.pullbackHeadWith (C := MetrizableLCA.{u}) f
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) right)
        (YonedaExtension.pullbackHeadWith (C := MetrizableLCA.{u}) g
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e g) right)
  | _, YonedaExtension.cons e tail =>
      RelIso.cons
        (MetrizableLCA.shortExactExtensionPullbackDomainIsoBetween α e f g hfg)
        (RelIso.refl tail)

/-- MetrizableLCA left splicing preserves recursive chain isomorphisms. -/
noncomputable def RelIso.spliceLeftWith_metrizable :
    {X X' Y Z : MetrizableLCA.{u}} → {α : X ≅ X'} → {m n : ℕ} →
      {a : YonedaExtension (C := MetrizableLCA.{u}) X Y m} →
      {b : YonedaExtension (C := MetrizableLCA.{u}) X' Y m} →
      RelIso (C := MetrizableLCA.{u}) α a b →
      (right : YonedaExtension (C := MetrizableLCA.{u}) Y Z (n + 1)) →
        RelIso (C := MetrizableLCA.{u}) α
          (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
            (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a right)
          (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
            (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) b right)
  | _, _, _, _, _, 0, _, YonedaExtension.ofHom f, YonedaExtension.ofHom g,
      RelIso.ofHom α hfg, right =>
      RelIso.pullbackHeadDomain_metrizable hfg right
  | _, _, _, _, _, _ + 1, _, _, _, RelIso.cons he htail, right => by
      simpa [YonedaExtension.spliceLeftWith, Nat.add_assoc] using
        RelIso.cons he (RelIso.spliceLeftWith_metrizable htail right)

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
  | homTail {n : ℕ} {a b : YonedaExtension X Y (n + 1)}
      (h : YonedaExtension.HomTailData a b) :
      YonedaRelGenerator X Y n (FreeAbelianGroup.of a - FreeAbelianGroup.of b)
  | homTailLeft {W : C} {m n : ℕ}
      (pull : {A B V : C} → (f : A ⟶ B) → ShortExactExtension B V →
        ShortExactExtension A V)
      {a b : YonedaExtension X W (m + 1)}
      (h : YonedaExtension.HomTailData a b)
      (c : YonedaExtension W Y (n + 1)) :
      YonedaRelGenerator X Y (n + (m + 1))
        (FreeAbelianGroup.of (YonedaExtension.spliceLeftWith pull a c) -
          FreeAbelianGroup.of (YonedaExtension.spliceLeftWith pull b c))

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

/-- The generator associated to a positive chain whose factors are one-fold extensions. -/
def ofPositiveChain (p : YonedaExtension.PositiveChain X Y n) : YonedaExt X Y (n + 1) :=
  ofExtension p.toYonedaExtension

@[simp]
theorem ofPositiveChain_eq_ofExtension (p : YonedaExtension.PositiveChain X Y n) :
    ofPositiveChain (X := X) (Y := Y) p =
      ofExtension (X := X) (Y := Y) p.toYonedaExtension :=
  rfl

/--
The `Ext¹` class represented by a strict short exact sequence of metrizable
LCA groups, using the canonical exact-category structure.
-/
def ofStrictShortExact {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero)) :
    YonedaExt (C := MetrizableLCA.{u}) X Y 1 :=
  ofExtension (C := MetrizableLCA.{u})
    ((MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension)

@[simp]
theorem ofStrictShortExact_eq_ofExtension
    {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero)) :
    ofStrictShortExact i p zero h =
      ofExtension (C := MetrizableLCA.{u})
        ((MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension) :=
  rfl

/-- Transport formal positive-degree generators across propositionally equal degrees. -/
def positiveYonedaExtFreeCast {X Y : C} {n n' : ℕ} (h : n = n') :
    PositiveYonedaExtFree X Y n →+ PositiveYonedaExtFree X Y n' :=
  FreeAbelianGroup.map (fun a => cast (by rw [h]) a)

/-- The local relation subgroup is stable under degree transports. -/
theorem positiveYonedaExtFreeCast_relationSubgroup_mem {X Y : C} {n n' : ℕ}
    (h : n = n') {x : PositiveYonedaExtFree X Y n}
    (hx : x ∈ yonedaRelationSubgroup X Y n) :
    positiveYonedaExtFreeCast (C := C) (X := X) (Y := Y) h x ∈
      yonedaRelationSubgroup X Y n' := by
  cases h
  change (FreeAbelianGroup.map id) x ∈ yonedaRelationSubgroup X Y n
  simpa [FreeAbelianGroup.map_id_apply] using hx

/-- Quotient-level positive-degree Yoneda Ext cast induced by a degree equality. -/
noncomputable def positiveYonedaExtCast {X Y : C} {n n' : ℕ} (h : n = n') :
    PositiveYonedaExt X Y n →+ PositiveYonedaExt X Y n' :=
  QuotientAddGroup.map (yonedaRelationSubgroup X Y n) (yonedaRelationSubgroup X Y n')
    (positiveYonedaExtFreeCast (C := C) (X := X) (Y := Y) h)
    (by
      intro x hx
      exact positiveYonedaExtFreeCast_relationSubgroup_mem
        (C := C) (X := X) (Y := Y) h hx)

@[simp]
theorem positiveYonedaExtCast_mk {X Y : C} {n n' : ℕ} (h : n = n')
    (x : PositiveYonedaExtFree X Y n) :
    positiveYonedaExtCast (C := C) (X := X) (Y := Y) h
        ((x : PositiveYonedaExtFree X Y n) : PositiveYonedaExt X Y n) =
      ((positiveYonedaExtFreeCast (C := C) (X := X) (Y := Y) h x :
        PositiveYonedaExtFree X Y n') : PositiveYonedaExt X Y n') := by
  exact QuotientAddGroup.map_mk (yonedaRelationSubgroup X Y n)
    (yonedaRelationSubgroup X Y n')
    (positiveYonedaExtFreeCast (C := C) (X := X) (Y := Y) h)
    (by
      intro y hy
      exact positiveYonedaExtFreeCast_relationSubgroup_mem
        (C := C) (X := X) (Y := Y) h hy)
    x

@[simp]
theorem positiveYonedaExtCast_ofExtension {X Y : C} {n n' : ℕ} (h : n = n')
    (a : YonedaExtension X Y (n + 1)) :
    positiveYonedaExtCast (C := C) (X := X) (Y := Y) h
        (ofExtension (C := C) (X := X) (Y := Y) (n := n) a) =
      ofExtension (C := C) (X := X) (Y := Y) (n := n') (cast (by rw [h]) a) := by
  exact positiveYonedaExtCast_mk (C := C) (X := X) (Y := Y) h (FreeAbelianGroup.of a)

@[simp]
theorem positiveYonedaExtCast_refl {X Y : C} {n : ℕ}
    (a : PositiveYonedaExt (C := C) X Y n) :
    positiveYonedaExtCast (C := C) (X := X) (Y := Y) (by rfl : n = n) a = a := by
  induction a using QuotientAddGroup.induction_on with
  | H x =>
      rw [positiveYonedaExtCast_mk]
      change ((FreeAbelianGroup.map id x :
        PositiveYonedaExtFree (C := C) X Y n) : PositiveYonedaExt (C := C) X Y n) =
        (x : PositiveYonedaExt (C := C) X Y n)
      simp [FreeAbelianGroup.map_id_apply]

/-- Generator-level pullback action by a degree-zero head hom, before quotient descent. -/
noncomputable def pullbackHeadOfExtensionWith {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    {n : ℕ} (a : YonedaExtension X Y (n + 1)) : YonedaExt X' Y (n + 1) :=
  ofExtension (YonedaExtension.pullbackHeadWith f pull a)

/-- Generator-level pushout action by a degree-zero tail hom, before quotient descent. -/
noncomputable def pushoutTailOfExtensionWith {X Y Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    {n : ℕ} (a : YonedaExtension X Y (n + 1)) : YonedaExt X Y' (n + 1) :=
  ofExtension (YonedaExtension.pushoutTailWith f push a)

/-- The free abelian group map induced by composing a degree-zero hom on the tail. -/
def composeTailHomFreeHom {X Y Y' : C} (f : Y ⟶ Y') (n : ℕ) :
    PositiveYonedaExtFree X Y n →+ PositiveYonedaExtFree X Y' n :=
  FreeAbelianGroup.map (YonedaExtension.composeTailHom f)

@[simp]
theorem composeTailHomFreeHom_of {Y' : C} (f : Y ⟶ Y')
    (a : YonedaExtension X Y (n + 1)) :
    composeTailHomFreeHom (X := X) f n (FreeAbelianGroup.of a) =
      FreeAbelianGroup.of (YonedaExtension.composeTailHom f a) :=
  rfl

theorem composeTailHomFreeHom_rel_mem {Y' : C} (f : Y ⟶ Y')
    {a b : YonedaExtension X Y (n + 1)} (h : YonedaExtension.Rel a b) :
    composeTailHomFreeHom (X := X) f n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X Y' n := by
  simpa [composeTailHomFreeHom, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.iso (X := X) (Y := Y')
        (YonedaExtension.Rel.composeTailHom f h))

theorem composeTailHomFreeHom_relIso_mem {Y' : C} (f : Y ⟶ Y')
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) :
    composeTailHomFreeHom (X := X) f n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X Y' n := by
  simpa [composeTailHomFreeHom, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.chainIso (X := X) (Y := Y')
        (YonedaExtension.RelIso.composeTailHom f h))

theorem composeTailHomFreeHom_rightSplit_mem {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting)
    {a : YonedaExtension X Y (n + 1)} (h : YonedaExtension.RightSplitData a) :
    composeTailHomFreeHom (X := X) f n (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup X Y' n := by
  let pushed := YonedaExtension.pushoutTailWith f push a
  have hdiff :
      FreeAbelianGroup.of (YonedaExtension.composeTailHom f a) -
          FreeAbelianGroup.of pushed ∈
        yonedaRelationSubgroup X Y' n := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X) (Y := Y')
        (YonedaExtension.pushoutTailWithData f push pushData a))
  have hpushed : FreeAbelianGroup.of pushed ∈ yonedaRelationSubgroup X Y' n := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.rightSplit (X := X) (Y := Y')
        (YonedaExtension.RightSplitData.pushoutTailWith f push pushSplit h))
  have hsum := (yonedaRelationSubgroup X Y' n).add_mem hdiff hpushed
  simpa [composeTailHomFreeHom, pushed, sub_eq_add_neg, add_assoc] using hsum

theorem composeTailHomFreeHom_split_mem {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting)
    (e : ShortExactExtension X Y) (s : e.shortComplex.Splitting) :
    composeTailHomFreeHom (X := X) f 0 (FreeAbelianGroup.of e.toYonedaExtension) ∈
      yonedaRelationSubgroup X Y' 0 :=
  composeTailHomFreeHom_rightSplit_mem (X := X) f push pushData pushSplit
    (YonedaExtension.RightSplitData.one e s)

theorem composeTailHomFreeHom_leftSplit_mem {Y' Z : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting)
    (e : ShortExactExtension X Z) (g : ShortExactExtension Z Y)
    (s : g.shortComplex.Splitting) :
    composeTailHomFreeHom (X := X) f 1
        (FreeAbelianGroup.of (YonedaExtension.cons e g.toYonedaExtension)) ∈
      yonedaRelationSubgroup X Y' 1 :=
  composeTailHomFreeHom_rightSplit_mem (X := X) f push pushData pushSplit
    (YonedaExtension.RightSplitData.cons e (YonedaExtension.RightSplitData.one g s))

theorem composeTailHomFreeHom_splitFactor_mem {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting)
    {a : YonedaExtension X Y (n + 1)} (h : YonedaExtension.SplitFactorData a) :
    composeTailHomFreeHom (X := X) f n (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup X Y' n := by
  let pushed := YonedaExtension.pushoutTailWith f push a
  have hdiff :
      FreeAbelianGroup.of (YonedaExtension.composeTailHom f a) -
          FreeAbelianGroup.of pushed ∈
        yonedaRelationSubgroup X Y' n := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X) (Y := Y')
        (YonedaExtension.pushoutTailWithData f push pushData a))
  have hpushed : FreeAbelianGroup.of pushed ∈ yonedaRelationSubgroup X Y' n := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.splitFactor (X := X) (Y := Y')
        (YonedaExtension.SplitFactorData.pushoutTailWith f push pushSplit h))
  have hsum := (yonedaRelationSubgroup X Y' n).add_mem hdiff hpushed
  simpa [composeTailHomFreeHom, pushed, sub_eq_add_neg, add_assoc] using hsum

theorem composeTailHomFreeHom_baer_mem {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y] [HasBinaryBiproduct Y' Y']
    {e₁ e₂ sum : ShortExactExtension X Y}
    (_h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (pushBaer : ShortExactExtension.BaerSumData (push e₁ f) (push e₂ f) (push sum f)) :
    composeTailHomFreeHom (X := X) f 0
        (FreeAbelianGroup.of sum.toYonedaExtension -
          FreeAbelianGroup.of e₁.toYonedaExtension -
          FreeAbelianGroup.of e₂.toYonedaExtension) ∈
      yonedaRelationSubgroup X Y' 0 := by
  let R := yonedaRelationSubgroup X Y' 0
  have hsum :
      FreeAbelianGroup.of (YonedaExtension.cons sum (YonedaExtension.ofHom f)) -
          FreeAbelianGroup.of (push sum f).toYonedaExtension ∈ R := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X) (Y := Y')
        (YonedaExtension.HomTailData.one sum f (pushData sum f)))
  have he₁ :
      FreeAbelianGroup.of (YonedaExtension.cons e₁ (YonedaExtension.ofHom f)) -
          FreeAbelianGroup.of (push e₁ f).toYonedaExtension ∈ R := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X) (Y := Y')
        (YonedaExtension.HomTailData.one e₁ f (pushData e₁ f)))
  have he₂ :
      FreeAbelianGroup.of (YonedaExtension.cons e₂ (YonedaExtension.ofHom f)) -
          FreeAbelianGroup.of (push e₂ f).toYonedaExtension ∈ R := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X) (Y := Y')
        (YonedaExtension.HomTailData.one e₂ f (pushData e₂ f)))
  have hbaer :
      FreeAbelianGroup.of (push sum f).toYonedaExtension -
          FreeAbelianGroup.of (push e₁ f).toYonedaExtension -
          FreeAbelianGroup.of (push e₂ f).toYonedaExtension ∈ R := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.baer (X := X) (Y := Y') pushBaer)
  have htotal := R.sub_mem (R.sub_mem (R.add_mem hsum hbaer) he₁) he₂
  simpa [R, composeTailHomFreeHom, ShortExactExtension.toYonedaExtension,
    YonedaExtension.composeTailHom, map_sub, Category.id_comp, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm] using htotal

theorem composeTailHomFreeHom_homTail_one_mem {Y' Z : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (e : ShortExactExtension X Z) (g : Z ⟶ Y)
    {out : ShortExactExtension X Y}
    (_h : ShortExactExtension.PushoutData e g out)
    (pushAssocIso : ShortExactExtension.Iso (push e (g ≫ f)) (push out f)) :
    composeTailHomFreeHom (X := X) f 0
        (FreeAbelianGroup.of (YonedaExtension.cons e (YonedaExtension.ofHom g)) -
          FreeAbelianGroup.of out.toYonedaExtension) ∈
      yonedaRelationSubgroup X Y' 0 := by
  let R := yonedaRelationSubgroup X Y' 0
  have hleft :
      FreeAbelianGroup.of (YonedaExtension.cons e (YonedaExtension.ofHom (g ≫ f))) -
          FreeAbelianGroup.of (push e (g ≫ f)).toYonedaExtension ∈ R := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X) (Y := Y')
        (YonedaExtension.HomTailData.one e (g ≫ f) (pushData e (g ≫ f))))
  have hright :
      FreeAbelianGroup.of (YonedaExtension.cons out (YonedaExtension.ofHom f)) -
          FreeAbelianGroup.of (push out f).toYonedaExtension ∈ R := by
    exact AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X) (Y := Y')
        (YonedaExtension.HomTailData.one out f (pushData out f)))
  have hiso :
      FreeAbelianGroup.of (push e (g ≫ f)).toYonedaExtension -
          FreeAbelianGroup.of (push out f).toYonedaExtension ∈ R := by
    simpa [R, ShortExactExtension.toYonedaExtension, map_sub] using
      AddSubgroup.subset_closure
        (YonedaRelGenerator.iso (X := X) (Y := Y')
          (YonedaExtension.Rel.cons pushAssocIso (YonedaExtension.Rel.ofHom rfl)))
  have htotal := R.sub_mem (R.add_mem hleft hiso) hright
  simpa [R, composeTailHomFreeHom, ShortExactExtension.toYonedaExtension,
    YonedaExtension.composeTailHom, map_sub, Category.id_comp, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm] using htotal

theorem composeTailHomFreeHom_baerChain_head_mem {Y' Z : C} (f : Y ⟶ Y')
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Z Z]
    {e₁ e₂ sum : ShortExactExtension X Z}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (tail : YonedaExtension Z Y (n + 1)) :
    composeTailHomFreeHom (X := X) f (n + 1)
        (FreeAbelianGroup.of (YonedaExtension.cons sum tail) -
          FreeAbelianGroup.of (YonedaExtension.cons e₁ tail) -
          FreeAbelianGroup.of (YonedaExtension.cons e₂ tail)) ∈
      yonedaRelationSubgroup X Y' (n + 1) := by
  simpa [composeTailHomFreeHom, YonedaExtension.composeTailHom, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.baerChain (X := X) (Y := Y')
        (YonedaExtension.BaerSumData.head h (YonedaExtension.composeTailHom f tail)))

/-- The free abelian group map induced by pulling back the head one-fold extension. -/
def pullbackHeadFreeHomWith {X X' Y : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z) (n : ℕ) :
    PositiveYonedaExtFree X Y n →+ PositiveYonedaExtFree X' Y n :=
  FreeAbelianGroup.map (YonedaExtension.pullbackHeadWith f pull)

@[simp]
theorem pullbackHeadFreeHomWith_of {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (a : YonedaExtension X Y (n + 1)) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n (FreeAbelianGroup.of a) =
      FreeAbelianGroup.of (YonedaExtension.pullbackHeadWith f pull a) :=
  rfl

theorem pullbackHeadFreeHomWith_rel_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullIso : ∀ {Z : C} {e e' : ShortExactExtension X Z},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull e) (pull e'))
    {a b : YonedaExtension X Y (n + 1)} (h : YonedaExtension.Rel a b) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X' Y n := by
  simpa [pullbackHeadFreeHomWith, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.iso (X := X') (Y := Y)
        (YonedaExtension.Rel.pullbackHeadWith f pull pullIso h))

theorem pullbackHeadFreeHomWith_relIso_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullIsoBetween : ∀ {Z Z' : C} {β : Z ≅ Z'} {e : ShortExactExtension X Z}
        {e' : ShortExactExtension X Z'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X') β (pull e) (pull e'))
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X' Y n := by
  simpa [pullbackHeadFreeHomWith, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.chainIso (X := X') (Y := Y)
        (YonedaExtension.RelIso.pullbackHeadWith f pull pullIsoBetween h))

theorem pullbackHeadFreeHomWith_split_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting)
    (e : ShortExactExtension X Y) (s : e.shortComplex.Splitting) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull 0
        (FreeAbelianGroup.of e.toYonedaExtension) ∈
      yonedaRelationSubgroup X' Y 0 := by
  simpa [pullbackHeadFreeHomWith, ShortExactExtension.toYonedaExtension,
    YonedaExtension.pullbackHeadWith] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.split (X := X') (Y := Y) (pull e) (pullSplit e s))

theorem pullbackHeadFreeHomWith_leftSplit_mem {X' Z : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (e : ShortExactExtension X Z) (g : ShortExactExtension Z Y)
    (s : g.shortComplex.Splitting) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull 1
        (FreeAbelianGroup.of (YonedaExtension.cons e g.toYonedaExtension)) ∈
      yonedaRelationSubgroup X' Y 1 := by
  simpa [pullbackHeadFreeHomWith, YonedaExtension.pullbackHeadWith] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.leftSplit (X := X') (Y := Y) (pull e) g s)

theorem pullbackHeadFreeHomWith_rightSplit_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting)
    {a : YonedaExtension X Y (n + 1)} (h : YonedaExtension.RightSplitData a) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup X' Y n := by
  simpa [pullbackHeadFreeHomWith] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.rightSplit (X := X') (Y := Y)
        (YonedaExtension.RightSplitData.pullbackHeadWith f pull pullSplit h))

theorem pullbackHeadFreeHomWith_splitFactor_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting)
    {a : YonedaExtension X Y (n + 1)} (h : YonedaExtension.SplitFactorData a) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n (FreeAbelianGroup.of a) ∈
      yonedaRelationSubgroup X' Y n := by
  simpa [pullbackHeadFreeHomWith] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.splitFactor (X := X') (Y := Y)
        (YonedaExtension.SplitFactorData.pullbackHeadWith f pull pullSplit h))

theorem pullbackHeadFreeHomWith_baer_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X'] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension X Y}
    (_h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (pullBaer : ShortExactExtension.BaerSumData (pull e₁) (pull e₂) (pull sum)) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull 0
        (FreeAbelianGroup.of sum.toYonedaExtension -
          FreeAbelianGroup.of e₁.toYonedaExtension -
          FreeAbelianGroup.of e₂.toYonedaExtension) ∈
      yonedaRelationSubgroup X' Y 0 := by
  simpa [pullbackHeadFreeHomWith, ShortExactExtension.toYonedaExtension,
    YonedaExtension.pullbackHeadWith, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.baer (X := X') (Y := Y) pullBaer)

theorem pullbackHeadFreeHomWith_homTail_one_mem {X' Z : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (e : ShortExactExtension X Z) (g : Z ⟶ Y)
    {out : ShortExactExtension X Y}
    (_h : ShortExactExtension.PushoutData e g out)
    (pullPushoutData : ShortExactExtension.PushoutData (pull e) g (pull out)) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull 0
        (FreeAbelianGroup.of (YonedaExtension.cons e (YonedaExtension.ofHom g)) -
          FreeAbelianGroup.of out.toYonedaExtension) ∈
      yonedaRelationSubgroup X' Y 0 := by
  simpa [pullbackHeadFreeHomWith, ShortExactExtension.toYonedaExtension,
    YonedaExtension.pullbackHeadWith, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X') (Y := Y)
        (YonedaExtension.HomTailData.one (pull e) g pullPushoutData))

theorem pullbackHeadFreeHomWith_baerChain_cons_mem {X' Z : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (e : ShortExactExtension X Z)
    {a b sum : YonedaExtension Z Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull (n + 1)
        (FreeAbelianGroup.of (YonedaExtension.cons e sum) -
          FreeAbelianGroup.of (YonedaExtension.cons e a) -
          FreeAbelianGroup.of (YonedaExtension.cons e b)) ∈
      yonedaRelationSubgroup X' Y (n + 1) := by
  simpa [pullbackHeadFreeHomWith, YonedaExtension.pullbackHeadWith, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.baerChain (X := X') (Y := Y)
        (YonedaExtension.BaerSumData.cons (pull e) h))

theorem pullbackHeadFreeHomWith_homTail_cons_mem {X' Z : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (e : ShortExactExtension X Z)
    {tail tail' : YonedaExtension Z Y (n + 1)}
    (h : YonedaExtension.HomTailData tail tail') :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull (n + 1)
        (FreeAbelianGroup.of (YonedaExtension.cons e tail) -
          FreeAbelianGroup.of (YonedaExtension.cons e tail')) ∈
      yonedaRelationSubgroup X' Y (n + 1) := by
  simpa [pullbackHeadFreeHomWith, YonedaExtension.pullbackHeadWith, map_sub] using
    AddSubgroup.subset_closure
      (YonedaRelGenerator.homTail (X := X') (Y := Y)
        (YonedaExtension.HomTailData.cons (pull e) h))

theorem pullbackHeadFreeHomWith_baerChain_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    [HasBinaryBiproduct X' X']
    (pullBaer :
      ∀ {Z : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X']
        [HasBinaryBiproduct Z Z] {e₁ e₂ sum : ShortExactExtension X Z},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull e₁) (pull e₂) (pull sum))
    {a b sum : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n
        (FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X' Y n := by
  cases h with
  | one h =>
      exact pullbackHeadFreeHomWith_baer_mem (X := X) (Y := Y) f pull h (pullBaer h)
  | head h tail =>
      simpa [pullbackHeadFreeHomWith, YonedaExtension.pullbackHeadWith, map_sub] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.baerChain (X := X') (Y := Y)
            (YonedaExtension.BaerSumData.head (pullBaer h) tail))
  | cons e h =>
      exact pullbackHeadFreeHomWith_baerChain_cons_mem (X := X) (Y := Y) f pull e h

theorem pullbackHeadFreeHomWith_homTail_mem {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullPushoutData :
      ∀ {Z W : C} (e : ShortExactExtension X Z) (g : Z ⟶ W)
        {out : ShortExactExtension X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull e) g (pull out))
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.HomTailData a b) :
    pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X' Y n := by
  cases h with
  | one e g h =>
      exact pullbackHeadFreeHomWith_homTail_one_mem (X := X) f pull e g h
        (pullPushoutData e g h)
  | cons e h =>
      exact pullbackHeadFreeHomWith_homTail_cons_mem (X := X) (Y := Y) f pull e h

/--
Under the expected pullback compatibility data, pulling back the head one-fold
extension preserves every positive-degree Yoneda relation generator.
-/
theorem pullbackHead_relationSubgroup_le {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullIso : ∀ {Z : C} {e e' : ShortExactExtension X Z},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull e) (pull e'))
    (pullIsoBetween : ∀ {Z Z' : C} {β : Z ≅ Z'} {e : ShortExactExtension X Z}
        {e' : ShortExactExtension X Z'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X') β (pull e) (pull e'))
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting)
    [HasBinaryBiproduct X' X']
    (pullBaer :
      ∀ {Z : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X']
        [HasBinaryBiproduct Z Z] {e₁ e₂ sum : ShortExactExtension X Z},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull e₁) (pull e₂) (pull sum))
    (pullPushoutData :
      ∀ {Z W : C} (e : ShortExactExtension X Z) (g : Z ⟶ W)
        {out : ShortExactExtension X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull e) g (pull out)) :
    yonedaRelationSubgroup X Y n ≤
      (yonedaRelationSubgroup X' Y n).comap
        (pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n) := by
  rw [yonedaRelationSubgroup]
  refine (AddSubgroup.closure_le _).mpr ?_
  intro z hz
  change pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n z ∈
    yonedaRelationSubgroup X' Y n
  cases hz with
  | iso h =>
      exact pullbackHeadFreeHomWith_rel_mem (X := X) (Y := Y) f pull pullIso h
  | chainIso h =>
      exact pullbackHeadFreeHomWith_relIso_mem (X := X) (Y := Y) f pull
        pullIsoBetween h
  | split e s =>
      exact pullbackHeadFreeHomWith_split_mem (X := X) (Y := Y) f pull pullSplit e s
  | baer h =>
      exact pullbackHeadFreeHomWith_baer_mem (X := X) (Y := Y) f pull h (pullBaer h)
  | baerChain h =>
      exact pullbackHeadFreeHomWith_baerChain_mem (X := X) (Y := Y) f pull pullBaer h
  | leftSplit e g s =>
      exact pullbackHeadFreeHomWith_leftSplit_mem (X := X) (Y := Y) f pull e g s
  | rightSplit h =>
      exact pullbackHeadFreeHomWith_rightSplit_mem (X := X) (Y := Y) f pull pullSplit h
  | splitFactor h =>
      exact pullbackHeadFreeHomWith_splitFactor_mem (X := X) (Y := Y) f pull pullSplit h
  | homTail h =>
      exact pullbackHeadFreeHomWith_homTail_mem (X := X) (Y := Y) f pull
        pullPushoutData h
  | homTailLeft pullLeft h c =>
      simpa [pullbackHeadFreeHomWith, map_sub, Nat.add_assoc] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.homTailLeft (X := X') (Y := Y) pullLeft
            (YonedaExtension.HomTailData.pullbackHeadWith f pull pullPushoutData h) c)

/-- The additive group structure on exact-category Yoneda Ext. -/
noncomputable instance instAddCommGroup : AddCommGroup (YonedaExt X Y n) := by
  cases n with
  | zero =>
      dsimp [YonedaExt]
      infer_instance
  | succ n =>
      dsimp [YonedaExt, PositiveYonedaExt]
      infer_instance

/--
Positive-degree head pullback, descended from formal chains to the local
Yoneda Ext quotient under the same compatibility data.
-/
noncomputable def pullbackHeadMapWith {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullIso : ∀ {Z : C} {e e' : ShortExactExtension X Z},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull e) (pull e'))
    (pullIsoBetween : ∀ {Z Z' : C} {β : Z ≅ Z'} {e : ShortExactExtension X Z}
        {e' : ShortExactExtension X Z'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X') β (pull e) (pull e'))
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting)
    [HasBinaryBiproduct X' X']
    (pullBaer :
      ∀ {Z : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X']
        [HasBinaryBiproduct Z Z] {e₁ e₂ sum : ShortExactExtension X Z},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull e₁) (pull e₂) (pull sum))
    (pullPushoutData :
      ∀ {Z W : C} (e : ShortExactExtension X Z) (g : Z ⟶ W)
        {out : ShortExactExtension X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull e) g (pull out)) :
    YonedaExt X Y (n + 1) →+ YonedaExt X' Y (n + 1) :=
  QuotientAddGroup.map (yonedaRelationSubgroup X Y n) (yonedaRelationSubgroup X' Y n)
    (pullbackHeadFreeHomWith (X := X) (Y := Y) f pull n)
    (pullbackHead_relationSubgroup_le (X := X) (Y := Y) f pull pullIso
      pullIsoBetween pullSplit pullBaer pullPushoutData)

@[simp]
theorem pullbackHeadMapWith_ofExtension {X' : C} (f : X' ⟶ X)
    (pull : {Z : C} → ShortExactExtension X Z → ShortExactExtension X' Z)
    (pullIso : ∀ {Z : C} {e e' : ShortExactExtension X Z},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull e) (pull e'))
    (pullIsoBetween : ∀ {Z Z' : C} {β : Z ≅ Z'} {e : ShortExactExtension X Z}
        {e' : ShortExactExtension X Z'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl X') β (pull e) (pull e'))
    (pullSplit : ∀ {Z : C} (e : ShortExactExtension X Z)
      (_ : e.shortComplex.Splitting), (pull e).shortComplex.Splitting)
    [HasBinaryBiproduct X' X']
    (pullBaer :
      ∀ {Z : C} [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X']
        [HasBinaryBiproduct Z Z] {e₁ e₂ sum : ShortExactExtension X Z},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull e₁) (pull e₂) (pull sum))
    (pullPushoutData :
      ∀ {Z W : C} (e : ShortExactExtension X Z) (g : Z ⟶ W)
        {out : ShortExactExtension X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull e) g (pull out))
    (a : YonedaExtension X Y (n + 1)) :
    pullbackHeadMapWith f pull pullIso pullIsoBetween pullSplit pullBaer pullPushoutData
        (ofExtension (X := X) (Y := Y) (n := n) a) =
      ofExtension (X := X') (Y := Y) (n := n)
        (YonedaExtension.pullbackHeadWith f pull a) :=
  rfl

/--
For canonical MetrizableLCA pullbacks, head pullback preserves positive-degree
Yoneda relations once the remaining pullback-pushout exchange data is supplied.
-/
theorem pullbackHead_relationSubgroup_le_metrizableWithPushoutData
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) (n : ℕ)
    [HasBinaryBiproduct X' X']
    (pullPushoutData :
      ∀ {Z W : MetrizableLCA.{u}}
        (e : ShortExactExtension (C := MetrizableLCA.{u}) X Z) (g : Z ⟶ W)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f)) :
    yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y n ≤
      (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X' Y n).comap
        (pullbackHeadFreeHomWith (C := MetrizableLCA.{u}) (X := X) (Y := Y) f
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) n) :=
  pullbackHead_relationSubgroup_le (C := MetrizableLCA.{u}) (X := X) (Y := Y) f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_} {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _} {_} {_} {_} h => MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_} e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {Z} [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X']
        [HasBinaryBiproduct Z Z] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _} e g {_} h => pullPushoutData e g h)

/--
Canonical MetrizableLCA head pullback on positive-degree Yoneda Ext, conditional
only on the pullback-pushout exchange data.
-/
noncomputable def pullbackHeadMap_metrizableWithPushoutData
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) (n : ℕ)
    [HasBinaryBiproduct X' X']
    (pullPushoutData :
      ∀ {Z W : MetrizableLCA.{u}}
        (e : ShortExactExtension (C := MetrizableLCA.{u}) X Z) (g : Z ⟶ W)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f)) :
    YonedaExt (C := MetrizableLCA.{u}) X Y (n + 1) →+
      YonedaExt (C := MetrizableLCA.{u}) X' Y (n + 1) :=
  pullbackHeadMapWith (C := MetrizableLCA.{u}) (X := X) (Y := Y) f
    (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_} {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _} {_} {_} {_} h => MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_} e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {Z} [HasBinaryBiproduct X X] [HasBinaryBiproduct X' X']
        [HasBinaryBiproduct Z Z] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _} e g {_} h => pullPushoutData e g h)

@[simp]
theorem pullbackHeadMap_metrizableWithPushoutData_ofExtension
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) (n : ℕ)
    [HasBinaryBiproduct X' X']
    (pullPushoutData :
      ∀ {Z W : MetrizableLCA.{u}}
        (e : ShortExactExtension (C := MetrizableLCA.{u}) X Z) (g : Z ⟶ W)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) X W},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f))
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)) :
    pullbackHeadMap_metrizableWithPushoutData (X := X) f n pullPushoutData
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := n) a) =
      ofExtension (C := MetrizableLCA.{u}) (X := X') (Y := Y) (n := n)
        (YonedaExtension.pullbackHeadWith f
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a) :=
  rfl

/-- Canonical MetrizableLCA head pullback preserves positive-degree Yoneda relations. -/
theorem pullbackHead_relationSubgroup_le_metrizable
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) (n : ℕ)
    [HasBinaryBiproduct X' X'] :
    yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y n ≤
      (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X' Y n).comap
        (pullbackHeadFreeHomWith (C := MetrizableLCA.{u}) (X := X) (Y := Y) f
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) n) :=
  pullbackHead_relationSubgroup_le_metrizableWithPushoutData (X := X) (Y := Y) f n
    (fun {_ _} e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)

/-- Canonical MetrizableLCA head pullback on positive-degree Yoneda Ext. -/
noncomputable def pullbackHeadMap_metrizable
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) (n : ℕ)
    [HasBinaryBiproduct X' X'] :
    YonedaExt (C := MetrizableLCA.{u}) X Y (n + 1) →+
      YonedaExt (C := MetrizableLCA.{u}) X' Y (n + 1) :=
  pullbackHeadMap_metrizableWithPushoutData (X := X) (Y := Y) f n
    (fun {_ _} e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)

@[simp]
theorem pullbackHeadMap_metrizable_ofExtension
    {X X' Y : MetrizableLCA.{u}} (f : X' ⟶ X) (n : ℕ)
    [HasBinaryBiproduct X' X']
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)) :
    pullbackHeadMap_metrizable (X := X) f n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := n) a) =
      ofExtension (C := MetrizableLCA.{u}) (X := X') (Y := Y) (n := n)
        (YonedaExtension.pullbackHeadWith f
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a) :=
  pullbackHeadMap_metrizableWithPushoutData_ofExtension (X := X) (Y := Y) f n
    (fun {_ _} e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)
    a

/-- Head pullback on Ext sends the strict-sequence constructor to the pulled-back generator. -/
@[simp]
theorem pullbackHeadMap_metrizable_ofStrictShortExact
    {X X' Y M : MetrizableLCA.{u}} (f : X' ⟶ X)
    [HasBinaryBiproduct X' X'] (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero)) :
    pullbackHeadMap_metrizable (X := X) f 0
        (ofStrictShortExact (X := X) (Y := Y) i p zero h) =
      ofExtension (C := MetrizableLCA.{u}) (X := X') (Y := Y) (n := 0)
        (YonedaExtension.pullbackHeadWith (C := MetrizableLCA.{u}) f
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
          (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension) := by
  rw [ofStrictShortExact_eq_ofExtension]
  exact pullbackHeadMap_metrizable_ofExtension (X := X) (Y := Y) f 0
    ((MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension)

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

/-- Termwise-related positive chains represent the same Yoneda Ext class. -/
theorem ofPositiveChain_eq_ofPositiveChain_of_rel
    {p q : YonedaExtension.PositiveChain X Y n}
    (h : YonedaExtension.PositiveChain.Rel p q) :
    ofPositiveChain (X := X) (Y := Y) p =
      ofPositiveChain (X := X) (Y := Y) q :=
  ofExtension_eq_ofExtension_of_rel h.toYonedaExtension

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

/-- A split strict short exact sequence represents zero under the strict `Ext¹` constructor. -/
theorem ofStrictShortExact_eq_zero_of_split
    {X Y M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero))
    (s : (ShortComplex.mk i p zero).Splitting) :
    ofStrictShortExact (X := X) (Y := Y) i p zero h =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X Y 1) := by
  rw [ofStrictShortExact_eq_ofExtension]
  exact ofExtension_eq_zero_of_split
    (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h)
    (by simpa using s)

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

/-- A positive chain with a split factor represents zero in Yoneda Ext. -/
theorem ofPositiveChain_eq_zero_of_splitFactor
    {p : YonedaExtension.PositiveChain X Y n}
    (h : YonedaExtension.PositiveChain.SplitFactorData p) :
    ofPositiveChain (X := X) (Y := Y) p = 0 :=
  ofExtension_eq_zero_of_splitFactorData h.toYonedaExtension

/-- Hom-tail pushout data identifies a chain with the pushed-out chain in local Yoneda Ext. -/
theorem ofExtension_eq_ofExtension_of_homTailData
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.HomTailData a b) :
    ofExtension (X := X) (Y := Y) (n := n) a =
      ofExtension (X := X) (Y := Y) (n := n) b := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of a : PositiveYonedaExtFree X Y n) : PositiveYonedaExt X Y n) =
    ((FreeAbelianGroup.of b : PositiveYonedaExtFree X Y n) : PositiveYonedaExt X Y n)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure (YonedaRelGenerator.homTail (X := X) (Y := Y) h)

/-- A hom-tail relation in the left chain remains an equality after right splicing. -/
theorem ofExtension_eq_ofExtension_of_homTailLeftWith
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {W : C} {m n : ℕ} {a b : YonedaExtension X W (m + 1)}
    (h : YonedaExtension.HomTailData a b) (c : YonedaExtension W Y (n + 1)) :
    ofExtension (X := X) (Y := Y) (n := n + (m + 1))
        (YonedaExtension.spliceLeftWith pull a c) =
      ofExtension (X := X) (Y := Y) (n := n + (m + 1))
        (YonedaExtension.spliceLeftWith pull b c) := by
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of (YonedaExtension.spliceLeftWith pull a c) :
      PositiveYonedaExtFree X Y (n + (m + 1))) : PositiveYonedaExt X Y (n + (m + 1))) =
    ((FreeAbelianGroup.of (YonedaExtension.spliceLeftWith pull b c) :
      PositiveYonedaExtFree X Y (n + (m + 1))) : PositiveYonedaExt X Y (n + (m + 1)))
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact AddSubgroup.subset_closure
    (YonedaRelGenerator.homTailLeft (X := X) (Y := Y) pull h c)

/-- A one-fold extension followed by a hom tail equals its pushed-out extension. -/
theorem ofExtension_cons_ofHom_eq_of_pushoutData
    {Z : C} (e : ShortExactExtension X Z) (f : Z ⟶ Y)
    {out : ShortExactExtension X Y}
    (h : ShortExactExtension.PushoutData e f out) :
    ofExtension (X := X) (Y := Y) (n := 0)
        (YonedaExtension.cons e (YonedaExtension.ofHom f)) =
      ofExtension (X := X) (Y := Y) (n := 0) out.toYonedaExtension :=
  ofExtension_eq_ofExtension_of_homTailData
    (YonedaExtension.HomTailData.one e f h)

/-- Composing a tail hom equals recursively pushing out the tail extension. -/
theorem ofExtension_composeTailHom_eq_pushoutTailWith
    {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (h : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (a : YonedaExtension X Y (n + 1)) :
    ofExtension (X := X) (Y := Y') (n := n) (YonedaExtension.composeTailHom f a) =
      ofExtension (X := X) (Y := Y') (n := n) (YonedaExtension.pushoutTailWith f push a) :=
  ofExtension_eq_ofExtension_of_homTailData
    (YonedaExtension.pushoutTailWithData f push h a)

/-- Tail hom composition respects termwise related chains in Ext. -/
theorem ofExtension_composeTailHom_eq_of_rel {Y' : C} (f : Y ⟶ Y')
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.Rel a b) :
    ofExtension (X := X) (Y := Y') (n := n) (YonedaExtension.composeTailHom f a) =
      ofExtension (X := X) (Y := Y') (n := n) (YonedaExtension.composeTailHom f b) :=
  ofExtension_eq_ofExtension_of_rel (YonedaExtension.Rel.composeTailHom f h)

/-- Tail hom composition respects recursively isomorphic chains in Ext. -/
theorem ofExtension_composeTailHom_eq_of_relIso {Y' : C} (f : Y ⟶ Y')
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) :
    ofExtension (X := X) (Y := Y') (n := n) (YonedaExtension.composeTailHom f a) =
      ofExtension (X := X) (Y := Y') (n := n) (YonedaExtension.composeTailHom f b) :=
  ofExtension_eq_ofExtension_of_relIso (YonedaExtension.RelIso.composeTailHom f h)

/-- A tail hom composed after a split one-fold MetrizableLCA extension is zero in Ext. -/
theorem ofExtension_composeTailHom_eq_zero_of_metrizable_split
    {X Y Y' : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y)
    (s : e.shortComplex.Splitting) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (YonedaExtension.composeTailHom f e.toYonedaExtension) =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X Y' 1) := by
  rw [YonedaExt.ofExtension_composeTailHom_eq_pushoutTailWith f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    e.toYonedaExtension]
  simpa [ShortExactExtension.toYonedaExtension, YonedaExtension.pushoutTailWith,
    Category.id_comp] using
    (YonedaExt.ofExtension_eq_zero_of_split
      (MetrizableLCA.shortExactExtensionPushout e f)
      (MetrizableLCA.shortExactExtensionPushoutSplitting e f s))

/-- Pulling back a split one-fold MetrizableLCA extension is zero in Ext. -/
theorem pullbackHeadOfExtension_eq_zero_of_metrizable_split
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y)
    (s : e.shortComplex.Splitting) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA.{u}) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
        e.toYonedaExtension =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X' Y 1) := by
  simpa [YonedaExt.pullbackHeadOfExtensionWith, ShortExactExtension.toYonedaExtension,
    YonedaExtension.pullbackHeadWith] using
    (YonedaExt.ofExtension_eq_zero_of_split
      (MetrizableLCA.shortExactExtensionPullback e f)
      (MetrizableLCA.shortExactExtensionPullbackSplitting e f s))

/-- Head pullback respects termwise related MetrizableLCA chains in Ext. -/
theorem pullbackHeadOfExtension_eq_of_metrizable_rel
    {X X' Y : MetrizableLCA.{u}} {n : ℕ}
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.Rel a b) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA.{u}) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a =
      YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA.{u}) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) b :=
  YonedaExt.ofExtension_eq_ofExtension_of_rel
    (MetrizableLCA.yonedaExtensionPullbackHeadRel f h)

/-- Head pullback respects recursively isomorphic MetrizableLCA chains in Ext. -/
theorem pullbackHeadOfExtension_eq_of_metrizable_relIso
    {X X' Y : MetrizableLCA.{u}} {n : ℕ}
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RelIso (CategoryTheory.Iso.refl X) a b) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA.{u}) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a =
      YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA.{u}) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) b :=
  YonedaExt.ofExtension_eq_ofExtension_of_relIso
    (MetrizableLCA.yonedaExtensionPullbackHeadRelIso f h)

/-- Pulling back along the identity does not change the Ext class of a MetrizableLCA chain. -/
theorem ofExtension_pullbackHeadId_eq
    {X Y : MetrizableLCA.{u}} {n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)) :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (YonedaExtension.pullbackHeadWith (C := MetrizableLCA.{u}) (𝟙 X)
          (fun {_} e => MetrizableLCA.shortExactExtensionPullback e (𝟙 X)) a) =
      YonedaExt.ofExtension (C := MetrizableLCA.{u}) a :=
  YonedaExt.ofExtension_eq_ofExtension_of_rel
    (MetrizableLCA.yonedaExtensionPullbackHeadIdRel a)

/-- Pushing out a one-fold MetrizableLCA extension along the identity preserves its Ext class. -/
theorem ofExtension_pushoutTailId_eq
    {X Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)).toYonedaExtension =
      YonedaExt.ofExtension (C := MetrizableLCA.{u}) e.toYonedaExtension :=
  YonedaExt.ofExtension_eq_ofExtension_of_rel
    (MetrizableLCA.yonedaExtensionPushoutTailIdRel e)

/-- Pulling back an identity-tail pushout preserves the pulled-back Ext generator. -/
theorem ofExtension_pullbackPushoutTailId_eq
    {X X' Y : MetrizableLCA.{u}}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y) (f : X' ⟶ X) :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (MetrizableLCA.shortExactExtensionPullback
          (MetrizableLCA.shortExactExtensionPushout e (𝟙 Y)) f).toYonedaExtension =
      YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (MetrizableLCA.shortExactExtensionPullback e f).toYonedaExtension :=
  YonedaExt.ofExtension_eq_ofExtension_of_rel
    (MetrizableLCA.yonedaExtensionPullbackPushoutTailIdRel e f)

/-- Head pullback sends a MetrizableLCA right-split chain to zero in Ext. -/
theorem pullbackHeadOfExtension_eq_zero_of_metrizable_rightSplitData
    {X X' Y : MetrizableLCA.{u}} {n : ℕ}
    {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA.{u}) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X' Y (n + 1)) :=
  YonedaExt.ofExtension_eq_zero_of_rightSplitData
    (YonedaExtension.RightSplitData.pullbackHeadWith f
      (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
      (fun {_} e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s) h)

/-- Head pullback sends a MetrizableLCA chain with a split factor to zero in Ext. -/
theorem pullbackHeadOfExtension_eq_zero_of_metrizable_splitFactorData
    {X X' Y : MetrizableLCA.{u}} {n : ℕ}
    {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : X' ⟶ X) :
    YonedaExt.pullbackHeadOfExtensionWith (C := MetrizableLCA.{u}) f
        (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f) a =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X' Y (n + 1)) :=
  YonedaExt.ofExtension_eq_zero_of_splitFactorData
    (YonedaExtension.SplitFactorData.pullbackHeadWith f
      (fun {_} e => MetrizableLCA.shortExactExtensionPullback e f)
      (fun {_} e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s) h)

/-- Canonical tail pushout sends a MetrizableLCA right-split chain to zero in Ext. -/
theorem ofExtension_pushoutTailWith_eq_zero_of_metrizable_rightSplitData
    {X Y Y' : MetrizableLCA.{u}} {n : ℕ}
    {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (YonedaExtension.pushoutTailWith f
          (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g) a) =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X Y' (n + 1)) :=
  YonedaExt.ofExtension_eq_zero_of_rightSplitData
    (YonedaExtension.RightSplitData.pushoutTailWith f
      (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
      (fun {_ _} e g s => MetrizableLCA.shortExactExtensionPushoutSplitting e g s) h)

/-- Canonical tail pushout sends a MetrizableLCA chain with a split factor to zero in Ext. -/
theorem ofExtension_pushoutTailWith_eq_zero_of_metrizable_splitFactorData
    {X Y Y' : MetrizableLCA.{u}} {n : ℕ}
    {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (YonedaExtension.pushoutTailWith f
          (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g) a) =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X Y' (n + 1)) :=
  YonedaExt.ofExtension_eq_zero_of_splitFactorData
    (YonedaExtension.SplitFactorData.pushoutTailWith f
      (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
      (fun {_ _} e g s => MetrizableLCA.shortExactExtensionPushoutSplitting e g s) h)

/-- Tail hom composition sends a MetrizableLCA right-split chain to zero in Ext. -/
theorem ofExtension_composeTailHom_eq_zero_of_metrizable_rightSplitData
    {X Y Y' : MetrizableLCA.{u}} {n : ℕ}
    {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.RightSplitData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (YonedaExtension.composeTailHom f a) =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X Y' (n + 1)) := by
  rw [YonedaExt.ofExtension_composeTailHom_eq_pushoutTailWith f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    a]
  exact ofExtension_pushoutTailWith_eq_zero_of_metrizable_rightSplitData h f

/-- Tail hom composition sends a MetrizableLCA chain with a split factor to zero in Ext. -/
theorem ofExtension_composeTailHom_eq_zero_of_metrizable_splitFactorData
    {X Y Y' : MetrizableLCA.{u}} {n : ℕ}
    {a : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.SplitFactorData a) (f : Y ⟶ Y') :
    YonedaExt.ofExtension (C := MetrizableLCA.{u})
        (YonedaExtension.composeTailHom f a) =
      (0 : YonedaExt (C := MetrizableLCA.{u}) X Y' (n + 1)) := by
  rw [YonedaExt.ofExtension_composeTailHom_eq_pushoutTailWith f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    a]
  exact ofExtension_pushoutTailWith_eq_zero_of_metrizable_splitFactorData h f

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

/-- A witnessed Baer sum of positive chains is addition in local Yoneda Ext. -/
theorem ofPositiveChain_eq_add_of_baerChain
    {a b sum : YonedaExtension.PositiveChain X Y n}
    (h : YonedaExtension.PositiveChain.BaerSumData a b sum) :
    ofPositiveChain (X := X) (Y := Y) sum =
      ofPositiveChain (X := X) (Y := Y) a +
        ofPositiveChain (X := X) (Y := Y) b :=
  ofExtension_eq_add_of_baerChain h.toYonedaExtension

/-- A Baer sum in the leftmost one-fold factor remains addition after a fixed positive tail. -/
theorem ofExtension_eq_add_of_baerHead [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {Z : C} {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (tail : YonedaExtension Y Z (n + 1)) :
    ofExtension (X := X) (Y := Z) (n := n + 1) (YonedaExtension.cons sum tail) =
      ofExtension (X := X) (Y := Z) (n := n + 1) (YonedaExtension.cons e₁ tail) +
        ofExtension (X := X) (Y := Z) (n := n + 1) (YonedaExtension.cons e₂ tail) := by
  exact ofExtension_eq_add_of_baerChain
    (YonedaExtension.BaerSumData.head h tail)

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

/-- A witnessed Baer sum of strict short exact sequences is addition in `Ext¹`. -/
theorem ofStrictShortExact_eq_add_of_baer
    {X Y M₁ M₂ Msum : MetrizableLCA.{u}}
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    (i₁ : Y ⟶ M₁) (p₁ : M₁ ⟶ X) (zero₁ : i₁ ≫ p₁ = 0)
    (h₁ : MetrizableLCA.strictShortExact (ShortComplex.mk i₁ p₁ zero₁))
    (i₂ : Y ⟶ M₂) (p₂ : M₂ ⟶ X) (zero₂ : i₂ ≫ p₂ = 0)
    (h₂ : MetrizableLCA.strictShortExact (ShortComplex.mk i₂ p₂ zero₂))
    (isum : Y ⟶ Msum) (psum : Msum ⟶ X) (zerosum : isum ≫ psum = 0)
    (hsum : MetrizableLCA.strictShortExact (ShortComplex.mk isum psum zerosum))
    (hBaer :
      ShortExactExtension.BaerSumData
        (C := MetrizableLCA.{u})
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i₁ p₁ zero₁ h₁)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i₂ p₂ zero₂ h₂)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact isum psum zerosum hsum)) :
    ofStrictShortExact (X := X) (Y := Y) isum psum zerosum hsum =
      ofStrictShortExact (X := X) (Y := Y) i₁ p₁ zero₁ h₁ +
        ofStrictShortExact (X := X) (Y := Y) i₂ p₂ zero₂ h₂ := by
  simpa [ofStrictShortExact_eq_ofExtension] using
    (ofExtension_eq_add_of_baer (C := MetrizableLCA.{u}) hBaer)

/-- The public `baer_sum` operation computes witnessed Baer sums of strict short exact sequences. -/
theorem baer_sum_ofStrictShortExact_eq_of_baer
    {X Y M₁ M₂ Msum : MetrizableLCA.{u}}
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    (i₁ : Y ⟶ M₁) (p₁ : M₁ ⟶ X) (zero₁ : i₁ ≫ p₁ = 0)
    (h₁ : MetrizableLCA.strictShortExact (ShortComplex.mk i₁ p₁ zero₁))
    (i₂ : Y ⟶ M₂) (p₂ : M₂ ⟶ X) (zero₂ : i₂ ≫ p₂ = 0)
    (h₂ : MetrizableLCA.strictShortExact (ShortComplex.mk i₂ p₂ zero₂))
    (isum : Y ⟶ Msum) (psum : Msum ⟶ X) (zerosum : isum ≫ psum = 0)
    (hsum : MetrizableLCA.strictShortExact (ShortComplex.mk isum psum zerosum))
    (hBaer :
      ShortExactExtension.BaerSumData
        (C := MetrizableLCA.{u})
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i₁ p₁ zero₁ h₁)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i₂ p₂ zero₂ h₂)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact isum psum zerosum hsum)) :
    baer_sum
        (ofStrictShortExact (X := X) (Y := Y) i₁ p₁ zero₁ h₁)
        (ofStrictShortExact (X := X) (Y := Y) i₂ p₂ zero₂ h₂) =
      ofStrictShortExact (X := X) (Y := Y) isum psum zerosum hsum := by
  dsimp [baer_sum]
  exact (ofStrictShortExact_eq_add_of_baer i₁ p₁ zero₁ h₁ i₂ p₂ zero₂ h₂
    isum psum zerosum hsum hBaer).symm

/--
The Baer sum of two strict short exact sequences is represented by the canonical
Baer-sum extension.
-/
theorem baer_sum_ofStrictShortExact_eq_canonicalBaerSum
    {X Y M₁ M₂ : MetrizableLCA.{u}}
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    (i₁ : Y ⟶ M₁) (p₁ : M₁ ⟶ X) (zero₁ : i₁ ≫ p₁ = 0)
    (h₁ : MetrizableLCA.strictShortExact (ShortComplex.mk i₁ p₁ zero₁))
    (i₂ : Y ⟶ M₂) (p₂ : M₂ ⟶ X) (zero₂ : i₂ ≫ p₂ = 0)
    (h₂ : MetrizableLCA.strictShortExact (ShortComplex.mk i₂ p₂ zero₂)) :
    baer_sum
        (ofStrictShortExact (X := X) (Y := Y) i₁ p₁ zero₁ h₁)
        (ofStrictShortExact (X := X) (Y := Y) i₂ p₂ zero₂ h₂) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := 0)
        (ShortExactExtension.toYonedaExtension
          (MetrizableLCA.shortExactExtensionBaerSum
            (MetrizableLCA.shortExactExtensionOfStrictShortExact i₁ p₁ zero₁ h₁)
            (MetrizableLCA.shortExactExtensionOfStrictShortExact i₂ p₂ zero₂ h₂))) := by
  simpa [ofStrictShortExact_eq_ofExtension] using
    (baer_sum_ofExtension_eq_of_baer (C := MetrizableLCA.{u})
      (MetrizableLCA.shortExactExtensionBaerSumData
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i₁ p₁ zero₁ h₁)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i₂ p₂ zero₂ h₂)))

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

/-- A witnessed Baer sum of positive chains computes the public `baer_sum` operation. -/
theorem baer_sum_ofPositiveChain_eq_of_baerChain
    {a b sum : YonedaExtension.PositiveChain X Y n}
    (h : YonedaExtension.PositiveChain.BaerSumData a b sum) :
    baer_sum
        (ofPositiveChain (X := X) (Y := Y) a)
        (ofPositiveChain (X := X) (Y := Y) b) =
      ofPositiveChain (X := X) (Y := Y) sum := by
  dsimp [baer_sum]
  exact (ofPositiveChain_eq_add_of_baerChain h).symm

/-- A Baer sum in the leftmost one-fold factor computes `baer_sum` after a fixed positive tail. -/
theorem baer_sum_ofExtension_eq_of_baerHead [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {Z : C} {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (tail : YonedaExtension Y Z (n + 1)) :
    baer_sum
        (ofExtension (X := X) (Y := Z) (n := n + 1) (YonedaExtension.cons e₁ tail))
        (ofExtension (X := X) (Y := Z) (n := n + 1) (YonedaExtension.cons e₂ tail)) =
      ofExtension (X := X) (Y := Z) (n := n + 1) (YonedaExtension.cons sum tail) := by
  dsimp [baer_sum]
  exact (ofExtension_eq_add_of_baerHead h tail).symm

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
  | homTail h =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap, map_sub] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.homTail (X := X) (Y := Z)
            (YonedaExtension.HomTailData.cons e h))
  | homTailLeft pull h c =>
      simpa [consLeftFreeHom, YonedaExtension.consLeftMap, map_sub,
        YonedaExtension.spliceLeftWith, Nat.add_assoc] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.homTailLeft (X := X) (Y := Z) pull
            (YonedaExtension.HomTailData.cons e h) c)
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

/-- The free abelian group map induced by splicing a fixed arbitrary left chain. -/
def leftProductByYonedaExtensionFreeHomWith
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {X Y Z : C} : {m : ℕ} →
      YonedaExtension X Y m → (n : ℕ) →
        PositiveYonedaExtFree Y Z n →+ PositiveYonedaExtFree X Z (n + m)
  | 0, YonedaExtension.ofHom f, n =>
      pullbackHeadFreeHomWith (X := Y) (Y := Z) f (fun {_} e => pull f e) n
  | m + 1, YonedaExtension.cons e tail, n => by
      simpa [Nat.add_assoc] using
        (consLeftFreeHom e (n + m)).comp
          (leftProductByYonedaExtensionFreeHomWith (Z := Z) pull tail n)

@[simp]
theorem leftProductByYonedaExtensionFreeHomWith_of
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    {m : ℕ} (a : YonedaExtension X Y m) (b : YonedaExtension Y Z (n + 1)) :
    leftProductByYonedaExtensionFreeHomWith (Z := Z) pull a n
        (FreeAbelianGroup.of b) =
      FreeAbelianGroup.of (YonedaExtension.spliceLeftWith pull a b) :=
  by
    induction a with
    | ofHom f =>
        rfl
    | cons e tail ih =>
        simp [leftProductByYonedaExtensionFreeHomWith, consLeftFreeHom,
          YonedaExtension.consLeftMap, ih]

/--
Under the same head-pullback compatibility data used for degree-zero maps,
splicing a fixed arbitrary left Yoneda chain preserves all right-variable
Yoneda relations.
-/
theorem leftProductByYonedaExtension_relationSubgroup_leWith
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out)) :
    {X Y Z : C} → {m : ℕ} →
      (a : YonedaExtension X Y m) → (n : ℕ) →
        yonedaRelationSubgroup Y Z n ≤
          (yonedaRelationSubgroup X Z (n + m)).comap
            (leftProductByYonedaExtensionFreeHomWith (Z := Z) pull a n)
  | X, Y, Z, 0, YonedaExtension.ofHom f, n => by
      simpa [leftProductByYonedaExtensionFreeHomWith, YonedaExtension.spliceLeftWith] using
        (pullbackHead_relationSubgroup_le (C := C) (X := Y) (Y := Z) (X' := X) f
          (fun {_} e => pull f e)
          (fun {_} {_ _} h => pullIso f h)
          (fun {_ _} {_} {_} {_} h => pullIsoBetween f h)
          (fun {_} e s => pullSplit f e s)
          (fun {W} [HasBinaryBiproduct Y Y] [HasBinaryBiproduct X X]
              [HasBinaryBiproduct W W] {_ _ _} h => pullBaer f h)
          (fun {_ _} e g {_} h => pullPushoutData f e g h))
  | X, Y, Z, m + 1, YonedaExtension.cons e tail, n => by
      intro z hz
      have htail :=
        leftProductByYonedaExtension_relationSubgroup_leWith pull pullIso
          pullIsoBetween pullSplit pullBaer pullPushoutData tail n hz
      have hhead := consLeft_relationSubgroup_le (X := X) (Z := Z) e (n + m) htail
      simpa [leftProductByYonedaExtensionFreeHomWith, YonedaExtension.spliceLeftWith,
        consLeftFreeHom, YonedaExtension.consLeftMap, Nat.add_assoc] using hhead

/--
Splicing by a fixed arbitrary left Yoneda chain, descended to the right Ext
quotient under the supplied head-pullback compatibility data.
-/
noncomputable def leftProductByYonedaExtensionWith
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} (a : YonedaExtension X Y m) (n : ℕ) :
    YonedaExt Y Z (n + 1) →+ YonedaExt X Z ((n + m) + 1) :=
  QuotientAddGroup.map (yonedaRelationSubgroup Y Z n) (yonedaRelationSubgroup X Z (n + m))
    (leftProductByYonedaExtensionFreeHomWith (Z := Z) pull a n)
    (leftProductByYonedaExtension_relationSubgroup_leWith pull pullIso pullIsoBetween
      pullSplit pullBaer pullPushoutData a n)

@[simp]
theorem leftProductByYonedaExtensionWith_ofExtension
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} (a : YonedaExtension X Y m) (b : YonedaExtension Y Z (n + 1)) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n (ofExtension (X := Y) (Y := Z) (n := n) b) =
      ofExtension (X := X) (Y := Z) (n := n + m)
        (YonedaExtension.spliceLeftWith pull a b) :=
  by
    dsimp [leftProductByYonedaExtensionWith, ofExtension]
    calc
      (QuotientAddGroup.map (yonedaRelationSubgroup Y Z n)
            (yonedaRelationSubgroup X Z (n + m))
            (leftProductByYonedaExtensionFreeHomWith (Z := Z) pull a n)
            (leftProductByYonedaExtension_relationSubgroup_leWith pull pullIso
              pullIsoBetween pullSplit pullBaer pullPushoutData a n))
          ((FreeAbelianGroup.of b : PositiveYonedaExtFree Y Z n) :
            PositiveYonedaExt Y Z n) =
          ((leftProductByYonedaExtensionFreeHomWith (Z := Z) pull a n
              (FreeAbelianGroup.of b) : PositiveYonedaExtFree X Z (n + m)) :
            PositiveYonedaExt X Z (n + m)) := by
            simp
      _ = ((FreeAbelianGroup.of (YonedaExtension.spliceLeftWith pull a b) :
            PositiveYonedaExtFree X Z (n + m)) :
            PositiveYonedaExt X Z (n + m)) := by
            rw [leftProductByYonedaExtensionFreeHomWith_of]

/-- Termwise-related arbitrary left chains give the same spliced class on generators. -/
theorem leftProductByYonedaExtensionWith_ofExtension_eq_of_rel
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a a' : YonedaExtension X Y m}
    (h : YonedaExtension.Rel a a') (b : YonedaExtension Y Z (n + 1)) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n (ofExtension (X := Y) (Y := Z) (n := n) b) =
      leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a' n (ofExtension (X := Y) (Y := Z) (n := n) b) := by
  rw [leftProductByYonedaExtensionWith_ofExtension,
    leftProductByYonedaExtensionWith_ofExtension]
  exact ofExtension_eq_ofExtension_of_rel (h.spliceLeftWith pull b)

/-- Termwise-related arbitrary left chains induce the same conditional homomorphism. -/
theorem leftProductByYonedaExtensionWith_eq_of_rel
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a a' : YonedaExtension X Y m}
    (h : YonedaExtension.Rel a a') (n : ℕ) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n =
      leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a' n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro b
  change leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
      pullBaer pullPushoutData a n
      (ofExtension (X := Y) (Y := Z) (n := n) b) =
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
      pullBaer pullPushoutData a' n
      (ofExtension (X := Y) (Y := Z) (n := n) b)
  exact leftProductByYonedaExtensionWith_ofExtension_eq_of_rel
    pull pullIso pullIsoBetween pullSplit pullBaer pullPushoutData h b

/-- An arbitrary fixed left chain with a split factor acts by zero on generators. -/
theorem leftProductByYonedaExtensionWith_ofExtension_eq_zero_of_splitFactor
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a : YonedaExtension X Y (m + 1)}
    (h : YonedaExtension.SplitFactorData a) (b : YonedaExtension Y Z (n + 1)) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n
        (ofExtension (X := Y) (Y := Z) (n := n) b) =
      (0 : YonedaExt X Z ((n + (m + 1)) + 1)) := by
  rw [leftProductByYonedaExtensionWith_ofExtension]
  exact ofExtension_eq_zero_of_splitFactorData (h.spliceLeftWith pull b)

/-- An arbitrary fixed left chain with a split factor induces the zero homomorphism. -/
theorem leftProductByYonedaExtensionWith_eq_zero_of_splitFactor
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a : YonedaExtension X Y (m + 1)}
    (h : YonedaExtension.SplitFactorData a) (n : ℕ) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n = 0 := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro b
  change leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
      pullBaer pullPushoutData a n
      (ofExtension (X := Y) (Y := Z) (n := n) b) = 0
  exact leftProductByYonedaExtensionWith_ofExtension_eq_zero_of_splitFactor
    pull pullIso pullIsoBetween pullSplit pullBaer pullPushoutData h b

/-- Arbitrary fixed-left Baer relations remain additive on generators. -/
theorem leftProductByYonedaExtensionWith_ofExtension_eq_add_of_baerLeftChain
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a b sum : YonedaExtension X Y (m + 1)}
    (h : YonedaExtension.BaerSumData a b sum) (c : YonedaExtension Y Z (n + 1)) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData sum n
        (ofExtension (X := Y) (Y := Z) (n := n) c) =
      leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
          pullBaer pullPushoutData a n
          (ofExtension (X := Y) (Y := Z) (n := n) c) +
        leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
          pullBaer pullPushoutData b n
          (ofExtension (X := Y) (Y := Z) (n := n) c) := by
  rw [leftProductByYonedaExtensionWith_ofExtension,
    leftProductByYonedaExtensionWith_ofExtension,
    leftProductByYonedaExtensionWith_ofExtension]
  exact ofExtension_eq_add_of_baerChain (h.spliceLeftWith pull c)

/-- Arbitrary fixed-left Baer relations give additive conditional homomorphisms. -/
theorem leftProductByYonedaExtensionWith_eq_add_of_baerLeftChain
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a b sum : YonedaExtension X Y (m + 1)}
    (h : YonedaExtension.BaerSumData a b sum) (n : ℕ) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData sum n =
      leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
          pullBaer pullPushoutData a n +
        leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
          pullBaer pullPushoutData b n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro c
  change leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
      pullBaer pullPushoutData sum n
      (ofExtension (X := Y) (Y := Z) (n := n) c) =
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n
        (ofExtension (X := Y) (Y := Z) (n := n) c) +
      leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData b n
        (ofExtension (X := Y) (Y := Z) (n := n) c)
  exact leftProductByYonedaExtensionWith_ofExtension_eq_add_of_baerLeftChain
    pull pullIso pullIsoBetween pullSplit pullBaer pullPushoutData h c

/--
For canonical MetrizableLCA pullbacks, a fixed arbitrary left Yoneda extension
acts on the right Ext quotient once the remaining pullback-pushout exchange data
is supplied for degree-zero left tails.
-/
noncomputable def leftProductByYonedaExtension_metrizableWithPushoutData
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y m) (n : ℕ)
    (pullPushoutData :
      ∀ {A B W V : MetrizableLCA.{u}} (f : A ⟶ B)
        (e : ShortExactExtension (C := MetrizableLCA.{u}) B W) (g : W ⟶ V)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f)) :
    YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1) →+
      YonedaExt (C := MetrizableLCA.{u}) X Z ((n + m) + 1) :=
  leftProductByYonedaExtensionWith (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_ _ _} f {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _ _ _} f {_} {_} {_} h =>
      MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_ _ _} f e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {_ _ W} f [HasBinaryBiproduct _ _] [HasBinaryBiproduct _ _]
        [HasBinaryBiproduct W W] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _ _ _} f e g {_} h => pullPushoutData f e g h)
    a n

@[simp]
theorem leftProductByYonedaExtension_metrizableWithPushoutData_ofExtension
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y m)
    (pullPushoutData :
      ∀ {A B W V : MetrizableLCA.{u}} (f : A ⟶ B)
        (e : ShortExactExtension (C := MetrizableLCA.{u}) B W) (g : W ⟶ V)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f))
    (b : YonedaExtension (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    leftProductByYonedaExtension_metrizableWithPushoutData
        (X := X) (Y := Y) (Z := Z) a n pullPushoutData
        (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) b) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := n + m)
        (YonedaExtension.spliceLeftWith
          (C := MetrizableLCA.{u})
          (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a b) :=
  leftProductByYonedaExtensionWith_ofExtension
    (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_ _ _} f {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _ _ _} f {_} {_} {_} h =>
      MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_ _ _} f e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {_ _ W} f [HasBinaryBiproduct _ _] [HasBinaryBiproduct _ _]
        [HasBinaryBiproduct W W] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _ _ _} f e g {_} h => pullPushoutData f e g h)
    a b

/-- Termwise-related arbitrary left MetrizableLCA chains induce the same conditional map. -/
theorem leftProductByYonedaExtension_metrizableWithPushoutData_eq_of_rel
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a a' : YonedaExtension (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.Rel a a') (n : ℕ)
    (pullPushoutData :
      ∀ {A B W V : MetrizableLCA.{u}} (f : A ⟶ B)
        (e : ShortExactExtension (C := MetrizableLCA.{u}) B W) (g : W ⟶ V)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f)) :
    leftProductByYonedaExtension_metrizableWithPushoutData
        (X := X) (Y := Y) (Z := Z) a n pullPushoutData =
      leftProductByYonedaExtension_metrizableWithPushoutData
        (X := X) (Y := Y) (Z := Z) a' n pullPushoutData :=
  leftProductByYonedaExtensionWith_eq_of_rel
    (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_ _ _} f {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _ _ _} f {_} {_} {_} h =>
      MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_ _ _} f e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {_ _ W} f [HasBinaryBiproduct _ _] [HasBinaryBiproduct _ _]
        [HasBinaryBiproduct W W] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _ _ _} f e g {_} h => pullPushoutData f e g h)
    h n

/-- A fixed arbitrary left MetrizableLCA chain with a split factor acts by zero. -/
theorem leftProductByYonedaExtension_metrizableWithPushoutData_eq_zero_of_splitFactor
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.SplitFactorData a) (n : ℕ)
    (pullPushoutData :
      ∀ {A B W V : MetrizableLCA.{u}} (f : A ⟶ B)
        (e : ShortExactExtension (C := MetrizableLCA.{u}) B W) (g : W ⟶ V)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f)) :
    leftProductByYonedaExtension_metrizableWithPushoutData
        (X := X) (Y := Y) (Z := Z) a n pullPushoutData = 0 :=
  leftProductByYonedaExtensionWith_eq_zero_of_splitFactor
    (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_ _ _} f {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _ _ _} f {_} {_} {_} h =>
      MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_ _ _} f e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {_ _ W} f [HasBinaryBiproduct _ _] [HasBinaryBiproduct _ _]
        [HasBinaryBiproduct W W] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _ _ _} f e g {_} h => pullPushoutData f e g h)
    h n

/-- Fixed arbitrary left MetrizableLCA Baer relations give additive conditional maps. -/
theorem leftProductByYonedaExtension_metrizableWithPushoutData_eq_add_of_baerLeftChain
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a b sum : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.BaerSumData a b sum) (n : ℕ)
    (pullPushoutData :
      ∀ {A B W V : MetrizableLCA.{u}} (f : A ⟶ B)
        (e : ShortExactExtension (C := MetrizableLCA.{u}) B W) (g : W ⟶ V)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f)) :
    leftProductByYonedaExtension_metrizableWithPushoutData
        (X := X) (Y := Y) (Z := Z) sum n pullPushoutData =
      leftProductByYonedaExtension_metrizableWithPushoutData
          (X := X) (Y := Y) (Z := Z) a n pullPushoutData +
        leftProductByYonedaExtension_metrizableWithPushoutData
          (X := X) (Y := Y) (Z := Z) b n pullPushoutData :=
  leftProductByYonedaExtensionWith_eq_add_of_baerLeftChain
    (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_ _ _} f {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _ _ _} f {_} {_} {_} h =>
      MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_ _ _} f e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {_ _ W} f [HasBinaryBiproduct _ _] [HasBinaryBiproduct _ _]
        [HasBinaryBiproduct W W] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _ _ _} f e g {_} h => pullPushoutData f e g h)
    h n

/-- A fixed arbitrary left MetrizableLCA chain acts on positive-degree right Ext. -/
noncomputable def leftProductByYonedaExtension_metrizable
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y m) (n : ℕ) :
    YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1) →+
      YonedaExt (C := MetrizableLCA.{u}) X Z ((n + m) + 1) :=
  leftProductByYonedaExtension_metrizableWithPushoutData (X := X) (Y := Y) (Z := Z) a n
    (fun {_ _ _ _} f e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)

@[simp]
theorem leftProductByYonedaExtension_metrizable_ofExtension
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y m)
    (b : YonedaExtension (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    leftProductByYonedaExtension_metrizable (X := X) (Y := Y) (Z := Z) a n
        (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) b) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := n + m)
        (YonedaExtension.spliceLeftWith
          (C := MetrizableLCA.{u})
          (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a b) :=
  leftProductByYonedaExtension_metrizableWithPushoutData_ofExtension
    (X := X) (Y := Y) (Z := Z) a
    (fun {_ _ _ _} f e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)
    b

/-- Termwise-related arbitrary left MetrizableLCA chains induce the same map. -/
theorem leftProductByYonedaExtension_metrizable_eq_of_rel
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a a' : YonedaExtension (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.Rel a a') (n : ℕ) :
    leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) a n =
      leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) a' n :=
  leftProductByYonedaExtension_metrizableWithPushoutData_eq_of_rel
    (X := X) (Y := Y) (Z := Z) h n
    (fun {_ _ _ _} f e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)

/-- Recursively isomorphic arbitrary left MetrizableLCA chains induce the same map. -/
theorem leftProductByYonedaExtension_metrizable_eq_of_relIso
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.RelIso (C := MetrizableLCA.{u}) (CategoryTheory.Iso.refl X) a b)
    (n : ℕ) :
    leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) a n =
      leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) b n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro c
  change leftProductByYonedaExtension_metrizable
      (X := X) (Y := Y) (Z := Z) a n
      (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) c) =
    leftProductByYonedaExtension_metrizable
      (X := X) (Y := Y) (Z := Z) b n
      (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) c)
  rw [leftProductByYonedaExtension_metrizable_ofExtension,
    leftProductByYonedaExtension_metrizable_ofExtension]
  exact ofExtension_eq_ofExtension_of_relIso
    (YonedaExtension.RelIso.spliceLeftWith_metrizable h c)

/-- A fixed arbitrary left MetrizableLCA chain with a split factor acts by zero. -/
theorem leftProductByYonedaExtension_metrizable_eq_zero_of_splitFactor
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.SplitFactorData a) (n : ℕ) :
    leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) a n = 0 :=
  leftProductByYonedaExtension_metrizableWithPushoutData_eq_zero_of_splitFactor
    (X := X) (Y := Y) (Z := Z) h n
    (fun {_ _ _ _} f e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)

/-- Fixed arbitrary left MetrizableLCA Baer relations give additive maps. -/
theorem leftProductByYonedaExtension_metrizable_eq_add_of_baerLeftChain
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a b sum : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.BaerSumData a b sum) (n : ℕ) :
    leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) sum n =
      leftProductByYonedaExtension_metrizable
          (X := X) (Y := Y) (Z := Z) a n +
        leftProductByYonedaExtension_metrizable
          (X := X) (Y := Y) (Z := Z) b n :=
  leftProductByYonedaExtension_metrizableWithPushoutData_eq_add_of_baerLeftChain
    (X := X) (Y := Y) (Z := Z) h n
    (fun {_ _ _ _} f e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)

theorem composeTailHomFreeHom_baerChain_mem {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    [HasBinaryBiproduct Y' Y']
    (pushBaer : ∀ {Z : C} [HasBinaryBiproduct Z Z] [HasBinaryBiproduct Y Y]
      [HasBinaryBiproduct Y' Y'] {e₁ e₂ sum : ShortExactExtension Z Y},
      ShortExactExtension.BaerSumData e₁ e₂ sum →
        ShortExactExtension.BaerSumData (push e₁ f) (push e₂ f) (push sum f))
    {a b sum : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.BaerSumData a b sum) :
    composeTailHomFreeHom (X := X) f n
        (FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X Y' n := by
  induction h with
  | one h =>
      exact composeTailHomFreeHom_baer_mem f push pushData h (pushBaer h)
  | head h tail =>
      exact composeTailHomFreeHom_baerChain_head_mem f h tail
  | cons e h ih =>
      have htail := ih f pushBaer
      have hlift := consLeft_relationSubgroup_le (Z := Y') e _ htail
      simpa [composeTailHomFreeHom, consLeftFreeHom, YonedaExtension.consLeftMap,
        YonedaExtension.composeTailHom, map_sub] using hlift

theorem composeTailHomFreeHom_homTail_mem {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushAssocIso : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y)
      {out : ShortExactExtension Z Y},
      ShortExactExtension.PushoutData e g out →
        ShortExactExtension.Iso (push e (g ≫ f)) (push out f))
    {a b : YonedaExtension X Y (n + 1)}
    (h : YonedaExtension.HomTailData a b) :
    composeTailHomFreeHom (X := X) f n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup X Y' n := by
  induction h with
  | one e g h =>
      exact composeTailHomFreeHom_homTail_one_mem f push pushData e g h
        (pushAssocIso e g h)
  | cons e h ih =>
      have htail := ih f pushAssocIso
      have hlift := consLeft_relationSubgroup_le (Z := Y') e _ htail
      simpa [composeTailHomFreeHom, consLeftFreeHom, YonedaExtension.consLeftMap,
        YonedaExtension.composeTailHom, map_sub] using hlift

/--
For the canonical MetrizableLCA pushout model, tail composition sends every
hom-tail relation generator to the target relation subgroup.
-/
theorem composeTailHomFreeHom_homTail_mem_metrizable
    {X Y Y' : MetrizableLCA.{u}} {n : ℕ} (f : Y ⟶ Y')
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)}
    (h : YonedaExtension.HomTailData (C := MetrizableLCA.{u}) a b) :
    composeTailHomFreeHom (C := MetrizableLCA.{u}) (X := X) f n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) ∈
      yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y' n :=
  composeTailHomFreeHom_homTail_mem (C := MetrizableLCA.{u}) (X := X) (Y := Y) f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    (fun {_ _} e g {_} h => MetrizableLCA.shortExactExtensionPushoutAssocIso e g f h)
    h

/--
Under the expected pushout compatibility data, composing a hom on the tail
preserves every positive-degree Yoneda relation generator.
-/
theorem composeTailHom_relationSubgroup_le {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting)
    [HasBinaryBiproduct Y' Y']
    (pushBaer : ∀ {Z : C} [HasBinaryBiproduct Z Z] [HasBinaryBiproduct Y Y]
      [HasBinaryBiproduct Y' Y'] {e₁ e₂ sum : ShortExactExtension Z Y},
      ShortExactExtension.BaerSumData e₁ e₂ sum →
        ShortExactExtension.BaerSumData (push e₁ f) (push e₂ f) (push sum f))
    (pushAssocIso : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y)
      {out : ShortExactExtension Z Y},
      ShortExactExtension.PushoutData e g out →
        ShortExactExtension.Iso (push e (g ≫ f)) (push out f)) :
    yonedaRelationSubgroup X Y n ≤
      (yonedaRelationSubgroup X Y' n).comap
        (composeTailHomFreeHom (X := X) f n) := by
  rw [yonedaRelationSubgroup]
  refine (AddSubgroup.closure_le _).mpr ?_
  intro z hz
  change composeTailHomFreeHom (X := X) f n z ∈ yonedaRelationSubgroup X Y' n
  cases hz with
  | iso h =>
      exact composeTailHomFreeHom_rel_mem (X := X) f h
  | chainIso h =>
      exact composeTailHomFreeHom_relIso_mem (X := X) f h
  | split e s =>
      exact composeTailHomFreeHom_split_mem (X := X) f push pushData pushSplit e s
  | baer h =>
      exact composeTailHomFreeHom_baer_mem (X := X) f push pushData h (pushBaer h)
  | baerChain h =>
      exact composeTailHomFreeHom_baerChain_mem (X := X) f push pushData pushBaer h
  | leftSplit e g s =>
      exact composeTailHomFreeHom_leftSplit_mem (X := X) f push pushData pushSplit e g s
  | rightSplit h =>
      exact composeTailHomFreeHom_rightSplit_mem (X := X) f push pushData pushSplit h
  | splitFactor h =>
      exact composeTailHomFreeHom_splitFactor_mem (X := X) f push pushData pushSplit h
  | homTail h =>
      exact composeTailHomFreeHom_homTail_mem (X := X) f push pushData pushAssocIso h
  | homTailLeft pullLeft h c =>
      simpa [composeTailHomFreeHom, map_sub, Nat.add_assoc] using
        AddSubgroup.subset_closure
          (YonedaRelGenerator.homTailLeft (X := X) (Y := Y') pullLeft h
            (YonedaExtension.composeTailHom f c))

/--
Positive-degree tail hom composition, descended from formal chains to the
local Yoneda Ext quotient under the same compatibility data.
-/
noncomputable def composeTailHomMapWith {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting)
    [HasBinaryBiproduct Y' Y']
    (pushBaer : ∀ {Z : C} [HasBinaryBiproduct Z Z] [HasBinaryBiproduct Y Y]
      [HasBinaryBiproduct Y' Y'] {e₁ e₂ sum : ShortExactExtension Z Y},
      ShortExactExtension.BaerSumData e₁ e₂ sum →
        ShortExactExtension.BaerSumData (push e₁ f) (push e₂ f) (push sum f))
    (pushAssocIso : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y)
      {out : ShortExactExtension Z Y},
      ShortExactExtension.PushoutData e g out →
        ShortExactExtension.Iso (push e (g ≫ f)) (push out f)) :
    YonedaExt X Y (n + 1) →+ YonedaExt X Y' (n + 1) :=
  QuotientAddGroup.map (yonedaRelationSubgroup X Y n) (yonedaRelationSubgroup X Y' n)
    (composeTailHomFreeHom (X := X) f n)
    (composeTailHom_relationSubgroup_le (X := X) (Y := Y) f push pushData pushSplit
      pushBaer pushAssocIso)

@[simp]
theorem composeTailHomMapWith_ofExtension {Y' : C} (f : Y ⟶ Y')
    (push : {Z W : C} → (e : ShortExactExtension Z W) → (g : W ⟶ Y') →
      ShortExactExtension Z Y')
    (pushData : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y'),
      ShortExactExtension.PushoutData e g (push e g))
    (pushSplit : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y')
      (_ : e.shortComplex.Splitting), (push e g).shortComplex.Splitting)
    [HasBinaryBiproduct Y' Y']
    (pushBaer : ∀ {Z : C} [HasBinaryBiproduct Z Z] [HasBinaryBiproduct Y Y]
      [HasBinaryBiproduct Y' Y'] {e₁ e₂ sum : ShortExactExtension Z Y},
      ShortExactExtension.BaerSumData e₁ e₂ sum →
        ShortExactExtension.BaerSumData (push e₁ f) (push e₂ f) (push sum f))
    (pushAssocIso : ∀ {Z W : C} (e : ShortExactExtension Z W) (g : W ⟶ Y)
      {out : ShortExactExtension Z Y},
      ShortExactExtension.PushoutData e g out →
        ShortExactExtension.Iso (push e (g ≫ f)) (push out f))
    (a : YonedaExtension X Y (n + 1)) :
    composeTailHomMapWith f push pushData pushSplit pushBaer pushAssocIso
        (ofExtension (X := X) (Y := Y) (n := n) a) =
      ofExtension (X := X) (Y := Y') (n := n) (YonedaExtension.composeTailHom f a) :=
  rfl

/--
For the canonical MetrizableLCA pushout model, tail composition sends every
positive-degree Yoneda relation into the target relation subgroup.
-/
theorem composeTailHom_relationSubgroup_le_metrizable
    {X Y Y' : MetrizableLCA.{u}} (f : Y ⟶ Y') (n : ℕ)
    [HasBinaryBiproduct Y' Y'] :
    yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y n ≤
      (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y' n).comap
        (composeTailHomFreeHom (C := MetrizableLCA.{u}) (X := X) f n) :=
  composeTailHom_relationSubgroup_le (C := MetrizableLCA.{u}) (X := X) (Y := Y) f
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushout e g)
    (fun {_ _} e g => MetrizableLCA.shortExactExtensionPushoutData e g)
    (fun {_ _} e g s => MetrizableLCA.shortExactExtensionPushoutSplitting e g s)
    (fun {Z} [HasBinaryBiproduct Z Z] [HasBinaryBiproduct Y Y]
        [HasBinaryBiproduct Y' Y'] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPushoutBaerSumData f h)
    (fun {_ _} e g {_} h => MetrizableLCA.shortExactExtensionPushoutAssocIso e g f h)

/-- Positive-degree tail composition for canonical MetrizableLCA pushouts. -/
noncomputable def composeTailHomMap_metrizable
    {X Y Y' : MetrizableLCA.{u}} (f : Y ⟶ Y') (n : ℕ)
    [HasBinaryBiproduct Y' Y'] :
    YonedaExt (C := MetrizableLCA.{u}) X Y (n + 1) →+
      YonedaExt (C := MetrizableLCA.{u}) X Y' (n + 1) :=
  QuotientAddGroup.map
    (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y n)
    (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y' n)
    (composeTailHomFreeHom (C := MetrizableLCA.{u}) (X := X) f n)
    (composeTailHom_relationSubgroup_le_metrizable (X := X) f n)

@[simp]
theorem composeTailHomMap_metrizable_ofExtension
    {X Y Y' : MetrizableLCA.{u}} (f : Y ⟶ Y') (n : ℕ)
    [HasBinaryBiproduct Y' Y'] (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (n + 1)) :
    composeTailHomMap_metrizable (X := X) f n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := n) a) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y') (n := n)
        (YonedaExtension.composeTailHom f a) :=
  rfl

/-- Tail hom composition on Ext sends the strict-sequence constructor to the composed generator. -/
@[simp]
theorem composeTailHomMap_metrizable_ofStrictShortExact
    {X Y Y' M : MetrizableLCA.{u}} (f : Y ⟶ Y')
    [HasBinaryBiproduct Y' Y'] (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero)) :
    composeTailHomMap_metrizable (X := X) f 0
        (ofStrictShortExact (X := X) (Y := Y) i p zero h) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y') (n := 0)
        (YonedaExtension.composeTailHom f
          (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension) := by
  rw [ofStrictShortExact_eq_ofExtension]
  exact composeTailHomMap_metrizable_ofExtension (X := X) f 0
    ((MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension)

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

/-- Left splicing respects isomorphism of the fixed one-fold left factor. -/
theorem leftProductByExtension_ofExtension_eq_of_isoLeft
    {e e' : ShortExactExtension X Y} (h : ShortExactExtension.Iso e e')
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      leftProductByExtension (X := X) (Y := Y) (Z := Z) e' n
        (ofExtension (X := Y) (Y := Z) (n := n) a) := by
  rw [leftProductByExtension_ofExtension, leftProductByExtension_ofExtension]
  exact ofExtension_eq_ofExtension_of_rel
    (YonedaExtension.Rel.cons h (YonedaExtension.Rel.refl a))

/-- Left splicing respects a Baer relation in the fixed one-fold left factor. -/
theorem leftProductByExtension_ofExtension_eq_add_of_baerLeft
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) sum n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      leftProductByExtension (X := X) (Y := Y) (Z := Z) e₁ n
          (ofExtension (X := Y) (Y := Z) (n := n) a) +
        leftProductByExtension (X := X) (Y := Y) (Z := Z) e₂ n
          (ofExtension (X := Y) (Y := Z) (n := n) a) := by
  rw [leftProductByExtension_ofExtension, leftProductByExtension_ofExtension,
    leftProductByExtension_ofExtension]
  simpa [YonedaExtension.consLeftMap] using ofExtension_eq_add_of_baerHead h a

/-- The public `baer_sum` API agrees with left-product additivity for a Baer left factor. -/
theorem leftProductByExtension_baer_sum_ofExtension_eq_of_baerLeft
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (a : YonedaExtension Y Z (n + 1)) :
    baer_sum
        (leftProductByExtension (X := X) (Y := Y) (Z := Z) e₁ n
          (ofExtension (X := Y) (Y := Z) (n := n) a))
        (leftProductByExtension (X := X) (Y := Y) (Z := Z) e₂ n
          (ofExtension (X := Y) (Y := Z) (n := n) a)) =
      leftProductByExtension (X := X) (Y := Y) (Z := Z) sum n
        (ofExtension (X := Y) (Y := Z) (n := n) a) := by
  dsimp [baer_sum]
  exact (leftProductByExtension_ofExtension_eq_add_of_baerLeft h a).symm

/-- A split one-fold left factor gives the zero homomorphism on right Ext. -/
theorem leftProductByExtension_eq_zero_of_split
    (e : ShortExactExtension X Y) (s : e.shortComplex.Splitting) (n : ℕ) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e n = 0 := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByExtension (X := X) (Y := Y) (Z := Z) e n
      (ofExtension (X := Y) (Y := Z) (n := n) a) = 0
  exact leftProductByExtension_ofExtension_eq_zero_of_split e s a

/--
Left splicing by a strict short exact sequence sends a generator to the
corresponding cons extension.
-/
theorem leftProductByStrictShortExact_ofExtension
    {X Y Z M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero))
    (n : ℕ) (a : YonedaExtension (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    leftProductByExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h) n
        (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) a) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := n + 1)
        (YonedaExtension.consLeftMap
          (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h) n a) :=
  leftProductByExtension_ofExtension
    (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h) a

/--
Left splicing by a strict short exact sequence sends a strict right `Ext¹`
generator to the corresponding two-fold Yoneda extension.
-/
theorem leftProductByStrictShortExact_ofStrictShortExact
    {X Y Z M N : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero))
    (j : Z ⟶ N) (q : N ⟶ Y) (zero' : j ≫ q = 0)
    (h' : MetrizableLCA.strictShortExact (ShortComplex.mk j q zero')) :
    leftProductByExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h) 0
        (ofStrictShortExact (X := Y) (Y := Z) j q zero' h') =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := 1)
        (YonedaExtension.consLeftMap
          (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h) 0
          (ShortExactExtension.toYonedaExtension
            (MetrizableLCA.shortExactExtensionOfStrictShortExact j q zero' h'))) := by
  rw [ofStrictShortExact_eq_ofExtension]
  exact leftProductByStrictShortExact_ofExtension i p zero h 0
    ((MetrizableLCA.shortExactExtensionOfStrictShortExact j q zero' h').toYonedaExtension)

/-- A split strict short exact sequence gives the zero left-product map. -/
theorem leftProductByStrictShortExact_eq_zero_of_split
    {X Y Z M : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero))
    (s : (ShortComplex.mk i p zero).Splitting) (n : ℕ) :
    leftProductByExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
        (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h) n = 0 := by
  exact leftProductByExtension_eq_zero_of_split
    (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h)
    (by simpa using s) n

/-- Isomorphic one-fold left factors induce the same homomorphism on right Ext. -/
theorem leftProductByExtension_eq_of_isoLeft
    {e e' : ShortExactExtension X Y} (h : ShortExactExtension.Iso e e') (n : ℕ) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e n =
      leftProductByExtension (X := X) (Y := Y) (Z := Z) e' n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByExtension (X := X) (Y := Y) (Z := Z) e n
      (ofExtension (X := Y) (Y := Z) (n := n) a) =
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e' n
      (ofExtension (X := Y) (Y := Z) (n := n) a)
  exact leftProductByExtension_ofExtension_eq_of_isoLeft h a

/-- A Baer relation in a one-fold left factor is additive as a homomorphism. -/
theorem leftProductByExtension_eq_add_of_baerLeft
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum) (n : ℕ) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) sum n =
      leftProductByExtension (X := X) (Y := Y) (Z := Z) e₁ n +
        leftProductByExtension (X := X) (Y := Y) (Z := Z) e₂ n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByExtension (X := X) (Y := Y) (Z := Z) sum n
      (ofExtension (X := Y) (Y := Z) (n := n) a) =
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e₁ n
        (ofExtension (X := Y) (Y := Z) (n := n) a) +
      leftProductByExtension (X := X) (Y := Y) (Z := Z) e₂ n
        (ofExtension (X := Y) (Y := Z) (n := n) a)
  exact leftProductByExtension_ofExtension_eq_add_of_baerLeft h a

/-- Left splicing by a fixed one-fold extension is additive in the right Ext variable. -/
theorem leftProductByExtension_add (e : ShortExactExtension X Y) (n : ℕ)
    (a b : YonedaExt Y Z (n + 1)) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e n (a + b) =
      leftProductByExtension (X := X) (Y := Y) (Z := Z) e n a +
        leftProductByExtension (X := X) (Y := Y) (Z := Z) e n b :=
  (leftProductByExtension (X := X) (Y := Y) (Z := Z) e n).map_add a b

/-- The public `baer_sum` API is preserved by left splicing in the right Ext variable. -/
theorem leftProductByExtension_baer_sum (e : ShortExactExtension X Y) (n : ℕ)
    (a b : YonedaExt Y Z (n + 1)) :
    leftProductByExtension (X := X) (Y := Y) (Z := Z) e n (baer_sum a b) =
      baer_sum
        (leftProductByExtension (X := X) (Y := Y) (Z := Z) e n a)
        (leftProductByExtension (X := X) (Y := Y) (Z := Z) e n b) := by
  dsimp [baer_sum]
  exact leftProductByExtension_add (X := X) (Y := Y) (Z := Z) e n a b

/-- Arbitrary fixed-left hom-tail relations induce equal maps on generators. -/
theorem leftProductByYonedaExtensionWith_ofExtension_eq_of_homTailLeftChain
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a b : YonedaExtension X Y (m + 1)}
    (h : YonedaExtension.HomTailData a b) (c : YonedaExtension Y Z (n + 1)) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n
        (ofExtension (X := Y) (Y := Z) (n := n) c) =
      leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData b n
        (ofExtension (X := Y) (Y := Z) (n := n) c) := by
  rw [leftProductByYonedaExtensionWith_ofExtension,
    leftProductByYonedaExtensionWith_ofExtension]
  exact ofExtension_eq_ofExtension_of_homTailLeftWith pull h c

/-- Conditional HomTail left descent gives equality of arbitrary fixed-left maps. -/
theorem leftProductByYonedaExtensionWith_eq_of_homTailLeftChain
    [HasBinaryBiproducts C]
    (pull : {A B W : C} → (f : A ⟶ B) → ShortExactExtension B W →
      ShortExactExtension A W)
    (pullIso : ∀ {A B W : C} (f : A ⟶ B)
      {e e' : ShortExactExtension B W},
      ShortExactExtension.Iso e e' → ShortExactExtension.Iso (pull f e) (pull f e'))
    (pullIsoBetween : ∀ {A B W W' : C} (f : A ⟶ B) {β : W ≅ W'}
        {e : ShortExactExtension B W} {e' : ShortExactExtension B W'},
        ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl B) β e e' →
          ShortExactExtension.IsoBetween (CategoryTheory.Iso.refl A) β (pull f e) (pull f e'))
    (pullSplit : ∀ {A B W : C} (f : A ⟶ B) (e : ShortExactExtension B W)
      (_ : e.shortComplex.Splitting), (pull f e).shortComplex.Splitting)
    (pullBaer :
      ∀ {A B W : C} (f : A ⟶ B) [HasBinaryBiproduct B B]
        [HasBinaryBiproduct A A] [HasBinaryBiproduct W W]
        {e₁ e₂ sum : ShortExactExtension B W},
        ShortExactExtension.BaerSumData e₁ e₂ sum →
          ShortExactExtension.BaerSumData (pull f e₁) (pull f e₂) (pull f sum))
    (pullPushoutData :
      ∀ {A B W V : C} (f : A ⟶ B) (e : ShortExactExtension B W) (g : W ⟶ V)
        {out : ShortExactExtension B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData (pull f e) g (pull f out))
    {m : ℕ} {a b : YonedaExtension X Y (m + 1)}
    (h : YonedaExtension.HomTailData a b) (n : ℕ) :
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData a n =
      leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
        pullBaer pullPushoutData b n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro c
  change leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
      pullBaer pullPushoutData a n
      (ofExtension (X := Y) (Y := Z) (n := n) c) =
    leftProductByYonedaExtensionWith (Z := Z) pull pullIso pullIsoBetween pullSplit
      pullBaer pullPushoutData b n
      (ofExtension (X := Y) (Y := Z) (n := n) c)
  exact leftProductByYonedaExtensionWith_ofExtension_eq_of_homTailLeftChain
    pull pullIso pullIsoBetween pullSplit pullBaer pullPushoutData h c

/-- MetrizableLCA HomTail left descent for arbitrary fixed-left maps. -/
theorem leftProductByYonedaExtension_metrizableWithPushoutData_eq_of_homTailLeftChain
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.HomTailData (C := MetrizableLCA.{u}) a b) (n : ℕ)
    (pullPushoutData :
      ∀ {A B W V : MetrizableLCA.{u}} (f : A ⟶ B)
        (e : ShortExactExtension (C := MetrizableLCA.{u}) B W) (g : W ⟶ V)
        {out : ShortExactExtension (C := MetrizableLCA.{u}) B V},
        ShortExactExtension.PushoutData e g out →
          ShortExactExtension.PushoutData
            (MetrizableLCA.shortExactExtensionPullback e f) g
            (MetrizableLCA.shortExactExtensionPullback out f)) :
    leftProductByYonedaExtension_metrizableWithPushoutData
        (X := X) (Y := Y) (Z := Z) a n pullPushoutData =
      leftProductByYonedaExtension_metrizableWithPushoutData
        (X := X) (Y := Y) (Z := Z) b n pullPushoutData :=
  leftProductByYonedaExtensionWith_eq_of_homTailLeftChain
    (C := MetrizableLCA.{u}) (X := X) (Y := Y) (Z := Z)
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
    (fun {_ _ _} f {_ _} h => MetrizableLCA.shortExactExtensionPullbackIso f h)
    (fun {_ _ _ _} f {_} {_} {_} h =>
      MetrizableLCA.shortExactExtensionPullbackIsoBetween f h)
    (fun {_ _ _} f e s => MetrizableLCA.shortExactExtensionPullbackSplitting e f s)
    (fun {_ _ W} f [HasBinaryBiproduct _ _] [HasBinaryBiproduct _ _]
        [HasBinaryBiproduct W W] {_ _ _} h =>
      MetrizableLCA.shortExactExtensionPullbackBaerSumData f h)
    (fun {_ _ _ _} f e g {_} h => pullPushoutData f e g h)
    h n

/-- MetrizableLCA HomTail left descent for arbitrary fixed-left maps. -/
theorem leftProductByYonedaExtension_metrizable_eq_of_homTailLeftChain
    {X Y Z : MetrizableLCA.{u}} {m : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.HomTailData (C := MetrizableLCA.{u}) a b) (n : ℕ) :
    leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) a n =
      leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) b n :=
  leftProductByYonedaExtension_metrizableWithPushoutData_eq_of_homTailLeftChain
    (X := X) (Y := Y) (Z := Z) h n
    (fun {_ _ _ _} f e g {_} h =>
      MetrizableLCA.shortExactExtensionPullbackPushoutDataOfPushoutData e f g h)

/--
Free left-variable Yoneda product: a formal left extension chain is sent to the
homomorphism that splices it with the right Ext quotient.
-/
noncomputable def yonedaProductLeftFreeHom
    {X Y Z : MetrizableLCA.{u}} (m n : ℕ) :
    PositiveYonedaExtFree (C := MetrizableLCA.{u}) X Y m →+
      (YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1) →+
        YonedaExt (C := MetrizableLCA.{u}) X Z ((n + (m + 1)) + 1)) :=
  FreeAbelianGroup.lift
    (fun a => leftProductByYonedaExtension_metrizable
      (X := X) (Y := Y) (Z := Z) a n)

@[simp]
theorem yonedaProductLeftFreeHom_of
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of a) =
      leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) a n :=
  FreeAbelianGroup.lift_apply_of
    (fun a => leftProductByYonedaExtension_metrizable
      (X := X) (Y := Y) (Z := Z) a n) a

/-- Termwise-related left representatives map to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_rel_eq_zero
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.Rel (C := MetrizableLCA.{u}) a b) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) = 0 := by
  rw [map_sub, yonedaProductLeftFreeHom_of, yonedaProductLeftFreeHom_of, sub_eq_zero]
  exact leftProductByYonedaExtension_metrizable_eq_of_rel (X := X) (Y := Y) (Z := Z) h n

/-- Recursively isomorphic left representatives map to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_relIso_eq_zero
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.RelIso (C := MetrizableLCA.{u}) (CategoryTheory.Iso.refl X) a b) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) = 0 := by
  rw [map_sub, yonedaProductLeftFreeHom_of, yonedaProductLeftFreeHom_of, sub_eq_zero]
  exact leftProductByYonedaExtension_metrizable_eq_of_relIso
    (X := X) (Y := Y) (Z := Z) h n

/-- A split one-fold left representative maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_split_eq_zero
    {X Y Z : MetrizableLCA.{u}} {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X Y)
    (s : e.shortComplex.Splitting) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) 0 n
        (FreeAbelianGroup.of e.toYonedaExtension) = 0 := by
  rw [yonedaProductLeftFreeHom_of]
  exact leftProductByYonedaExtension_metrizable_eq_zero_of_splitFactor
    (X := X) (Y := Y) (Z := Z)
    (YonedaExtension.SplitFactorData.head e s (YonedaExtension.ofHom (𝟙 Y))) n

/-- A right-split left representative maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_rightSplit_eq_zero
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.RightSplitData (C := MetrizableLCA.{u}) a) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of a) = 0 := by
  rw [yonedaProductLeftFreeHom_of]
  exact leftProductByYonedaExtension_metrizable_eq_zero_of_splitFactor
    (X := X) (Y := Y) (Z := Z) h.toSplitFactorData n

/-- A split-factor left representative maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_splitFactor_eq_zero
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {a : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.SplitFactorData (C := MetrizableLCA.{u}) a) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of a) = 0 := by
  rw [yonedaProductLeftFreeHom_of]
  exact leftProductByYonedaExtension_metrizable_eq_zero_of_splitFactor
    (X := X) (Y := Y) (Z := Z) h n

/-- A one-fold Baer left relation maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_baer_eq_zero
    {X Y Z : MetrizableLCA.{u}} {n : ℕ}
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {e₁ e₂ sum : ShortExactExtension (C := MetrizableLCA.{u}) X Y}
    (h : ShortExactExtension.BaerSumData (C := MetrizableLCA.{u}) e₁ e₂ sum) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) 0 n
        (FreeAbelianGroup.of sum.toYonedaExtension -
          FreeAbelianGroup.of e₁.toYonedaExtension -
          FreeAbelianGroup.of e₂.toYonedaExtension) = 0 := by
  rw [map_sub, map_sub, yonedaProductLeftFreeHom_of, yonedaProductLeftFreeHom_of,
    yonedaProductLeftFreeHom_of]
  rw [leftProductByYonedaExtension_metrizable_eq_add_of_baerLeftChain
    (X := X) (Y := Y) (Z := Z) (YonedaExtension.BaerSumData.one h) n]
  abel

/-- A positive-chain Baer left relation maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_baerChain_eq_zero
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {a b sum : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.BaerSumData (C := MetrizableLCA.{u}) a b sum) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of sum - FreeAbelianGroup.of a - FreeAbelianGroup.of b) = 0 := by
  rw [map_sub, map_sub, yonedaProductLeftFreeHom_of, yonedaProductLeftFreeHom_of,
    yonedaProductLeftFreeHom_of]
  rw [leftProductByYonedaExtension_metrizable_eq_add_of_baerLeftChain
    (X := X) (Y := Y) (Z := Z) h n]
  abel

/-- A left-split two-fold representative maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_leftSplit_eq_zero
    {X Y W Z : MetrizableLCA.{u}} {n : ℕ}
    (e : ShortExactExtension (C := MetrizableLCA.{u}) X W)
    (f : ShortExactExtension (C := MetrizableLCA.{u}) W Y)
    (s : f.shortComplex.Splitting) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) 1 n
        (FreeAbelianGroup.of (YonedaExtension.cons e f.toYonedaExtension)) = 0 := by
  rw [yonedaProductLeftFreeHom_of]
  exact leftProductByYonedaExtension_metrizable_eq_zero_of_splitFactor
    (X := X) (Y := Y) (Z := Z)
    (YonedaExtension.SplitFactorData.cons e
      (YonedaExtension.SplitFactorData.head f s (YonedaExtension.ofHom (𝟙 Y)))) n

/-- A hom-tail left relation maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_homTail_eq_zero
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)}
    (h : YonedaExtension.HomTailData (C := MetrizableLCA.{u}) a b) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n
        (FreeAbelianGroup.of a - FreeAbelianGroup.of b) = 0 := by
  rw [map_sub, yonedaProductLeftFreeHom_of, yonedaProductLeftFreeHom_of, sub_eq_zero]
  exact leftProductByYonedaExtension_metrizable_eq_of_homTailLeftChain
    (X := X) (Y := Y) (Z := Z) h n

/-- A spliced hom-tail left relation maps to zero in the free-left product target. -/
theorem yonedaProductLeftFreeHom_homTailLeft_eq_zero
    {X Y W Z : MetrizableLCA.{u}} {m n k : ℕ}
    (pull : {A B V : MetrizableLCA.{u}} → (f : A ⟶ B) →
      ShortExactExtension (C := MetrizableLCA.{u}) B V →
        ShortExactExtension (C := MetrizableLCA.{u}) A V)
    {a b : YonedaExtension (C := MetrizableLCA.{u}) X W (m + 1)}
    (h : YonedaExtension.HomTailData (C := MetrizableLCA.{u}) a b)
    (c : YonedaExtension (C := MetrizableLCA.{u}) W Y (n + 1)) :
    yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) (n + (m + 1)) k
        (FreeAbelianGroup.of (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u}) pull a c) -
          FreeAbelianGroup.of (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u}) pull b c)) =
      0 := by
  rw [map_sub, yonedaProductLeftFreeHom_of, yonedaProductLeftFreeHom_of, sub_eq_zero]
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro r
  change leftProductByYonedaExtension_metrizable
      (X := X) (Y := Y) (Z := Z)
      (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u}) pull a c) k
      (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := k) r) =
    leftProductByYonedaExtension_metrizable
      (X := X) (Y := Y) (Z := Z)
      (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u}) pull b c) k
      (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := k) r)
  rw [leftProductByYonedaExtension_metrizable_ofExtension,
    leftProductByYonedaExtension_metrizable_ofExtension]
  dsimp [ofExtension]
  change ((FreeAbelianGroup.of (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
      (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
      (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u}) pull a c) r) :
      PositiveYonedaExtFree (C := MetrizableLCA.{u}) X Z (k + (n + (m + 1) + 1))) :
      PositiveYonedaExt (C := MetrizableLCA.{u}) X Z (k + (n + (m + 1) + 1))) =
    ((FreeAbelianGroup.of (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
      (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
      (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u}) pull b c) r) :
      PositiveYonedaExtFree (C := MetrizableLCA.{u}) X Z (k + (n + (m + 1) + 1))) :
      PositiveYonedaExt (C := MetrizableLCA.{u}) X Z (k + (n + (m + 1) + 1)))
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have ha := YonedaExtension.spliceLeftWith_assoc_heq pull
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a c r
  have hb := YonedaExtension.spliceLeftWith_assoc_heq pull
    (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) b c r
  have gen := AddSubgroup.subset_closure
    (YonedaRelGenerator.homTailLeft (C := MetrizableLCA.{u}) (X := X) (Y := Z) pull h
      (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
        (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) c r))
  rw! [ha, hb]
  have hdeg : k + (n + 1) + (m + 1) = k + (n + (m + 1) + 1) := by omega
  have hcast := positiveYonedaExtFreeCast_relationSubgroup_mem
    (C := MetrizableLCA.{u}) (X := X) (Y := Z) hdeg gen
  simpa [positiveYonedaExtFreeCast, map_sub] using hcast

/-- The free-left product kills the full left-variable relation subgroup. -/
theorem yonedaProductLeft_relationSubgroup_le
    {X Y Z : MetrizableLCA.{u}} (m n : ℕ) :
    yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y m ≤
      (yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n).ker := by
  rw [yonedaRelationSubgroup]
  refine (AddSubgroup.closure_le _).mpr ?_
  intro z hz
  change yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n z = 0
  cases hz with
  | iso h =>
      exact yonedaProductLeftFreeHom_rel_eq_zero (X := X) (Y := Y) (Z := Z) h
  | chainIso h =>
      exact yonedaProductLeftFreeHom_relIso_eq_zero (X := X) (Y := Y) (Z := Z) h
  | split e s =>
      exact yonedaProductLeftFreeHom_split_eq_zero (X := X) (Y := Y) (Z := Z) e s
  | baer h =>
      exact yonedaProductLeftFreeHom_baer_eq_zero (X := X) (Y := Y) (Z := Z) h
  | baerChain h =>
      exact yonedaProductLeftFreeHom_baerChain_eq_zero (X := X) (Y := Y) (Z := Z) h
  | leftSplit e f s =>
      exact yonedaProductLeftFreeHom_leftSplit_eq_zero (X := X) (Y := Y) (Z := Z) e f s
  | rightSplit h =>
      exact yonedaProductLeftFreeHom_rightSplit_eq_zero (X := X) (Y := Y) (Z := Z) h
  | splitFactor h =>
      exact yonedaProductLeftFreeHom_splitFactor_eq_zero (X := X) (Y := Y) (Z := Z) h
  | homTail h =>
      exact yonedaProductLeftFreeHom_homTail_eq_zero (X := X) (Y := Y) (Z := Z) h
  | homTailLeft pull h c =>
      exact yonedaProductLeftFreeHom_homTailLeft_eq_zero
        (X := X) (Y := Y) (Z := Z) pull h c

/-- Quotient-wide positive-degree Yoneda product, additive in both variables. -/
noncomputable def yonedaProduct
    {X Y Z : MetrizableLCA.{u}} (m n : ℕ) :
    YonedaExt (C := MetrizableLCA.{u}) X Y (m + 1) →+
      (YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1) →+
        YonedaExt (C := MetrizableLCA.{u}) X Z ((n + (m + 1)) + 1)) :=
  QuotientAddGroup.lift (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y m)
    (yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n)
    (yonedaProductLeft_relationSubgroup_le (X := X) (Y := Y) (Z := Z) m n)

@[simp]
theorem yonedaProduct_ofExtension
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1)) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m) a) =
      leftProductByYonedaExtension_metrizable (X := X) (Y := Y) (Z := Z) a n := by
  dsimp [yonedaProduct, ofExtension]
  calc
    (QuotientAddGroup.lift (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y m)
        (yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n)
        (yonedaProductLeft_relationSubgroup_le (X := X) (Y := Y) (Z := Z) m n))
        ((FreeAbelianGroup.of a :
          PositiveYonedaExtFree (C := MetrizableLCA.{u}) X Y m) :
          PositiveYonedaExt (C := MetrizableLCA.{u}) X Y m) =
      yonedaProductLeftFreeHom (X := X) (Y := Y) (Z := Z) m n (FreeAbelianGroup.of a) := by
        exact QuotientAddGroup.lift_mk (yonedaRelationSubgroup (C := MetrizableLCA.{u}) X Y m)
          (yonedaProductLeft_relationSubgroup_le (X := X) (Y := Y) (Z := Z) m n)
          (FreeAbelianGroup.of a)
    _ = leftProductByYonedaExtension_metrizable (X := X) (Y := Y) (Z := Z) a n := by
        exact yonedaProductLeftFreeHom_of (X := X) (Y := Y) (Z := Z) a

@[simp]
theorem yonedaProduct_ofExtension_ofExtension
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X Y (m + 1))
    (b : YonedaExtension (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m) a)
        (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) b) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := n + (m + 1))
        (YonedaExtension.spliceLeftWith
          (C := MetrizableLCA.{u})
          (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a b) := by
  rw [yonedaProduct_ofExtension, leftProductByYonedaExtension_metrizable_ofExtension]

/-- Yoneda product on two strict short exact sequence generators. -/
theorem yonedaProduct_ofStrictShortExact_ofStrictShortExact
    {X Y Z M N : MetrizableLCA.{u}} (i : Y ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero))
    (j : Z ⟶ N) (q : N ⟶ Y) (zero' : j ≫ q = 0)
    (h' : MetrizableLCA.strictShortExact (ShortComplex.mk j q zero')) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) 0 0
        (ofStrictShortExact (X := X) (Y := Y) i p zero h)
        (ofStrictShortExact (X := Y) (Y := Z) j q zero' h') =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := 1)
        (YonedaExtension.spliceLeftWith
          (C := MetrizableLCA.{u})
          (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
          (ShortExactExtension.toYonedaExtension
            (MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h))
          (ShortExactExtension.toYonedaExtension
            (MetrizableLCA.shortExactExtensionOfStrictShortExact j q zero' h'))) := by
  rw [ofStrictShortExact_eq_ofExtension, ofStrictShortExact_eq_ofExtension]
  exact yonedaProduct_ofExtension_ofExtension
    ((MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension)
    ((MetrizableLCA.shortExactExtensionOfStrictShortExact j q zero' h').toYonedaExtension)

/-- The quotient cast bridges the two parenthesizations of a triple splice. -/
theorem positiveYonedaExtCast_spliceLeftWith_assoc
    {X W Y Z : MetrizableLCA.{u}} {m n l : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X W (m + 1))
    (b : YonedaExtension (C := MetrizableLCA.{u}) W Y (n + 1))
    (c : YonedaExtension (C := MetrizableLCA.{u}) Y Z (l + 1))
    (hdeg : l + (n + (m + 1) + 1) = (l + (n + 1)) + (m + 1)) :
    positiveYonedaExtCast (C := MetrizableLCA.{u}) (X := X) (Y := Z) hdeg
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z)
          (n := l + (n + (m + 1) + 1))
          (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
            (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
            (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
              (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a b) c)) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z)
        (n := (l + (n + 1)) + (m + 1))
        (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
          (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a
          (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
            (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) b c)) := by
  dsimp [positiveYonedaExtCast, ofExtension]
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hfree :
      positiveYonedaExtFreeCast (C := MetrizableLCA.{u}) (X := X) (Y := Z) hdeg
          (FreeAbelianGroup.of
            (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
              (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
              (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
                (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a b) c) :
            PositiveYonedaExtFree (C := MetrizableLCA.{u}) X Z
              (l + (n + (m + 1) + 1))) =
        (FreeAbelianGroup.of
          (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
            (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a
            (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
              (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) b c)) :
          PositiveYonedaExtFree (C := MetrizableLCA.{u}) X Z
            ((l + (n + 1)) + (m + 1))) := by
    dsimp [positiveYonedaExtFreeCast]
    rw! [YonedaExtension.spliceLeftWith_assoc_heq
      (C := MetrizableLCA.{u})
      (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
      (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f) a b c]
    simp
  rw [hfree, sub_self]
  exact AddSubgroup.zero_mem _

/-- Product-level associativity on generators after casting the target degree. -/
theorem yonedaProduct_ofExtension_assoc_cast
    {X W Y Z : MetrizableLCA.{u}} {m n l : ℕ}
    (a : YonedaExtension (C := MetrizableLCA.{u}) X W (m + 1))
    (b : YonedaExtension (C := MetrizableLCA.{u}) W Y (n + 1))
    (c : YonedaExtension (C := MetrizableLCA.{u}) Y Z (l + 1))
    (hdeg : l + (n + (m + 1) + 1) = (l + (n + 1)) + (m + 1)) :
    positiveYonedaExtCast (C := MetrizableLCA.{u}) (X := X) (Y := Z) hdeg
        (yonedaProduct (X := X) (Y := Y) (Z := Z) (n + (m + 1)) l
          (yonedaProduct (X := X) (Y := W) (Z := Y) m n
            (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := W) (n := m) a)
            (ofExtension (C := MetrizableLCA.{u}) (X := W) (Y := Y) (n := n) b))
          (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := l) c)) =
      yonedaProduct (X := X) (Y := W) (Z := Z) m (l + (n + 1))
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := W) (n := m) a)
        (yonedaProduct (X := W) (Y := Y) (Z := Z) n l
          (ofExtension (C := MetrizableLCA.{u}) (X := W) (Y := Y) (n := n) b)
          (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := l) c)) := by
  rw [yonedaProduct_ofExtension_ofExtension,
    yonedaProduct_ofExtension_ofExtension,
    yonedaProduct_ofExtension_ofExtension,
    yonedaProduct_ofExtension_ofExtension]
  exact positiveYonedaExtCast_spliceLeftWith_assoc (a := a) (b := b) (c := c) (hdeg := hdeg)

/-- Product-level associativity on strict short exact sequence generators. -/
theorem yonedaProduct_ofStrictShortExact_assoc_cast
    {X W Y Z M N P : MetrizableLCA.{u}} (i : W ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero))
    (j : Y ⟶ N) (q : N ⟶ W) (zero' : j ≫ q = 0)
    (h' : MetrizableLCA.strictShortExact (ShortComplex.mk j q zero'))
    (k : Z ⟶ P) (r : P ⟶ Y) (zero'' : k ≫ r = 0)
    (h'' : MetrizableLCA.strictShortExact (ShortComplex.mk k r zero'')) :
    positiveYonedaExtCast (C := MetrizableLCA.{u}) (X := X) (Y := Z)
        (show 0 + (0 + (0 + 1) + 1) = (0 + (0 + 1)) + (0 + 1) by rfl)
        (yonedaProduct (X := X) (Y := Y) (Z := Z) 1 0
          (yonedaProduct (X := X) (Y := W) (Z := Y) 0 0
            (ofStrictShortExact (X := X) (Y := W) i p zero h)
            (ofStrictShortExact (X := W) (Y := Y) j q zero' h'))
          (ofStrictShortExact (X := Y) (Y := Z) k r zero'' h'')) =
      yonedaProduct (X := X) (Y := W) (Z := Z) 0 1
        (ofStrictShortExact (X := X) (Y := W) i p zero h)
        (yonedaProduct (X := W) (Y := Y) (Z := Z) 0 0
          (ofStrictShortExact (X := W) (Y := Y) j q zero' h')
          (ofStrictShortExact (X := Y) (Y := Z) k r zero'' h'')) := by
  rw [ofStrictShortExact_eq_ofExtension, ofStrictShortExact_eq_ofExtension,
    ofStrictShortExact_eq_ofExtension]
  exact yonedaProduct_ofExtension_assoc_cast
    (a := ((MetrizableLCA.shortExactExtensionOfStrictShortExact i p zero h).toYonedaExtension))
    (b := ((MetrizableLCA.shortExactExtensionOfStrictShortExact j q zero' h').toYonedaExtension))
    (c := ((MetrizableLCA.shortExactExtensionOfStrictShortExact k r zero'' h'').toYonedaExtension))
    (hdeg := by rfl)

/-- Product-level associativity on strict `Ext¹` generators without a visible degree cast. -/
theorem yonedaProduct_ofStrictShortExact_assoc
    {X W Y Z M N P : MetrizableLCA.{u}} (i : W ⟶ M) (p : M ⟶ X)
    (zero : i ≫ p = 0)
    (h : MetrizableLCA.strictShortExact (ShortComplex.mk i p zero))
    (j : Y ⟶ N) (q : N ⟶ W) (zero' : j ≫ q = 0)
    (h' : MetrizableLCA.strictShortExact (ShortComplex.mk j q zero'))
    (k : Z ⟶ P) (r : P ⟶ Y) (zero'' : k ≫ r = 0)
    (h'' : MetrizableLCA.strictShortExact (ShortComplex.mk k r zero'')) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) 1 0
        (yonedaProduct (X := X) (Y := W) (Z := Y) 0 0
          (ofStrictShortExact (X := X) (Y := W) i p zero h)
          (ofStrictShortExact (X := W) (Y := Y) j q zero' h'))
        (ofStrictShortExact (X := Y) (Y := Z) k r zero'' h'') =
      yonedaProduct (X := X) (Y := W) (Z := Z) 0 1
        (ofStrictShortExact (X := X) (Y := W) i p zero h)
        (yonedaProduct (X := W) (Y := Y) (Z := Z) 0 0
          (ofStrictShortExact (X := W) (Y := Y) j q zero' h')
          (ofStrictShortExact (X := Y) (Y := Z) k r zero'' h'')) := by
  simpa using
    yonedaProduct_ofStrictShortExact_assoc_cast i p zero h j q zero' h' k r zero'' h''

theorem yonedaProduct_add_left
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a b : YonedaExt (C := MetrizableLCA.{u}) X Y (m + 1)) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n (a + b) =
      yonedaProduct (X := X) (Y := Y) (Z := Z) m n a +
        yonedaProduct (X := X) (Y := Y) (Z := Z) m n b :=
  map_add (yonedaProduct (X := X) (Y := Y) (Z := Z) m n) a b

theorem yonedaProduct_add_right
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExt (C := MetrizableLCA.{u}) X Y (m + 1))
    (b c : YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n a (b + c) =
      yonedaProduct (X := X) (Y := Y) (Z := Z) m n a b +
        yonedaProduct (X := X) (Y := Y) (Z := Z) m n a c :=
  map_add (yonedaProduct (X := X) (Y := Y) (Z := Z) m n a) b c

/-- Zero in the left Ext variable gives the zero Yoneda product homomorphism. -/
theorem yonedaProduct_zero_left
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ} :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (0 : YonedaExt (C := MetrizableLCA.{u}) X Y (m + 1)) =
      0 :=
  map_zero (yonedaProduct (X := X) (Y := Y) (Z := Z) m n)

/-- Zero in the right Ext variable is killed by the Yoneda product. -/
theorem yonedaProduct_zero_right
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExt (C := MetrizableLCA.{u}) X Y (m + 1)) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n a
        (0 : YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1)) =
      0 :=
  map_zero (yonedaProduct (X := X) (Y := Y) (Z := Z) m n a)

/-- The public `baer_sum` API is additive in the left Ext variable of the Yoneda product. -/
theorem yonedaProduct_baer_sum_left
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a b : YonedaExt (C := MetrizableLCA.{u}) X Y (m + 1))
    (c : YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n (baer_sum a b) c =
      baer_sum
        (yonedaProduct (X := X) (Y := Y) (Z := Z) m n a c)
        (yonedaProduct (X := X) (Y := Y) (Z := Z) m n b c) := by
  simpa [baer_sum] using
    congrArg (fun f => f c)
      (yonedaProduct_add_left (X := X) (Y := Y) (Z := Z) (m := m) (n := n) a b)

/-- The public `baer_sum` API is additive in the right Ext variable of the Yoneda product. -/
theorem yonedaProduct_baer_sum_right
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (a : YonedaExt (C := MetrizableLCA.{u}) X Y (m + 1))
    (b c : YonedaExt (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n a (baer_sum b c) =
      baer_sum
        (yonedaProduct (X := X) (Y := Y) (Z := Z) m n a b)
        (yonedaProduct (X := X) (Y := Y) (Z := Z) m n a c) := by
  simpa [baer_sum] using
    yonedaProduct_add_right (X := X) (Y := Y) (Z := Z) (m := m) (n := n) a b c

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

/--
MetrizableLCA left splicing by a positive chain agrees in Ext with the
canonical arbitrary-left splice representative.
-/
theorem ofExtension_spliceLeftWith_positiveChain_eq
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m)
    (a : YonedaExtension (C := MetrizableLCA.{u}) Y Z (n + 1)) :
    ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := n + (m + 1))
        (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
          (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
          p.toYonedaExtension a) =
      ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Z) (n := n + (m + 1))
        (YonedaExtension.PositiveChain.consLeftMap p a) := by
  induction p generalizing Z n with
  | @one X0 Y0 e =>
      change ofExtension (C := MetrizableLCA.{u}) (X := X0) (Y := Z) (n := n + 1)
          (YonedaExtension.cons e
            (YonedaExtension.pullbackHeadWith (C := MetrizableLCA.{u}) (𝟙 Y0)
              (fun {_} e => MetrizableLCA.shortExactExtensionPullback e (𝟙 Y0)) a)) =
        ofExtension (C := MetrizableLCA.{u}) (X := X0) (Y := Z) (n := n + 1)
          (YonedaExtension.cons e a)
      exact ofExtension_eq_ofExtension_of_rel
        (YonedaExtension.Rel.cons (ShortExactExtension.Iso.refl e)
          (MetrizableLCA.yonedaExtensionPullbackHeadIdRel a))
  | @cons X0 Y0 W0 m0 e tail ih =>
      calc
        ofExtension (C := MetrizableLCA.{u}) (X := X0) (Y := Z)
            (n := n + ((m0 + 1) + 1))
            (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
              (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
              (YonedaExtension.PositiveChain.cons e tail).toYonedaExtension a) =
          leftProductByExtension (C := MetrizableLCA.{u}) (X := X0) (Y := W0)
            (Z := Z) e (n + (m0 + 1))
            (ofExtension (C := MetrizableLCA.{u}) (X := W0) (Y := Z)
              (n := n + (m0 + 1))
              (YonedaExtension.spliceLeftWith (C := MetrizableLCA.{u})
                (fun {_ _ _} f e => MetrizableLCA.shortExactExtensionPullback e f)
                tail.toYonedaExtension a)) := by
            rw [leftProductByExtension_ofExtension]
            simp [YonedaExtension.PositiveChain.toYonedaExtension, YonedaExtension.consLeftMap]
        _ = leftProductByExtension (C := MetrizableLCA.{u}) (X := X0) (Y := W0)
            (Z := Z) e (n + (m0 + 1))
            (ofExtension (C := MetrizableLCA.{u}) (X := W0) (Y := Z)
              (n := n + (m0 + 1))
              (YonedaExtension.PositiveChain.consLeftMap tail a)) := by
            rw [ih]
        _ = ofExtension (C := MetrizableLCA.{u}) (X := X0) (Y := Z)
            (n := n + ((m0 + 1) + 1))
            (YonedaExtension.PositiveChain.consLeftMap
              (YonedaExtension.PositiveChain.cons e tail) a) := by
            rw [leftProductByExtension_ofExtension]
            simp [YonedaExtension.PositiveChain.consLeftMap, YonedaExtension.consLeftMap]

/-- Arbitrary-left MetrizableLCA product by a positive chain equals the positive-chain action. -/
theorem leftProductByYonedaExtension_metrizable_ofPositiveChain
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m) :
    leftProductByYonedaExtension_metrizable
        (X := X) (Y := Y) (Z := Z) p.toYonedaExtension n =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByYonedaExtension_metrizable
      (X := X) (Y := Y) (Z := Z) p.toYonedaExtension n
      (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) a) =
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n
      (ofExtension (C := MetrizableLCA.{u}) (X := Y) (Y := Z) (n := n) a)
  rw [leftProductByYonedaExtension_metrizable_ofExtension,
    leftProductByPositiveChain_ofExtension]
  exact ofExtension_spliceLeftWith_positiveChain_eq p a

/-- Yoneda product by a positive one-fold chain agrees with the positive-chain action. -/
theorem yonedaProduct_ofPositiveChain
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    (p : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
          p.toYonedaExtension) =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n := by
  rw [yonedaProduct_ofExtension]
  exact leftProductByYonedaExtension_metrizable_ofPositiveChain p

/-- Termwise-related positive left chains give the same spliced class on generators. -/
theorem leftProductByPositiveChain_ofExtension_eq_of_rel {m : ℕ}
    {p q : YonedaExtension.PositiveChain X Y m}
    (h : YonedaExtension.PositiveChain.Rel p q)
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) q n
        (ofExtension (X := Y) (Y := Z) (n := n) a) := by
  rw [leftProductByPositiveChain_ofExtension, leftProductByPositiveChain_ofExtension]
  exact ofExtension_eq_ofExtension_of_rel (h.consLeftMap a)

/-- A positive-chain Baer sum in the left factor is additive after splicing a generator. -/
theorem leftProductByPositiveChain_ofExtension_eq_add_of_baerLeftChain {m : ℕ}
    {p₁ p₂ sum : YonedaExtension.PositiveChain X Y m}
    (h : YonedaExtension.PositiveChain.BaerSumData p₁ p₂ sum)
    (a : YonedaExtension Y Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) sum n
        (ofExtension (X := Y) (Y := Z) (n := n) a) =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₁ n
          (ofExtension (X := Y) (Y := Z) (n := n) a) +
        leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₂ n
          (ofExtension (X := Y) (Y := Z) (n := n) a) := by
  rw [leftProductByPositiveChain_ofExtension, leftProductByPositiveChain_ofExtension,
    leftProductByPositiveChain_ofExtension]
  exact ofExtension_eq_add_of_baerChain (h.consLeftMap a)

/-- The public `baer_sum` API agrees with positive-chain left-factor additivity. -/
theorem leftProductByPositiveChain_baer_sum_ofExtension_eq_of_baerLeftChain {m : ℕ}
    {p₁ p₂ sum : YonedaExtension.PositiveChain X Y m}
    (h : YonedaExtension.PositiveChain.BaerSumData p₁ p₂ sum)
    (a : YonedaExtension Y Z (n + 1)) :
    baer_sum
        (leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₁ n
          (ofExtension (X := Y) (Y := Z) (n := n) a))
        (leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₂ n
          (ofExtension (X := Y) (Y := Z) (n := n) a)) =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) sum n
        (ofExtension (X := Y) (Y := Z) (n := n) a) := by
  dsimp [baer_sum]
  exact (leftProductByPositiveChain_ofExtension_eq_add_of_baerLeftChain h a).symm

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

/-- A head isomorphism of positive left chains gives the same spliced class. -/
theorem leftProductByPositiveChain_cons_ofExtension_eq_of_isoHead
    {W : C} {m : ℕ} {e e' : ShortExactExtension X Y}
    (h : ShortExactExtension.Iso e e')
    (p : YonedaExtension.PositiveChain Y W m)
    (a : YonedaExtension W Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e p) n
        (ofExtension (X := W) (Y := Z) (n := n) a) =
      leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e' p) n
        (ofExtension (X := W) (Y := Z) (n := n) a) := by
  rw [leftProductByPositiveChain_ofExtension, leftProductByPositiveChain_ofExtension]
  exact ofExtension_eq_ofExtension_of_rel
    (YonedaExtension.Rel.cons h
      (YonedaExtension.Rel.refl (YonedaExtension.PositiveChain.consLeftMap p a)))

/-- A Baer relation in the head of a positive left chain remains additive after splicing. -/
theorem leftProductByPositiveChain_cons_ofExtension_eq_add_of_baerHead
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {W : C} {m : ℕ} {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (p : YonedaExtension.PositiveChain Y W m)
    (a : YonedaExtension W Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons sum p) n
        (ofExtension (X := W) (Y := Z) (n := n) a) =
      leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₁ p) n
          (ofExtension (X := W) (Y := Z) (n := n) a) +
        leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₂ p) n
          (ofExtension (X := W) (Y := Z) (n := n) a) := by
  rw [leftProductByPositiveChain_ofExtension, leftProductByPositiveChain_ofExtension,
    leftProductByPositiveChain_ofExtension]
  simpa [YonedaExtension.PositiveChain.consLeftMap, Nat.add_assoc] using
    ofExtension_eq_add_of_baerHead h (YonedaExtension.PositiveChain.consLeftMap p a)

/-- The public `baer_sum` API agrees with head-Baer additivity for positive left chains. -/
theorem leftProductByPositiveChain_cons_baer_sum_ofExtension_eq_of_baerHead
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {W : C} {m : ℕ} {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (p : YonedaExtension.PositiveChain Y W m)
    (a : YonedaExtension W Z (n + 1)) :
    baer_sum
        (leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₁ p) n
          (ofExtension (X := W) (Y := Z) (n := n) a))
        (leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₂ p) n
          (ofExtension (X := W) (Y := Z) (n := n) a)) =
      leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons sum p) n
        (ofExtension (X := W) (Y := Z) (n := n) a) := by
  dsimp [baer_sum]
  exact (leftProductByPositiveChain_cons_ofExtension_eq_add_of_baerHead h p a).symm

/-- A fixed positive left chain with a split factor gives the zero homomorphism. -/
theorem leftProductByPositiveChain_eq_zero_of_splitFactor {m : ℕ}
    {p : YonedaExtension.PositiveChain X Y m}
    (h : YonedaExtension.PositiveChain.SplitFactorData p) (n : ℕ) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n = 0 := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n
      (ofExtension (X := Y) (Y := Z) (n := n) a) = 0
  exact leftProductByPositiveChain_ofExtension_eq_zero_of_splitFactor h a

/-- Termwise-related positive left chains induce the same homomorphism. -/
theorem leftProductByPositiveChain_eq_of_rel {m : ℕ}
    {p q : YonedaExtension.PositiveChain X Y m}
    (h : YonedaExtension.PositiveChain.Rel p q) (n : ℕ) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) q n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n
      (ofExtension (X := Y) (Y := Z) (n := n) a) =
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) q n
      (ofExtension (X := Y) (Y := Z) (n := n) a)
  exact leftProductByPositiveChain_ofExtension_eq_of_rel h a

/-- Isomorphic heads of positive left chains induce the same homomorphism on right Ext. -/
theorem leftProductByPositiveChain_cons_eq_of_isoHead
    {W : C} {m : ℕ} {e e' : ShortExactExtension X Y}
    (h : ShortExactExtension.Iso e e') (p : YonedaExtension.PositiveChain Y W m) (n : ℕ) :
    leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e p) n =
      leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e' p) n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
      (YonedaExtension.PositiveChain.cons e p) n
      (ofExtension (X := W) (Y := Z) (n := n) a) =
    leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
      (YonedaExtension.PositiveChain.cons e' p) n
      (ofExtension (X := W) (Y := Z) (n := n) a)
  exact leftProductByPositiveChain_cons_ofExtension_eq_of_isoHead h p a

/-- A positive-chain Baer sum in the left factor is additive as a homomorphism. -/
theorem leftProductByPositiveChain_eq_add_of_baerLeftChain {m : ℕ}
    {p₁ p₂ sum : YonedaExtension.PositiveChain X Y m}
    (h : YonedaExtension.PositiveChain.BaerSumData p₁ p₂ sum) (n : ℕ) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) sum n =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₁ n +
        leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₂ n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) sum n
      (ofExtension (X := Y) (Y := Z) (n := n) a) =
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₁ n
        (ofExtension (X := Y) (Y := Z) (n := n) a) +
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p₂ n
        (ofExtension (X := Y) (Y := Z) (n := n) a)
  exact leftProductByPositiveChain_ofExtension_eq_add_of_baerLeftChain h a

/-- A Baer relation in the head of a positive left chain is additive as a homomorphism. -/
theorem leftProductByPositiveChain_cons_eq_add_of_baerHead
    [HasBinaryBiproduct X X] [HasBinaryBiproduct Y Y]
    {W : C} {m : ℕ} {e₁ e₂ sum : ShortExactExtension X Y}
    (h : ShortExactExtension.BaerSumData e₁ e₂ sum)
    (p : YonedaExtension.PositiveChain Y W m) (n : ℕ) :
    leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons sum p) n =
      leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₁ p) n +
        leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
          (YonedaExtension.PositiveChain.cons e₂ p) n := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro a
  change leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
      (YonedaExtension.PositiveChain.cons sum p) n
      (ofExtension (X := W) (Y := Z) (n := n) a) =
    leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e₁ p) n
        (ofExtension (X := W) (Y := Z) (n := n) a) +
      leftProductByPositiveChain (X := X) (Y := W) (Z := Z)
        (YonedaExtension.PositiveChain.cons e₂ p) n
        (ofExtension (X := W) (Y := Z) (n := n) a)
  exact leftProductByPositiveChain_cons_ofExtension_eq_add_of_baerHead h p a

/-- Left splicing by a fixed positive chain is additive in the right Ext variable. -/
theorem leftProductByPositiveChain_add {m : ℕ}
    (p : YonedaExtension.PositiveChain X Y m) (n : ℕ)
    (a b : YonedaExt Y Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n (a + b) =
      leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n a +
        leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n b :=
  (leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n).map_add a b

/-- The public `baer_sum` API is preserved by fixed positive-chain left splicing. -/
theorem leftProductByPositiveChain_baer_sum {m : ℕ}
    (p : YonedaExtension.PositiveChain X Y m) (n : ℕ)
    (a b : YonedaExt Y Z (n + 1)) :
    leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n (baer_sum a b) =
      baer_sum
        (leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n a)
        (leftProductByPositiveChain (X := X) (Y := Y) (Z := Z) p n b) := by
  dsimp [baer_sum]
  exact leftProductByPositiveChain_add (X := X) (Y := Y) (Z := Z) p n a b

/-- Termwise-related positive left chains give the same public Yoneda product. -/
theorem yonedaProduct_ofPositiveChain_eq_of_rel
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {p q : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.PositiveChain.Rel p q) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
          p.toYonedaExtension) =
      yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
          q.toYonedaExtension) := by
  rw [yonedaProduct_ofPositiveChain, yonedaProduct_ofPositiveChain]
  exact leftProductByPositiveChain_eq_of_rel h n

/-- A positive left chain with a split factor gives the zero public Yoneda product. -/
theorem yonedaProduct_ofPositiveChain_eq_zero_of_splitFactor
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {p : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.PositiveChain.SplitFactorData p) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
          p.toYonedaExtension) =
      0 := by
  rw [yonedaProduct_ofPositiveChain]
  exact leftProductByPositiveChain_eq_zero_of_splitFactor h n

/-- A positive-chain Baer sum in the left factor is additive for the public Yoneda product. -/
theorem yonedaProduct_ofPositiveChain_eq_add_of_baerLeftChain
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {p₁ p₂ sum : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.PositiveChain.BaerSumData p₁ p₂ sum) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
          sum.toYonedaExtension) =
      yonedaProduct (X := X) (Y := Y) (Z := Z) m n
          (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
            p₁.toYonedaExtension) +
        yonedaProduct (X := X) (Y := Y) (Z := Z) m n
          (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
            p₂.toYonedaExtension) := by
  rw [yonedaProduct_ofPositiveChain, yonedaProduct_ofPositiveChain,
    yonedaProduct_ofPositiveChain]
  exact leftProductByPositiveChain_eq_add_of_baerLeftChain h n

/-- A positive-chain Baer sum is additive for the public Yoneda product on Ext classes. -/
theorem yonedaProduct_ofPositiveChainClass_eq_add_of_baerLeftChain
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {p₁ p₂ sum : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.PositiveChain.BaerSumData p₁ p₂ sum) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofPositiveChain (X := X) (Y := Y) sum) =
      yonedaProduct (X := X) (Y := Y) (Z := Z) m n
          (ofPositiveChain (X := X) (Y := Y) p₁) +
        yonedaProduct (X := X) (Y := Y) (Z := Z) m n
          (ofPositiveChain (X := X) (Y := Y) p₂) := by
  rw [ofPositiveChain_eq_ofExtension, ofPositiveChain_eq_ofExtension,
    ofPositiveChain_eq_ofExtension]
  exact yonedaProduct_ofPositiveChain_eq_add_of_baerLeftChain h

/-- The public `baer_sum` API in the left Ext variable respects positive-chain Baer sums. -/
theorem yonedaProduct_baer_sum_left_ofPositiveChain
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {p₁ p₂ sum : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.PositiveChain.BaerSumData p₁ p₂ sum) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (baer_sum
          (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
            p₁.toYonedaExtension)
          (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
            p₂.toYonedaExtension)) =
      yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofExtension (C := MetrizableLCA.{u}) (X := X) (Y := Y) (n := m)
          sum.toYonedaExtension) := by
  rw [baer_sum_ofExtension_eq_of_baerChain h.toYonedaExtension]

/-- The public `baer_sum` API in the left Ext variable respects `ofPositiveChain` Baer sums. -/
theorem yonedaProduct_baer_sum_left_ofPositiveChainClass
    {X Y Z : MetrizableLCA.{u}} {m n : ℕ}
    {p₁ p₂ sum : YonedaExtension.PositiveChain (C := MetrizableLCA.{u}) X Y m}
    (h : YonedaExtension.PositiveChain.BaerSumData p₁ p₂ sum) :
    yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (baer_sum
          (ofPositiveChain (X := X) (Y := Y) p₁)
          (ofPositiveChain (X := X) (Y := Y) p₂)) =
      yonedaProduct (X := X) (Y := Y) (Z := Z) m n
        (ofPositiveChain (X := X) (Y := Y) sum) := by
  rw [ofPositiveChain_eq_ofExtension, ofPositiveChain_eq_ofExtension,
    ofPositiveChain_eq_ofExtension]
  exact yonedaProduct_baer_sum_left_ofPositiveChain h

end LeftProduct

end YonedaExt

end LeanLCAExactChallenge
