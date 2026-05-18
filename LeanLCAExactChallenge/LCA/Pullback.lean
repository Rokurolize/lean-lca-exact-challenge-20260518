import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Constructions

/-!
Explicit pullbacks in the local `MetrizableLCA` category.

The pullback of continuous additive homomorphisms is realised as the closed
additive subgroup of the product cut out by the equality relation.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

variable {A B C : MetrizableLCA.{u}} (f : A ⟶ C) (g : B ⟶ C)

/-- The additive subgroup of `A × B` underlying the explicit pullback of `f` and `g`. -/
def pullbackSubgroup : AddSubgroup (A × B) where
  carrier := {p | f p.1 = g p.2}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    calc
      f (x.1 + y.1) = f x.1 + f y.1 := (f.hom : A →+ C).map_add x.1 y.1
      _ = g x.2 + g y.2 := by rw [hx, hy]
      _ = g (x.2 + y.2) := ((g.hom : B →+ C).map_add x.2 y.2).symm
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    calc
      f (-x.1) = - f x.1 := (f.hom : A →+ C).map_neg x.1
      _ = - g x.2 := by rw [hx]
      _ = g (-x.2) := ((g.hom : B →+ C).map_neg x.2).symm

lemma pullbackSubgroup_isClosed : IsClosed (pullbackSubgroup f g : Set (A × B)) := by
  dsimp [pullbackSubgroup]
  exact isClosed_eq (f.hom.continuous.comp continuous_fst) (g.hom.continuous.comp continuous_snd)

lemma isClosedEmbedding_zero_prod (A B : MetrizableLCA.{u}) :
    IsClosedEmbedding (fun y : B => ((0 : A), y)) := by
  refine ⟨isEmbedding_prodMkRight (0 : A), ?_⟩
  have hrange : Set.range (fun y : B => ((0 : A), y)) = {p : A × B | p.1 = 0} := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hp
      exact ⟨p.2, by ext <;> simp [hp.symm]⟩
  rw [hrange]
  exact isClosed_singleton.preimage continuous_fst

/-- The explicit pullback object in `MetrizableLCA`. -/
def pullbackObj : MetrizableLCA.{u} where
  carrier := pullbackSubgroup f g
  locallyCompactSpace := by
    change LocallyCompactSpace {p : A × B // p ∈ (pullbackSubgroup f g : Set (A × B))}
    exact (pullbackSubgroup_isClosed f g).locallyCompactSpace
  metrizableSpace := by
    change TopologicalSpace.MetrizableSpace {p : A × B // p ∈ (pullbackSubgroup f g : Set (A × B))}
    infer_instance

/-- First projection from the explicit pullback. -/
noncomputable def pullbackFst : pullbackObj f g ⟶ A where
  hom' :=
    { toFun := fun p => p.1.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_subtype_val.fst }

/-- Second projection from the explicit pullback. -/
noncomputable def pullbackSnd : pullbackObj f g ⟶ B where
  hom' :=
    { toFun := fun p => p.1.2
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_subtype_val.snd }

lemma pullback_condition : pullbackFst f g ≫ f = pullbackSnd f g ≫ g := by
  ext p
  exact p.2

/-- The universal lift into the explicit pullback. -/
noncomputable def pullbackLift {X : MetrizableLCA.{u}} (a : X ⟶ A) (b : X ⟶ B)
    (w : a ≫ f = b ≫ g) : X ⟶ pullbackObj f g where
  hom' :=
    { toFun := fun x => ⟨(a x, b x), by
        exact congrArg (fun h : X ⟶ C => h x) w⟩
      map_zero' := by
        apply Subtype.ext
        calc
          ((a 0, b 0) : A × B) = 0 := by ext <;> simp
          _ = ↑(0 : pullbackSubgroup f g) := (AddSubgroup.coe_zero (pullbackSubgroup f g)).symm
      map_add' := by
        intro x y
        apply Subtype.ext
        let ux : pullbackSubgroup f g := ⟨(a x, b x), congrArg (fun h : X ⟶ C => h x) w⟩
        let uy : pullbackSubgroup f g := ⟨(a y, b y), congrArg (fun h : X ⟶ C => h y) w⟩
        calc
          ((a (x + y), b (x + y)) : A × B) = (↑ux + ↑uy : A × B) := by
            ext <;> simp [ux, uy, map_add]
          _ = ↑(ux + uy) := (AddSubgroup.coe_add (pullbackSubgroup f g) ux uy).symm
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact a.hom.continuous.prodMk b.hom.continuous }

lemma pullbackLift_fst {X : MetrizableLCA.{u}} (a : X ⟶ A) (b : X ⟶ B)
    (w : a ≫ f = b ≫ g) : pullbackLift f g a b w ≫ pullbackFst f g = a := by
  ext x
  rfl

lemma pullbackLift_snd {X : MetrizableLCA.{u}} (a : X ⟶ A) (b : X ⟶ B)
    (w : a ≫ f = b ≫ g) : pullbackLift f g a b w ≫ pullbackSnd f g = b := by
  ext x
  rfl

lemma pullback_hom_ext {X : MetrizableLCA.{u}} {k l : X ⟶ pullbackObj f g}
    (hfst : k ≫ pullbackFst f g = l ≫ pullbackFst f g)
    (hsnd : k ≫ pullbackSnd f g = l ≫ pullbackSnd f g) : k = l := by
  apply MetrizableLCA.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun h : X ⟶ A => h x) hfst
  · exact congrArg (fun h : X ⟶ B => h x) hsnd

/-- The explicit pullback cone in `MetrizableLCA`. -/
noncomputable def pullbackCone : PullbackCone f g :=
  PullbackCone.mk (pullbackFst f g) (pullbackSnd f g) (pullback_condition f g)

/-- The explicit pullback cone is limiting. -/
noncomputable def pullbackIsLimit : IsLimit (pullbackCone f g) :=
  PullbackCone.isLimitAux (pullbackCone f g)
    (fun s => pullbackLift f g s.fst s.snd s.condition)
    (fun s => pullbackLift_fst f g s.fst s.snd s.condition)
    (fun s => pullbackLift_snd f g s.fst s.snd s.condition)
    (fun s m hm => by
      apply pullback_hom_ext f g
      · exact hm WalkingCospan.left
      · exact hm WalkingCospan.right)

noncomputable instance hasPullback : HasPullback f g where
  exists_limit := ⟨⟨pullbackCone f g, pullbackIsLimit f g⟩⟩

noncomputable def pullbackIsoPullbackObj : pullback f g ≅ pullbackObj f g :=
  limit.isoLimitCone ⟨pullbackCone f g, pullbackIsLimit f g⟩

lemma pullbackIsoPullbackObj_hom_fst :
    (pullbackIsoPullbackObj f g).hom ≫ pullbackFst f g = pullback.fst f g := by
  simpa [pullbackIsoPullbackObj, pullbackCone] using
    (limit.isoLimitCone_hom_π (F := cospan f g)
      ⟨pullbackCone f g, pullbackIsLimit f g⟩ WalkingCospan.left)

lemma pullbackIsoPullbackObj_hom_snd :
    (pullbackIsoPullbackObj f g).hom ≫ pullbackSnd f g = pullback.snd f g := by
  simpa [pullbackIsoPullbackObj, pullbackCone] using
    (limit.isoLimitCone_hom_π (F := cospan f g)
      ⟨pullbackCone f g, pullbackIsLimit f g⟩ WalkingCospan.right)

lemma pullbackIsoPullbackObj_inv_fst :
    (pullbackIsoPullbackObj f g).inv ≫ pullback.fst f g = pullbackFst f g := by
  simpa [pullbackIsoPullbackObj, pullbackCone] using
    (limit.isoLimitCone_inv_π (F := cospan f g)
      ⟨pullbackCone f g, pullbackIsLimit f g⟩ WalkingCospan.left)

lemma pullbackIsoPullbackObj_inv_snd :
    (pullbackIsoPullbackObj f g).inv ≫ pullback.snd f g = pullbackSnd f g := by
  simpa [pullbackIsoPullbackObj, pullbackCone] using
    (limit.isoLimitCone_inv_π (F := cospan f g)
      ⟨pullbackCone f g, pullbackIsLimit f g⟩ WalkingCospan.right)

lemma pullbackFst_surjective_of_snd_surjective (hg : Function.Surjective (g : B → C)) :
    Function.Surjective (pullbackFst f g : pullbackObj f g → A) := by
  intro x
  rcases hg (f x) with ⟨y, hy⟩
  refine ⟨⟨(x, y), hy.symm⟩, rfl⟩

lemma pullbackFst_openMap_of_snd_openMap (hg : IsOpenMap (g : B → C)) :
    IsOpenMap (pullbackFst f g : pullbackObj f g → A) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨p, hpU, hpa⟩
  rw [← hpa]
  have hUnhds : U ∈ 𝓝 p := hU.mem_nhds hpU
  rcases (mem_nhds_subtype (pullbackSubgroup f g : Set (A × B)) p U).1 hUnhds with
    ⟨W, hWnhds, hWsubU⟩
  rcases mem_nhds_prod_iff'.1 hWnhds with
    ⟨V, N, hVopen, hpV, hNopen, hpN, hVNsubW⟩
  let T : Set A := V ∩ f ⁻¹' (g '' N)
  have hTopen : IsOpen T := by
    exact hVopen.inter ((hg N hNopen).preimage f.hom.continuous)
  have hpT : (pullbackFst f g) p ∈ T := by
    refine ⟨hpV, ?_⟩
    exact ⟨p.1.2, hpN, p.2.symm⟩
  have hTsub : T ⊆ (pullbackFst f g : pullbackObj f g → A) '' U := by
    intro x hx
    rcases hx.2 with ⟨y, hyN, hgy⟩
    let q : pullbackObj f g := ⟨(x, y), hgy.symm⟩
    refine ⟨q, ?_, rfl⟩
    apply hWsubU
    exact hVNsubW ⟨hx.1, hyN⟩
  exact Filter.mem_of_superset (hTopen.mem_nhds hpT) hTsub

lemma pullbackSnd_surjective_of_fst_surjective (hf : Function.Surjective (f : A → C)) :
    Function.Surjective (pullbackSnd f g : pullbackObj f g → B) := by
  intro y
  rcases hf (g y) with ⟨x, hx⟩
  refine ⟨⟨(x, y), hx⟩, rfl⟩

noncomputable def pullbackKernelMap {X : MetrizableLCA.{u}} (i : X ⟶ B)
    (zero : i ≫ g = 0) : X ⟶ pullbackObj f g where
  hom' :=
    { toFun := fun x => ⟨((0 : A), i x), by
        change f 0 = g (i x)
        rw [map_zero]
        exact (congrArg (fun h : X ⟶ C => h x) zero).symm⟩
      map_zero' := by
        apply Subtype.ext
        calc
          (((0 : A), i 0) : A × B) = 0 := by ext <;> simp
          _ = ↑(0 : pullbackSubgroup f g) := (AddSubgroup.coe_zero (pullbackSubgroup f g)).symm
      map_add' := by
        intro x y
        apply Subtype.ext
        let ux : pullbackSubgroup f g := ⟨((0 : A), i x), by
          change f 0 = g (i x)
          rw [map_zero]
          exact (congrArg (fun h : X ⟶ C => h x) zero).symm⟩
        let uy : pullbackSubgroup f g := ⟨((0 : A), i y), by
          change f 0 = g (i y)
          rw [map_zero]
          exact (congrArg (fun h : X ⟶ C => h y) zero).symm⟩
        calc
          (((0 : A), i (x + y)) : A × B) = (↑ux + ↑uy : A × B) := by
            ext <;> simp [ux, uy, map_add]
          _ = ↑(ux + uy) := (AddSubgroup.coe_add (pullbackSubgroup f g) ux uy).symm
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_const.prodMk i.hom.continuous }

lemma pullbackKernelMap_fst {X : MetrizableLCA.{u}} (i : X ⟶ B)
    (zero : i ≫ g = 0) :
    pullbackKernelMap f g i zero ≫ pullbackFst f g = 0 := by
  ext x
  rfl

lemma pullbackKernelMap_snd {X : MetrizableLCA.{u}} (i : X ⟶ B)
    (zero : i ≫ g = 0) :
    pullbackKernelMap f g i zero ≫ pullbackSnd f g = i := by
  ext x
  rfl

lemma pullbackKernelMap_algebraic_exact {X : MetrizableLCA.{u}} (i : X ⟶ B)
    (zero : i ≫ g = 0)
    (hker : ∀ b : B, g b = 0 → ∃ x : X, i x = b) :
    ∀ p : pullbackObj f g, (pullbackFst f g) p = 0 →
      ∃ x : X, (pullbackKernelMap f g i zero) x = p := by
  intro p hp
  have hp' : p.1.1 = 0 := hp
  have hg : g p.1.2 = 0 := by
    have hrel : f p.1.1 = g p.1.2 := p.2
    rw [← hrel, hp']
    simp
  rcases hker p.1.2 hg with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  ext
  · exact hp'.symm
  · exact hx

lemma pullbackKernelMap_closedEmbedding {X : MetrizableLCA.{u}} (i : X ⟶ B)
    (zero : i ≫ g = 0) (hi : IsClosedEmbedding (i : X → B)) :
    IsClosedEmbedding (pullbackKernelMap f g i zero : X → pullbackObj f g) := by
  have hprod : IsClosedEmbedding (fun x : X => ((0 : A), i x)) := by
    exact (isClosedEmbedding_zero_prod A B).comp hi
  have hval : IsEmbedding (fun p : pullbackObj f g => (p.1 : A × B)) := by
    exact Topology.IsEmbedding.subtypeVal
  have hcomp : IsClosedEmbedding ((fun p : pullbackObj f g => (p.1 : A × B)) ∘
      (pullbackKernelMap f g i zero : X → pullbackObj f g)) := by
    simpa [Function.comp_def, pullbackKernelMap] using hprod
  exact Topology.IsClosedEmbedding.of_comp hval hcomp

lemma strictShortExact_pullback {S : ShortComplex MetrizableLCA.{u}} (hS : strictShortExact S)
    {Y : MetrizableLCA.{u}} (a : Y ⟶ S.X₃) :
    strictShortExact (ShortComplex.mk (pullbackKernelMap a S.g S.f S.zero)
      (pullbackFst a S.g) (pullbackKernelMap_fst a S.g S.f S.zero)) where
  closed_inclusion := pullbackKernelMap_closedEmbedding a S.g S.f S.zero hS.closed_inclusion
  open_map := pullbackFst_openMap_of_snd_openMap a S.g hS.open_map
  surjective := pullbackFst_surjective_of_snd_surjective a S.g hS.surjective
  algebraic_exact := pullbackKernelMap_algebraic_exact a S.g S.f S.zero hS.algebraic_exact

lemma strictShortExact_categorical_pullback {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) {Y : MetrizableLCA.{u}} (a : Y ⟶ S.X₃) :
    ∃ (X : MetrizableLCA.{u}) (i : X ⟶ pullback a S.g)
      (zero : i ≫ pullback.fst a S.g = 0),
      strictShortExact (ShortComplex.mk i (pullback.fst a S.g) zero) := by
  let e := pullbackIsoPullbackObj a S.g
  let k₀ := pullbackKernelMap a S.g S.f S.zero
  let k : S.X₁ ⟶ pullback a S.g := k₀ ≫ e.inv
  have zero : k ≫ pullback.fst a S.g = 0 := by
    dsimp [k]
    rw [Category.assoc, pullbackIsoPullbackObj_inv_fst]
    exact pullbackKernelMap_fst a S.g S.f S.zero
  refine ⟨S.X₁, k, zero, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · let e₂ : pullbackObj a S.g ≃ₜ+ (pullback a S.g : MetrizableLCA.{u}) :=
      isoToContinuousAddEquiv e.symm
    have hk₀ : IsClosedEmbedding (k₀ : S.X₁ → pullbackObj a S.g) :=
      pullbackKernelMap_closedEmbedding a S.g S.f S.zero hS.closed_inclusion
    have hcomp : IsClosedEmbedding (fun x : S.X₁ => e₂ (k₀ x)) :=
      e₂.toHomeomorph.isClosedEmbedding.comp hk₀
    have hfun : (fun x : S.X₁ => e₂ (k₀ x)) =
        (k : S.X₁ → ((pullback a S.g : MetrizableLCA.{u}) : Type u)) := by
      funext x
      rfl
    rwa [hfun] at hcomp
  · let e₂ : (pullback a S.g : MetrizableLCA.{u}) ≃ₜ+ pullbackObj a S.g :=
      isoToContinuousAddEquiv e
    have hopen₀ : IsOpenMap (pullbackFst a S.g : pullbackObj a S.g → Y) :=
      pullbackFst_openMap_of_snd_openMap a S.g hS.open_map
    have hcomp : IsOpenMap (fun z : ((pullback a S.g : MetrizableLCA.{u}) : Type u) =>
        pullbackFst a S.g (e₂ z)) :=
      hopen₀.comp e₂.toHomeomorph.isOpenMap
    have hfun : (fun z : ((pullback a S.g : MetrizableLCA.{u}) : Type u) =>
        pullbackFst a S.g (e₂ z)) =
        (pullback.fst a S.g : ((pullback a S.g : MetrizableLCA.{u}) : Type u) → Y) := by
      funext z
      exact congrArg (fun h : pullback a S.g ⟶ Y => h z)
        (pullbackIsoPullbackObj_hom_fst a S.g)
    rwa [hfun] at hcomp
  · intro y
    rcases pullbackFst_surjective_of_snd_surjective a S.g hS.surjective y with ⟨p, hp⟩
    refine ⟨e.inv p, ?_⟩
    change (pullback.fst a S.g) (e.inv p) = y
    have h : (pullback.fst a S.g) (e.inv p) = (pullbackFst a S.g) p := by
      exact congrArg (fun h : pullbackObj a S.g ⟶ Y => h p)
        (pullbackIsoPullbackObj_inv_fst a S.g)
    rw [h, hp]
  · intro z hz
    change (pullback.fst a S.g) z = 0 at hz
    have hp : pullbackFst a S.g (e.hom z) = 0 := by
      have h : pullbackFst a S.g (e.hom z) = (pullback.fst a S.g) z := by
        exact congrArg (fun h : pullback a S.g ⟶ Y => h z)
          (pullbackIsoPullbackObj_hom_fst a S.g)
      rw [h, hz]
    rcases pullbackKernelMap_algebraic_exact a S.g S.f S.zero hS.algebraic_exact
        (e.hom z) hp with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    dsimp [k]
    calc
      (k₀ ≫ e.inv) x = e.inv (k₀ x) := rfl
      _ = e.inv (e.hom z) := by rw [hx]
      _ = z := by
        exact congrArg (fun h : pullback a S.g ⟶ pullback a S.g => h z) e.hom_inv_id

end MetrizableLCA

end LeanLCAExactChallenge
