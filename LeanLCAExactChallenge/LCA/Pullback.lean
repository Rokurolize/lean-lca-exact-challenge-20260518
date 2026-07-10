import LeanLCAExactChallenge.LCA.StrictExact
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Constructions

/-!
Explicit pullbacks in the local `MetrizableLCA` category.

The pullback of continuous additive homomorphisms is realised as the closed
additive subgroup of the product cut out by the equality relation.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

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

noncomputable instance instHasPullbacks : HasPullbacks MetrizableLCA.{u} :=
  hasPullbacks_of_hasLimit_cospan MetrizableLCA.{u}

noncomputable instance instHasFiniteLimits : HasFiniteLimits MetrizableLCA.{u} :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-! ### Explicit equalizers -/

section ExplicitEqualizer

variable {E T : MetrizableLCA.{u}} (r s : E ⟶ T)

/-- The closed additive subgroup cut out by an equalizer relation. -/
def equalizerSubgroup : AddSubgroup E where
  carrier := {x | r x = s x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    calc
      r (x + y) = r x + r y := (r.hom : E →+ T).map_add x y
      _ = s x + s y := by rw [hx, hy]
      _ = s (x + y) := ((s.hom : E →+ T).map_add x y).symm
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    calc
      r (-x) = - r x := (r.hom : E →+ T).map_neg x
      _ = - s x := by rw [hx]
      _ = s (-x) := ((s.hom : E →+ T).map_neg x).symm

lemma equalizerSubgroup_isClosed : IsClosed (equalizerSubgroup r s : Set E) := by
  dsimp [equalizerSubgroup]
  exact isClosed_eq r.hom.continuous s.hom.continuous

/-- The explicit equalizer object in `MetrizableLCA`. -/
def equalizerObj : MetrizableLCA.{u} where
  carrier := equalizerSubgroup r s
  locallyCompactSpace := by
    change LocallyCompactSpace {x : E // x ∈ (equalizerSubgroup r s : Set E)}
    exact (equalizerSubgroup_isClosed r s).locallyCompactSpace
  metrizableSpace := by
    change TopologicalSpace.MetrizableSpace {x : E // x ∈ (equalizerSubgroup r s : Set E)}
    infer_instance

/-- Inclusion of the explicit equalizer object. -/
noncomputable def equalizerι : equalizerObj r s ⟶ E where
  hom' :=
    { toFun := fun x => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_subtype_val }

lemma equalizerι_condition : equalizerι r s ≫ r = equalizerι r s ≫ s := by
  ext x
  exact x.2

/-- The explicit equalizer fork. -/
noncomputable def equalizerFork : Fork r s :=
  Fork.ofι (equalizerι r s) (equalizerι_condition r s)

/-- The universal lift into the explicit equalizer. -/
noncomputable def equalizerLift {X : MetrizableLCA.{u}} (a : X ⟶ E)
    (w : a ≫ r = a ≫ s) : X ⟶ equalizerObj r s where
  hom' :=
    { toFun := fun x => ⟨a x, congrArg (fun h : X ⟶ T => h x) w⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero a.hom
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add a.hom x y
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact a.hom.continuous }

lemma equalizerLift_ι {X : MetrizableLCA.{u}} (a : X ⟶ E)
    (w : a ≫ r = a ≫ s) : equalizerLift r s a w ≫ equalizerι r s = a := by
  ext x
  rfl

lemma equalizer_hom_ext {X : MetrizableLCA.{u}} {k l : X ⟶ equalizerObj r s}
    (hι : k ≫ equalizerι r s = l ≫ equalizerι r s) : k = l := by
  apply MetrizableLCA.ext
  intro x
  apply Subtype.ext
  exact congrArg (fun h : X ⟶ E => h x) hι

/-- The explicit equalizer fork is limiting. -/
noncomputable def equalizerIsLimit : IsLimit (equalizerFork r s) :=
  Fork.IsLimit.mk (equalizerFork r s)
    (fun t => equalizerLift r s t.ι t.condition)
    (fun t => by
      simpa [equalizerFork] using equalizerLift_ι r s t.ι t.condition)
    (fun _t m hm => by
      apply equalizer_hom_ext r s
      change m ≫ equalizerι r s = _t.ι at hm
      exact hm.trans (equalizerLift_ι r s _t.ι _t.condition).symm)

lemma equalizerι_closedEmbedding_explicit :
    IsClosedEmbedding (equalizerι r s : equalizerObj r s → E) :=
  (equalizerSubgroup_isClosed r s).isClosedEmbedding_subtypeVal

/-- The chosen categorical equalizer is isomorphic to the explicit closed subgroup model. -/
noncomputable def equalizerIsoEqualizerObj [HasEqualizer r s] :
    equalizer r s ≅ equalizerObj r s :=
  (equalizerIsEqualizer r s).conePointUniqueUpToIso (equalizerIsLimit r s)

lemma equalizerIsoEqualizerObj_hom_ι [HasEqualizer r s] :
    (equalizerIsoEqualizerObj r s).hom ≫ equalizerι r s = equalizer.ι r s := by
  simpa [equalizerIsoEqualizerObj, equalizerFork] using
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (equalizerIsEqualizer r s) (equalizerIsLimit r s) WalkingParallelPair.zero)

/-- The chosen categorical equalizer inclusion is a closed embedding. -/
lemma equalizer_ι_closedEmbedding [HasEqualizer r s] :
    IsClosedEmbedding
      (equalizer.ι r s : ((equalizer r s : MetrizableLCA.{u}) : Type u) → E) := by
  let e : (equalizer r s : MetrizableLCA.{u}) ≃ₜ+ equalizerObj r s :=
    isoToContinuousAddEquiv (equalizerIsoEqualizerObj r s)
  have hcomp : IsClosedEmbedding
      (fun x : ((equalizer r s : MetrizableLCA.{u}) : Type u) => (equalizerι r s) (e x)) :=
    (equalizerι_closedEmbedding_explicit r s).comp e.toHomeomorph.isClosedEmbedding
  have hfun :
      (fun x : ((equalizer r s : MetrizableLCA.{u}) : Type u) => (equalizerι r s) (e x)) =
        (equalizer.ι r s : ((equalizer r s : MetrizableLCA.{u}) : Type u) → E) := by
    funext x
    exact congrArg (fun h : equalizer r s ⟶ E => h x)
      (equalizerIsoEqualizerObj_hom_ι r s)
  rwa [hfun] at hcomp

/-- Any limiting equalizer fork in `MetrizableLCA` has a closed-embedding inclusion. -/
lemma isLimit_fork_ι_closedEmbedding {fork : Fork r s} (hfork : IsLimit fork) :
    IsClosedEmbedding (fork.ι : fork.pt → E) := by
  let eIso := IsLimit.conePointUniqueUpToIso hfork (equalizerIsEqualizer r s)
  let e := isoToContinuousAddEquiv eIso
  have hcomp : IsClosedEmbedding
      (fun x : fork.pt => (equalizer.ι r s) (e x)) :=
    (equalizer_ι_closedEmbedding r s).comp e.toHomeomorph.isClosedEmbedding
  have hcomp_eq : eIso.hom ≫ equalizer.ι r s = fork.ι := by
    simpa using
      (IsLimit.conePointUniqueUpToIso_hom_comp
        hfork (equalizerIsEqualizer r s) WalkingParallelPair.zero)
  have hfun :
      (fun x : fork.pt => (equalizer.ι r s) (e x)) =
        (fork.ι : fork.pt → E) := by
    funext x
    change (eIso.hom ≫ equalizer.ι r s) x = fork.ι x
    exact congrArg (fun h : fork.pt ⟶ E => h x) hcomp_eq
  rwa [hfun] at hcomp

end ExplicitEqualizer

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

/-- Pull a morphism in the second coordinate through explicit pullbacks. -/
noncomputable def pullbackMapSnd {A B C D : MetrizableLCA.{u}} (f : A ⟶ C)
    (q : B ⟶ D) (h : D ⟶ C) : pullbackObj f (q ≫ h) ⟶ pullbackObj f h where
  hom' :=
    { toFun := fun p => ⟨(p.1.1, q p.1.2), by
        change f p.1.1 = h (q p.1.2)
        exact p.2⟩
      map_zero' := by
        apply Subtype.ext
        change (((0 : A), q (0 : B)) : A × D) = 0
        ext <;> simp
      map_add' := by
        intro x y
        apply Subtype.ext
        change (((x + y).1.1, q ((x + y).1.2)) : A × D) =
          (((x.1.1, q x.1.2)) + ((y.1.1, q y.1.2)) : A × D)
        have hxy := AddSubgroup.coe_add (pullbackSubgroup f (q ≫ h)) x y
        ext
        · change (x + y).1.1 = ((x.1 : A × B) + (y.1 : A × B)).1
          exact congrArg (fun p : A × B => p.1) hxy
        · have hsnd : (x + y).1.2 = ((x.1 : A × B) + (y.1 : A × B)).2 := by
            exact congrArg (fun p : A × B => p.2) hxy
          change q ((x + y).1.2) = q x.1.2 + q y.1.2
          rw [hsnd]
          exact map_add q.hom x.1.2 y.1.2
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.fst.prodMk
          (q.hom.continuous.comp continuous_subtype_val.snd) }

@[simp]
lemma pullbackMapSnd_fst {A B C D : MetrizableLCA.{u}} (f : A ⟶ C) (q : B ⟶ D)
    (h : D ⟶ C) : pullbackMapSnd f q h ≫ pullbackFst f h = pullbackFst f (q ≫ h) := by
  ext p
  rfl

@[simp]
lemma pullbackMapSnd_snd {A B C D : MetrizableLCA.{u}} (f : A ⟶ C) (q : B ⟶ D)
    (h : D ⟶ C) : pullbackMapSnd f q h ≫ pullbackSnd f h =
      pullbackSnd f (q ≫ h) ≫ q := by
  ext p
  rfl

lemma pullbackMapSnd_openMap_of_openMap {A B C D : MetrizableLCA.{u}} (f : A ⟶ C)
    (q : B ⟶ D) (h : D ⟶ C) (hq : IsOpenMap (q : B → D)) :
    IsOpenMap (pullbackMapSnd f q h : pullbackObj f (q ≫ h) → pullbackObj f h) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨p, hpU, hpz⟩
  rw [← hpz]
  have hUnhds : U ∈ 𝓝 p := hU.mem_nhds hpU
  rcases (mem_nhds_subtype (pullbackSubgroup f (q ≫ h) : Set (A × B)) p U).1 hUnhds with
    ⟨W, hWnhds, hWsubU⟩
  rcases mem_nhds_prod_iff'.1 hWnhds with
    ⟨V, N, hVopen, hpV, hNopen, hpN, hVNsubW⟩
  let T : Set (pullbackObj f h) := { z | z.1.1 ∈ V ∧ z.1.2 ∈ (q : B → D) '' N }
  have hTopen : IsOpen T := by
    dsimp [T]
    exact (hVopen.preimage continuous_subtype_val.fst).inter
      ((hq N hNopen).preimage continuous_subtype_val.snd)
  have hpT : pullbackMapSnd f q h p ∈ T := by
    exact ⟨hpV, ⟨p.1.2, hpN, rfl⟩⟩
  have hTsub : T ⊆ (pullbackMapSnd f q h : pullbackObj f (q ≫ h) → pullbackObj f h) '' U := by
    intro z hz
    rcases hz.2 with ⟨b, hbN, hbz⟩
    let r : pullbackObj f (q ≫ h) := ⟨(z.1.1, b), by
      change f z.1.1 = h (q b)
      rw [hbz]
      exact z.2⟩
    refine ⟨r, ?_, ?_⟩
    · apply hWsubU
      exact hVNsubW ⟨hz.1, hbN⟩
    · apply Subtype.ext
      ext
      · rfl
      · exact hbz
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
    change IsClosedEmbedding (fun x : X => ((0 : A), i x))
    exact hprod
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
