import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Constructions

/-!
Strict short exact sequences in the local `MetrizableLCA` category.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace MetrizableLCA

/--
The strict short exact sequences specified in the challenge: closed inclusion on
the left, open surjection on the right, and exactness after forgetting topology.
-/
structure StrictShortExact (S : ShortComplex MetrizableLCA.{u}) : Prop where
  closed_inclusion : IsClosedEmbedding (S.f : S.X₁ → S.X₂)
  open_map : IsOpenMap (S.g : S.X₂ → S.X₃)
  surjective : Function.Surjective (S.g : S.X₂ → S.X₃)
  algebraic_exact : ∀ x₂ : S.X₂, S.g x₂ = 0 → ∃ x₁ : S.X₁, S.f x₁ = x₂

/-- Predicate for strict short exact complexes. -/
def strictShortExact (S : ShortComplex MetrizableLCA.{u}) : Prop :=
  StrictShortExact S

lemma closed_inclusion_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) : IsClosedEmbedding (S.f : S.X₁ → S.X₂) :=
  hS.closed_inclusion

lemma open_surjection_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) :
    IsOpenMap (S.g : S.X₂ → S.X₃) ∧ Function.Surjective (S.g : S.X₂ → S.X₃) :=
  ⟨hS.open_map, hS.surjective⟩

lemma algebraic_kernel_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) :
    Function.Injective (S.f : S.X₁ → S.X₂) ∧
      ∀ x₂ : S.X₂, S.g x₂ = 0 ↔ ∃ x₁ : S.X₁, S.f x₁ = x₂ := by
  refine ⟨hS.closed_inclusion.injective, ?_⟩
  intro x₂
  constructor
  · exact hS.algebraic_exact x₂
  · rintro ⟨x₁, rfl⟩
    change (S.f ≫ S.g : S.X₁ ⟶ S.X₃) x₁ = (0 : S.X₁ ⟶ S.X₃) x₁
    exact congrArg (fun h : S.X₁ ⟶ S.X₃ ↦ h x₁) S.zero

lemma algebraic_cokernel_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) :
    Function.Surjective (S.g : S.X₂ → S.X₃) :=
  hS.surjective

/--
After forgetting the topology, a strict short exact sequence is exact as a short
complex of abelian groups.
-/
lemma forgetToAddCommGrpCat_exact_of_strict {S : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) :
    (S.map forgetToAddCommGrpCat).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x₂ hx₂
  rcases hS.algebraic_exact x₂ hx₂ with ⟨x₁, hx₁⟩
  exact ⟨x₁, hx₁⟩

lemma strictShortExact_of_exact_of_topology {S : ShortComplex MetrizableLCA.{u}}
    (hhom : S.HasHomology)
    (hpres : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (hS : S.Exact) (hclosed : IsClosedEmbedding (S.f : S.X₁ → S.X₂))
    (hopen : IsOpenMap (S.g : S.X₂ → S.X₃))
    (hsurj : Function.Surjective (S.g : S.X₂ → S.X₃)) :
    strictShortExact S where
  closed_inclusion := hclosed
  open_map := hopen
  surjective := hsurj
  algebraic_exact := by
    letI := hhom
    letI := hpres
    intro x₂ hx₂
    exact (ShortComplex.exact_iff_of_hasForget S).mp hS x₂ hx₂

lemma rangeSubgroup_coe {A B : MetrizableLCA.{u}} (f : A ⟶ B) :
    ((AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup A) : AddSubgroup B) :
        Set B) = Set.range (f : A → B) := by
  ext b
  constructor
  · rintro ⟨a, _ha, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, trivial, rfl⟩

lemma denseRange_of_cokernelSubgroup_eq_top {A B : MetrizableLCA.{u}} (f : A ⟶ B)
    (hcok : cokernelSubgroup f = ⊤) :
    DenseRange (f : A → B) := by
  rw [denseRange_iff_closure_range]
  have hset := congrArg (fun S : AddSubgroup B => (S : Set B)) hcok
  simpa [cokernelSubgroup, AddSubgroup.topologicalClosure_coe, rangeSubgroup_coe f] using hset

lemma surjective_of_denseRange_of_isOpenMap {A B : MetrizableLCA.{u}} (f : A ⟶ B)
    (hdense : DenseRange (f : A → B)) (hopen : IsOpenMap (f : A → B)) :
    Function.Surjective (f : A → B) := by
  let R : AddSubgroup B := AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup A)
  have hRopen : IsOpen (R : Set B) := by
    have h_image : IsOpen ((f : A → B) '' Set.univ) := hopen Set.univ isOpen_univ
    simpa [R, Set.image_univ, rangeSubgroup_coe f] using h_image
  have hRclosed : IsClosed (R : Set B) := AddSubgroup.isClosed_of_isOpen R hRopen
  have hRclosure : closure (R : Set B) = Set.univ := by
    simpa [R, rangeSubgroup_coe f] using hdense.closure_range
  have hRuniv : (R : Set B) = Set.univ := by
    rw [← hRclosed.closure_eq, hRclosure]
  intro b
  have hb : b ∈ (R : Set B) := by
    rw [hRuniv]
    exact Set.mem_univ b
  rcases hb with ⟨a, _ha, ha⟩
  exact ⟨a, ha⟩

lemma surjective_of_cokernelSubgroup_eq_top_of_isOpenMap {A B : MetrizableLCA.{u}}
    (f : A ⟶ B) (hcok : cokernelSubgroup f = ⊤) (hopen : IsOpenMap (f : A → B)) :
    Function.Surjective (f : A → B) :=
  surjective_of_denseRange_of_isOpenMap f
    (denseRange_of_cokernelSubgroup_eq_top f hcok) hopen

lemma surjective_iff_cokernelSubgroup_eq_top_of_isOpenMap {A B : MetrizableLCA.{u}}
    (f : A ⟶ B) (hopen : IsOpenMap (f : A → B)) :
    Function.Surjective (f : A → B) ↔ cokernelSubgroup f = ⊤ :=
  ⟨cokernelSubgroup_eq_top_of_surjective f,
    fun hcok => surjective_of_cokernelSubgroup_eq_top_of_isOpenMap f hcok hopen⟩

structure CokernelTopStrictInput (T : ShortComplex MetrizableLCA.{u}) : Prop where
  kernel_equality : ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂
  closed_embedding_f : IsClosedEmbedding (T.f : T.X₁ → T.X₂)
  open_map_g : IsOpenMap (T.g : T.X₂ → T.X₃)
  cokernel_top_g : cokernelSubgroup T.g = ⊤

lemma strictShortExact_of_cokernelTopStrictInput
    {T : ShortComplex MetrizableLCA.{u}} (hT : CokernelTopStrictInput T) :
    strictShortExact T where
  closed_inclusion := hT.closed_embedding_f
  open_map := hT.open_map_g
  surjective :=
    surjective_of_cokernelSubgroup_eq_top_of_isOpenMap T.g hT.cokernel_top_g hT.open_map_g
  algebraic_exact := by
    intro x₂ hx₂
    exact (hT.kernel_equality x₂).mp hx₂

lemma strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top
    {T : ShortComplex MetrizableLCA.{u}}
    (hker : ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂)
    (hclosed : IsClosedEmbedding (T.f : T.X₁ → T.X₂))
    (hopen : IsOpenMap (T.g : T.X₂ → T.X₃))
    (hcok : cokernelSubgroup T.g = ⊤) :
    strictShortExact T :=
  strictShortExact_of_cokernelTopStrictInput
    { kernel_equality := hker
      closed_embedding_f := hclosed
      open_map_g := hopen
      cokernel_top_g := hcok }

lemma strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero
    {T : ShortComplex MetrizableLCA.{u}}
    (hker : ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂)
    (hclosed : IsClosedEmbedding (T.f : T.X₁ → T.X₂))
    (hopen : IsOpenMap (T.g : T.X₂ → T.X₃))
    (hπ : cokernelπ T.g = 0) :
    strictShortExact T :=
  strictShortExact_of_kernel_open_closed_cokernelSubgroup_eq_top hker hclosed hopen
    (cokernelSubgroup_eq_top_of_cokernelπ_eq_zero T.g hπ)

lemma strictShortExact_of_kernel_open_closed_epi
    {T : ShortComplex MetrizableLCA.{u}} [Epi T.g]
    (hker : ∀ x₂ : T.X₂, T.g x₂ = 0 ↔ ∃ x₁ : T.X₁, T.f x₁ = x₂)
    (hclosed : IsClosedEmbedding (T.f : T.X₁ → T.X₂))
    (hopen : IsOpenMap (T.g : T.X₂ → T.X₃)) :
    strictShortExact T :=
  strictShortExact_of_kernel_open_closed_cokernelπ_eq_zero hker hclosed hopen
    (cokernelπ_eq_zero_of_epi T.g)

/-- Coordinatewise product of two short complexes. -/
def strictShortExactBiprodComplex (S T : ShortComplex MetrizableLCA.{u}) :
    ShortComplex MetrizableLCA.{u} where
  X₁ := biprodObj S.X₁ T.X₁
  X₂ := biprodObj S.X₂ T.X₂
  X₃ := biprodObj S.X₃ T.X₃
  f := biprodMap S.f T.f
  g := biprodMap S.g T.g
  zero := by
    ext p
    · exact congrArg (fun h : S.X₁ ⟶ S.X₃ => h p.1) S.zero
    · exact congrArg (fun h : T.X₁ ⟶ T.X₃ => h p.2) T.zero

lemma strictShortExact_biprod {S T : ShortComplex MetrizableLCA.{u}}
    (hS : strictShortExact S) (hT : strictShortExact T) :
    strictShortExact (strictShortExactBiprodComplex S T) where
  closed_inclusion := by
    change IsClosedEmbedding (Prod.map (S.f : S.X₁ → S.X₂) (T.f : T.X₁ → T.X₂))
    exact hS.closed_inclusion.prodMap hT.closed_inclusion
  open_map := by
    change IsOpenMap (Prod.map (S.g : S.X₂ → S.X₃) (T.g : T.X₂ → T.X₃))
    exact hS.open_map.prodMap hT.open_map
  surjective := by
    intro p
    rcases hS.surjective p.1 with ⟨x, hx⟩
    rcases hT.surjective p.2 with ⟨y, hy⟩
    exact ⟨(x, y), by
      change (S.g x, T.g y) = p
      exact Prod.ext hx hy⟩
  algebraic_exact := by
    intro p hp
    have hS_zero : S.g p.1 = 0 := by
      simpa [strictShortExactBiprodComplex] using congrArg Prod.fst hp
    have hT_zero : T.g p.2 = 0 := by
      simpa [strictShortExactBiprodComplex] using congrArg Prod.snd hp
    rcases hS.algebraic_exact p.1 hS_zero with ⟨x, hx⟩
    rcases hT.algebraic_exact p.2 hT_zero with ⟨y, hy⟩
    exact ⟨(x, y), by
      change (S.f x, T.f y) = p
      exact Prod.ext hx hy⟩

/--
A splitting of a short complex identifies the middle LCA group with the product
of the left and right terms.
-/
noncomputable def splittingContinuousAddEquiv {S : ShortComplex MetrizableLCA.{u}}
    (s : S.Splitting) : S.X₂ ≃ₜ+ (S.X₁ × S.X₃) where
  toFun x := (s.r x, S.g x)
  invFun p := S.f p.1 + s.s p.2
  left_inv x := by
    have h := congrArg (fun h : S.X₂ ⟶ S.X₂ => h x) s.id
    simpa using h
  right_inv p := by
    ext
    · have h1 : s.r (S.f p.1) = p.1 := by
        exact congrArg (fun h : S.X₁ ⟶ S.X₁ => h p.1) s.f_r
      have h2 : s.r (s.s p.2) = 0 := by
        exact congrArg (fun h : S.X₃ ⟶ S.X₁ => h p.2) (ShortComplex.Splitting.s_r s)
      simp [map_add, h1, h2]
    · have h1 : S.g (S.f p.1) = 0 := by
        exact congrArg (fun h : S.X₁ ⟶ S.X₃ => h p.1) S.zero
      have h2 : S.g (s.s p.2) = p.2 := by
        exact congrArg (fun h : S.X₃ ⟶ S.X₃ => h p.2) s.s_g
      simp [map_add, h1, h2]
  map_add' x y := by
    ext <;> simp [map_add]
  continuous_toFun := s.r.hom.continuous.prodMk S.g.hom.continuous
  continuous_invFun :=
    (S.f.hom.continuous.comp continuous_fst).add (s.s.hom.continuous.comp continuous_snd)

lemma isClosedEmbedding_prod_zero (A B : MetrizableLCA.{u}) :
    IsClosedEmbedding (fun x : A => (x, (0 : B))) := by
  refine ⟨isEmbedding_prodMkLeft (0 : B), ?_⟩
  have hrange : Set.range (fun x : A => (x, (0 : B))) = {p : A × B | p.2 = 0} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro hp
      exact ⟨p.1, by ext <;> simp [hp.symm]⟩
  rw [hrange]
  exact isClosed_singleton.preimage continuous_snd

lemma split_closedEmbedding_f {S : ShortComplex MetrizableLCA.{u}}
    (s : S.Splitting) : IsClosedEmbedding (S.f : S.X₁ → S.X₂) := by
  let e := splittingContinuousAddEquiv s
  have hfun : (fun x : S.X₁ => e (S.f x)) = (fun x : S.X₁ => (x, (0 : S.X₃))) := by
    funext x
    ext
    · exact congrArg (fun h : S.X₁ ⟶ S.X₁ => h x) s.f_r
    · exact congrArg (fun h : S.X₁ ⟶ S.X₃ => h x) S.zero
  have hcomp : IsClosedEmbedding (fun x : S.X₁ => e (S.f x)) := by
    rw [hfun]
    exact isClosedEmbedding_prod_zero S.X₁ S.X₃
  exact e.toHomeomorph.isClosedEmbedding.of_comp_iff.mp hcomp

lemma split_open_map_g {S : ShortComplex MetrizableLCA.{u}}
    (s : S.Splitting) : IsOpenMap (S.g : S.X₂ → S.X₃) := by
  let e := splittingContinuousAddEquiv s
  have h : IsOpenMap (fun x : S.X₂ => (e x).2) :=
    isOpenMap_snd.comp e.toHomeomorph.isOpenMap
  simpa [e, splittingContinuousAddEquiv] using h

lemma split_surjective_g {S : ShortComplex MetrizableLCA.{u}}
    (s : S.Splitting) : Function.Surjective (S.g : S.X₂ → S.X₃) := by
  intro y
  refine ⟨s.s y, ?_⟩
  exact congrArg (fun h : S.X₃ ⟶ S.X₃ => h y) s.s_g

lemma split_algebraic_exact {S : ShortComplex MetrizableLCA.{u}}
    (s : S.Splitting) : ∀ x₂ : S.X₂, S.g x₂ = 0 → ∃ x₁ : S.X₁, S.f x₁ = x₂ := by
  intro x₂ hx₂
  refine ⟨s.r x₂, ?_⟩
  have h := congrArg (fun h : S.X₂ ⟶ S.X₂ => h x₂) s.id
  calc
    S.f (s.r x₂) = S.f (s.r x₂) + s.s (S.g x₂) := by simp [hx₂]
    _ = x₂ := h

lemma split_strictShortExact {S : ShortComplex MetrizableLCA.{u}}
    (s : S.Splitting) : strictShortExact S where
  closed_inclusion := split_closedEmbedding_f s
  open_map := split_open_map_g s
  surjective := split_surjective_g s
  algebraic_exact := split_algebraic_exact s

lemma iso_closedEmbedding_f {S T : ShortComplex MetrizableLCA.{u}} (e : S ≅ T)
    (hS : strictShortExact S) : IsClosedEmbedding (T.f : T.X₁ → T.X₂) := by
  let e₁ : T.X₁ ≃ₜ+ S.X₁ := isoToContinuousAddEquiv (asIso e.inv.τ₁)
  let e₂ : S.X₂ ≃ₜ+ T.X₂ := isoToContinuousAddEquiv (asIso e.hom.τ₂)
  have hcomp : IsClosedEmbedding (fun x : T.X₁ => e₂ (S.f (e₁ x))) := by
    exact (e₂.toHomeomorph.isClosedEmbedding.comp hS.closed_inclusion).comp
      e₁.toHomeomorph.isClosedEmbedding
  have hmap : e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂ = T.f := by
    rw [e.inv.comm₁₂_assoc]
    have h₂ : e.inv.τ₂ ≫ e.hom.τ₂ = 𝟙 T.X₂ := by
      exact congrArg ShortComplex.Hom.τ₂ e.inv_hom_id
    rw [h₂, Category.comp_id]
  have hfun : (fun x : T.X₁ => e₂ (S.f (e₁ x))) = (T.f : T.X₁ → T.X₂) := by
    funext x
    exact congrArg (fun h : T.X₁ ⟶ T.X₂ => h x) hmap
  rwa [hfun] at hcomp

lemma iso_open_map_g {S T : ShortComplex MetrizableLCA.{u}} (e : S ≅ T)
    (hS : strictShortExact S) : IsOpenMap (T.g : T.X₂ → T.X₃) := by
  let e₂ : T.X₂ ≃ₜ+ S.X₂ := isoToContinuousAddEquiv (asIso e.inv.τ₂)
  let e₃ : S.X₃ ≃ₜ+ T.X₃ := isoToContinuousAddEquiv (asIso e.hom.τ₃)
  have hcomp : IsOpenMap (fun x : T.X₂ => e₃ (S.g (e₂ x))) :=
    e₃.toHomeomorph.isOpenMap.comp (hS.open_map.comp e₂.toHomeomorph.isOpenMap)
  have hmap : e.inv.τ₂ ≫ S.g ≫ e.hom.τ₃ = T.g := by
    rw [e.inv.comm₂₃_assoc]
    have h₃ : e.inv.τ₃ ≫ e.hom.τ₃ = 𝟙 T.X₃ := by
      exact congrArg ShortComplex.Hom.τ₃ e.inv_hom_id
    rw [h₃, Category.comp_id]
  have hfun : (fun x : T.X₂ => e₃ (S.g (e₂ x))) = (T.g : T.X₂ → T.X₃) := by
    funext x
    exact congrArg (fun h : T.X₂ ⟶ T.X₃ => h x) hmap
  rwa [hfun] at hcomp

lemma iso_surjective_g {S T : ShortComplex MetrizableLCA.{u}} (e : S ≅ T)
    (hS : strictShortExact S) : Function.Surjective (T.g : T.X₂ → T.X₃) := by
  intro y
  rcases hS.surjective (e.inv.τ₃ y) with ⟨x, hx⟩
  refine ⟨e.hom.τ₂ x, ?_⟩
  have hcomm : T.g (e.hom.τ₂ x) = e.hom.τ₃ (S.g x) := by
    exact congrArg (fun h : S.X₂ ⟶ T.X₃ => h x) e.hom.comm₂₃
  have h₃ : e.inv.τ₃ ≫ e.hom.τ₃ = 𝟙 T.X₃ := by
    exact congrArg ShortComplex.Hom.τ₃ e.inv_hom_id
  have hright : e.hom.τ₃ (e.inv.τ₃ y) = y := by
    exact congrArg (fun h : T.X₃ ⟶ T.X₃ => h y) h₃
  rw [hx] at hcomm
  exact hcomm.trans hright

lemma iso_algebraic_exact {S T : ShortComplex MetrizableLCA.{u}} (e : S ≅ T)
    (hS : strictShortExact S) :
    ∀ x₂ : T.X₂, T.g x₂ = 0 → ∃ x₁ : T.X₁, T.f x₁ = x₂ := by
  intro y₂ hy₂
  have hker : S.g (e.inv.τ₂ y₂) = 0 := by
    have hcomm : S.g (e.inv.τ₂ y₂) = e.inv.τ₃ (T.g y₂) := by
      exact congrArg (fun h : T.X₂ ⟶ S.X₃ => h y₂) e.inv.comm₂₃
    rw [hcomm, hy₂]
    simp
  rcases hS.algebraic_exact (e.inv.τ₂ y₂) hker with ⟨x₁, hx₁⟩
  refine ⟨e.hom.τ₁ x₁, ?_⟩
  have hcomm : T.f (e.hom.τ₁ x₁) = e.hom.τ₂ (S.f x₁) := by
    exact congrArg (fun h : S.X₁ ⟶ T.X₂ => h x₁) e.hom.comm₁₂
  have h₂ : e.inv.τ₂ ≫ e.hom.τ₂ = 𝟙 T.X₂ := by
    exact congrArg ShortComplex.Hom.τ₂ e.inv_hom_id
  have hright : e.hom.τ₂ (e.inv.τ₂ y₂) = y₂ := by
    exact congrArg (fun h : T.X₂ ⟶ T.X₂ => h y₂) h₂
  rw [hcomm, hx₁]
  exact hright

lemma strictShortExact_iso {S T : ShortComplex MetrizableLCA.{u}} (e : S ≅ T) :
    strictShortExact S → strictShortExact T := by
  intro hS
  exact
    { closed_inclusion := iso_closedEmbedding_f e hS
      open_map := iso_open_map_g e hS
      surjective := iso_surjective_g e hS
      algebraic_exact := iso_algebraic_exact e hS }

end MetrizableLCA

end LeanLCAExactChallenge
