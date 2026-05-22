import LeanLCAExactChallenge.LCA.Quotient
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
Categorical cokernels in `MetrizableLCA`.

The cokernel of a continuous homomorphism `f : A ⟶ B` is the quotient of `B` by the
topological closure of the algebraic range of `f`.  This is the standard LCA construction:
the closedness condition needed by `MetrizableLCA.quotientObj` is supplied by
`AddSubgroup.topologicalClosure`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

variable {A B Z : MetrizableLCA.{u}} (f : A ⟶ B)

/-- The closed subgroup used to form the cokernel quotient of `f`. -/
def cokernelSubgroup : AddSubgroup B :=
  (AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup A)).topologicalClosure

/-- The algebraic range of `f` is contained in the closed cokernel subgroup. -/
lemma range_le_cokernelSubgroup :
    AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup A) ≤ cokernelSubgroup f :=
  AddSubgroup.le_topologicalClosure _

/-- Every value of `f` lies in its closed cokernel subgroup. -/
lemma map_mem_cokernelSubgroup (a : A) : f a ∈ cokernelSubgroup f :=
  range_le_cokernelSubgroup f ⟨a, trivial, rfl⟩

/-- The cokernel object of `f`, as a closed-subgroup quotient. -/
def cokernelObj : MetrizableLCA.{u} :=
  quotientObj B (cokernelSubgroup f) (AddSubgroup.isClosed_topologicalClosure _)

/-- The quotient projection onto the cokernel object. -/
def cokernelπ : B ⟶ cokernelObj f :=
  quotientMap B (cokernelSubgroup f) (AddSubgroup.isClosed_topologicalClosure _)

@[simp]
lemma cokernelπ_apply (b : B) : cokernelπ f b = (b : B ⧸ cokernelSubgroup f) :=
  rfl

lemma cokernelSubgroup_eq_top_of_cokernelπ_eq_zero (hπ : cokernelπ f = 0) :
    cokernelSubgroup f = ⊤ := by
  apply le_antisymm le_top
  intro b _hb
  have h := congrArg (fun q : B ⟶ cokernelObj f => q b) hπ
  change ((b : B) : B ⧸ cokernelSubgroup f) = 0 at h
  rw [QuotientAddGroup.eq_zero_iff] at h
  exact h

lemma cokernelπ_eq_zero_of_cokernelSubgroup_eq_top (hcok : cokernelSubgroup f = ⊤) :
    cokernelπ f = 0 := by
  ext b
  change ((b : B) : B ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  rw [hcok]
  trivial

lemma cokernelπ_eq_zero_iff_cokernelSubgroup_eq_top :
    cokernelπ f = 0 ↔ cokernelSubgroup f = ⊤ :=
  ⟨cokernelSubgroup_eq_top_of_cokernelπ_eq_zero f,
    cokernelπ_eq_zero_of_cokernelSubgroup_eq_top f⟩

lemma cokernelSubgroup_eq_top_of_surjective (hsurj : Function.Surjective (f : A → B)) :
    cokernelSubgroup f = ⊤ := by
  apply le_antisymm le_top
  intro b _hb
  rcases hsurj b with ⟨a, rfl⟩
  exact map_mem_cokernelSubgroup f a

private lemma cokernelObj_all_eq_zero_of_cokernelSubgroup_eq_top
    (hcok : cokernelSubgroup f = ⊤) (q : cokernelObj f) :
    q = 0 := by
  rcases quotientMap_surjective B (cokernelSubgroup f)
      (AddSubgroup.isClosed_topologicalClosure _) q with ⟨b, rfl⟩
  change ((b : B) : B ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  rw [hcok]
  trivial

lemma cokernelObj_isZero_of_cokernelSubgroup_eq_top
    (hcok : cokernelSubgroup f = ⊤) :
    IsZero (cokernelObj f) where
  unique_to Y := ⟨{
    default := 0
    uniq := by
      intro g
      ext q
      have hq : q = 0 := cokernelObj_all_eq_zero_of_cokernelSubgroup_eq_top f hcok q
      rw [hq]
      exact map_zero g.hom }⟩
  unique_from Y := ⟨{
    default := 0
    uniq := by
      intro g
      ext y
      have hg : g y = 0 := cokernelObj_all_eq_zero_of_cokernelSubgroup_eq_top f hcok (g y)
      simpa using hg }⟩

lemma cokernelSubgroup_eq_top_of_cokernelObj_isZero
    (hzero : IsZero (cokernelObj f)) :
    cokernelSubgroup f = ⊤ := by
  letI : Unique (B ⟶ cokernelObj f) := Classical.choice (hzero.unique_from B)
  have hπzero : cokernelπ f = 0 := Subsingleton.elim _ _
  exact cokernelSubgroup_eq_top_of_cokernelπ_eq_zero f hπzero

lemma cokernelSubgroup_eq_top_iff_cokernelObj_isZero :
    cokernelSubgroup f = ⊤ ↔ IsZero (cokernelObj f) :=
  ⟨cokernelObj_isZero_of_cokernelSubgroup_eq_top f,
    cokernelSubgroup_eq_top_of_cokernelObj_isZero f⟩

/-- The cokernel projection kills `f`. -/
lemma comp_cokernelπ : f ≫ cokernelπ f = 0 := by
  ext a
  change ((f a : B) : B ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f a

lemma cokernelπ_eq_zero_of_epi [Epi f] : cokernelπ f = 0 := by
  rw [← cancel_epi f]
  simpa using comp_cokernelπ f

/--
If a morphism kills `f`, then the closed cokernel subgroup of `f` is contained in its
kernel.
-/
lemma cokernel_desc_ker_le {k : B ⟶ Z} (hk : f ≫ k = 0) :
    cokernelSubgroup f ≤ k.hom.toAddMonoidHom.ker := by
  apply AddSubgroup.topologicalClosure_minimal
  · intro b hb
    rcases hb with ⟨a, _ha, rfl⟩
    change k (f a) = 0
    have h := congrArg (fun q : A ⟶ Z => q a) hk
    simpa using h
  · change IsClosed {b : B | k.hom.toAddMonoidHom b = 0}
    have hcont : Continuous fun b : B => k b := k.hom.continuous
    simpa using isClosed_singleton.preimage hcont

/-- The morphism induced from a map that kills `f`. -/
def cokernelDesc {k : B ⟶ Z} (hk : f ≫ k = 0) : cokernelObj f ⟶ Z :=
  quotientLift B (cokernelSubgroup f) (AddSubgroup.isClosed_topologicalClosure _) k
    (cokernel_desc_ker_le f hk)

/-- The cokernel projection followed by the induced morphism recovers the original map. -/
lemma cokernelπ_desc {k : B ⟶ Z} (hk : f ≫ k = 0) :
    cokernelπ f ≫ cokernelDesc f hk = k :=
  quotientLift_quotientMap B (cokernelSubgroup f) (AddSubgroup.isClosed_topologicalClosure _) k
    (cokernel_desc_ker_le f hk)

lemma epi_of_cokernelπ_eq_zero (hπ : cokernelπ f = 0) : Epi f := by
  constructor
  intro Z g h hgh
  rw [← sub_eq_zero]
  have hkill : f ≫ (g - h) = 0 := by
    rw [Preadditive.comp_sub, hgh, sub_self]
  have hdesc := cokernelπ_desc f hkill
  rw [hπ, zero_comp] at hdesc
  simpa using hdesc.symm

/-- Uniqueness of the morphism induced from a map that kills `f`. -/
lemma cokernelDesc_unique {k : B ⟶ Z} (hk : f ≫ k = 0) (m : cokernelObj f ⟶ Z)
    (hm : cokernelπ f ≫ m = k) : m = cokernelDesc f hk := by
  ext q
  rcases quotientMap_surjective B (cokernelSubgroup f)
      (AddSubgroup.isClosed_topologicalClosure _) q with ⟨b, rfl⟩
  have hm_fun := congrArg (fun q : B ⟶ Z => q b) hm
  have hdesc := congrArg (fun q : B ⟶ Z => q b) (cokernelπ_desc f hk)
  simpa using hm_fun.trans hdesc.symm

/-- The closed-range quotient is a categorical cokernel. -/
def cokernelIsColimit :
    IsColimit (CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)) :=
  CokernelCofork.IsColimit.ofπ (cokernelπ f) (comp_cokernelπ f)
    (fun _g hg => cokernelDesc f hg)
    (fun g hg => show cokernelπ f ≫ cokernelDesc f hg = g from cokernelπ_desc f hg)
    (fun _g hg m hm => show m = cokernelDesc f hg from cokernelDesc_unique f hg m hm)

instance instHasCokernel : HasCokernel f where
  exists_colimit := ⟨⟨_, cokernelIsColimit f⟩⟩

instance instHasCokernels : HasCokernels MetrizableLCA.{u} where
  has_colimit := inferInstance

instance instHasFiniteColimits : HasFiniteColimits MetrizableLCA.{u} :=
  letI : HasFiniteCoproducts MetrizableLCA.{u} := by
    haveI : HasInitial MetrizableLCA.{u} := inferInstance
    haveI : HasBinaryCoproducts MetrizableLCA.{u} := inferInstance
    exact hasFiniteCoproducts_of_has_binary_and_initial
  letI : HasCoequalizers MetrizableLCA.{u} :=
    Preadditive.hasCoequalizers_of_hasCokernels
  hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts

/-- The underlying map of an isomorphism in `MetrizableLCA` is open. -/
lemma iso_hom_openMap {A B : MetrizableLCA.{u}} (e : A ≅ B) :
    IsOpenMap (e.hom : A → B) := by
  intro U hU
  have hpre : e.hom '' U = (e.inv : B → A) ⁻¹' U := by
    ext b
    constructor
    · intro hb
      rcases hb with ⟨a, ha, hb⟩
      subst hb
      have h := congrArg (fun f : A ⟶ A => f a) e.hom_inv_id
      simpa using congrArg (fun x => x ∈ U) h.symm ▸ ha
    · intro hb
      refine ⟨e.inv b, hb, ?_⟩
      have h := congrArg (fun f : B ⟶ B => f b) e.inv_hom_id
      simpa using h
  rw [hpre]
  exact hU.preimage e.inv.hom.continuous

/-- Surjectivity is preserved by composing on the right with an isomorphism. -/
lemma surjective_comp_iso {A B C : MetrizableLCA.{u}} (q : A ⟶ B) (e : B ≅ C)
    (hq : Function.Surjective (q : A → B)) :
    Function.Surjective ((q ≫ e.hom : A ⟶ C) : A → C) := by
  intro c
  rcases hq (e.inv c) with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  change e.hom (q a) = c
  rw [ha]
  have h := congrArg (fun f : C ⟶ C => f c) e.inv_hom_id
  simpa using h

/-- Openness is preserved by composing on the right with an isomorphism. -/
lemma openMap_comp_iso {A B C : MetrizableLCA.{u}} (q : A ⟶ B) (e : B ≅ C)
    (hq : IsOpenMap (q : A → B)) :
    IsOpenMap ((q ≫ e.hom : A ⟶ C) : A → C) :=
  (iso_hom_openMap e).comp hq

/--
The coequalizer projection in `MetrizableLCA` is surjective on underlying
groups.  The proof compares the chosen coequalizer with the explicit cokernel
quotient of `f - g`.
-/
lemma coequalizerπ_surjective {A B : MetrizableLCA.{u}} (f g : A ⟶ B) :
    Function.Surjective
      ((coequalizer.π f g : B ⟶ (coequalizer f g : MetrizableLCA.{u})) :
        B → (coequalizer f g : MetrizableLCA.{u})) := by
  let ck : CokernelCofork (f - g) :=
    CokernelCofork.ofπ (cokernelπ (f - g)) (comp_cokernelπ (f - g))
  let cf : Cofork f g := Preadditive.coforkOfCokernelCofork ck
  have hcf : IsColimit cf :=
    Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsColimit (f - g))
  let e : cf.pt ≅ coequalizer f g :=
    IsColimit.coconePointUniqueUpToIso hcf (colimit.isColimit (parallelPair f g))
  have hπe : cf.π ≫ e.hom = coequalizer.π f g := by
    simpa [e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom hcf
        (colimit.isColimit (parallelPair f g)) WalkingParallelPair.one)
  have hck : cf.π = cokernelπ (f - g) := by
    simpa [cf, ck] using Preadditive.coforkOfCokernelCofork_π ck
  have hsurj : Function.Surjective
      ((cf.π ≫ e.hom : B ⟶ (coequalizer f g : MetrizableLCA.{u})) :
        B → (coequalizer f g : MetrizableLCA.{u})) := by
    rw [hck]
    exact surjective_comp_iso (cokernelπ (f - g)) e
      (quotientMap_surjective B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _))
  simpa [hπe] using hsurj

/--
The coequalizer projection in `MetrizableLCA` is an open map.  The proof
compares the chosen coequalizer with the explicit cokernel quotient of `f - g`.
-/
lemma coequalizerπ_openMap {A B : MetrizableLCA.{u}} (f g : A ⟶ B) :
    IsOpenMap
      ((coequalizer.π f g : B ⟶ (coequalizer f g : MetrizableLCA.{u})) :
        B → (coequalizer f g : MetrizableLCA.{u})) := by
  let ck : CokernelCofork (f - g) :=
    CokernelCofork.ofπ (cokernelπ (f - g)) (comp_cokernelπ (f - g))
  let cf : Cofork f g := Preadditive.coforkOfCokernelCofork ck
  have hcf : IsColimit cf :=
    Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsColimit (f - g))
  let e : cf.pt ≅ coequalizer f g :=
    IsColimit.coconePointUniqueUpToIso hcf (colimit.isColimit (parallelPair f g))
  have hπe : cf.π ≫ e.hom = coequalizer.π f g := by
    simpa [e] using
      (IsColimit.comp_coconePointUniqueUpToIso_hom hcf
        (colimit.isColimit (parallelPair f g)) WalkingParallelPair.one)
  have hck : cf.π = cokernelπ (f - g) := by
    simpa [cf, ck] using Preadditive.coforkOfCokernelCofork_π ck
  have hopen : IsOpenMap
      ((cf.π ≫ e.hom : B ⟶ (coequalizer f g : MetrizableLCA.{u})) :
        B → (coequalizer f g : MetrizableLCA.{u})) := by
    rw [hck]
    exact openMap_comp_iso (cokernelπ (f - g)) e
      (quotientMap_openMap B (cokernelSubgroup (f - g))
        (AddSubgroup.isClosed_topologicalClosure _))
  simpa [hπe] using hopen

/-- The `one` leg of the colimit cocone of a parallel pair is surjective. -/
lemma parallelPair_colimit_ι_one_surjective {A B : MetrizableLCA.{u}} (f g : A ⟶ B) :
    Function.Surjective
      ((colimit.ι (parallelPair f g) WalkingParallelPair.one :
          B ⟶ (colimit (parallelPair f g) : MetrizableLCA.{u})) :
        B → (colimit (parallelPair f g) : MetrizableLCA.{u})) :=
  coequalizerπ_surjective f g

/-- The `one` leg of the colimit cocone of a parallel pair is open. -/
lemma parallelPair_colimit_ι_one_openMap {A B : MetrizableLCA.{u}} (f g : A ⟶ B) :
    IsOpenMap
      ((colimit.ι (parallelPair f g) WalkingParallelPair.one :
          B ⟶ (colimit (parallelPair f g) : MetrizableLCA.{u})) :
        B → (colimit (parallelPair f g) : MetrizableLCA.{u})) :=
  coequalizerπ_openMap f g

end MetrizableLCA

end LeanLCAExactChallenge
