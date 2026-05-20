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

/-- The cokernel projection kills `f`. -/
lemma comp_cokernelπ : f ≫ cokernelπ f = 0 := by
  ext a
  change ((f a : B) : B ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f a

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

end MetrizableLCA

end LeanLCAExactChallenge
