import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Kernels

/-!
Forgetting an LCA cokernel to abelian groups.

The cokernel object in `MetrizableLCA` quotients by the closure of the algebraic
range.  After forgetting to `AddCommGrpCat`, this quotient has the algebraic
cokernel universal property precisely when every target map killing the source
map also kills that closed subgroup.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableLCA

/-- The forgetful functor from metrizable LCA groups to abelian groups. -/
abbrev underlyingAddCommGrpFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The forgotten explicit LCA cokernel projection. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingAddCommGrpFunctor.obj Y ⟶ underlyingAddCommGrpFunctor.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

/-- The forgotten explicit LCA cokernel projection kills the forgotten source map. -/
theorem forgottenCokernelπ_condition {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingAddCommGrpFunctor.map f ≫ forgottenCokernelπ f = 0 := by
  ext x
  change ((f x : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f x

/-- The forgotten explicit LCA cokernel as an `AddCommGrpCat` cokernel cofork. -/
def forgottenCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork (underlyingAddCommGrpFunctor.map f) :=
  CokernelCofork.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)

/-- The forgotten closed-range quotient projection is surjective. -/
theorem forgottenCokernelπ_surjective {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Function.Surjective (forgottenCokernelπ f) :=
  QuotientAddGroup.mk'_surjective (cokernelSubgroup f)

/-- The closed cokernel subgroup is killed by the forgotten quotient projection. -/
theorem cokernelSubgroup_le_forgottenCokernelπ_ker {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) :
    cokernelSubgroup f ≤ (forgottenCokernelπ f).hom.ker := by
  intro y hy
  change ((y : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact hy

/--
A cofork equation in `AddCommGrpCat` only gives algebraic range containment in
the target kernel.
-/
theorem algebraicRange_le_ker_of_forgotten_condition {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) {Z : AddCommGrpCat.{0}} (k : underlyingAddCommGrpFunctor.obj Y ⟶ Z)
    (hk : underlyingAddCommGrpFunctor.map f ≫ k = 0) :
    AddSubgroup.map (underlyingAddCommGrpFunctor.map f).hom
        (⊤ : AddSubgroup (underlyingAddCommGrpFunctor.obj X)) ≤ k.hom.ker := by
  intro y hy
  rcases hy with ⟨x, _hx, rfl⟩
  change k (f x) = 0
  have h := congrArg (fun q : underlyingAddCommGrpFunctor.obj X ⟶ Z => q x) hk
  simpa using h

/--
The descent map through the forgotten closed-range quotient, under the exact
closure-kernel hypothesis needed in `AddCommGrpCat`.
-/
def forgottenCokernelDesc {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingAddCommGrpFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker) :
    underlyingAddCommGrpFunctor.obj (cokernelObj f) ⟶ Z :=
  AddCommGrpCat.ofHom
    (QuotientAddGroup.lift (cokernelSubgroup f) k.hom hkClosure)

/-- The descended forgotten map composes with the quotient projection to the original map. -/
theorem forgottenCokernelπ_desc {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingAddCommGrpFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker) :
    forgottenCokernelπ f ≫ forgottenCokernelDesc f k hkClosure = k := by
  ext y
  rfl

/-- Uniqueness of the descended map follows from quotient-projecton surjectivity. -/
theorem forgottenCokernelDesc_unique {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingAddCommGrpFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker)
    (m : underlyingAddCommGrpFunctor.obj (cokernelObj f) ⟶ Z)
    (hm : forgottenCokernelπ f ≫ m = k) :
    m = forgottenCokernelDesc f k hkClosure := by
  haveI : Epi (forgottenCokernelπ f) :=
    (AddCommGrpCat.epi_iff_surjective (forgottenCokernelπ f)).mpr
      (forgottenCokernelπ_surjective f)
  apply (cancel_epi (forgottenCokernelπ f)).mp
  rw [hm, forgottenCokernelπ_desc]

/--
Closure-kernel containment for every target map killing `f` makes the forgotten
explicit LCA cokernel cofork an algebraic cokernel.
-/
def forgottenCokernelCoforkIsColimit_of_closureKernel
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hClosureKernel :
      ∀ {Z : AddCommGrpCat.{0}} (k : underlyingAddCommGrpFunctor.obj Y ⟶ Z),
        underlyingAddCommGrpFunctor.map f ≫ k = 0 →
          cokernelSubgroup f ≤ k.hom.ker) :
    IsColimit (forgottenCokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)
    (fun k hk => forgottenCokernelDesc f k (hClosureKernel k hk))
    (fun k hk => forgottenCokernelπ_desc f k (hClosureKernel k hk))
    (fun k hk m hm => forgottenCokernelDesc_unique f k (hClosureKernel k hk) m hm)

end MetrizableLCA

end LeanLCAExactChallenge
