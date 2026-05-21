import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W437: mapped explicit cokernel cocone frontier.

W433 reduces finite-colimit preservation for
`forget₂ MetrizableLCA AddCommGrpCat` to the missing assertion that the
forgotten explicit closed-range cokernel cofork is colimiting in
`AddCommGrpCat`.  This file checks the local quotient comparison available at
that frontier.

The key obstruction is algebraic: `MetrizableLCA.cokernelSubgroup f` is the
topological closure of the algebraic range.  The categorical cokernel in
`AddCommGrpCat` quotients only by the algebraic range, so the forgotten LCA
quotient has the cokernel universal property only for target homomorphisms
whose kernel contains the closed cokernel subgroup.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportW437

open LeanLCAExactChallenge.MetrizableLCA

/-- The forgetful functor targeted by the W433 reduction. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The forgotten explicit cokernel projection. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.obj Y ⟶ underlyingForgetfulFunctor.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

/-- The forgotten explicit cokernel projection kills the forgotten source map. -/
theorem forgottenCokernelπ_condition {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.map f ≫ forgottenCokernelπ f = 0 := by
  ext x
  change ((f x : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f x

/-- The mapped explicit cokernel cofork, expressed as an `AddCommGrpCat` cokernel cofork. -/
def forgottenExplicitCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork (underlyingForgetfulFunctor.map f) :=
  CokernelCofork.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)

/--
The closed-range quotient projection is surjective after forgetting to
`AddCommGrpCat`.
-/
theorem forgottenCokernelπ_surjective {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Function.Surjective (forgottenCokernelπ f) :=
  QuotientAddGroup.mk'_surjective (cokernelSubgroup f)

/--
Every element of the closed cokernel subgroup is killed by the forgotten
projection.
-/
theorem cokernelSubgroup_le_forgottenCokernelπ_ker {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) :
    cokernelSubgroup f ≤ (forgottenCokernelπ f).hom.ker := by
  intro y hy
  change ((y : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact hy

/--
The algebraic range of the forgotten source map is contained in the kernel of
any AddCommGrp morphism satisfying the cokernel-cofork equation.
-/
theorem algebraicRange_le_ker_of_forgotten_condition {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hk : underlyingForgetfulFunctor.map f ≫ k = 0) :
    AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
        (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X)) ≤ k.hom.ker := by
  intro y hy
  rcases hy with ⟨x, _hx, rfl⟩
  change k (f x) = 0
  have h := congrArg (fun q : underlyingForgetfulFunctor.obj X ⟶ Z => q x) hk
  simpa using h

/--
The exact extra hypothesis needed to descend an arbitrary AddCommGrp target map
through the forgotten closed-range quotient.
-/
def forgottenCokernelDesc {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker) :
    underlyingForgetfulFunctor.obj (cokernelObj f) ⟶ Z :=
  AddCommGrpCat.ofHom
    (QuotientAddGroup.lift (cokernelSubgroup f) k.hom hkClosure)

/-- The descended AddCommGrp map composes with the quotient projection to the original map. -/
theorem forgottenCokernelπ_desc {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker) :
    forgottenCokernelπ f ≫ forgottenCokernelDesc f k hkClosure = k := by
  ext y
  rfl

/-- Uniqueness of the descended AddCommGrp map from the surjective quotient projection. -/
theorem forgottenCokernelDesc_unique {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hkClosure : cokernelSubgroup f ≤ k.hom.ker)
    (m : underlyingForgetfulFunctor.obj (cokernelObj f) ⟶ Z)
    (hm : forgottenCokernelπ f ≫ m = k) :
    m = forgottenCokernelDesc f k hkClosure := by
  haveI : Epi (forgottenCokernelπ f) :=
    (AddCommGrpCat.epi_iff_surjective (forgottenCokernelπ f)).mpr
      (forgottenCokernelπ_surjective f)
  apply (cancel_epi (forgottenCokernelπ f)).mp
  rw [hm, forgottenCokernelπ_desc]

/--
If the algebraic condition supplied by a cofork equation can always be upgraded
from algebraic range containment to closed cokernel-subgroup containment, the
forgotten explicit cofork is an AddCommGrp cokernel.
-/
def forgottenExplicitCokernelCoforkIsColimit_of_closureKernel
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hClosureKernel :
      ∀ {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z),
        underlyingForgetfulFunctor.map f ≫ k = 0 →
          cokernelSubgroup f ≤ k.hom.ker) :
    IsColimit (forgottenExplicitCokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)
    (fun k hk => forgottenCokernelDesc f k (hClosureKernel k hk))
    (fun k hk => forgottenCokernelπ_desc f k (hClosureKernel k hk))
    (fun k hk m hm => forgottenCokernelDesc_unique f k (hClosureKernel k hk) m hm)

/--
The W433-shaped downstream application remains checked once the missing mapped
colimit input is supplied.
-/
theorem downstream_preserves_walkingParallelPair_from_mapped_colimits
    (hMapped : ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
      IsColimit
        ((forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapCocone
          (CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)))) :
    PreservesColimitsOfShape WalkingParallelPair underlyingForgetfulFunctor := by
  haveI :
      ∀ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y),
        PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor := by
    intro X Y f
    exact preservesColimit_of_preserves_colimit_cocone
      (cokernelIsColimit f) (hMapped f)
  exact CategoryTheory.Functor.preservesCoequalizers_of_preservesCokernels
    underlyingForgetfulFunctor

/-- Checked summary for downstream audit scripts and review packets. -/
structure AddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  mappedExplicitCokernelCoconeResult : String
  missingTheoremNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportState :
    AddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportState where
  seed := "cb05f3fd5d0b7b4b7a3b071601919169"
  checkedConstructors :=
    ["forgottenCokernelπ",
      "forgottenCokernelπ_condition",
      "forgottenExplicitCokernelCofork",
      "forgottenCokernelπ_surjective",
      "cokernelSubgroup_le_forgottenCokernelπ_ker",
      "algebraicRange_le_ker_of_forgotten_condition",
      "forgottenCokernelDesc",
      "forgottenCokernelπ_desc",
      "forgottenCokernelDesc_unique",
      "forgottenExplicitCokernelCoforkIsColimit_of_closureKernel",
      "downstream_preserves_walkingParallelPair_from_mapped_colimits"]
  mappedExplicitCokernelCoconeResult := "blocked"
  missingTheoremNames :=
    ["mappedExplicitCokernelCocone_isColimit",
      "closureKernel_of_forgotten_cokernel_condition",
      "closed_range_quotient_forgetful_addcommgrp_cokernel_comparison"]
  remainingInputs :=
    ["A cofork equation in `AddCommGrpCat` gives only algebraic range containment in the target kernel.",
      "`MetrizableLCA.cokernelSubgroup f` is the topological closure of that algebraic range.",
      "To prove the W433 mapped colimit for arbitrary `f`, one would need to upgrade algebraic range containment to closed cokernel-subgroup containment for arbitrary AddCommGrp targets, or replace the target with the algebraic quotient by `AddMonoidHom.range`.",
      "For non-closed range maps, the forgotten closed-range quotient is generally a quotient of the algebraic cokernel, not the algebraic cokernel itself."]
  productSuccessClaimed := false

theorem currentAddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportState_productSuccess :
    currentAddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check forgottenCokernelπ
#check forgottenCokernelπ_condition
#check forgottenExplicitCokernelCofork
#check forgottenCokernelπ_surjective
#check cokernelSubgroup_le_forgottenCokernelπ_ker
#check algebraicRange_le_ker_of_forgotten_condition
#check forgottenCokernelDesc
#check forgottenCokernelπ_desc
#check forgottenCokernelDesc_unique
#check forgottenExplicitCokernelCoforkIsColimit_of_closureKernel
#check downstream_preserves_walkingParallelPair_from_mapped_colimits
#check currentAddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportState_productSuccess

end Checks

end AddCommGrpMappedExplicitCokernelCoconeIsColimitV370SupportW437

end LeanLCAExactChallenge
