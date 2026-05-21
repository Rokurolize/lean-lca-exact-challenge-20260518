import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W440: closed-range/closure-kernel support for the mapped explicit cokernel cocone.

W437 identified the obstruction: after forgetting topology, the explicit LCA
cokernel quotient is by `MetrizableLCA.cokernelSubgroup f`, the topological
closure of the algebraic range.  An arbitrary `AddCommGrpCat` cofork equation
only proves that the algebraic range is contained in the target kernel.

This file packages the usable conditional theorem.  If that algebraic range
subgroup is exactly `MetrizableLCA.cokernelSubgroup f` (the closed-range
comparison, or equivalently the closure-kernel input needed for arbitrary
abelian-group targets), then the forgotten explicit cokernel cofork is
colimiting in `AddCommGrpCat`.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportW440

open LeanLCAExactChallenge.MetrizableLCA

/-- The forgetful functor targeted by the W433 reduction. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The algebraic range subgroup of the forgotten source map. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup (underlyingForgetfulFunctor.obj Y) :=
  AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
    (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X))

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

/-- The closed-range quotient projection is surjective after forgetting to `AddCommGrpCat`. -/
theorem forgottenCokernelπ_surjective {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Function.Surjective (forgottenCokernelπ f) :=
  QuotientAddGroup.mk'_surjective (cokernelSubgroup f)

/--
The algebraic range of the forgotten source map is contained in the kernel of
any AddCommGrp morphism satisfying the cokernel-cofork equation.
-/
theorem algebraicRange_le_ker_of_forgotten_condition {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hk : underlyingForgetfulFunctor.map f ≫ k = 0) :
    forgottenAlgebraicRangeSubgroup f ≤ k.hom.ker := by
  intro y hy
  rcases hy with ⟨x, _hx, rfl⟩
  change k (f x) = 0
  have h := congrArg (fun q : underlyingForgetfulFunctor.obj X ⟶ Z => q x) hk
  simpa using h

/--
Closed-range comparison form of the closure-kernel input: if the closed LCA
cokernel subgroup equals the algebraic range subgroup after forgetting, then
every cofork equation supplies the stronger subgroup containment needed to
descend through the closed-range quotient.
-/
theorem closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)))
    {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hk : underlyingForgetfulFunctor.map f ≫ k = 0) :
    cokernelSubgroup f ≤ k.hom.ker := by
  rw [← hRange]
  exact algebraicRange_le_ker_of_forgotten_condition f k hk

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
Closure-kernel theorem: if every forgotten cofork equation upgrades to
containment of the closed cokernel subgroup in the target kernel, then the
forgotten explicit closed-range quotient cofork is an abelian-group cokernel.
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
Closed-range theorem: equality between the forgotten algebraic range subgroup
and `MetrizableLCA.cokernelSubgroup f` proves that the forgotten explicit
closed-range quotient cofork is an abelian-group cokernel.
-/
def forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y))) :
    IsColimit (forgottenExplicitCokernelCofork f) :=
  forgottenExplicitCokernelCoforkIsColimit_of_closureKernel f
    (fun k hk =>
      closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk)

/-- Checked summary for downstream audit scripts and review packets. -/
structure AddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  closedRangeResult : String
  missingTheoremNames : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportState :
    AddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportState where
  seed := "MyzGLsVlq8tfIQXb5WNS3N4o"
  checkedConstructors :=
    ["forgottenAlgebraicRangeSubgroup",
      "forgottenCokernelπ",
      "forgottenCokernelπ_condition",
      "forgottenExplicitCokernelCofork",
      "forgottenCokernelπ_surjective",
      "algebraicRange_le_ker_of_forgotten_condition",
      "closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup",
      "forgottenCokernelDesc",
      "forgottenCokernelπ_desc",
      "forgottenCokernelDesc_unique",
      "forgottenExplicitCokernelCoforkIsColimit_of_closureKernel",
      "forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq"]
  closedRangeResult := "proved"
  missingTheoremNames :=
    ["closed_range_as_forgottenAlgebraicRange_eq_cokernelSubgroup",
      "category_strict_exact_data_to_forgottenAlgebraicRange_eq_cokernelSubgroup",
      "mappedExplicitCokernelCocone_identifies_forgottenExplicitCokernelCofork"]
  remainingInputs :=
    ["Port the category's closed-map/strict-exact data to the local equality `forgottenAlgebraicRangeSubgroup f = MetrizableLCA.cokernelSubgroup f`.",
      "Add the local declaration identifying W433's `(forget₂ MetrizableLCA AddCommGrpCat).mapCocone (CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f))` with `forgottenExplicitCokernelCofork f`.",
      "For arbitrary morphisms without this equality, W437's obstruction remains: `AddCommGrpCat` cofork equations only provide algebraic range containment."]
  productSuccessClaimed := false

theorem currentAddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportState_productSuccess :
    currentAddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check forgottenAlgebraicRangeSubgroup
#check forgottenCokernelπ
#check forgottenCokernelπ_condition
#check forgottenExplicitCokernelCofork
#check forgottenCokernelπ_surjective
#check algebraicRange_le_ker_of_forgotten_condition
#check closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup
#check forgottenCokernelDesc
#check forgottenCokernelπ_desc
#check forgottenCokernelDesc_unique
#check forgottenExplicitCokernelCoforkIsColimit_of_closureKernel
#check forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq
#check currentAddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportState_productSuccess

end Checks

end AddCommGrpMappedExplicitCokernelCoconeClosedRangeV370SupportW440

end LeanLCAExactChallenge
