import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W442: bridge from the W433 mapped explicit cokernel cocone to the W440
closed-range cokernel cofork theorem.

W433 asks for `IsColimit` of the cocone obtained by applying
`forget₂ MetrizableLCA AddCommGrpCat` to the explicit LCA cokernel cofork.
W440 proves the same cokernel universal property for an explicitly written
`AddCommGrpCat` cofork under the closed-range equality input.  This file keeps
both shapes in one namespace and checks the definitional bridge between them.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportW442

open LeanLCAExactChallenge.MetrizableLCA

/-- The forgetful functor targeted by W433. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- W433's explicit local cokernel cofork before forgetting topology. -/
def explicitMetrizableCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

/-- W433's mapped concrete cokernel cocone. -/
def mappedExplicitCokernelCocone {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Cocone (parallelPair f 0 ⋙ underlyingForgetfulFunctor) :=
  underlyingForgetfulFunctor.mapCocone (explicitMetrizableCokernelCofork f)

/-- The algebraic range subgroup of the forgotten source map, as in W440. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup (underlyingForgetfulFunctor.obj Y) :=
  AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
    (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X))

/-- The forgotten explicit cokernel projection, as in W440. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.obj Y ⟶ underlyingForgetfulFunctor.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

/-- The mapped W433 projection is W440's explicitly written projection. -/
theorem mappedExplicitCokernelCocone_ι_one_eq_forgottenCokernelπ
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelCocone f).ι.app WalkingParallelPair.one =
      forgottenCokernelπ f :=
  rfl

/-- W440's projection is the forgotten image of the LCA cokernel projection. -/
theorem forgottenCokernelπ_eq_map_cokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    forgottenCokernelπ f = underlyingForgetfulFunctor.map (cokernelπ f) := by
  ext y
  rfl

/-- The forgotten explicit cokernel projection kills the forgotten source map. -/
theorem forgottenCokernelπ_condition {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.map f ≫ forgottenCokernelπ f = 0 := by
  ext x
  change ((f x : Y) : Y ⧸ cokernelSubgroup f) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact map_mem_cokernelSubgroup f x

/-- W440's explicit AddCommGrp cokernel cofork. -/
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
Closed-range comparison form of the closure-kernel input: equality with the
forgotten algebraic range upgrades every cofork equation to closed-subgroup
kernel containment.
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

/-- Descend an AddCommGrp target map through the forgotten closed-range quotient. -/
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
W440's closed-range theorem in the local W442 namespace: equality between the
forgotten algebraic range subgroup and `cokernelSubgroup f` proves that the
forgotten explicit closed-range quotient cofork is an abelian-group cokernel.
-/
def forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y))) :
    IsColimit (forgottenExplicitCokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (forgottenCokernelπ f) (forgottenCokernelπ_condition f)
    (fun k hk =>
      forgottenCokernelDesc f k
        (closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk))
    (fun k hk =>
      forgottenCokernelπ_desc f k
        (closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk))
    (fun k hk m hm =>
      forgottenCokernelDesc_unique f k
        (closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk) m hm)

/--
Bridge theorem: W440's closed-range equality input proves W433's mapped
explicit cokernel cocone is colimiting.
-/
def mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y))) :
    IsColimit (mappedExplicitCokernelCocone f) := by
  let e : parallelPair f 0 ⋙ underlyingForgetfulFunctor ≅
      parallelPair (underlyingForgetfulFunctor.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  let hc : IsColimit (forgottenExplicitCokernelCofork f) :=
    forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq f hRange
  refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv e _).symm hc) ?_
  refine Cocone.ext (Iso.refl _) ?_
  rintro (_ | _) <;>
    simp [mappedExplicitCokernelCocone, explicitMetrizableCokernelCofork,
      forgottenExplicitCokernelCofork, forgottenCokernelπ_eq_map_cokernelπ, e]

/-- W433's downstream preservation bridge, now fed by W440's closed-range theorem. -/
@[reducible] def preservesCokernelOf_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y))) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  preservesColimit_of_preserves_colimit_cocone
    (cokernelIsColimit f)
    (mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f hRange)

/-- Checked summary for downstream audit scripts and review packets. -/
structure AddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportState : Type where
  seed : String
  checkedConstructors : List String
  bridgeResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportState :
    AddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportState where
  seed := "G8jABH28yENR48pHFsfP0e5O"
  checkedConstructors :=
    ["explicitMetrizableCokernelCofork",
      "mappedExplicitCokernelCocone",
      "forgottenAlgebraicRangeSubgroup",
      "forgottenCokernelπ",
      "mappedExplicitCokernelCocone_ι_one_eq_forgottenCokernelπ",
      "forgottenCokernelπ_eq_map_cokernelπ",
      "forgottenExplicitCokernelCofork",
      "forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq",
      "mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq",
      "preservesCokernelOf_forgottenAlgebraicRange_eq"]
  bridgeResult := "proved"
  remainingInputs :=
    ["Port or supply the closed-range equality `forgottenAlgebraicRangeSubgroup f = MetrizableLCA.cokernelSubgroup f` for each morphism where W433 is applied.",
      "For arbitrary morphisms without this equality, W437's non-closed-range obstruction remains."]
  productSuccessClaimed := false

theorem currentAddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportState_productSuccess :
    currentAddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check explicitMetrizableCokernelCofork
#check mappedExplicitCokernelCocone
#check forgottenAlgebraicRangeSubgroup
#check forgottenCokernelπ
#check mappedExplicitCokernelCocone_ι_one_eq_forgottenCokernelπ
#check forgottenCokernelπ_eq_map_cokernelπ
#check forgottenExplicitCokernelCofork
#check forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq
#check mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq
#check preservesCokernelOf_forgottenAlgebraicRange_eq
#check currentAddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportState_productSuccess

end Checks

end AddCommGrpW433MappedCoconeClosedRangeBridgeV370SupportW442

end LeanLCAExactChallenge
