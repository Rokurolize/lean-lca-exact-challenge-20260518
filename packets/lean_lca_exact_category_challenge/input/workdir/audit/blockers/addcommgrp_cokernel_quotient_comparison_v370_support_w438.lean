import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
W438: AddCommGrp quotient/cokernel comparison for W433.

W433 needs the cocone obtained by forgetting the explicit `MetrizableLCA`
cokernel quotient to be colimiting in `AddCommGrpCat`.  The quotient object is
`B ⧸ MetrizableLCA.cokernelSubgroup f`, where the subgroup is the topological
closure of the algebraic range.  This file exposes the exact algebraic input
needed for that forgotten quotient projection to satisfy the AddCommGrp
cokernel universal property, plus checked closed-range variants.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace AddCommGrpCokernelQuotientComparisonV370SupportW438

/-- The forgetful functor under comparison in W433. -/
abbrev FgtCat : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

variable {A B : MetrizableLCA.{0}} (f : A ⟶ B)

/-- The algebraic range of the underlying additive homomorphism. -/
abbrev algebraicRange : AddSubgroup B :=
  AddSubgroup.map f.hom.toAddMonoidHom ⊤

/-- The range term appearing in the standard AddCommGrp cokernel quotient. -/
abbrev addCommGrpCokernelRange : AddSubgroup B :=
  AddMonoidHom.range (FgtCat.map f).hom

/-- The local topological cokernel subgroup is the closure of the algebraic range. -/
theorem cokernelSubgroup_eq_algebraicRange_closure :
    MetrizableLCA.cokernelSubgroup f = (algebraicRange f).topologicalClosure := by
  rfl

/-- The algebraic range is contained in the closed subgroup used by the topological quotient. -/
theorem algebraicRange_le_cokernelSubgroup :
    algebraicRange f ≤ MetrizableLCA.cokernelSubgroup f := by
  intro b hb
  rw [cokernelSubgroup_eq_algebraicRange_closure f]
  exact AddSubgroup.le_topologicalClosure _ hb

/-- The forgotten explicit quotient cofork, typed as an AddCommGrp cokernel cofork. -/
def forgottenCokernelCofork : CokernelCofork (FgtCat.map f) :=
  CokernelCofork.ofπ
    (FgtCat.map (MetrizableLCA.cokernelπ f))
    (by
      rw [← Functor.map_comp]
      rw [MetrizableLCA.comp_cokernelπ]
      simp)

/-- The W433-shaped mapped explicit quotient cocone. -/
def mappedExplicitCokernelCocone :
    Cocone (parallelPair f 0 ⋙ FgtCat) :=
  FgtCat.mapCocone
    (CokernelCofork.ofπ (MetrizableLCA.cokernelπ f) (MetrizableLCA.comp_cokernelπ f))

/-- Its `one` leg is the forgotten quotient projection. -/
theorem mappedExplicitCokernelCocone_ι_one :
    (mappedExplicitCokernelCocone f).ι.app WalkingParallelPair.one =
      FgtCat.map (MetrizableLCA.cokernelπ f) :=
  rfl

/-- The AddCommGrp cokernel diagram and the W433 mapped diagram are canonically isomorphic. -/
def forgottenCokernelParallelPairIso :
    parallelPair (FgtCat.map f) 0 ≅ parallelPair f 0 ⋙ FgtCat :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- The typed cokernel cofork is the same concrete cocone as the W433 mapped cocone. -/
def forgottenCokernelCoforkMappedCoconeIso :
    (Cocone.precompose (forgottenCokernelParallelPairIso f).inv).obj
        (forgottenCokernelCofork f) ≅
      mappedExplicitCokernelCocone f :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [forgottenCokernelParallelPairIso, forgottenCokernelCofork,
        mappedExplicitCokernelCocone]
    · simp [forgottenCokernelParallelPairIso, forgottenCokernelCofork,
        mappedExplicitCokernelCocone])

/--
The exact arbitrary-`f` comparison input: every AddCommGrp morphism out of the
underlying target that kills `f` must kill the closed subgroup used by the
topological quotient.
-/
structure ClosureKernelInput : Prop where
  closure_le_ker_of_comp_zero :
    forall {Z : AddCommGrpCat.{0}} (k : FgtCat.obj B ⟶ Z),
      FgtCat.map f ≫ k = 0 ->
        MetrizableLCA.cokernelSubgroup f ≤ k.hom.ker

/--
If the closure-kernel input is available, the forgotten topological quotient is
an AddCommGrp cokernel of the underlying homomorphism.
-/
def forgottenCokernelCofork_isColimit_of_closureKernelInput
    (h : ClosureKernelInput f) :
    IsColimit (forgottenCokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ
    (FgtCat.map (MetrizableLCA.cokernelπ f))
    (by
      rw [← Functor.map_comp]
      rw [MetrizableLCA.comp_cokernelπ]
      simp)
    (fun {Z} k hk =>
      AddCommGrpCat.ofHom
        (QuotientAddGroup.lift (MetrizableLCA.cokernelSubgroup f) k.hom
          (h.closure_le_ker_of_comp_zero k hk)))
    (fun {Z} k hk => by
      ext b
      rfl)
    (fun {Z} k hk m hm => by
      ext q
      refine QuotientAddGroup.induction_on q ?_
      intro b
      have hm_apply := congrArg (fun g : FgtCat.obj B ⟶ Z => g b) hm
      simpa using hm_apply)

/-- The same proof, stated directly for the W433-shaped mapped cocone. -/
def mappedExplicitCokernelCocone_isColimit_of_closureKernelInput
    (h : ClosureKernelInput f) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  (IsColimit.equivOfNatIsoOfIso
    (forgottenCokernelParallelPairIso f)
    (forgottenCokernelCofork f)
    (mappedExplicitCokernelCocone f)
    (forgottenCokernelCoforkMappedCoconeIso f))
    (forgottenCokernelCofork_isColimit_of_closureKernelInput f h)

/-- Closed-range sufficient condition in subgroup-inclusion form. -/
theorem closureKernelInput_of_algebraicRange_topologicalClosure_le
    (hclosed : (algebraicRange f).topologicalClosure ≤ algebraicRange f) :
    ClosureKernelInput f where
  closure_le_ker_of_comp_zero := by
    intro Z k hk b hb
    rw [cokernelSubgroup_eq_algebraicRange_closure f] at hb
    have hb_alg : b ∈ algebraicRange f := hclosed hb
    rcases hb_alg with ⟨a, _ha, rfl⟩
    change k.hom (f a) = 0
    have hk_apply := congrArg (fun q : FgtCat.obj A ⟶ Z => q a) hk
    simpa using hk_apply

/-- Closed-range sufficient condition as equality with the closure. -/
theorem closureKernelInput_of_algebraicRange_topologicalClosure_eq
    (hclosed : (algebraicRange f).topologicalClosure = algebraicRange f) :
    ClosureKernelInput f :=
  closureKernelInput_of_algebraicRange_topologicalClosure_le f (by
    intro b hb
    rwa [hclosed] at hb)

/-- Closed-range sufficient condition as equality with `MetrizableLCA.cokernelSubgroup f`. -/
theorem closureKernelInput_of_cokernelSubgroup_eq_algebraicRange
    (hclosed : MetrizableLCA.cokernelSubgroup f = algebraicRange f) :
    ClosureKernelInput f :=
  closureKernelInput_of_algebraicRange_topologicalClosure_eq f (by
    rwa [← cokernelSubgroup_eq_algebraicRange_closure f])

/-- Closed-range quotient comparison in the W433-shaped cocone type. -/
def mappedExplicitCokernelCocone_isColimit_of_algebraicRange_topologicalClosure_le
    (hclosed : (algebraicRange f).topologicalClosure ≤ algebraicRange f) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  mappedExplicitCokernelCocone_isColimit_of_closureKernelInput f
    (closureKernelInput_of_algebraicRange_topologicalClosure_le f hclosed)

/-- Equality variant of the closed-range W433-shaped quotient comparison. -/
def mappedExplicitCokernelCocone_isColimit_of_algebraicRange_topologicalClosure_eq
    (hclosed : (algebraicRange f).topologicalClosure = algebraicRange f) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  mappedExplicitCokernelCocone_isColimit_of_closureKernelInput f
    (closureKernelInput_of_algebraicRange_topologicalClosure_eq f hclosed)

/-- Local-subgroup equality variant of the closed-range W433-shaped quotient comparison. -/
def mappedExplicitCokernelCocone_isColimit_of_cokernelSubgroup_eq_algebraicRange
    (hclosed : MetrizableLCA.cokernelSubgroup f = algebraicRange f) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  mappedExplicitCokernelCocone_isColimit_of_closureKernelInput f
    (closureKernelInput_of_cokernelSubgroup_eq_algebraicRange f hclosed)

/-- Declaration-level summary for downstream review. -/
structure AddCommGrpCokernelQuotientComparisonV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  quotientComparisonResult : String
  missingApi : List String
  productSuccessClaimed : Bool

def currentAddCommGrpCokernelQuotientComparisonV370SupportState :
    AddCommGrpCokernelQuotientComparisonV370SupportState where
  seed := "w438-20260521T001542Z-5afb5c48a8ffae30"
  checkedDeclarations :=
    ["cokernelSubgroup_eq_algebraicRange_closure",
      "algebraicRange_le_cokernelSubgroup",
      "forgottenCokernelCofork",
      "mappedExplicitCokernelCocone",
      "mappedExplicitCokernelCocone_ι_one",
      "forgottenCokernelParallelPairIso",
      "forgottenCokernelCoforkMappedCoconeIso",
      "ClosureKernelInput",
      "forgottenCokernelCofork_isColimit_of_closureKernelInput",
      "mappedExplicitCokernelCocone_isColimit_of_closureKernelInput",
      "closureKernelInput_of_algebraicRange_topologicalClosure_le",
      "closureKernelInput_of_algebraicRange_topologicalClosure_eq",
      "closureKernelInput_of_cokernelSubgroup_eq_algebraicRange",
      "mappedExplicitCokernelCocone_isColimit_of_algebraicRange_topologicalClosure_le",
      "mappedExplicitCokernelCocone_isColimit_of_algebraicRange_topologicalClosure_eq",
      "mappedExplicitCokernelCocone_isColimit_of_cokernelSubgroup_eq_algebraicRange"]
  quotientComparisonResult := "partial"
  missingApi :=
    ["arbitrary-f input: ClosureKernelInput f",
      "equivalently: every AddCommGrp map out of the underlying target that kills f must kill MetrizableLCA.cokernelSubgroup f",
      "closed-range variants are checked, but no proof is provided that every MetrizableLCA morphism has algebraically closed range",
      "W433 can use mappedExplicitCokernelCocone_isColimit_of_closureKernelInput after supplying this input for each f"]
  productSuccessClaimed := false

theorem currentAddCommGrpCokernelQuotientComparisonV370SupportState_productSuccess :
    currentAddCommGrpCokernelQuotientComparisonV370SupportState.productSuccessClaimed = false :=
  rfl

section Checks

#check FgtCat
#check algebraicRange
#check addCommGrpCokernelRange
#check cokernelSubgroup_eq_algebraicRange_closure
#check algebraicRange_le_cokernelSubgroup
#check forgottenCokernelCofork
#check mappedExplicitCokernelCocone
#check mappedExplicitCokernelCocone_ι_one
#check forgottenCokernelParallelPairIso
#check forgottenCokernelCoforkMappedCoconeIso
#check ClosureKernelInput
#check forgottenCokernelCofork_isColimit_of_closureKernelInput
#check mappedExplicitCokernelCocone_isColimit_of_closureKernelInput
#check closureKernelInput_of_algebraicRange_topologicalClosure_le
#check closureKernelInput_of_algebraicRange_topologicalClosure_eq
#check closureKernelInput_of_cokernelSubgroup_eq_algebraicRange
#check mappedExplicitCokernelCocone_isColimit_of_algebraicRange_topologicalClosure_le
#check mappedExplicitCokernelCocone_isColimit_of_algebraicRange_topologicalClosure_eq
#check mappedExplicitCokernelCocone_isColimit_of_cokernelSubgroup_eq_algebraicRange
#check currentAddCommGrpCokernelQuotientComparisonV370SupportState
#check currentAddCommGrpCokernelQuotientComparisonV370SupportState_productSuccess
#check MetrizableLCA.cokernelπ
#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.comp_cokernelπ
#check MetrizableLCA.cokernelIsColimit
#check AddCommGrpCat.cokernelIsoQuotient
#check CokernelCofork.IsColimit.ofπ
#check QuotientAddGroup.lift
#check QuotientAddGroup.eq_zero_iff

end Checks

end AddCommGrpCokernelQuotientComparisonV370SupportW438

end LeanLCAExactChallenge
