import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Topology.Defs.Induced

/-!
W468: selected component quotient-identification bridge from closed-range data.

Seed: `8843a19a6d3720b455bd63af1607f259`.

This standalone support file weakens W463's selected component
quotient-identification input by deriving the three explicit quotient cofork
`IsColimit` fields from closed-range hypotheses for the selected component
difference maps.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpQuotientIdentificationFromClosedRangeV370SupportW468

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318
open MetrizableLCA

/-- Worker seed recorded before edits, used only to diversify proof search. -/
def supportSeed : String := "8843a19a6d3720b455bd63af1607f259"

/-- Local name for the short-complex functor forgetting topology. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The underlying functor used by the one-component wrappers. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The selected left arrow before forgetting topology. -/
def selectedMetrizableLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- The selected right arrow before forgetting topology. -/
def selectedMetrizableRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- The selected short-complex difference map whose components are normalized below. -/
def selectedMetrizableDifference
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  selectedMetrizableLeft S - selectedMetrizableRight S

/-- First component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₁
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₁ ⟶ (S.obj ordinaryTargetIndex).X₁ :=
  (selectedMetrizableDifference S).τ₁

/-- Second component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₂
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₂ ⟶ (S.obj ordinaryTargetIndex).X₂ :=
  (selectedMetrizableDifference S).τ₂

/-- Third component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₃
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₃ ⟶ (S.obj ordinaryTargetIndex).X₃ :=
  (selectedMetrizableDifference S).τ₃

/-- The selected leg before forgetting topology. -/
def selectedMetrizableTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    S.obj ordinaryTargetIndex ⟶ cs.pt :=
  cs.ι.app ordinaryTargetIndex

/-- Cocone naturality says the selected target leg coequalizes the two WPP arrows. -/
theorem selectedMetrizableTargetCoconeLeg_parallel_pair
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableLeft S ≫ selectedMetrizableTargetCoconeLeg S cs =
      selectedMetrizableRight S ≫ selectedMetrizableTargetCoconeLeg S cs :=
  (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).trans
    (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)).symm

/-- The selected target leg as a cofork in short complexes of metrizable LCA groups. -/
def selectedMetrizableTargetCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cofork (selectedMetrizableLeft S) (selectedMetrizableRight S) :=
  Cofork.ofπ (selectedMetrizableTargetCoconeLeg S cs)
    (selectedMetrizableTargetCoconeLeg_parallel_pair S cs)

/-- The selected metrizable target leg is a cokernel cofork for `(left - right)`. -/
def selectedMetrizableTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedMetrizableDifference S) :=
  Preadditive.cokernelCoforkOfCofork (selectedMetrizableTargetCofork S cs)

/-- The short-complex forgetful functor preserves zero morphisms, componentwise. -/
instance forgottenShortComplexFunctor_preservesZeroMorphisms :
    forgottenShortComplexFunctor.PreservesZeroMorphisms where
  map_zero S T := by
    ext x <;> rfl

/-- The short-complex forgetful functor is additive, componentwise. -/
instance forgottenShortComplexFunctor_additive :
    forgottenShortComplexFunctor.Additive where
  map_add {S T} {f g} := by
    ext x <;> rfl

/-- The selected component difference kills the first component target leg. -/
theorem selectedMetrizableDifferenceπ₁_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₁ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₁ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₁ h

/-- The selected component difference kills the second component target leg. -/
theorem selectedMetrizableDifferenceπ₂_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₂ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₂ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₂ h

/-- The selected component difference kills the third component target leg. -/
theorem selectedMetrizableDifferenceπ₃_comp_target
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableDifferenceπ₃ S ≫ (selectedMetrizableTargetCoconeLeg S cs).τ₃ = 0 := by
  have h :
      selectedMetrizableDifference S ≫ selectedMetrizableTargetCoconeLeg S cs = 0 := by
    rw [selectedMetrizableDifference, Preadditive.sub_comp, sub_eq_zero]
    exact selectedMetrizableTargetCoconeLeg_parallel_pair S cs
  exact congrArg ShortComplex.Hom.τ₃ h

/-- The first selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₁CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₁_comp_target S cs]
      rfl)

/-- The second selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₂CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₂_comp_target S cs]
      rfl)

/-- The third selected component cofork after forgetting topology. -/
def selectedForgottenComponentπ₃CokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S)) :=
  CokernelCofork.ofπ
    (underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃) (by
      rw [← underlyingForgetfulFunctor.map_comp,
        selectedMetrizableDifferenceπ₃_comp_target S cs]
      rfl)

/-- The mapped selected short-complex cofork after forgetting topology. -/
abbrev selectedForgottenShortComplexCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cocone (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) :=
  (selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor

/-- W433's explicit local cokernel cofork before forgetting topology. -/
def explicitMetrizableCokernelCofork {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

/-- W433's mapped concrete cokernel cocone. -/
def mappedExplicitCokernelCocone {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Cocone (parallelPair f 0 ⋙ underlyingForgetfulFunctor) :=
  underlyingForgetfulFunctor.mapCocone (explicitMetrizableCokernelCofork f)

/-- The forgotten explicit cokernel projection, as in W440. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.obj Y ⟶ underlyingForgetfulFunctor.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

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

/-- The algebraic range subgroup of the forgotten source map. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup (underlyingForgetfulFunctor.obj Y) :=
  AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
    (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X))

/-- The same algebraic range subgroup, kept in the topological target object. -/
abbrev algebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup Y :=
  AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup X)

/-- The local algebraic range subgroup has carrier `Set.range f`. -/
theorem mem_algebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ algebraicRangeSubgroup f ↔ y ∈ Set.range (f : X → Y) := by
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- The forgotten algebraic range subgroup has the same carrier as the topological one. -/
theorem mem_forgottenAlgebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ forgottenAlgebraicRangeSubgroup f ↔ y ∈ algebraicRangeSubgroup f := by
  rw [mem_algebraicRangeSubgroup_iff]
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- Closedness of the underlying set range gives closedness of the algebraic range subgroup. -/
theorem isClosed_algebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsClosed (algebraicRangeSubgroup f : Set Y) := by
  rwa [Set.ext_iff.mpr (mem_algebraicRangeSubgroup_iff f)]

/-- In `Y`, a closed algebraic range is equal to the closed cokernel subgroup. -/
theorem algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    algebraicRangeSubgroup f = cokernelSubgroup f := by
  apply le_antisymm
  · exact range_le_cokernelSubgroup f
  · unfold cokernelSubgroup
    apply AddSubgroup.topologicalClosure_minimal
    · intro y hy
      exact hy
    · exact isClosed_algebraicRangeSubgroup_of_isClosed_range f hclosed

/-- Closed-range equality needed by the explicit AddCommGrp cokernel proof. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    forgottenAlgebraicRangeSubgroup f =
      (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) := by
  ext y
  constructor
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f :=
      (mem_forgottenAlgebraicRangeSubgroup_iff f y).mp hy
    rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed] at hyalg
    exact hyalg
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f := by
      rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed]
      exact hy
    exact (mem_forgottenAlgebraicRangeSubgroup_iff f y).mpr hyalg

/-- The closed-range quotient projection is surjective after forgetting to `AddCommGrpCat`. -/
theorem forgottenCokernelπ_surjective {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Function.Surjective (forgottenCokernelπ f) :=
  QuotientAddGroup.mk'_surjective (cokernelSubgroup f)

/-- The algebraic range lies in the kernel of every cofork morphism. -/
theorem algebraicRange_le_ker_of_forgotten_condition {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) {Z : AddCommGrpCat.{0}} (k : underlyingForgetfulFunctor.obj Y ⟶ Z)
    (hk : underlyingForgetfulFunctor.map f ≫ k = 0) :
    forgottenAlgebraicRangeSubgroup f ≤ k.hom.ker := by
  intro y hy
  rcases hy with ⟨x, _hx, rfl⟩
  change k (f x) = 0
  have h := congrArg (fun q : underlyingForgetfulFunctor.obj X ⟶ Z => q x) hk
  simpa using h

/-- Closed-range comparison upgrades the cofork equation to closed-subgroup kernel containment. -/
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

/-- Equality between algebraic range and closed cokernel subgroup proves the explicit cofork. -/
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

/-- Closed range proves the explicit AddCommGrp cokernel cofork is colimiting. -/
def forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (forgottenExplicitCokernelCofork f) :=
  forgottenExplicitCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed)

/-- Transport data identifying the selected component cofork with the explicit quotient cofork. -/
structure SelectedComponentQuotientIdentificationInputsW463
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  pointIsoπ₁ :
    underlyingForgetfulFunctor.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₁ S))
  pointIsoπ₂ :
    underlyingForgetfulFunctor.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₂ S))
  pointIsoπ₃ :
    underlyingForgetfulFunctor.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₃ S))
  legπ₁ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      pointIsoπ₁.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₁ S)
  legπ₂ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      pointIsoπ₂.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₂ S)
  legπ₃ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      pointIsoπ₃.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₃ S)
  explicitπ₁CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S))
  explicitπ₂CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S))
  explicitπ₃CokernelIsColimit :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S))

/-- Point-identification data plus closed ranges, without explicit AddCommGrp cokernel proofs. -/
structure SelectedComponentPointIdentificationClosedRangeInputsW468
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  pointIsoπ₁ :
    underlyingForgetfulFunctor.obj (cs.pt.X₁) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₁ S))
  pointIsoπ₂ :
    underlyingForgetfulFunctor.obj (cs.pt.X₂) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₂ S))
  pointIsoπ₃ :
    underlyingForgetfulFunctor.obj (cs.pt.X₃) ≅
      underlyingForgetfulFunctor.obj (cokernelObj (selectedMetrizableDifferenceπ₃ S))
  legπ₁ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₁ ≫
      pointIsoπ₁.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₁ S)
  legπ₂ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₂ ≫
      pointIsoπ₂.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₂ S)
  legπ₃ :
    underlyingForgetfulFunctor.map (selectedMetrizableTargetCoconeLeg S cs).τ₃ ≫
      pointIsoπ₃.hom =
        forgottenCokernelπ (selectedMetrizableDifferenceπ₃ S)
  closedRangeπ₁ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₁ S :
        (S.obj ordinarySourceIndex).X₁ → (S.obj ordinaryTargetIndex).X₁))
  closedRangeπ₂ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₂ S :
        (S.obj ordinarySourceIndex).X₂ → (S.obj ordinaryTargetIndex).X₂))
  closedRangeπ₃ :
    IsClosed (Set.range
      (selectedMetrizableDifferenceπ₃ S :
        (S.obj ordinarySourceIndex).X₃ → (S.obj ordinaryTargetIndex).X₃))

/-- The first selected component explicit quotient cofork is colimiting under closed range. -/
def explicitπ₁CokernelIsColimit_of_closedRange_w468
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hclosed :
      IsClosed (Set.range
        (selectedMetrizableDifferenceπ₁ S :
          (S.obj ordinarySourceIndex).X₁ → (S.obj ordinaryTargetIndex).X₁))) :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S)) :=
  forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
    (selectedMetrizableDifferenceπ₁ S) hclosed

/-- The second selected component explicit quotient cofork is colimiting under closed range. -/
def explicitπ₂CokernelIsColimit_of_closedRange_w468
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hclosed :
      IsClosed (Set.range
        (selectedMetrizableDifferenceπ₂ S :
          (S.obj ordinarySourceIndex).X₂ → (S.obj ordinaryTargetIndex).X₂))) :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S)) :=
  forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
    (selectedMetrizableDifferenceπ₂ S) hclosed

/-- The third selected component explicit quotient cofork is colimiting under closed range. -/
def explicitπ₃CokernelIsColimit_of_closedRange_w468
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    (hclosed :
      IsClosed (Set.range
        (selectedMetrizableDifferenceπ₃ S :
          (S.obj ordinarySourceIndex).X₃ → (S.obj ordinaryTargetIndex).X₃))) :
    IsColimit (forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S)) :=
  forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
    (selectedMetrizableDifferenceπ₃ S) hclosed

/-- Closed-range point identifications supply W463's stronger quotient-identification inputs. -/
def selectedComponentQuotientIdentificationInputs_of_closedRange_w468
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentPointIdentificationClosedRangeInputsW468 S cs) :
    SelectedComponentQuotientIdentificationInputsW463 S cs where
  pointIsoπ₁ := h.pointIsoπ₁
  pointIsoπ₂ := h.pointIsoπ₂
  pointIsoπ₃ := h.pointIsoπ₃
  legπ₁ := h.legπ₁
  legπ₂ := h.legπ₂
  legπ₃ := h.legπ₃
  explicitπ₁CokernelIsColimit :=
    explicitπ₁CokernelIsColimit_of_closedRange_w468 h.closedRangeπ₁
  explicitπ₂CokernelIsColimit :=
    explicitπ₂CokernelIsColimit_of_closedRange_w468 h.closedRangeπ₂
  explicitπ₃CokernelIsColimit :=
    explicitπ₃CokernelIsColimit_of_closedRange_w468 h.closedRangeπ₃

/-- The selected first-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₁CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₁CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₁ S) :=
  Cocone.ext h.pointIsoπ₁ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S) ≫ q) h.legπ₁
      simpa [Category.assoc, selectedForgottenComponentπ₁CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₁CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₁)

/-- The selected second-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₂CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₂CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₂ S) :=
  Cocone.ext h.pointIsoπ₂ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S) ≫ q) h.legπ₂
      simpa [Category.assoc, selectedForgottenComponentπ₂CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₂CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₂)

/-- The selected third-component cofork is isomorphic to the explicit quotient cofork. -/
def selectedComponentπ₃CoforkIso_of_quotientIdentification
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    selectedForgottenComponentπ₃CokernelCofork S cs ≅
      forgottenExplicitCokernelCofork (selectedMetrizableDifferenceπ₃ S) :=
  Cocone.ext h.pointIsoπ₃ (by
    rintro (_ | _)
    · have hzero := congrArg
        (fun q => underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S) ≫ q) h.legπ₃
      simpa [Category.assoc, selectedForgottenComponentπ₃CokernelCofork,
        forgottenExplicitCokernelCofork] using hzero
    · simpa [selectedForgottenComponentπ₃CokernelCofork, forgottenExplicitCokernelCofork] using h.legπ₃)

/-- Quotient-identification data transports the explicit first-component cokernel proof. -/
def selectedComponentπ₁_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₁CokernelIsColimit
    (selectedComponentπ₁CoforkIso_of_quotientIdentification h).symm

/-- Quotient-identification data transports the explicit second-component cokernel proof. -/
def selectedComponentπ₂_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₂CokernelIsColimit
    (selectedComponentπ₂CoforkIso_of_quotientIdentification h).symm

/-- Quotient-identification data transports the explicit third-component cokernel proof. -/
def selectedComponentπ₃_isColimit_of_quotientIdentification_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs) :=
  IsColimit.ofIsoColimit h.explicitπ₃CokernelIsColimit
    (selectedComponentπ₃CoforkIso_of_quotientIdentification h).symm

/-- The projected `π₁` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₁DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₁ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₁]) (by rfl)

/-- The projected `π₂` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₂DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₂ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₂]) (by rfl)

/-- The projected `π₃` parallel-pair diagram is the selected component diagram. -/
def selectedProjectionπ₃DiagramIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    parallelPair (underlyingForgetfulFunctor.map (selectedMetrizableDifferenceπ₃ S)) 0 ≅
      (parallelPair (forgottenShortComplexFunctor.map (selectedMetrizableDifference S)) 0) ⋙
        (ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}) :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [selectedMetrizableDifferenceπ₃]) (by rfl)

/-- The first selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₁CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₁DiagramIso S).inv).obj
        (selectedForgottenComponentπ₁CokernelCofork S cs) ≅
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The second selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₂CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₂DiagramIso S).inv).obj
        (selectedForgottenComponentπ₂CokernelCofork S cs) ≅
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- The third selected component cofork is the precomposed projected cofork. -/
def selectedProjectionπ₃CoforkIso
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (Cocone.precompose (selectedProjectionπ₃DiagramIso S).inv).obj
        (selectedForgottenComponentπ₃CokernelCofork S cs) ≅
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _) <;> rfl)

/-- Transport a selected first-component `IsColimit` proof to the projected cofork. -/
def projectionπ₁_isColimit_of_selectedComponentπ₁
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₁DiagramIso S)
    (selectedForgottenComponentπ₁CokernelCofork S cs)
    _
    (selectedProjectionπ₁CoforkIso S cs)) h

/-- Transport a selected second-component `IsColimit` proof to the projected cofork. -/
def projectionπ₂_isColimit_of_selectedComponentπ₂
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₂DiagramIso S)
    (selectedForgottenComponentπ₂CokernelCofork S cs)
    _
    (selectedProjectionπ₂CoforkIso S cs)) h

/-- Transport a selected third-component `IsColimit` proof to the projected cofork. -/
def projectionπ₃_isColimit_of_selectedComponentπ₃
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)) :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        (selectedForgottenShortComplexCokernelCofork S cs)) :=
  (IsColimit.equivOfNatIsoOfIso (selectedProjectionπ₃DiagramIso S)
    (selectedForgottenComponentπ₃CokernelCofork S cs)
    _
    (selectedProjectionπ₃CoforkIso S cs)) h

/-- W457's selected projection colimit input shape. -/
def SelectedProjectionComponentIsColimitInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 :=
  IsColimit
    ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs)) ×
  IsColimit
    ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs)) ×
  IsColimit
    ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
      (selectedForgottenShortComplexCokernelCofork S cs))

/-- Component `IsColimit` proofs for the selected coforks supply W457's projected fields. -/
def selectedProjectionComponentIsColimitInputs_of_selectedComponentCoforks
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (hπ₁ : IsColimit (selectedForgottenComponentπ₁CokernelCofork S cs))
    (hπ₂ : IsColimit (selectedForgottenComponentπ₂CokernelCofork S cs))
    (hπ₃ : IsColimit (selectedForgottenComponentπ₃CokernelCofork S cs)) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  ⟨projectionπ₁_isColimit_of_selectedComponentπ₁ hπ₁,
    projectionπ₂_isColimit_of_selectedComponentπ₂ hπ₂,
    projectionπ₃_isColimit_of_selectedComponentπ₃ hπ₃⟩

/-- Quotient-identification inputs provide all projected component `IsColimit` fields. -/
def selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentQuotientIdentificationInputsW463 S cs) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  selectedProjectionComponentIsColimitInputs_of_selectedComponentCoforks
    (selectedComponentπ₁_isColimit_of_quotientIdentification_w463 h)
    (selectedComponentπ₂_isColimit_of_quotientIdentification_w463 h)
    (selectedComponentπ₃_isColimit_of_quotientIdentification_w463 h)

/-- Closed-range point identifications provide all projected component `IsColimit` fields. -/
def selectedProjectionComponentIsColimitInputs_of_closedRangePointIdentifications_w468
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (h : SelectedComponentPointIdentificationClosedRangeInputsW468 S cs) :
    SelectedProjectionComponentIsColimitInputs S cs :=
  selectedProjectionComponentIsColimitInputs_of_quotientIdentifications_w463
    (selectedComponentQuotientIdentificationInputs_of_closedRange_w468 h)

/-- Machine-readable W468 support state. -/
structure AddCommGrpQuotientIdentificationFromClosedRangeV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  quotientIdentificationResult : String
  selectedComponentIsColimitResult : String
  projectionFieldsResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpQuotientIdentificationFromClosedRangeV370SupportState :
    AddCommGrpQuotientIdentificationFromClosedRangeV370SupportState where
  seed := supportSeed
  checkedDeclarations :=
    ["supportSeed",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range",
      "forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range",
      "SelectedComponentPointIdentificationClosedRangeInputsW468",
      "SelectedComponentQuotientIdentificationInputsW463",
      "explicitπ₁CokernelIsColimit_of_closedRange_w468",
      "explicitπ₂CokernelIsColimit_of_closedRange_w468",
      "explicitπ₃CokernelIsColimit_of_closedRange_w468",
      "selectedComponentQuotientIdentificationInputs_of_closedRange_w468",
      "selectedProjectionComponentIsColimitInputs_of_closedRangePointIdentifications_w468"]
  quotientIdentificationResult := "proved"
  selectedComponentIsColimitResult := "proved"
  projectionFieldsResult := "proved"
  remainingInputs :=
    ["At the call site, supply the three AddCommGrp point isomorphisms from `cs.pt.Xᵢ` to the forgotten explicit cokernel quotients.",
      "At the call site, prove the three selected component legs compose with those isomorphisms to the forgotten explicit quotient projections.",
      "At the call site, supply closed-range hypotheses for the three selected component difference maps."]
  productSuccessClaimed := false

theorem currentAddCommGrpQuotientIdentificationFromClosedRangeV370SupportState_productSuccess :
    currentAddCommGrpQuotientIdentificationFromClosedRangeV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check supportSeed
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
#check forgottenExplicitCokernelCoforkIsColimit_of_isClosed_range
#check SelectedComponentPointIdentificationClosedRangeInputsW468
#check SelectedComponentQuotientIdentificationInputsW463
#check explicitπ₁CokernelIsColimit_of_closedRange_w468
#check explicitπ₂CokernelIsColimit_of_closedRange_w468
#check explicitπ₃CokernelIsColimit_of_closedRange_w468
#check selectedComponentQuotientIdentificationInputs_of_closedRange_w468
#check selectedProjectionComponentIsColimitInputs_of_closedRangePointIdentifications_w468
#check currentAddCommGrpQuotientIdentificationFromClosedRangeV370SupportState_productSuccess

end Checks

end AddCommGrpQuotientIdentificationFromClosedRangeV370SupportW468

end LeanLCAExactChallenge
