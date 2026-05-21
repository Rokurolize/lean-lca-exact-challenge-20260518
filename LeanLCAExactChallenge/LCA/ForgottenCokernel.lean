import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Topology.Defs.Induced

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
open Topology

namespace MetrizableLCA

/-- The forgetful functor from metrizable LCA groups to abelian groups. -/
abbrev underlyingAddCommGrpFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The algebraic range of a morphism after forgetting to abelian groups. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup Y :=
  AddSubgroup.map (underlyingAddCommGrpFunctor.map f).hom
    (⊤ : AddSubgroup X)

/-- The closed LCA cokernel subgroup is the closure of the forgotten algebraic range. -/
theorem cokernelSubgroup_eq_forgottenAlgebraicRange_closure
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    cokernelSubgroup f = (forgottenAlgebraicRangeSubgroup f).topologicalClosure := by
  rfl

/-- The forgotten algebraic range is contained in the closed LCA cokernel subgroup. -/
theorem forgottenAlgebraicRange_le_cokernelSubgroup {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) :
    forgottenAlgebraicRangeSubgroup f ≤ cokernelSubgroup f := by
  intro y hy
  rw [cokernelSubgroup_eq_forgottenAlgebraicRange_closure f]
  exact AddSubgroup.le_topologicalClosure _ hy

/-- The forgotten algebraic range subgroup has carrier `Set.range f`. -/
theorem mem_forgottenAlgebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ forgottenAlgebraicRangeSubgroup f ↔ y ∈ Set.range (f : X → Y) := by
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- Closedness of the underlying set range gives closedness of the forgotten algebraic range. -/
theorem isClosed_forgottenAlgebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsClosed (forgottenAlgebraicRangeSubgroup f : Set Y) := by
  rwa [Set.ext_iff.mpr (mem_forgottenAlgebraicRangeSubgroup_iff f)]

/-- A closed underlying range identifies the algebraic and closed LCA cokernel subgroups. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    forgottenAlgebraicRangeSubgroup f = cokernelSubgroup f := by
  apply le_antisymm
  · exact forgottenAlgebraicRange_le_cokernelSubgroup f
  · rw [cokernelSubgroup_eq_forgottenAlgebraicRange_closure f]
    apply AddSubgroup.topologicalClosure_minimal
    · intro y hy
      exact hy
    · exact isClosed_forgottenAlgebraicRangeSubgroup_of_isClosed_range f hclosed

/-- Reversed orientation of the closed-range equality. -/
theorem cokernelSubgroup_eq_forgottenAlgebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    cokernelSubgroup f = forgottenAlgebraicRangeSubgroup f :=
  (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed).symm

/-- A closed map has closed full image, hence supplies the closed-range equality. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f = cokernelSubgroup f := by
  refine forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f ?_
  simpa [Set.image_univ] using hclosedMap Set.univ isClosed_univ

/-- A closed embedding supplies the closed-range equality. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f = cokernelSubgroup f :=
  forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f
    hclosedEmbedding.isClosed_range

/-- The forgotten explicit LCA cokernel projection. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingAddCommGrpFunctor.obj Y ⟶ underlyingAddCommGrpFunctor.obj (cokernelObj f) :=
  underlyingAddCommGrpFunctor.map (cokernelπ f)

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

/-- The mapped explicit LCA cokernel cocone in the W433 diagram shape. -/
def forgottenMappedExplicitCokernelCocone {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    Cocone (parallelPair f 0 ⋙ underlyingAddCommGrpFunctor) :=
  underlyingAddCommGrpFunctor.mapCocone
    (CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f))

/-- The `one` leg of the W433-shaped mapped cocone is the forgotten quotient projection. -/
theorem forgottenMappedExplicitCokernelCocone_ι_one {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) :
    (forgottenMappedExplicitCokernelCocone f).ι.app WalkingParallelPair.one =
      underlyingAddCommGrpFunctor.map (cokernelπ f) :=
  rfl

/-- The forgotten algebraic cokernel diagram is the W433 mapped diagram. -/
def forgottenCokernelParallelPairIso {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    parallelPair (underlyingAddCommGrpFunctor.map f) 0 ≅
      parallelPair f 0 ⋙ underlyingAddCommGrpFunctor :=
  parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- The typed forgotten cokernel cofork and the W433 mapped cocone are the same cocone. -/
def forgottenCokernelCoforkMappedCoconeIso {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (Cocone.precompose (forgottenCokernelParallelPairIso f).inv).obj
        (forgottenCokernelCofork f) ≅
      forgottenMappedExplicitCokernelCocone f :=
  Cocone.ext (Iso.refl _) (by
    rintro (_ | _)
    · simp [forgottenCokernelParallelPairIso, forgottenCokernelCofork,
        forgottenMappedExplicitCokernelCocone, forgottenCokernelπ]
    · simp [forgottenCokernelParallelPairIso, forgottenCokernelCofork,
        forgottenMappedExplicitCokernelCocone, forgottenCokernelπ])

/--
The exact arbitrary-`f` input needed after forgetting topology: every abelian
target map that kills `f` must kill the closed LCA cokernel subgroup.
-/
structure ClosureKernelInput {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) : Prop where
  closure_le_ker_of_comp_zero :
    ∀ {Z : AddCommGrpCat.{0}} (k : underlyingAddCommGrpFunctor.obj Y ⟶ Z),
      underlyingAddCommGrpFunctor.map f ≫ k = 0 →
        cokernelSubgroup f ≤ k.hom.ker

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
If the forgotten algebraic range already equals the closed LCA cokernel
subgroup, every forgotten cofork equation supplies closure-kernel containment.
-/
theorem closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        cokernelSubgroup f)
    {Z : AddCommGrpCat.{0}} (k : underlyingAddCommGrpFunctor.obj Y ⟶ Z)
    (hk : underlyingAddCommGrpFunctor.map f ≫ k = 0) :
    cokernelSubgroup f ≤ k.hom.ker := by
  rw [← hRange]
  exact algebraicRange_le_ker_of_forgotten_condition f k hk

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

/-- Structured-input variant of the forgotten cofork colimit theorem. -/
def forgottenCokernelCoforkIsColimit_of_closureKernelInput
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (h : ClosureKernelInput f) :
    IsColimit (forgottenCokernelCofork f) :=
  forgottenCokernelCoforkIsColimit_of_closureKernel f
    (fun k hk => h.closure_le_ker_of_comp_zero k hk)

/-- The W433-shaped mapped explicit cokernel cocone is colimiting from closure-kernel input. -/
def forgottenMappedExplicitCokernelCoconeIsColimit_of_closureKernelInput
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (h : ClosureKernelInput f) :
    IsColimit (forgottenMappedExplicitCokernelCocone f) :=
  (IsColimit.equivOfNatIsoOfIso
    (forgottenCokernelParallelPairIso f)
    (forgottenCokernelCofork f)
    (forgottenMappedExplicitCokernelCocone f)
    (forgottenCokernelCoforkMappedCoconeIso f))
    (forgottenCokernelCoforkIsColimit_of_closureKernelInput f h)

/-- Closed-range sufficient condition in subgroup-inclusion form. -/
theorem closureKernelInput_of_forgottenAlgebraicRange_topologicalClosure_le
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed :
      (forgottenAlgebraicRangeSubgroup f).topologicalClosure ≤
        forgottenAlgebraicRangeSubgroup f) :
    ClosureKernelInput f where
  closure_le_ker_of_comp_zero := by
    intro Z k hk y hy
    rw [cokernelSubgroup_eq_forgottenAlgebraicRange_closure f] at hy
    have hy_alg : y ∈ forgottenAlgebraicRangeSubgroup f := hclosed hy
    exact algebraicRange_le_ker_of_forgotten_condition f k hk hy_alg

/-- Closed-range sufficient condition as equality with the closure. -/
theorem closureKernelInput_of_forgottenAlgebraicRange_topologicalClosure_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed :
      (forgottenAlgebraicRangeSubgroup f).topologicalClosure =
        forgottenAlgebraicRangeSubgroup f) :
    ClosureKernelInput f :=
  closureKernelInput_of_forgottenAlgebraicRange_topologicalClosure_le f (by
    intro y hy
    rwa [hclosed] at hy)

/-- Closed-range sufficient condition as equality with the LCA cokernel subgroup. -/
theorem closureKernelInput_of_cokernelSubgroup_eq_forgottenAlgebraicRange
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : cokernelSubgroup f = forgottenAlgebraicRangeSubgroup f) :
    ClosureKernelInput f :=
  closureKernelInput_of_forgottenAlgebraicRange_topologicalClosure_eq f (by
    rwa [← cokernelSubgroup_eq_forgottenAlgebraicRange_closure f])

/-- Closed-range equality proves the forgotten explicit cokernel cofork is an algebraic cokernel. -/
def forgottenCokernelCoforkIsColimit_of_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        cokernelSubgroup f) :
    IsColimit (forgottenCokernelCofork f) :=
  forgottenCokernelCoforkIsColimit_of_closureKernel f
    (fun k hk =>
      closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk)

/-- Closed-range quotient comparison in the W433-shaped mapped cocone type. -/
def forgottenMappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        cokernelSubgroup f) :
    IsColimit (forgottenMappedExplicitCokernelCocone f) :=
  forgottenMappedExplicitCokernelCoconeIsColimit_of_closureKernelInput f
    { closure_le_ker_of_comp_zero := fun k hk =>
        closureKernel_of_forgottenAlgebraicRange_eq_cokernelSubgroup f hRange k hk }

/-- Closed range gives the W433-shaped mapped explicit cokernel cocone colimit. -/
def forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (forgottenMappedExplicitCokernelCocone f) :=
  forgottenMappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed)

/-- Closed-map variant of the W433-shaped mapped explicit cokernel cocone colimit. -/
def forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    IsColimit (forgottenMappedExplicitCokernelCocone f) :=
  forgottenMappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap f hclosedMap)

/-- Closed-embedding variant of the W433-shaped mapped explicit cokernel cocone colimit. -/
def forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    IsColimit (forgottenMappedExplicitCokernelCocone f) :=
  forgottenMappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding f hclosedEmbedding)

/-- Closed range makes the forgetful functor preserve the cokernel of `f`. -/
@[reducible] def preservesCokernelOf_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    PreservesColimit (parallelPair f 0) underlyingAddCommGrpFunctor :=
  preservesColimit_of_preserves_colimit_cocone
    (cokernelIsColimit f)
    (forgottenMappedExplicitCokernelCoconeIsColimit_of_isClosed_range f hclosed)

/-- Closed maps make the forgetful functor preserve the cokernel of `f`. -/
@[reducible] def preservesCokernelOf_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    PreservesColimit (parallelPair f 0) underlyingAddCommGrpFunctor :=
  preservesCokernelOf_isClosed_range f
    (by simpa [Set.image_univ] using hclosedMap Set.univ isClosed_univ)

/-- Closed embeddings make the forgetful functor preserve the cokernel of `f`. -/
@[reducible] def preservesCokernelOf_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    PreservesColimit (parallelPair f 0) underlyingAddCommGrpFunctor :=
  preservesCokernelOf_isClosed_range f hclosedEmbedding.isClosed_range

end MetrizableLCA

end LeanLCAExactChallenge
