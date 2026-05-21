import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Algebra.Category.Grp.Kernels
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Topology.Defs.Induced

/-!
W448: closed-embedding cokernel preservation package for exact-category use.

This standalone audit file combines the W433 mapped-cocone bridge with the
W443 closed-range equality input.  It proves that the forgetful functor
`MetrizableLCA ⥤ AddCommGrpCat` preserves the cokernel parallel-pair colimit
whenever the underlying range of the morphism is closed, and exposes the
corresponding mapped explicit cokernel cocone colimit theorem.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportW448

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

/-- The algebraic range subgroup of the forgotten source map. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup (underlyingForgetfulFunctor.obj Y) :=
  AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
    (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X))

/-- The same algebraic range subgroup, kept in the topological target object. -/
abbrev algebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup Y :=
  AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup X)

/-- The forgotten explicit cokernel projection. -/
abbrev forgottenCokernelπ {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    underlyingForgetfulFunctor.obj Y ⟶ underlyingForgetfulFunctor.obj (cokernelObj f) :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (cokernelSubgroup f))

/-- The mapped W433 projection is the explicitly written forgotten projection. -/
theorem mappedExplicitCokernelCocone_ι_one_eq_forgottenCokernelπ
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    (mappedExplicitCokernelCocone f).ι.app WalkingParallelPair.one =
      forgottenCokernelπ f :=
  rfl

/-- The forgotten explicit projection is the forgotten image of the LCA cokernel projection. -/
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
Equality between the forgotten algebraic range subgroup and `cokernelSubgroup f`
proves that the forgotten explicit closed-range quotient cofork is an
abelian-group cokernel.
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
W442 bridge theorem: the closed-range equality input proves W433's mapped
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

/-- W442 preservation bridge from the range-subgroup equality input. -/
@[reducible] def preservesCokernelOf_forgottenAlgebraicRange_eq
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hRange :
      forgottenAlgebraicRangeSubgroup f =
        (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y))) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  preservesColimit_of_preserves_colimit_cocone
    (cokernelIsColimit f)
    (mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f hRange)

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

/--
W443 closed-range equality: if the underlying image of `f` is closed, then the
forgotten algebraic range equals the closed subgroup used in the LCA cokernel
quotient.
-/
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

/-- Reversed orientation, matching W438's local-subgroup closed-range variant. -/
theorem cokernelSubgroup_eq_forgottenAlgebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) =
      forgottenAlgebraicRangeSubgroup f :=
  (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed).symm

/-- A closed map has closed full image, so it supplies W443's range equality. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f =
      (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) := by
  refine forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f ?_
  simpa [Set.image_univ] using hclosedMap Set.univ isClosed_univ

/-- A closed embedding supplies the same equality through its closed range field. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f =
      (cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) :=
  forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f
    hclosedEmbedding.isClosed_range

/--
Composed W442/W443 result: closed underlying range makes W433's mapped explicit
cokernel cocone colimiting after forgetting topology.
-/
def mappedExplicitCokernelCoconeIsColimit_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed)

/-- Closed underlying range makes the forgetful functor preserve the cokernel of `f`. -/
@[reducible] def preservesCokernelOf_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  preservesCokernelOf_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed)

/-- Closed maps make the forgetful functor preserve the cokernel of `f`. -/
@[reducible] def preservesCokernelOf_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  preservesCokernelOf_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap f hclosedMap)

/-- Closed embeddings make the forgetful functor preserve the cokernel of `f`. -/
@[reducible] def preservesCokernelOf_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  preservesCokernelOf_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding f hclosedEmbedding)

/--
Exact-category-facing input package for an admissible monomorphism or closed
inclusion whose cokernel preservation is needed after forgetting to
`AddCommGrpCat`.
-/
structure ClosedEmbeddingCokernelPreservationInput
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) : Prop where
  closed_embedding : IsClosedEmbedding (f : X → Y)

namespace ClosedEmbeddingCokernelPreservationInput

/-- A packaged closed embedding exposes the closed range input used above. -/
theorem closed_range {X Y : MetrizableLCA.{0}} {f : X ⟶ Y}
    (h : ClosedEmbeddingCokernelPreservationInput f) :
    IsClosed (Set.range (f : X → Y)) :=
  h.closed_embedding.isClosed_range

/-- A packaged closed embedding exposes the closed-map input used above. -/
theorem closed_map {X Y : MetrizableLCA.{0}} {f : X ⟶ Y}
    (h : ClosedEmbeddingCokernelPreservationInput f) :
    IsClosedMap (f : X → Y) :=
  h.closed_embedding.isClosedMap

/-- A packaged closed embedding preserves the cokernel of the underlying map. -/
@[reducible] def preservesCokernel {X Y : MetrizableLCA.{0}} {f : X ⟶ Y}
    (h : ClosedEmbeddingCokernelPreservationInput f) :
    PreservesColimit (parallelPair f 0) underlyingForgetfulFunctor :=
  preservesCokernelOf_isClosedEmbedding f h.closed_embedding

/-- A packaged closed embedding makes the mapped explicit cokernel cocone colimiting. -/
def mappedExplicitCokernelCoconeIsColimit
    {X Y : MetrizableLCA.{0}} {f : X ⟶ Y}
    (h : ClosedEmbeddingCokernelPreservationInput f) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding f
      h.closed_embedding)

end ClosedEmbeddingCokernelPreservationInput

/-- The local strict exact sequence structure exposes the desired closed embedding field. -/
def closedEmbeddingInput_of_strictShortExact
    {S : ShortComplex MetrizableLCA.{0}} (hS : strictShortExact S) :
    ClosedEmbeddingCokernelPreservationInput S.f where
  closed_embedding := hS.closed_inclusion

/-- Strict short exact sequences preserve the cokernel of their left map after forgetting. -/
@[reducible] def preservesCokernelOf_strictShortExact
    {S : ShortComplex MetrizableLCA.{0}} (hS : strictShortExact S) :
    PreservesColimit (parallelPair S.f 0) underlyingForgetfulFunctor :=
  (closedEmbeddingInput_of_strictShortExact hS).preservesCokernel

/-- The cokernel-topology input exposes the same closed embedding field. -/
def closedEmbeddingInput_of_cokernelTopStrictInput
    {S : ShortComplex MetrizableLCA.{0}} (hS : CokernelTopStrictInput S) :
    ClosedEmbeddingCokernelPreservationInput S.f where
  closed_embedding := hS.closed_embedding_f

/-- Cokernel-topology strict inputs preserve the cokernel of their left map after forgetting. -/
@[reducible] def preservesCokernelOf_cokernelTopStrictInput
    {S : ShortComplex MetrizableLCA.{0}} (hS : CokernelTopStrictInput S) :
    PreservesColimit (parallelPair S.f 0) underlyingForgetfulFunctor :=
  (closedEmbeddingInput_of_cokernelTopStrictInput hS).preservesCokernel

/-- Closed maps also expose the mapped explicit cokernel cocone as colimiting. -/
def mappedExplicitCokernelCoconeIsColimit_of_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap f hclosedMap)

/-- Closed embeddings also expose the mapped explicit cokernel cocone as colimiting. -/
def mappedExplicitCokernelCoconeIsColimit_of_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    IsColimit (mappedExplicitCokernelCocone f) :=
  mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq f
    (forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding f hclosedEmbedding)

/-- Checked summary for downstream audit scripts and review packets. -/
structure AddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  closedRangePreservationResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportState :
    AddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportState where
  seed := "fVbcdhalJGFoaIz6"
  checkedDeclarations :=
    ["mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq",
      "preservesCokernelOf_forgottenAlgebraicRange_eq",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding",
      "mappedExplicitCokernelCoconeIsColimit_of_isClosed_range",
      "mappedExplicitCokernelCoconeIsColimit_of_isClosedMap",
      "mappedExplicitCokernelCoconeIsColimit_of_isClosedEmbedding",
      "preservesCokernelOf_isClosed_range",
      "preservesCokernelOf_isClosedMap",
      "preservesCokernelOf_isClosedEmbedding",
      "ClosedEmbeddingCokernelPreservationInput.closed_range",
      "ClosedEmbeddingCokernelPreservationInput.closed_map",
      "ClosedEmbeddingCokernelPreservationInput.preservesCokernel",
      "ClosedEmbeddingCokernelPreservationInput.mappedExplicitCokernelCoconeIsColimit",
      "closedEmbeddingInput_of_strictShortExact",
      "preservesCokernelOf_strictShortExact",
      "closedEmbeddingInput_of_cokernelTopStrictInput",
      "preservesCokernelOf_cokernelTopStrictInput"]
  closedRangePreservationResult := "proved"
  remainingInputs := []
  productSuccessClaimed := false

theorem currentAddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportState_productSuccess :
    currentAddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check mappedExplicitCokernelCocone
#check mappedExplicitCokernelCoconeIsColimit_of_forgottenAlgebraicRange_eq
#check preservesCokernelOf_forgottenAlgebraicRange_eq
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding
#check mappedExplicitCokernelCoconeIsColimit_of_isClosed_range
#check mappedExplicitCokernelCoconeIsColimit_of_isClosedMap
#check mappedExplicitCokernelCoconeIsColimit_of_isClosedEmbedding
#check preservesCokernelOf_isClosed_range
#check preservesCokernelOf_isClosedMap
#check preservesCokernelOf_isClosedEmbedding
#check ClosedEmbeddingCokernelPreservationInput
#check ClosedEmbeddingCokernelPreservationInput.closed_range
#check ClosedEmbeddingCokernelPreservationInput.closed_map
#check ClosedEmbeddingCokernelPreservationInput.preservesCokernel
#check ClosedEmbeddingCokernelPreservationInput.mappedExplicitCokernelCoconeIsColimit
#check closedEmbeddingInput_of_strictShortExact
#check preservesCokernelOf_strictShortExact
#check closedEmbeddingInput_of_cokernelTopStrictInput
#check preservesCokernelOf_cokernelTopStrictInput
#check currentAddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportState
#check currentAddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportState_productSuccess

end Checks

end AddCommGrpClosedEmbeddingCokernelPreservationPackageV370SupportW448

end LeanLCAExactChallenge
