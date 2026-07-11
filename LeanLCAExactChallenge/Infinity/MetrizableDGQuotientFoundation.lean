import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModule
import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Object words for a corrected Drinfeld dg quotient

This file isolates the verified object-indexing part of a possible Drinfeld quotient of the dg
category of bounded metrizable complexes. A positive-length summand in a Drinfeld quotient Hom
complex is indexed by a finite word of objects in the dg subcategory being killed. Here that
subcategory is defined by the corrected cycle-object exact-acyclicity predicate.

No quotient carrier or localization claim is made in this file.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory

/-- Bounded metrizable complexes that the corrected derived localization must kill. -/
def CorrectedAcyclicObject : ObjectProperty ComplexCategory :=
  fun K ↦ exactAcyclicWithCycles MetrizableLCA.{0} K.obj

/-- The full dg-object subcategory to be killed by a corrected Drinfeld quotient. -/
abbrev CorrectedAcyclicComplexCategory : Type 1 :=
  CorrectedAcyclicObject.FullSubcategory

/-- A bar word indexing a summand of a Drinfeld quotient Hom complex from `X` to `Y`.

The `length` intermediate objects are required by their type to lie in the corrected acyclic
full subcategory. Length zero is the original, unlocalized Hom-complex summand.
-/
structure DrinfeldWord (X Y : ComplexCategory) where
  length : ℕ
  intermediate : Fin length → CorrectedAcyclicComplexCategory

namespace DrinfeldWord

open CategoryTheory.MonoidalCategory

/-- The length-zero word, indexing the original dg Hom complex. -/
def nil (X Y : ComplexCategory) : DrinfeldWord X Y where
  length := 0
  intermediate := Fin.elim0

/-- The one-letter word through a corrected acyclic object. -/
def singleton (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) :
    DrinfeldWord X Y where
  length := 1
  intermediate := fun _ ↦ A

/-- Concatenation of the intermediate-object words.  The endpoint parameters are phantom at
this indexing layer; they become relevant when the tensor factors of a quotient Hom summand
are attached. -/
def append {X Y Z : ComplexCategory} (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    DrinfeldWord X Z where
  length := w.length + v.length
  intermediate := Fin.addCases w.intermediate v.intermediate

/-- Remove one intermediate acyclic object.  These are the target words of the contraction
terms in the Drinfeld differential. -/
def eraseIntermediate {X Y : ComplexCategory} :
    (w : DrinfeldWord X Y) → Fin w.length → DrinfeldWord X Y
  | ⟨0, _⟩, i => Fin.elim0 i
  | ⟨k + 1, intermediate⟩, i =>
      { length := k
        intermediate := fun j ↦ intermediate (i.succAbove j) }

@[simp]
theorem eraseIntermediate_length {X Y : ComplexCategory}
    (w : DrinfeldWord X Y) (i : Fin w.length) :
    (eraseIntermediate w i).length + 1 = w.length := by
  cases w with
  | mk n intermediate =>
      cases n with
      | zero => exact Fin.elim0 i
      | succ k => rfl

@[simp]
theorem append_length {X Y Z : ComplexCategory}
    (w : DrinfeldWord X Y) (v : DrinfeldWord Y Z) :
    (w.append v).length = w.length + v.length :=
  rfl

@[simp]
theorem singleton_length (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory) :
    (singleton X Y A).length = 1 :=
  rfl

/-- The underlying bounded complex at an intermediate position. -/
def object {X Y : ComplexCategory} (w : DrinfeldWord X Y) (i : Fin w.length) :
    ComplexCategory :=
  (w.intermediate i).obj

/-- The ordered vertices of a word, including its source and target endpoints. -/
def vertex {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    Fin (w.length + 2) → ComplexCategory :=
  Fin.cases X (Fin.lastCases Y w.object)

/-- Source vertex of the `i`-th ordinary Hom factor in a word summand. -/
def arrowSource {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin (w.length + 1)) : ComplexCategory :=
  w.vertex i.castSucc

/-- Target vertex of the `i`-th ordinary Hom factor in a word summand. -/
def arrowTarget {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin (w.length + 1)) : ComplexCategory :=
  w.vertex i.succ

@[simp]
theorem vertex_zero {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    w.vertex 0 = X :=
  rfl

@[simp]
theorem vertex_last {X Y : ComplexCategory} (w : DrinfeldWord X Y) :
    w.vertex (Fin.last (w.length + 1)) = Y := by
  change Fin.lastCases Y w.object (Fin.last w.length) = Y
  simp

/-- Degree choices for the tensor factors of a Drinfeld word summand.  Each inserted
contracting generator has cohomological degree `-1`, hence the total quotient degree is the
sum of the ordinary Hom degrees minus the word length. -/
structure DegreeProfile {X Y : ComplexCategory} (w : DrinfeldWord X Y) (n : ℤ) where
  arrowDegree : Fin (w.length + 1) → ℤ
  totalDegree : (∑ i, arrowDegree i) - w.length = n

/-- Transport a degree profile along an equality of endpoint-compatible words. -/
def DegreeProfile.castWord {X Y : ComplexCategory} {w v : DrinfeldWord X Y}
    {n : ℤ} (h : w = v) (d : DegreeProfile w n) : DegreeProfile v n := by
  subst h
  exact d

/-- Degree profile of an internal-differential term: one ordinary Hom degree is raised by
one, so the total quotient degree is raised by one. -/
def DegreeProfile.raise {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) : DegreeProfile w (n + 1) where
  arrowDegree j := d.arrowDegree j + if j = i then 1 else 0
  totalDegree := by
    rw [Finset.sum_add_distrib]
    have hi : (∑ j : Fin (w.length + 1), if j = i then (1 : ℤ) else 0) = 1 := by
      simp
    rw [hi]
    have hd := d.totalDegree
    omega

/-- Merge the two ordinary Hom degrees adjacent to an intermediate object.  The chosen
`succAbove` enumeration omits the left factor and adds its degree to the surviving right
factor. -/
def contractedArrowDegree {k : ℕ} (a : Fin (k + 1) → ℤ) (i : Fin k) : Fin k → ℤ :=
  fun j ↦ a (i.castSucc.succAbove j) + if j = i then a i.castSucc else 0

theorem sum_contractedArrowDegree {k : ℕ} (a : Fin (k + 1) → ℤ) (i : Fin k) :
    ∑ j, contractedArrowDegree a i j = ∑ j, a j := by
  rw [show (∑ j, contractedArrowDegree a i j) =
      (∑ j, a (i.castSucc.succAbove j)) +
        ∑ j, (if j = i then a i.castSucc else 0) by
    simp only [contractedArrowDegree, Finset.sum_add_distrib]]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fin.sum_univ_succAbove a i.castSucc]
  exact add_comm _ _

/-- Degree profile of the contraction term at an intermediate object.  Merging two adjacent
ordinary Hom factors preserves their degree sum, while deleting one degree-`-1` contracting
generator raises the total quotient degree by one. -/
def DegreeProfile.contract {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin w.length) :
    DegreeProfile (eraseIntermediate w i) (n + 1) where
  arrowDegree j := contractedArrowDegree d.arrowDegree i
    (Fin.cast (eraseIntermediate_length w i) j)
  totalDegree := by
    have hs : (∑ j, contractedArrowDegree d.arrowDegree i
          (Fin.cast (eraseIntermediate_length w i) j)) =
        ∑ j, contractedArrowDegree d.arrowDegree i j := by
      apply Fintype.sum_equiv (finCongr (eraseIntermediate_length w i))
      intro j
      rfl
    rw [hs]
    rw [sum_contractedArrowDegree]
    have hd := d.totalDegree
    have hl := eraseIntermediate_length w i
    omega

/-- The ordinary Hom-cochain module attached to one arrow of a degree-profiled word. -/
def factorModule {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) : ModuleCat.{0} ℤ :=
  (dgHomZModuleCochainComplex (w.arrowSource i) (w.arrowTarget i)).X
    (d.arrowDegree i)

/-- The pointwise factor map contributing the internal differential at the chosen arrow;
all other tensor factors are identities. -/
def factorDifferential {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i j : Fin (w.length + 1)) :
    Quiver.Hom (factorModule d j) (factorModule (d.raise i) j) := by
  by_cases h : j = i
  · subst j
    simpa [factorModule, DegreeProfile.raise] using
      (dgHomZModuleCochainComplex (w.arrowSource i) (w.arrowTarget i)).d
        (d.arrowDegree i) (d.arrowDegree i + 1)
  · have hdeg : (d.raise i).arrowDegree j = d.arrowDegree j := by
      simp [DegreeProfile.raise, h]
    rw [factorModule, factorModule, hdeg]
    exact 𝟙 _

/-- Right-associated tensor product of a finite list of integer modules. -/
def tensorModuleList : List (ModuleCat.{0} ℤ) → ModuleCat.{0} ℤ
  | [] => 𝟙_ (ModuleCat.{0} ℤ)
  | M :: Ms => M ⊗ tensorModuleList Ms

/-- Pointwise morphisms between two lists of tensor factors. -/
inductive TensorMapData :
    (source target : List (ModuleCat.{0} ℤ)) → Type 1
  | nil : TensorMapData [] []
  | cons {M N : ModuleCat.{0} ℤ} {Ms Ns : List (ModuleCat.{0} ℤ)}
      (f : Quiver.Hom M N) (fs : TensorMapData Ms Ns) :
      TensorMapData (M :: Ms) (N :: Ns)

/-- Assemble pointwise maps indexed by a finite ordinal into tensor-map data. -/
def TensorMapData.ofFn : {k : ℕ} →
    (M N : Fin k → ModuleCat.{0} ℤ) →
    ((i : Fin k) → Quiver.Hom (M i) (N i)) →
    TensorMapData (List.ofFn M) (List.ofFn N)
  | 0, _, _, _ => .nil
  | k + 1, M, N, f => by
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons (f 0) (TensorMapData.ofFn
        (fun i : Fin k ↦ M i.succ) (fun i : Fin k ↦ N i.succ)
        (fun i ↦ f i.succ))

/-- Tensor a pointwise list of module morphisms. -/
def TensorMapData.tensorMap : {source target : List (ModuleCat.{0} ℤ)} →
    TensorMapData source target →
      Quiver.Hom (tensorModuleList source) (tensorModuleList target)
  | [], [], .nil =>
      (𝟙 (tensorModuleList []) :
        Quiver.Hom (tensorModuleList []) (tensorModuleList []))
  | M :: Ms, N :: Ns, @TensorMapData.cons _ _ _ _ f fs =>
      MonoidalCategoryStruct.tensorHom
        (C := ModuleCat.{0} ℤ)
        (X₁ := M) (Y₁ := N)
        (X₂ := tensorModuleList Ms) (Y₂ := tensorModuleList Ns)
        f fs.tensorMap

/-- Data for replacing two adjacent tensor factors by one factor. -/
inductive AdjacentMergeData :
    (source target : List (ModuleCat.{0} ℤ)) → Type 1
  | head {M N P : ModuleCat.{0} ℤ} {Ms : List (ModuleCat.{0} ℤ)}
      (f : Quiver.Hom (M ⊗ N) P) :
      AdjacentMergeData (M :: N :: Ms) (P :: Ms)
  | tail {M : ModuleCat.{0} ℤ} {Ms Ns : List (ModuleCat.{0} ℤ)}
      (f : AdjacentMergeData Ms Ns) :
      AdjacentMergeData (M :: Ms) (M :: Ns)

/-- Tensor morphism induced by an adjacent merge. -/
def AdjacentMergeData.tensorMap : {source target : List (ModuleCat.{0} ℤ)} →
    AdjacentMergeData source target →
      Quiver.Hom (tensorModuleList source) (tensorModuleList target)
  | _, _, @AdjacentMergeData.head M N P Ms f =>
      (α_ M N (tensorModuleList Ms)).inv ≫
        MonoidalCategoryStruct.tensorHom
          (C := ModuleCat.{0} ℤ)
          (X₁ := M ⊗ N) (Y₁ := P)
          (X₂ := tensorModuleList Ms) (Y₂ := tensorModuleList Ms)
          f (𝟙 _)
  | _, _, @AdjacentMergeData.tail M Ms Ns f =>
      MonoidalCategoryStruct.tensorHom
        (C := ModuleCat.{0} ℤ)
        (X₁ := M) (Y₁ := M)
        (X₂ := tensorModuleList Ms) (Y₂ := tensorModuleList Ns)
        (𝟙 _) f.tensorMap

/-- The tensor-product module belonging to one word and one compatible degree profile. -/
def summandModule {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) : ModuleCat.{0} ℤ :=
  tensorModuleList (List.ofFn (factorModule d))

/-- Transport of a word gives the corresponding canonical identification of tensor
summands. -/
def summandModuleCastWordIso {X Y : ComplexCategory} {w v : DrinfeldWord X Y}
    {n : ℤ} (h : w = v) (d : DegreeProfile w n) :
    summandModule d ≅ summandModule (d.castWord h) := by
  subst h
  exact Iso.refl _

/-- The length-zero word summand is canonically the original homogeneous Hom module. -/
def nilSummandIsoOriginal (X Y : ComplexCategory) {n : ℤ}
    (d : DegreeProfile (nil X Y) n) :
    summandModule d ≅ (dgHomZModuleCochainComplex X Y).X n := by
  have hdeg : d.arrowDegree 0 = n := by
    have hd := d.totalDegree
    rw [Fin.sum_univ_succ] at hd
    simpa [nil] using hd
  have hsource : (nil X Y).arrowSource 0 = X := rfl
  have htarget : (nil X Y).arrowTarget 0 = Y := by
    change (nil X Y).vertex (0 : Fin 1).succ = Y
    exact vertex_last (nil X Y)
  have hfactor : factorModule d 0 = (dgHomZModuleCochainComplex X Y).X n := by
    simp only [factorModule]
    rw [hsource, htarget, hdeg]
  exact (ρ_ (factorModule d 0)) ≪≫
    eqToIso hfactor

/-- Canonical degree profile on the zero-length word. -/
def nilDegreeProfile (X Y : ComplexCategory) (n : ℤ) :
    DegreeProfile (nil X Y) n where
  arrowDegree _ := n
  totalDegree := by simp [nil]

/-- Tensor map of an internal-differential summand before inserting the Koszul sign. -/
def internalDifferentialTensorMap {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) :
    Quiver.Hom (summandModule d) (summandModule (d.raise i)) :=
  (TensorMapData.ofFn (factorModule d) (factorModule (d.raise i))
    (factorDifferential d i)).tensorMap

/-- Index of a homogeneous summand of the corrected Drinfeld quotient. -/
abbrev GradedSummandIndex (X Y : ComplexCategory) (n : ℤ) :=
  Σ w : DrinfeldWord X Y, DegreeProfile w n

/-- A word summand lifted to the universe in which the family of all acyclic words is small. -/
def largeSummandModule {X Y : ComplexCategory} {n : ℤ}
    (s : GradedSummandIndex X Y n) : ModuleCat.{1} ℤ :=
  (ModuleCat.uliftFunctor.{1} ℤ).obj (summandModule s.2)

/-- The homogeneous carrier of the corrected Drinfeld quotient Hom complex.  This is the
actual coproduct over all acyclic words and all compatible allocations of ordinary Hom
degrees. -/
def quotientGradedModule (X Y : ComplexCategory) (n : ℤ) : ModuleCat.{1} ℤ :=
  ∐ fun s : GradedSummandIndex X Y n ↦ largeSummandModule s

/-- Inclusion of the original homogeneous Hom module as the zero-word summand of the
Drinfeld carrier (after the necessary universe lift). -/
def originalHomInclusion (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom
      ((ModuleCat.uliftFunctor.{1} ℤ).obj ((dgHomZModuleCochainComplex X Y).X n))
      (quotientGradedModule X Y n) :=
  (ModuleCat.uliftFunctor.{1} ℤ).map
      (nilSummandIsoOriginal X Y (nilDegreeProfile X Y n)).inv ≫
    Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y n ↦ largeSummandModule s)
      ⟨nil X Y, nilDegreeProfile X Y n⟩

/-- One internal-differential term, included into the degree-`n+1` coproduct carrier.  The
Koszul coefficient is deliberately kept separate from this unsigned structural map. -/
def internalDifferentialLargeMap {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y (n + 1)) :=
  (ModuleCat.uliftFunctor.{1} ℤ).map (internalDifferentialTensorMap d i) ≫
    Limits.Sigma.ι
      (fun s : GradedSummandIndex X Y (n + 1) ↦ largeSummandModule s)
      ⟨w, d.raise i⟩

/-- Total degree of the tensor entries strictly preceding an arrow factor, including one
degree-`-1` contracting symbol for every preceding intermediate object. -/
def DegreeProfile.prefixTotal {X Y : ComplexCategory} {w : DrinfeldWord X Y} {n : ℤ}
    (d : DegreeProfile w n) (i : Fin (w.length + 1)) : ℤ :=
  (∑ j ∈ Finset.univ.filter (fun j : Fin (w.length + 1) ↦ j < i), d.arrowDegree j) -
    i.val

/-- The Koszul sign of the internal differential on the `i`-th arrow factor. -/
def DegreeProfile.internalSign {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin (w.length + 1)) : ℤ :=
  if Even (d.prefixTotal i) then 1 else -1

/-- Koszul sign of the contraction at the `i`-th degree-`-1` symbol.  The symbol occurs
after the `i`-th arrow factor and after exactly `i` earlier contracting symbols. -/
def DegreeProfile.contractionSign {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n)
    (i : Fin w.length) : ℤ :=
  if Even
      ((∑ j ∈ Finset.univ.filter
          (fun j : Fin (w.length + 1) ↦ j.val ≤ i.val), d.arrowDegree j) - i.val)
    then 1 else -1

/-- Sum of all signed internal-differential terms leaving one homogeneous word summand. -/
def internalDifferentialFromSummand {X Y : ComplexCategory}
    {w : DrinfeldWord X Y} {n : ℤ} (d : DegreeProfile w n) :
    Quiver.Hom (largeSummandModule (⟨w, d⟩ : GradedSummandIndex X Y n))
      (quotientGradedModule X Y (n + 1)) :=
  ∑ i, d.internalSign i • internalDifferentialLargeMap d i

/-- The internal-Hom part of the Drinfeld differential on the whole coproduct carrier. -/
def quotientInternalDifferential (X Y : ComplexCategory) (n : ℤ) :
    Quiver.Hom (quotientGradedModule X Y n) (quotientGradedModule X Y (n + 1)) :=
  Limits.Sigma.desc fun s : GradedSummandIndex X Y n ↦
    internalDifferentialFromSummand s.2

@[reassoc (attr := simp)]
theorem quotientInternalDifferential_inclusion (X Y : ComplexCategory) (n : ℤ)
    (s : GradedSummandIndex X Y n) :
    Limits.Sigma.ι (fun t : GradedSummandIndex X Y n ↦ largeSummandModule t) s ≫
        quotientInternalDifferential X Y n =
      internalDifferentialFromSummand s.2 :=
  Limits.Sigma.ι_desc _ s

@[simp]
theorem singleton_object (X Y : ComplexCategory) (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton X Y A).length) : (singleton X Y A).object i = A.obj :=
  rfl

/-- Every intermediate object of a Drinfeld word is corrected exact-acyclic. -/
theorem object_exactAcyclicWithCycles {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (i : Fin w.length) :
    exactAcyclicWithCycles MetrizableLCA.{0} (w.object i).obj :=
  (w.intermediate i).property

/-- A word with no intermediate objects is uniquely the length-zero word. -/
theorem eq_nil_of_length_eq_zero {X Y : ComplexCategory} (w : DrinfeldWord X Y)
    (h : w.length = 0) : w = nil X Y := by
  cases w with
  | mk n intermediate =>
      change n = 0 at h
      subst n
      congr
      funext i
      exact Fin.elim0 i

@[simp]
theorem eraseIntermediate_singleton (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory)
    (i : Fin (singleton X Y A).length) :
    eraseIntermediate (singleton X Y A) i = nil X Y := by
  apply eq_nil_of_length_eq_zero
  rfl

/-- A contracted one-letter summand is canonically an original Hom summand in degree one
higher. -/
def singletonContractedSummandIsoOriginal (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    summandModule (d.contract i) ≅ (dgHomZModuleCochainComplex X Y).X (n + 1) :=
  let h := eraseIntermediate_singleton X Y A i
  summandModuleCastWordIso h (d.contract i) ≪≫
    nilSummandIsoOriginal X Y ((d.contract i).castWord h)

/-- Reassociate a one-letter word summand to the binary tensor on which homogeneous
composition is defined. -/
def singletonSummandIsoTensor (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n) :
    summandModule d ≅ factorModule d 0 ⊗ factorModule d 1 := by
  change factorModule d 0 ⊗ (factorModule d 1 ⊗ 𝟙_ (ModuleCat.{0} ℤ)) ≅ _
  exact (α_ (factorModule d 0) (factorModule d 1) (𝟙_ (ModuleCat.{0} ℤ))).symm ≪≫
    ρ_ (factorModule d 0 ⊗ factorModule d 1)

/-- The genuine contraction term for a one-letter word. -/
def singletonContractionTensorMap (X Y : ComplexCategory)
    (A : CorrectedAcyclicComplexCategory) {n : ℤ}
    (d : DegreeProfile (singleton X Y A) n)
    (i : Fin (singleton X Y A).length) :
    Quiver.Hom (summandModule d) (summandModule (d.contract i)) := by
  have hdeg : d.arrowDegree 0 + d.arrowDegree 1 = n + 1 := by
    have hd := d.totalDegree
    rw [Fin.sum_univ_succ] at hd
    have htail : (∑ j : Fin 1, d.arrowDegree j.succ) = d.arrowDegree 1 := by
      rw [Fin.sum_univ_succ]
      simp
      rfl
    change d.arrowDegree 0 + (∑ j : Fin 1, d.arrowDegree j.succ) - 1 = n at hd
    rw [htail] at hd
    omega
  have hs₀ : (singleton X Y A).arrowSource 0 = X := rfl
  have ht₀ : (singleton X Y A).arrowTarget 0 = A.obj := rfl
  have hs₁ : (singleton X Y A).arrowSource 1 = A.obj := rfl
  have ht₁ : (singleton X Y A).arrowTarget 1 = Y := by
    exact vertex_last (singleton X Y A)
  let f : Quiver.Hom (factorModule d 0 ⊗ factorModule d 1)
      ((dgHomZModuleCochainComplex X Y).X (n + 1)) := by
    simp only [factorModule]
    rw [hs₀, ht₀, hs₁, ht₁]
    exact dgCochainCompTensor X A.obj Y hdeg
  exact (singletonSummandIsoTensor X Y A d).hom ≫ f ≫
    (singletonContractedSummandIsoOriginal X Y A d i).inv

end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
