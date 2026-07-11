import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.LCA.ExactCategory
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Algebra.Group.OpenMapping

/-!
# Correct cycle-object exact acyclicity

This file isolates the corrected exact-category acyclicity predicate for cochain
complexes. The legacy predicate in `Derived.Bounded` is degreewise:

```lean
∀ i, QuillenExactCategory.Conflation (K.sc i)
```

That is too strong and is not the usual exact-category definition of an acyclic
complex. The replacement below records cycle objects `Z i`, conflations
`Z i ⟶ K.X i ⟶ Z (i + 1)`, and the factorization of the differential through
those cycle objects.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Category
open CategoryTheory.Limits
open HomologicalComplex
open scoped ZeroObject

universe w v u

namespace LeanLCAExactChallenge

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/--
Correct exact-category acyclicity data for a cochain complex.

For every degree `i`, there is a cycle object `Z i`, a conflation
`Z i ⟶ K.X i ⟶ Z (i + 1)`, and the differential factors as
`K.X i ⟶ Z (i + 1) ⟶ K.X (i + 1)`.
-/
structure ExactAcyclicWithCyclesData (K : CochainComplex C ℤ) where
  Z : ℤ → C
  incl : ∀ i : ℤ, Z i ⟶ K.X i
  proj : ∀ i : ℤ, K.X i ⟶ Z (i + 1)
  zero : ∀ i : ℤ, incl i ≫ proj i = 0
  conflation : ∀ i : ℤ,
    QuillenExactCategory.Conflation (ShortComplex.mk (incl i) (proj i) (zero i))
  d_eq : ∀ i : ℤ, proj i ≫ incl (i + 1) = K.d i (i + 1)

/-- The corrected acyclicity predicate, named as a predicate rather than as data. -/
def exactAcyclicWithCycles (K : CochainComplex C ℤ) : Prop :=
  Nonempty (ExactAcyclicWithCyclesData C K)

namespace ExactAcyclicWithCyclesData

variable {C}
variable {K : CochainComplex C ℤ}

/-- The actual short complex whose conflation is required in degree `i`. -/
def shortComplex (h : ExactAcyclicWithCyclesData C K) (i : ℤ) : ShortComplex C :=
  ShortComplex.mk (h.incl i) (h.proj i) (h.zero i)

@[simp]
theorem shortComplex_f (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    (h.shortComplex i).f = h.incl i := rfl

@[simp]
theorem shortComplex_g (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    (h.shortComplex i).g = h.proj i := rfl

/-- The corrected predicate gives a conflation in each cycle-object degree. -/
theorem conflation_shortComplex (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    QuillenExactCategory.Conflation (h.shortComplex i) :=
  h.conflation i

/-- The differential factors through the next cycle object. -/
theorem differential_factors (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    h.proj i ≫ h.incl (i + 1) = K.d i (i + 1) :=
  h.d_eq i

/-- The cycle inclusion of the corrected data is an inflation. -/
theorem inflation_incl (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    QuillenExactCategory.inflation (h.incl i) :=
  ⟨h.Z (i + 1), h.proj i, h.zero i, h.conflation i⟩

/-- The cycle projection of the corrected data is a deflation. -/
theorem deflation_proj (h : ExactAcyclicWithCyclesData C K) (i : ℤ) :
    QuillenExactCategory.deflation (h.proj i) :=
  ⟨h.Z i, h.incl i, h.zero i, h.conflation i⟩

omit [QuillenExactCategory C] in
/-- Componentwise `hom ≫ inv` cancellation for an isomorphism of cochain complexes. -/
theorem hom_f_inv_f {K L : CochainComplex C ℤ} (e : K ≅ L) (i : ℤ) :
    e.hom.f i ≫ e.inv.f i = 𝟙 (K.X i) := by
  rw [← HomologicalComplex.comp_f, e.hom_inv_id, HomologicalComplex.id_f]

omit [QuillenExactCategory C] in
/-- Componentwise `inv ≫ hom` cancellation for an isomorphism of cochain complexes. -/
theorem inv_f_hom_f {K L : CochainComplex C ℤ} (e : K ≅ L) (i : ℤ) :
    e.inv.f i ≫ e.hom.f i = 𝟙 (L.X i) := by
  rw [← HomologicalComplex.comp_f, e.inv_hom_id, HomologicalComplex.id_f]

/-- Transport corrected cycle-object acyclicity data along an isomorphism of
cochain complexes. The cycle objects stay the same; the structure maps are
conjugated by the componentwise isomorphisms. -/
@[simps Z incl proj]
def ofIso {K L : CochainComplex C ℤ} (h : ExactAcyclicWithCyclesData C K)
    (e : K ≅ L) : ExactAcyclicWithCyclesData C L where
  Z := h.Z
  incl i := h.incl i ≫ e.hom.f i
  proj i := e.inv.f i ≫ h.proj i
  zero i := by
    calc (h.incl i ≫ e.hom.f i) ≫ e.inv.f i ≫ h.proj i
        = h.incl i ≫ (e.hom.f i ≫ e.inv.f i) ≫ h.proj i := by
          simp only [Category.assoc]
      _ = h.incl i ≫ h.proj i := by rw [hom_f_inv_f, Category.id_comp]
      _ = 0 := h.zero i
  conflation i := by
    have hzero : (h.incl i ≫ e.hom.f i) ≫ e.inv.f i ≫ h.proj i = 0 := by
      calc (h.incl i ≫ e.hom.f i) ≫ e.inv.f i ≫ h.proj i
          = h.incl i ≫ (e.hom.f i ≫ e.inv.f i) ≫ h.proj i := by
            simp only [Category.assoc]
        _ = h.incl i ≫ h.proj i := by rw [hom_f_inv_f, Category.id_comp]
        _ = 0 := h.zero i
    have eiso : ShortComplex.mk (h.incl i) (h.proj i) (h.zero i) ≅
        ShortComplex.mk (h.incl i ≫ e.hom.f i) (e.inv.f i ≫ h.proj i) hzero :=
      ShortComplex.isoMk (Iso.refl _)
        ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).mapIso e)
        (Iso.refl _)
        (by dsimp; simp only [Category.id_comp])
        (by
          dsimp
          rw [Category.comp_id, ← Category.assoc, hom_f_inv_f, Category.id_comp])
    exact QuillenExactCategory.conflation_iso_transport eiso (h.conflation i)
  d_eq i := by
    calc (e.inv.f i ≫ h.proj i) ≫ h.incl (i + 1) ≫ e.hom.f (i + 1)
        = e.inv.f i ≫ (h.proj i ≫ h.incl (i + 1)) ≫ e.hom.f (i + 1) := by
          simp only [Category.assoc]
      _ = e.inv.f i ≫ K.d i (i + 1) ≫ e.hom.f (i + 1) := by rw [h.d_eq i]
      _ = e.inv.f i ≫ e.hom.f i ≫ L.d i (i + 1) := by
          rw [← e.hom.comm i (i + 1)]
      _ = L.d i (i + 1) := by rw [← Category.assoc, inv_f_hom_f, Category.id_comp]

/-- Transport corrected cycle data along the cochain shift `⟦n⟧`.

The cycle objects are reindexed by `n`; the projection absorbs the sign
`n.negOnePow` carried by the shifted differential, together with the
`eqToHom` transport identifying `Z (i + n + 1)` with `Z (i + 1 + n)`. -/
def shift {K : CochainComplex C ℤ} (h : ExactAcyclicWithCyclesData C K) (n : ℤ) :
    ExactAcyclicWithCyclesData C (K⟦n⟧) where
  Z i := h.Z (i + n)
  incl i := h.incl (i + n)
  proj i := n.negOnePow •
    (h.proj (i + n) ≫ eqToHom (congrArg h.Z (show i + n + 1 = i + 1 + n by omega)))
  zero i := by
    show h.incl (i + n) ≫
        (n.negOnePow • (h.proj (i + n) ≫
          eqToHom (congrArg h.Z (show i + n + 1 = i + 1 + n by omega)))) = 0
    rw [Linear.comp_units_smul, ← Category.assoc, h.zero (i + n), zero_comp, smul_zero]
  conflation i := by
    have hj : i + n + 1 = i + 1 + n := by omega
    have hzero : h.incl (i + n) ≫
        (n.negOnePow • (h.proj (i + n) ≫ eqToHom (congrArg h.Z hj))) = 0 := by
      rw [Linear.comp_units_smul, ← Category.assoc, h.zero (i + n), zero_comp, smul_zero]
    have eiso : ShortComplex.mk (h.incl (i + n)) (h.proj (i + n)) (h.zero (i + n)) ≅
        ShortComplex.mk (h.incl (i + n))
          (n.negOnePow • (h.proj (i + n) ≫ eqToHom (congrArg h.Z hj))) hzero :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
        ⟨n.negOnePow • eqToHom (congrArg h.Z hj),
          n.negOnePow • eqToHom (congrArg h.Z hj.symm),
          by
            simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
              Int.units_mul_self, eqToHom_trans, eqToHom_refl, one_smul],
          by
            simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
              Int.units_mul_self, eqToHom_trans, eqToHom_refl, one_smul]⟩
        (by simp)
        (by
          dsimp
          rw [Category.id_comp, Linear.comp_units_smul])
    exact QuillenExactCategory.conflation_iso_transport eiso (h.conflation (i + n))
  d_eq i := by
    show (n.negOnePow • (h.proj (i + n) ≫
        eqToHom (congrArg h.Z (show i + n + 1 = i + 1 + n by omega)))) ≫
          h.incl (i + 1 + n) =
      n.negOnePow • K.d (i + n) (i + 1 + n)
    have key : ∀ (m : ℤ) (hm : i + n + 1 = m),
        (h.proj (i + n) ≫ eqToHom (congrArg h.Z hm)) ≫ h.incl m = K.d (i + n) m := by
      rintro m rfl
      rw [eqToHom_refl, Category.comp_id, h.d_eq (i + n)]
    rw [Linear.units_smul_comp, key (i + 1 + n) (by omega)]

end ExactAcyclicWithCyclesData

/-- Any witness of corrected cycle-object data yields the corrected predicate. -/
theorem exactAcyclicWithCycles_of_data {K : CochainComplex C ℤ}
    (h : ExactAcyclicWithCyclesData C K) : exactAcyclicWithCycles C K :=
  ⟨h⟩

/-- The corrected cycle-object acyclicity predicate is invariant under
isomorphism of cochain complexes. -/
theorem exactAcyclicWithCycles_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L)
    (hK : exactAcyclicWithCycles C K) : exactAcyclicWithCycles C L := by
  obtain ⟨h⟩ := hK
  exact ⟨h.ofIso e⟩

/-- Isomorphic cochain complexes agree on the corrected acyclicity predicate. -/
theorem exactAcyclicWithCycles_iff_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L) :
    exactAcyclicWithCycles C K ↔ exactAcyclicWithCycles C L :=
  ⟨exactAcyclicWithCycles_of_iso C e, exactAcyclicWithCycles_of_iso C e.symm⟩

/-- The zero complex satisfies the corrected cycle-object acyclicity predicate. -/
theorem exactAcyclicWithCycles_zero [HasZeroObject C] :
    exactAcyclicWithCycles C (0 : CochainComplex C ℤ) := by
  refine ⟨{ Z := fun _ => 0
            incl := fun _ => 0
            proj := fun _ => 0
            zero := fun _ => zero_comp
            conflation := fun i => ?_
            d_eq := fun i => ?_ }⟩
  · apply QuillenExactCategory.split_conflation
    refine { r := 0, s := 0, f_r := ?_, s_g := ?_, id := ?_ }
    · exact (isZero_zero C).eq_of_src _ _
    · exact (isZero_zero C).eq_of_src _ _
    · apply (Functor.map_isZero
        (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
        (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))).eq_of_src
  · apply (Functor.map_isZero
      (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
      (isZero_zero (CochainComplex C ℤ) : IsZero (0 : CochainComplex C ℤ))).eq_of_src

/-- Cycle-object acyclicity of mapping cones is invariant under isomorphic
commutative squares. This is the corrected analogue of
`exactAcyclic_mappingCone_congr_iff`. -/
theorem exactAcyclicWithCycles_mappingCone_congr_iff [HasBinaryBiproducts C]
    {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
    (eK : K₁ ≅ K₂) (eL : L₁ ≅ L₂)
    (comm : φ₁ ≫ eL.hom = eK.hom ≫ φ₂) :
    exactAcyclicWithCycles C (CochainComplex.mappingCone φ₁) ↔
      exactAcyclicWithCycles C (CochainComplex.mappingCone φ₂) :=
  exactAcyclicWithCycles_iff_of_iso C (mappingConeIsoOfCommIso C eK eL comm)

/-- Corrected cycle-object acyclicity is stable under cochain shifts. -/
theorem exactAcyclicWithCycles_shift (K : CochainComplex C ℤ) (n : ℤ)
    (hK : exactAcyclicWithCycles C K) : exactAcyclicWithCycles C (K⟦n⟧) := by
  obtain ⟨h⟩ := hK
  exact ⟨h.shift n⟩

/-- Corrected cycle-object acyclicity is invariant under cochain shifts. -/
theorem exactAcyclicWithCycles_shift_iff (K : CochainComplex C ℤ) (n : ℤ) :
    exactAcyclicWithCycles C (K⟦n⟧) ↔ exactAcyclicWithCycles C K := by
  constructor
  · intro hK
    have hShift : exactAcyclicWithCycles C ((K⟦n⟧)⟦-n⟧) :=
      exactAcyclicWithCycles_shift C (K⟦n⟧) (-n) hK
    exact exactAcyclicWithCycles_of_iso C
      ((shiftEquiv (CochainComplex C ℤ) n).unitIso.app K).symm hShift
  · exact exactAcyclicWithCycles_shift C K n

/-- Corrected acyclicity of mapping cones is invariant under cochain shifts.
This is the corrected analogue of `exactAcyclic_mappingCone_shift_iff`. -/
theorem exactAcyclicWithCycles_mappingCone_shift_iff [HasBinaryBiproducts C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    exactAcyclicWithCycles C (CochainComplex.mappingCone (f⟦n⟧')) ↔
      exactAcyclicWithCycles C (CochainComplex.mappingCone f) := by
  constructor
  · intro hf
    have hShift : exactAcyclicWithCycles C ((CochainComplex.mappingCone f)⟦n⟧) :=
      exactAcyclicWithCycles_of_iso C (CochainComplex.mappingCone.shiftIso f n).symm hf
    exact (exactAcyclicWithCycles_shift_iff C (CochainComplex.mappingCone f) n).1 hShift
  · intro hf
    exact exactAcyclicWithCycles_of_iso C (CochainComplex.mappingCone.shiftIso f n)
      (exactAcyclicWithCycles_shift C (CochainComplex.mappingCone f) n hf)

/--
The legacy predicate from `Derived.Bounded`, given a descriptive name.
This is retained only to make the distinction explicit in later refactors.
-/
def degreewiseConflationAcyclic (K : CochainComplex C ℤ) : Prop :=
  ∀ i : ℤ, QuillenExactCategory.Conflation (K.sc i)

/-- The descriptive legacy name is definitionally the old `exactAcyclic`. -/
theorem degreewiseConflationAcyclic_eq_legacy (K : CochainComplex C ℤ) :
    degreewiseConflationAcyclic C K = exactAcyclic C K :=
  rfl

/--
Corrected weak equivalences for bounded complexes: the mapping cone is acyclic
in the cycle-object exact-category sense.
-/
def boundedExactWeakEquivalenceWithCycles [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C) :=
  fun _K _L f =>
    exactAcyclicWithCycles C
      (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f))

set_option linter.unusedVariables false in
@[simp]
theorem boundedExactWeakEquivalenceWithCycles_iff
    [HasBinaryBiproducts C]
    {K L : BoundedComplexCategory C} (f : K ⟶ L) :
    boundedExactWeakEquivalenceWithCycles C f ↔
      exactAcyclicWithCycles C
        (CochainComplex.mappingCone ((BoundedComplexCategory.ι C).map f)) :=
  Iff.rfl

namespace MetrizableLCA

/--
The corrected acyclicity predicate specialized to metrizable locally compact
abelian groups.
-/
abbrev challengeExactAcyclicWithCycles
    (K : CochainComplex MetrizableLCA.{u} ℤ) : Prop :=
  exactAcyclicWithCycles MetrizableLCA K

/-- The challenge's concrete exact-sequence predicate is strict short exactness
for metrizable LCA groups. -/
abbrev challengeExactSequence (S : ShortComplex MetrizableLCA.{u}) : Prop :=
  strictShortExact S

/-- Canonical Quillen conflations are exactly the challenge exact sequences. -/
theorem quillenConflation_iff_challengeExactSequence {S : ShortComplex MetrizableLCA.{u}} :
    QuillenExactCategory.Conflation S ↔ challengeExactSequence S :=
  quillenConflation_iff_strictShortExact

/--
For `MetrizableLCA`, the corrected predicate is exactly the existence of cycle
objects whose degreewise cycle short complexes satisfy `challengeExactSequence`,
and through which the complex differential factors.
-/
theorem exactAcyclicWithCycles_iff_challengeCycleExactSequences
    (K : CochainComplex MetrizableLCA.{u} ℤ) :
    exactAcyclicWithCycles MetrizableLCA K ↔
      ∃ (Z : ℤ → MetrizableLCA.{u})
        (incl : ∀ i : ℤ, Z i ⟶ K.X i)
        (proj : ∀ i : ℤ, K.X i ⟶ Z (i + 1))
        (zero : ∀ i : ℤ, incl i ≫ proj i = 0),
          (∀ i : ℤ,
            challengeExactSequence
              (ShortComplex.mk (incl i) (proj i) (zero i))) ∧
          (∀ i : ℤ, proj i ≫ incl (i + 1) = K.d i (i + 1)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.Z, h.incl, h.proj, h.zero,
      (fun i => (quillenConflation_iff_challengeExactSequence).1 (h.conflation i)),
      h.d_eq⟩
  · rintro ⟨Z, incl, proj, zero, hExact, hDiff⟩
    exact ⟨
      { Z := Z
        incl := incl
        proj := proj
        zero := zero
        conflation := fun i =>
          (quillenConflation_iff_challengeExactSequence).2 (hExact i)
        d_eq := hDiff }⟩

/--
The corrected mapping-cone weak equivalence for bounded complexes in
`MetrizableLCA`.
-/
def boundedExactWeakEquivalenceWithCycles :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{u}) :=
  LeanLCAExactChallenge.boundedExactWeakEquivalenceWithCycles MetrizableLCA

/-- The corrected metrizable predicate transports across isomorphisms of
cochain complexes. -/
theorem challengeExactAcyclicWithCycles_of_iso
    {K L : CochainComplex MetrizableLCA.{u} ℤ} (e : K ≅ L)
    (hK : challengeExactAcyclicWithCycles K) :
    challengeExactAcyclicWithCycles L :=
  exactAcyclicWithCycles_of_iso MetrizableLCA e hK

/-- The cycle short complexes of corrected metrizable data are strict short
exact sequences. -/
theorem strictShortExact_shortComplex_of_cyclesData
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (h : ExactAcyclicWithCyclesData MetrizableLCA.{u} K) (i : ℤ) :
    strictShortExact (h.shortComplex i) :=
  strictShortExact_of_quillenConflation (h.conflation i)

/-- The cycle short complexes of corrected metrizable data satisfy the
challenge exact-sequence predicate. -/
theorem challengeExactSequence_shortComplex_of_cyclesData
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (h : ExactAcyclicWithCyclesData MetrizableLCA.{u} K) (i : ℤ) :
    challengeExactSequence (h.shortComplex i) :=
  (quillenConflation_iff_challengeExactSequence).1 (h.conflation i)

lemma cyclesData_proj_eqToHom_comp_incl
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (h : ExactAcyclicWithCyclesData MetrizableLCA.{u} K) {j i : ℤ} (hji : j + 1 = i) :
    (h.proj j ≫ eqToHom (congrArg h.Z hji)) ≫ h.incl i = K.d j i := by
  subst i
  simpa using h.d_eq j

noncomputable def cyclesData_incl_kernel_d
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (h : ExactAcyclicWithCyclesData MetrizableLCA.{u} K) (i : ℤ) :
    IsLimit (KernelFork.ofι (h.incl i) (f := K.d i (i + 1)) (by
      rw [← h.d_eq i]
      simpa [Category.assoc] using congrArg (fun q => q ≫ h.incl (i + 1)) (h.zero i))) := by
  have hker : IsLimit (KernelFork.ofι (h.incl i) (f := h.proj i) (h.zero i)) :=
    kernelForkOfQuillenConflation (h.conflation i)
  haveI : Mono (h.incl (i + 1)) :=
    mono_of_isLimit_fork (kernelForkOfQuillenConflation (h.conflation (i + 1)))
  exact isKernelCompMono hker (h.incl (i + 1)) (h.d_eq i).symm

lemma cyclesDataMap_condition
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (f : K ⟶ L) (i : ℤ) :
    (hK.incl i ≫ f.f i) ≫ L.d i (i + 1) = 0 := by
  calc
    (hK.incl i ≫ f.f i) ≫ L.d i (i + 1) =
        hK.incl i ≫ (f.f i ≫ L.d i (i + 1)) := Category.assoc _ _ _
    _ = hK.incl i ≫ (K.d i (i + 1) ≫ f.f (i + 1)) := by rw [f.comm]
    _ = (hK.incl i ≫ K.d i (i + 1)) ≫ f.f (i + 1) := by
      rw [Category.assoc]
    _ = (hK.incl i ≫ (hK.proj i ≫ hK.incl (i + 1))) ≫ f.f (i + 1) := by
      rw [hK.d_eq]
    _ = ((hK.incl i ≫ hK.proj i) ≫ hK.incl (i + 1)) ≫ f.f (i + 1) := by
      simp only [Category.assoc]
    _ = 0 := by rw [hK.zero, zero_comp, zero_comp]

/-- A cochain map induces a map between any chosen corrected cycle objects. -/
noncomputable def cyclesDataMap
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    hK.Z i ⟶ hL.Z i :=
  (cyclesData_incl_kernel_d hL i).lift
    (KernelFork.ofι (hK.incl i ≫ f.f i) (cyclesDataMap_condition hK f i))

@[reassoc]
theorem cyclesDataMap_incl
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    cyclesDataMap hK hL f i ≫ hL.incl i = hK.incl i ≫ f.f i := by
  exact (cyclesData_incl_kernel_d hL i).fac
    (KernelFork.ofι (hK.incl i ≫ f.f i) (cyclesDataMap_condition hK f i))
    WalkingParallelPair.zero

@[reassoc]
theorem cyclesData_proj_map
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    hK.proj i ≫ cyclesDataMap hK hL f (i + 1) = f.f i ≫ hL.proj i := by
  haveI : Mono (hL.incl (i + 1)) :=
    mono_of_isLimit_fork (kernelForkOfQuillenConflation (hL.conflation (i + 1)))
  apply (cancel_mono (hL.incl (i + 1))).1
  calc
    (hK.proj i ≫ cyclesDataMap hK hL f (i + 1)) ≫ hL.incl (i + 1) =
        hK.proj i ≫ (hK.incl (i + 1) ≫ f.f (i + 1)) := by
      rw [Category.assoc, cyclesDataMap_incl]
    _ = (hK.proj i ≫ hK.incl (i + 1)) ≫ f.f (i + 1) := by
      simp only [Category.assoc]
    _ = K.d i (i + 1) ≫ f.f (i + 1) := by rw [hK.d_eq]
    _ = f.f i ≫ L.d i (i + 1) := (f.comm i (i + 1)).symm
    _ = f.f i ≫ (hL.proj i ≫ hL.incl (i + 1)) := by rw [hL.d_eq]
    _ = (f.f i ≫ hL.proj i) ≫ hL.incl (i + 1) := by rw [Category.assoc]

/-- The canonical cycle object for the mapping cone of a map between corrected
acyclic complexes. It is the pullback of the target cycle projection along the
negative of the induced map on cycle objects. -/
noncomputable abbrev mappingConeCyclesObj
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) : MetrizableLCA.{u} :=
  pullback (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i)

/-- The canonical cone-cycle inclusion, written in the two mapping-cone
coordinates. -/
noncomputable def mappingConeCyclesIncl
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesObj hK hL f i ⟶ (CochainComplex.mappingCone f).X i :=
  pullback.fst (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
      hK.incl (i + 1) ≫
        (CochainComplex.mappingCone.inl f).v (i + 1) i (by omega) +
    pullback.snd (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
      (CochainComplex.mappingCone.inr f).f i

@[reassoc]
lemma mappingConeCyclesIncl_fst
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesIncl hK hL f i ≫
        (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl =
      pullback.fst (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
        hK.incl (i + 1) := by
  simp [mappingConeCyclesIncl]

@[reassoc]
lemma mappingConeCyclesIncl_snd
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesIncl hK hL f i ≫
        (CochainComplex.mappingCone.snd f).v i i (add_zero i) =
      pullback.snd (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) := by
  simp [mappingConeCyclesIncl]

lemma mappingConeCyclesProj_condition
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    (-(CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫
          hK.proj (i + 1)) ≫
        (-(cyclesDataMap hK hL f (i + 1 + 1))) =
      ((CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫
            f.f (i + 1) +
          (CochainComplex.mappingCone.snd f).v i i (add_zero i) ≫
            L.d i (i + 1)) ≫
        hL.proj (i + 1) := by
  calc
    (-(CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫
          hK.proj (i + 1)) ≫
        (-(cyclesDataMap hK hL f (i + 1 + 1))) =
      (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫
        (hK.proj (i + 1) ≫ cyclesDataMap hK hL f (i + 1 + 1)) := by
          simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
            Category.assoc]
    _ = (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫
        (f.f (i + 1) ≫ hL.proj (i + 1)) := by
          rw [cyclesData_proj_map]
    _ = ((CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫
            f.f (i + 1) +
          (CochainComplex.mappingCone.snd f).v i i (add_zero i) ≫
            L.d i (i + 1)) ≫
        hL.proj (i + 1) := by
          have hzero : L.d i (i + 1) ≫ hL.proj (i + 1) = 0 := by
            rw [← hL.d_eq i, Category.assoc, hL.zero, comp_zero]
          rw [Preadditive.add_comp]
          simp [Category.assoc, hzero]

/-- The canonical cone-cycle projection, specified by its two pullback
coordinates. -/
noncomputable def mappingConeCyclesProj
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    (CochainComplex.mappingCone f).X i ⟶ mappingConeCyclesObj hK hL f (i + 1) :=
  pullback.lift
    (-(CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫ hK.proj (i + 1))
    ((CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫ f.f (i + 1) +
      (CochainComplex.mappingCone.snd f).v i i (add_zero i) ≫ L.d i (i + 1))
    (mappingConeCyclesProj_condition hK hL f i)

@[reassoc]
lemma mappingConeCyclesProj_fst
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesProj hK hL f i ≫
        pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      -(CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫
        hK.proj (i + 1) := by
  exact pullback.lift_fst _ _ _

@[reassoc]
lemma mappingConeCyclesProj_snd
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesProj hK hL f i ≫
        pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl ≫ f.f (i + 1) +
        (CochainComplex.mappingCone.snd f).v i i (add_zero i) ≫ L.d i (i + 1) := by
  exact pullback.lift_snd _ _ _

lemma mappingConeCyclesSourceLift_condition
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    (-hK.proj (i + 1)) ≫ (-(cyclesDataMap hK hL f (i + 1 + 1))) =
      f.f (i + 1) ≫ hL.proj (i + 1) := by
  simpa only [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg] using
    cyclesData_proj_map hK hL f (i + 1)

/-- The source-coordinate map into the next cone-cycle pullback. -/
noncomputable def mappingConeCyclesSourceLift
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    K.X (i + 1) ⟶ mappingConeCyclesObj hK hL f (i + 1) :=
  pullback.lift (-hK.proj (i + 1)) (f.f (i + 1))
    (mappingConeCyclesSourceLift_condition hK hL f i)

@[reassoc (attr := simp)]
lemma mappingConeCyclesSourceLift_fst
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSourceLift hK hL f i ≫
        pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      -hK.proj (i + 1) := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mappingConeCyclesSourceLift_snd
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSourceLift hK hL f i ≫
        pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      f.f (i + 1) := by
  exact pullback.lift_snd _ _ _

lemma mappingConeCyclesTargetLift_condition
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    (0 : hL.Z (i + 1) ⟶ hK.Z (i + 1 + 1)) ≫
        (-(cyclesDataMap hK hL f (i + 1 + 1))) =
      hL.incl (i + 1) ≫ hL.proj (i + 1) := by
  rw [zero_comp, hL.zero]

/-- The target-cycle-coordinate map into the next cone-cycle pullback. -/
noncomputable def mappingConeCyclesTargetLift
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    hL.Z (i + 1) ⟶ mappingConeCyclesObj hK hL f (i + 1) :=
  pullback.lift 0 (hL.incl (i + 1))
    (mappingConeCyclesTargetLift_condition hK hL f i)

@[reassoc (attr := simp)]
lemma mappingConeCyclesTargetLift_fst
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesTargetLift hK hL f i ≫
        pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      0 := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mappingConeCyclesTargetLift_snd
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesTargetLift hK hL f i ≫
        pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      hL.incl (i + 1) := by
  exact pullback.lift_snd _ _ _

/-- The second factor of the cone-cycle projection. It sends the source
coordinate and the quotient target-cycle coordinate into the next pullback. -/
noncomputable def mappingConeCyclesSecondFactor
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    K.X (i + 1) ⊞ hL.Z (i + 1) ⟶ mappingConeCyclesObj hK hL f (i + 1) :=
  biprod.desc
    (mappingConeCyclesSourceLift hK hL f i)
    (mappingConeCyclesTargetLift hK hL f i)

@[reassoc]
lemma mappingConeCyclesSecondFactor_fst
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondFactor hK hL f i ≫
        pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      biprod.fst ≫ (-hK.proj (i + 1)) := by
  simp [mappingConeCyclesSecondFactor, biprod.desc_eq, Category.assoc]

@[reassoc]
lemma mappingConeCyclesSecondFactor_snd
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondFactor hK hL f i ≫
        pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) =
      biprod.fst ≫ f.f (i + 1) + biprod.snd ≫ hL.incl (i + 1) := by
  simp [mappingConeCyclesSecondFactor, biprod.desc_eq, Category.assoc]

/-- The first factor of the cone-cycle projection: retain the source coordinate
and quotient the target coordinate onto its next cycle object. -/
noncomputable def mappingConeCyclesFirstFactor
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    (CochainComplex.mappingCone f).X i ⟶ K.X (i + 1) ⊞ hL.Z (i + 1) :=
  biprod.lift
    ((CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl)
    ((CochainComplex.mappingCone.snd f).v i i (add_zero i) ≫ hL.proj i)

/-- The biproduct of an identity with a corrected cycle projection is a
deflation. This is the strict-exact input for the first cone-projection factor. -/
theorem biprod_id_cyclesDataProj_deflation
    {L : CochainComplex MetrizableLCA.{u} ℤ}
    (X : MetrizableLCA.{u})
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L) (i : ℤ) :
    QuillenExactCategory.deflation (biprod.map (𝟙 X) (hL.proj i)) := by
  let S₀ : ShortComplex MetrizableLCA.{u} :=
    ShortComplex.mk (0 : (0 : MetrizableLCA.{u}) ⟶ X) (𝟙 X) (by simp)
  have hsplit : S₀.Splitting :=
    { r := 0
      s := 𝟙 X
      f_r := by
        apply Subsingleton.elim
      s_g := by
        simp [S₀]
      id := by
        simp [S₀] }
  have hS₀ : strictShortExact S₀ :=
    strictShortExact_of_quillenConflation
      (QuillenExactCategory.conflation_of_splitting S₀ hsplit)
  let S := strictShortExactBiprodComplex S₀ (hL.shortComplex i)
  have hS : strictShortExact S :=
    strictShortExact_biprod hS₀ (strictShortExact_shortComplex_of_cyclesData hL i)
  let e₂ : biprodObj X (L.X i) ≅ X ⊞ L.X i := biprodObjIsoBiprod X (L.X i)
  let e₃ : biprodObj X (hL.Z (i + 1)) ≅ X ⊞ hL.Z (i + 1) :=
    biprodObjIsoBiprod X (hL.Z (i + 1))
  have hnat :
      e₂.hom ≫ biprod.map (𝟙 X) (hL.proj i) =
        biprodMap (𝟙 X) (hL.proj i) ≫ e₃.hom := by
    dsimp [e₂, e₃]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst, biprodMap_biprodFst,
        biprodObjIsoBiprod_hom_fst]
      rw [← Category.assoc, biprodObjIsoBiprod_hom_fst]
    · simp only [Category.assoc, biprod.map_snd, biprodMap_biprodSnd,
        biprodObjIsoBiprod_hom_snd]
      rw [← Category.assoc, biprodObjIsoBiprod_hom_snd]
  let f' : S.X₁ ⟶ X ⊞ L.X i := S.f ≫ e₂.hom
  have zero' : f' ≫ biprod.map (𝟙 X) (hL.proj i) = 0 := by
    calc
      f' ≫ biprod.map (𝟙 X) (hL.proj i) =
          S.f ≫ (e₂.hom ≫ biprod.map (𝟙 X) (hL.proj i)) := by
            simp [f', Category.assoc]
      _ = S.f ≫ (S.g ≫ e₃.hom) := by
        simpa [S, S₀, strictShortExactBiprodComplex, Category.assoc] using
          congrArg (fun q => S.f ≫ q) hnat
      _ = (S.f ≫ S.g) ≫ e₃.hom := by rw [Category.assoc]
      _ = 0 := by rw [S.zero, zero_comp]
  let T : ShortComplex MetrizableLCA.{u} :=
    ShortComplex.mk f' (biprod.map (𝟙 X) (hL.proj i)) zero'
  let e : S ≅ T :=
    ShortComplex.isoMk (Iso.refl S.X₁) e₂ e₃
      (by simp [T, f'])
      (by
        dsimp [T, S, S₀, strictShortExactBiprodComplex]
        exact hnat)
  have hT : strictShortExact T := strictShortExact_iso e hS
  exact ⟨T.X₁, T.f, T.zero, quillenConflation_of_strictShortExact hT⟩

/-- Precomposing a deflation by an isomorphism preserves deflations. -/
theorem quillenDeflation_iso_hom_comp
    {X Y Z : MetrizableLCA.{u}} (e : X ≅ Y) {p : Y ⟶ Z}
    (hp : QuillenExactCategory.deflation p) :
    QuillenExactCategory.deflation (e.hom ≫ p) := by
  rcases hp with ⟨W, k, zero, hS⟩
  let k' : W ⟶ X := k ≫ e.inv
  have zero' : k' ≫ (e.hom ≫ p) = 0 := by
    simp [k', Category.assoc, zero]
  let S := ShortComplex.mk k p zero
  let T := ShortComplex.mk k' (e.hom ≫ p) zero'
  let eS : S ≅ T :=
    ShortComplex.isoMk (Iso.refl W) e.symm (Iso.refl Z)
      (by simp [S, T, k'])
      (by simp [S, T])
  exact ⟨W, k', zero', QuillenExactCategory.conflation_iso_transport eS hS⟩

/-- The standard mapping-cone coordinate isomorphism, expressed solely with
the public `fst`, `snd`, `inl`, and `inr` mapping-cone API. -/
noncomputable def mappingConeCyclesXIsoBiprod
    {K L : CochainComplex MetrizableLCA.{u} ℤ} (f : K ⟶ L) (i : ℤ) :
    (CochainComplex.mappingCone f).X i ≅ K.X (i + 1) ⊞ L.X i where
  hom := biprod.lift
    ((CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl)
    ((CochainComplex.mappingCone.snd f).v i i (add_zero i))
  inv := biprod.desc
    ((CochainComplex.mappingCone.inl f).v (i + 1) i (by omega))
    ((CochainComplex.mappingCone.inr f).f i)
  hom_inv_id := by
    rw [biprod.lift_desc]
    exact CochainComplex.mappingCone.id_X f i (i + 1) rfl
  inv_hom_id := by
    apply biprod.hom_ext
    · simp [biprod.desc_eq, Category.assoc]
    · simp [biprod.desc_eq, Category.assoc]

/-- The first cone-projection factor is the cone-coordinate isomorphism
followed by the biproduct of the identity and cycle projection. -/
lemma mappingConeCyclesFirstFactor_eq
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesFirstFactor hL f i =
      (mappingConeCyclesXIsoBiprod f i).hom ≫
        biprod.map (𝟙 (K.X (i + 1))) (hL.proj i) := by
  apply biprod.hom_ext
  · simp [mappingConeCyclesFirstFactor, mappingConeCyclesXIsoBiprod, Category.assoc]
  · simp [mappingConeCyclesFirstFactor, mappingConeCyclesXIsoBiprod, Category.assoc]

/-- The first factor of the canonical cone-cycle projection is a deflation. -/
theorem mappingConeCyclesFirstFactor_deflation
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    QuillenExactCategory.deflation (mappingConeCyclesFirstFactor hL f i) := by
  rw [mappingConeCyclesFirstFactor_eq]
  exact quillenDeflation_iso_hom_comp
    (mappingConeCyclesXIsoBiprod f i)
    (biprod_id_cyclesDataProj_deflation (K.X (i + 1)) hL i)

/-- The base map whose pullback along the source cycle projection models the
second cone-projection factor. -/
noncomputable def mappingConeCyclesSecondPullbackBase
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesObj hK hL f (i + 1) ⟶ hK.Z (i + 1 + 1) :=
  -pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1))

/-- The pullback of the source cycle projection used to model the second
cone-projection factor. -/
noncomputable abbrev mappingConeCyclesSecondPullbackObj
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) : MetrizableLCA.{u} :=
  pullback (mappingConeCyclesSecondPullbackBase hK hL f i) (hK.proj (i + 1))

lemma mappingConeCyclesSecondFactor_pullback_condition
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondFactor hK hL f i ≫
        mappingConeCyclesSecondPullbackBase hK hL f i =
      biprod.fst ≫ hK.proj (i + 1) := by
  simp [mappingConeCyclesSecondPullbackBase,
    mappingConeCyclesSecondFactor_fst]

/-- The comparison from the biproduct source of the second factor to the
pullback of the source cycle projection. -/
noncomputable def mappingConeCyclesSecondFactorToPullback
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    K.X (i + 1) ⊞ hL.Z (i + 1) ⟶
      mappingConeCyclesSecondPullbackObj hK hL f i :=
  pullback.lift (mappingConeCyclesSecondFactor hK hL f i) biprod.fst
    (mappingConeCyclesSecondFactor_pullback_condition hK hL f i)

@[reassoc (attr := simp)]
lemma mappingConeCyclesSecondFactorToPullback_fst
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondFactorToPullback hK hL f i ≫
        pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
          (hK.proj (i + 1)) =
      mappingConeCyclesSecondFactor hK hL f i := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mappingConeCyclesSecondFactorToPullback_snd
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondFactorToPullback hK hL f i ≫
        pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
          (hK.proj (i + 1)) =
      biprod.fst := by
  exact pullback.lift_snd _ _ _

/-- The target-coordinate residual on the pullback model. It lands in the
kernel of the next target cycle projection. -/
noncomputable def mappingConeCyclesSecondResidual
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondPullbackObj hK hL f i ⟶ L.X (i + 1) :=
  pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
      (hK.proj (i + 1)) ≫
      pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1)) -
    pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
      (hK.proj (i + 1)) ≫ f.f (i + 1)

lemma mappingConeCyclesSecondResidual_zero
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondResidual hK hL f i ≫ hL.proj (i + 1) = 0 := by
  have hEq :
      (pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
          (hK.proj (i + 1)) ≫
        pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1))) (hL.proj (i + 1))) ≫
          hL.proj (i + 1) =
      (pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
          (hK.proj (i + 1)) ≫ f.f (i + 1)) ≫ hL.proj (i + 1) := by
    calc
      _ = pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
          (hK.proj (i + 1)) ≫
            (pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1)))
              (hL.proj (i + 1)) ≫
                (-(cyclesDataMap hK hL f (i + 1 + 1)))) := by
                  simpa only [Category.assoc] using congrArg
                    (fun q =>
                      pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
                        (hK.proj (i + 1)) ≫ q)
                    (pullback.condition
                      (f := -(cyclesDataMap hK hL f (i + 1 + 1)))
                      (g := hL.proj (i + 1))).symm
      _ = (pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
            (hK.proj (i + 1)) ≫
              mappingConeCyclesSecondPullbackBase hK hL f i) ≫
          cyclesDataMap hK hL f (i + 1 + 1) := by
            simp [mappingConeCyclesSecondPullbackBase, Category.assoc]
      _ = (pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
            (hK.proj (i + 1)) ≫ hK.proj (i + 1)) ≫
          cyclesDataMap hK hL f (i + 1 + 1) := by
            rw [pullback.condition]
      _ = pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
          (hK.proj (i + 1)) ≫
            (f.f (i + 1) ≫ hL.proj (i + 1)) := by
              rw [Category.assoc, cyclesData_proj_map]
      _ = _ := by rw [Category.assoc]
  rw [mappingConeCyclesSecondResidual, Preadditive.sub_comp, hEq, sub_self]

/-- The residual lifted uniquely to the target cycle object. -/
noncomputable def mappingConeCyclesSecondResidualLift
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondPullbackObj hK hL f i ⟶ hL.Z (i + 1) :=
  (kernelForkOfQuillenConflation (hL.conflation (i + 1))).lift
    (KernelFork.ofι (mappingConeCyclesSecondResidual hK hL f i)
      (mappingConeCyclesSecondResidual_zero hK hL f i))

@[reassoc (attr := simp)]
lemma mappingConeCyclesSecondResidualLift_incl
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondResidualLift hK hL f i ≫ hL.incl (i + 1) =
      mappingConeCyclesSecondResidual hK hL f i := by
  exact (kernelForkOfQuillenConflation (hL.conflation (i + 1))).fac
    (KernelFork.ofι (mappingConeCyclesSecondResidual hK hL f i)
      (mappingConeCyclesSecondResidual_zero hK hL f i)) WalkingParallelPair.zero

/-- The comparison back from the pullback model to the biproduct source. -/
noncomputable def mappingConeCyclesSecondPullbackToFactor
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondPullbackObj hK hL f i ⟶
      K.X (i + 1) ⊞ hL.Z (i + 1) :=
  biprod.lift
    (pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
      (hK.proj (i + 1)))
    (mappingConeCyclesSecondResidualLift hK hL f i)

lemma mappingConeCyclesSecondFactorToPullback_hom_inv
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondFactorToPullback hK hL f i ≫
        mappingConeCyclesSecondPullbackToFactor hK hL f i =
      𝟙 (K.X (i + 1) ⊞ hL.Z (i + 1)) := by
  haveI : Mono (hL.incl (i + 1)) :=
    mono_of_isLimit_fork (kernelForkOfQuillenConflation (hL.conflation (i + 1)))
  apply biprod.hom_ext
  · simp [mappingConeCyclesSecondPullbackToFactor, Category.assoc]
  · apply (cancel_mono (hL.incl (i + 1))).1
    simp [mappingConeCyclesSecondPullbackToFactor, mappingConeCyclesSecondResidual,
      mappingConeCyclesSecondFactor_snd, Category.assoc]

lemma mappingConeCyclesSecondPullbackToFactor_hom_inv
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesSecondPullbackToFactor hK hL f i ≫
        mappingConeCyclesSecondFactorToPullback hK hL f i =
      𝟙 (mappingConeCyclesSecondPullbackObj hK hL f i) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.id_comp]
      have hc := pullback.condition
        (f := mappingConeCyclesSecondPullbackBase hK hL f i)
        (g := hK.proj (i + 1))
      calc
        (mappingConeCyclesSecondPullbackToFactor hK hL f i ≫
              mappingConeCyclesSecondFactorToPullback hK hL f i) ≫
            pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
              (hK.proj (i + 1)) ≫
              pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1)))
                (hL.proj (i + 1)) =
          mappingConeCyclesSecondPullbackToFactor hK hL f i ≫
            (mappingConeCyclesSecondFactor hK hL f i ≫
              pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1)))
                (hL.proj (i + 1))) := by
                  simp [Category.assoc]
        _ = mappingConeCyclesSecondPullbackToFactor hK hL f i ≫
            (biprod.fst ≫ (-hK.proj (i + 1))) := by
              rw [mappingConeCyclesSecondFactor_fst]
        _ = pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
              (hK.proj (i + 1)) ≫ (-hK.proj (i + 1)) := by
                simp [mappingConeCyclesSecondPullbackToFactor]
        _ = pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
              (hK.proj (i + 1)) ≫
                pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1)))
                  (hL.proj (i + 1)) := by
                    simp only [mappingConeCyclesSecondPullbackBase,
                      Preadditive.comp_neg] at hc ⊢
                    simpa only [Preadditive.comp_neg, Preadditive.neg_comp,
                      neg_neg] using congrArg Neg.neg hc.symm
    · simp only [Category.id_comp]
      calc
        (mappingConeCyclesSecondPullbackToFactor hK hL f i ≫
              mappingConeCyclesSecondFactorToPullback hK hL f i) ≫
            pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
              (hK.proj (i + 1)) ≫
              pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1)))
                (hL.proj (i + 1)) =
          mappingConeCyclesSecondPullbackToFactor hK hL f i ≫
            (mappingConeCyclesSecondFactor hK hL f i ≫
              pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1)))
                (hL.proj (i + 1))) := by
                  simp [Category.assoc]
        _ = mappingConeCyclesSecondPullbackToFactor hK hL f i ≫
            (biprod.fst ≫ f.f (i + 1) +
              biprod.snd ≫ hL.incl (i + 1)) := by
                rw [mappingConeCyclesSecondFactor_snd]
        _ = pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
              (hK.proj (i + 1)) ≫ f.f (i + 1) +
            mappingConeCyclesSecondResidualLift hK hL f i ≫
              hL.incl (i + 1) := by
                simp [mappingConeCyclesSecondPullbackToFactor,
                  Preadditive.comp_add]
        _ = pullback.snd (mappingConeCyclesSecondPullbackBase hK hL f i)
              (hK.proj (i + 1)) ≫ f.f (i + 1) +
            mappingConeCyclesSecondResidual hK hL f i := by
              rw [mappingConeCyclesSecondResidualLift_incl]
        _ = pullback.fst (mappingConeCyclesSecondPullbackBase hK hL f i)
              (hK.proj (i + 1)) ≫
                pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1)))
                  (hL.proj (i + 1)) := by
                    simp [mappingConeCyclesSecondResidual]
  · simp [mappingConeCyclesSecondPullbackToFactor, Category.assoc]

/-- The biproduct source of the second cone-projection factor is canonically
isomorphic to the pullback of the source cycle projection. -/
noncomputable def mappingConeCyclesSecondFactorIso
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    K.X (i + 1) ⊞ hL.Z (i + 1) ≅
      mappingConeCyclesSecondPullbackObj hK hL f i where
  hom := mappingConeCyclesSecondFactorToPullback hK hL f i
  inv := mappingConeCyclesSecondPullbackToFactor hK hL f i
  hom_inv_id := mappingConeCyclesSecondFactorToPullback_hom_inv hK hL f i
  inv_hom_id := mappingConeCyclesSecondPullbackToFactor_hom_inv hK hL f i

/-- The second factor of the canonical cone-cycle projection is a deflation. -/
theorem mappingConeCyclesSecondFactor_deflation
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    QuillenExactCategory.deflation (mappingConeCyclesSecondFactor hK hL f i) := by
  rw [← mappingConeCyclesSecondFactorToPullback_fst hK hL f i]
  exact quillenDeflation_iso_hom_comp
    (mappingConeCyclesSecondFactorIso hK hL f i)
    (quillenDeflation_pullback (hK.deflation_proj (i + 1))
      (mappingConeCyclesSecondPullbackBase hK hL f i))

/-- The canonical cone-cycle projection is the composite of the coordinate
quotient and the map from the resulting biproduct into the next pullback. -/
theorem mappingConeCyclesProj_factorization
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesProj hK hL f i =
      mappingConeCyclesFirstFactor hL f i ≫
        mappingConeCyclesSecondFactor hK hL f i := by
  apply pullback.hom_ext
  · rw [mappingConeCyclesProj_fst, Category.assoc,
      mappingConeCyclesSecondFactor_fst]
    simp [mappingConeCyclesFirstFactor]
  · rw [mappingConeCyclesProj_snd, ← hL.d_eq i, Category.assoc,
      mappingConeCyclesSecondFactor_snd, Preadditive.comp_add]
    simp [mappingConeCyclesFirstFactor, Category.assoc]

/-- The canonical cycle projection of a mapping cone between corrected
acyclic complexes is a Quillen deflation. -/
theorem mappingConeCyclesProj_deflation
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    QuillenExactCategory.deflation (mappingConeCyclesProj hK hL f i) := by
  rw [mappingConeCyclesProj_factorization]
  exact quillenDeflation_comp
    (mappingConeCyclesFirstFactor_deflation hL f i)
    (mappingConeCyclesSecondFactor_deflation hK hL f i)

/-- A displayed categorical kernel of a Quillen deflation completes to a
conflation. -/
theorem quillenConflation_of_deflation_of_kernel
    {K X Y : MetrizableLCA.{u}} {i : K ⟶ X} {p : X ⟶ Y}
    (zero : i ≫ p = 0) (hp : QuillenExactCategory.deflation p)
    (hi : IsLimit (KernelFork.ofι i zero)) :
    QuillenExactCategory.Conflation (ShortComplex.mk i p zero) := by
  rcases hp with ⟨W, k, zero', hS⟩
  let hk : IsLimit (KernelFork.ofι k zero') := kernelForkOfQuillenConflation hS
  let e₁ : W ≅ K := IsLimit.conePointUniqueUpToIso hk hi
  let S : ShortComplex MetrizableLCA.{u} := ShortComplex.mk k p zero'
  let T : ShortComplex MetrizableLCA.{u} := ShortComplex.mk i p zero
  let e : S ≅ T :=
    ShortComplex.isoMk e₁ (Iso.refl X) (Iso.refl Y)
      (by
        dsimp [S, T]
        exact IsLimit.conePointUniqueUpToIso_hom_comp hk hi WalkingParallelPair.zero)
      (by simp [S, T])
  exact QuillenExactCategory.conflation_iso_transport e hS

/-- The cone-cycle projection followed by the next cone-cycle inclusion is
the mapping-cone differential. -/
theorem mappingConeCyclesProj_incl
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesProj hK hL f i ≫
        mappingConeCyclesIncl hK hL f (i + 1) =
      (CochainComplex.mappingCone f).d i (i + 1) := by
  apply CochainComplex.mappingCone.ext_to f (i + 1) (i + 1 + 1) rfl
  · rw [Category.assoc, mappingConeCyclesIncl_fst,
      mappingConeCyclesProj_fst_assoc, CochainComplex.mappingCone.d_fst_v]
    rw [← hK.d_eq (i + 1)]
    simp [Category.assoc]
    rfl
  · rw [Category.assoc, mappingConeCyclesIncl_snd,
      mappingConeCyclesProj_snd, CochainComplex.mappingCone.d_snd_v]

/-- The displayed cone-cycle inclusion is annihilated by the cone-cycle
projection. -/
theorem mappingConeCyclesIncl_proj_zero
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    mappingConeCyclesIncl hK hL f i ≫
        mappingConeCyclesProj hK hL f i = 0 := by
  apply pullback.hom_ext
  · rw [Category.assoc, mappingConeCyclesProj_fst]
    simp [mappingConeCyclesIncl_fst_assoc, hK.zero]
  · rw [Category.assoc, mappingConeCyclesProj_snd, Preadditive.comp_add,
      ← Category.assoc, mappingConeCyclesIncl_fst, ← Category.assoc,
      mappingConeCyclesIncl_snd]
    have hpb := congrArg Neg.neg
      (pullback.condition
        (f := -(cyclesDataMap hK hL f (i + 1))) (g := hL.proj i))
    have hpb' :
        pullback.fst (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
            cyclesDataMap hK hL f (i + 1) =
          -(pullback.snd (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
            hL.proj i) := by
      simpa only [Preadditive.comp_neg, neg_neg] using hpb
    rw [zero_comp]
    calc
      (pullback.fst (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              hK.incl (i + 1)) ≫ f.f (i + 1) +
          pullback.snd (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              L.d i (i + 1) =
        pullback.fst (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              (hK.incl (i + 1) ≫ f.f (i + 1)) +
          pullback.snd (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              L.d i (i + 1) := by rw [Category.assoc]
      _ =
        pullback.fst (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              (cyclesDataMap hK hL f (i + 1) ≫ hL.incl (i + 1)) +
          pullback.snd (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              (hL.proj i ≫ hL.incl (i + 1)) := by
            rw [cyclesDataMap_incl, hL.d_eq i]
      _ =
        (pullback.fst (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              cyclesDataMap hK hL f (i + 1)) ≫ hL.incl (i + 1) +
          (pullback.snd (-(cyclesDataMap hK hL f (i + 1))) (hL.proj i) ≫
              hL.proj i) ≫ hL.incl (i + 1) := by
            simp only [Category.assoc]
      _ = 0 := by rw [hpb']; simp

/-- The displayed cone-cycle inclusion is a monomorphism. -/
theorem mappingConeCyclesIncl_mono
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    Mono (mappingConeCyclesIncl hK hL f i) := by
  haveI : Mono (hK.incl (i + 1)) :=
    mono_of_isLimit_fork (kernelForkOfQuillenConflation (hK.conflation (i + 1)))
  constructor
  intro T a b hab
  apply pullback.hom_ext
  · apply (cancel_mono (hK.incl (i + 1))).1
    have h := congrArg
      (fun q => q ≫
        (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl) hab
    simpa only [Category.assoc, mappingConeCyclesIncl_fst] using h
  · have h := congrArg
      (fun q => q ≫
        (CochainComplex.mappingCone.snd f).v i i (add_zero i)) hab
    simpa only [Category.assoc, mappingConeCyclesIncl_snd] using h

/-- The displayed cone-cycle inclusion is the categorical kernel of the
cone-cycle projection. -/
noncomputable def mappingConeCyclesIncl_isLimit
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    IsLimit (KernelFork.ofι
      (mappingConeCyclesIncl hK hL f i)
      (mappingConeCyclesIncl_proj_zero hK hL f i)) := by
  letI : Mono (mappingConeCyclesIncl hK hL f i) :=
    mappingConeCyclesIncl_mono hK hL f i
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  have hkfst :
      (k ≫ (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl) ≫
        hK.proj (i + 1) = 0 := by
    have h := congrArg
      (fun q => q ≫
        pullback.fst (-(cyclesDataMap hK hL f (i + 1 + 1)))
          (hL.proj (i + 1))) hk
    rw [Category.assoc, mappingConeCyclesProj_fst] at h
    simpa only [zero_comp, Category.assoc, Preadditive.comp_neg,
      Preadditive.neg_comp, neg_eq_zero] using h
  let hkerK := kernelForkOfQuillenConflation (hK.conflation (i + 1))
  let kfork := KernelFork.ofι
    (k ≫ (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl) hkfst
  let a : T ⟶ hK.Z (i + 1) := hkerK.lift kfork
  have ha : a ≫ hK.incl (i + 1) =
      k ≫ (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl :=
    hkerK.fac kfork WalkingParallelPair.zero
  let b : T ⟶ L.X i :=
    k ≫ (CochainComplex.mappingCone.snd f).v i i (add_zero i)
  have hsum :
      (k ≫ (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl) ≫
          f.f (i + 1) +
        b ≫ L.d i (i + 1) = 0 := by
    have h := congrArg
      (fun q => q ≫
        pullback.snd (-(cyclesDataMap hK hL f (i + 1 + 1)))
          (hL.proj (i + 1))) hk
    rw [Category.assoc, mappingConeCyclesProj_snd] at h
    simpa only [zero_comp, Category.assoc, Preadditive.comp_add, b] using h
  haveI : Mono (hL.incl (i + 1)) :=
    mono_of_isLimit_fork (kernelForkOfQuillenConflation (hL.conflation (i + 1)))
  have hcond :
      a ≫ (-(cyclesDataMap hK hL f (i + 1))) = b ≫ hL.proj i := by
    apply (cancel_mono (hL.incl (i + 1))).1
    calc
      (a ≫ (-(cyclesDataMap hK hL f (i + 1)))) ≫ hL.incl (i + 1) =
          -((a ≫ cyclesDataMap hK hL f (i + 1)) ≫
            hL.incl (i + 1)) := by simp
      _ = -((a ≫ hK.incl (i + 1)) ≫ f.f (i + 1)) := by
        rw [Category.assoc, cyclesDataMap_incl, ← Category.assoc]
      _ = -((k ≫ (CochainComplex.mappingCone.fst f).1.v i (i + 1) rfl) ≫
          f.f (i + 1)) := by rw [ha]
      _ = b ≫ L.d i (i + 1) := neg_eq_iff_add_eq_zero.mpr hsum
      _ = (b ≫ hL.proj i) ≫ hL.incl (i + 1) := by
        simp only [b, ← hL.d_eq i, Category.assoc]
  let l : T ⟶ mappingConeCyclesObj hK hL f i := pullback.lift a b hcond
  refine ⟨l, ?_⟩
  apply CochainComplex.mappingCone.ext_to f i (i + 1) rfl
  · rw [Category.assoc, mappingConeCyclesIncl_fst]
    rw [pullback.lift_fst_assoc, ha]
  · rw [Category.assoc, mappingConeCyclesIncl_snd]
    exact pullback.lift_snd _ _ _

/-- The displayed cycle short complex of the mapping cone is a Quillen
conflation. -/
theorem mappingConeCyclesConflation
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) (i : ℤ) :
    QuillenExactCategory.Conflation
      (ShortComplex.mk
        (mappingConeCyclesIncl hK hL f i)
        (mappingConeCyclesProj hK hL f i)
        (mappingConeCyclesIncl_proj_zero hK hL f i)) :=
  quillenConflation_of_deflation_of_kernel
    (mappingConeCyclesIncl_proj_zero hK hL f i)
    (mappingConeCyclesProj_deflation hK hL f i)
    (mappingConeCyclesIncl_isLimit hK hL f i)

/-- Corrected cycle-object exact-acyclicity data for the mapping cone of a map
between corrected exact-acyclic complexes. -/
noncomputable def cyclesDataMappingCone
    {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L)
    (f : K ⟶ L) :
    ExactAcyclicWithCyclesData MetrizableLCA.{u}
      (CochainComplex.mappingCone f) where
  Z i := mappingConeCyclesObj hK hL f i
  incl i := mappingConeCyclesIncl hK hL f i
  proj i := mappingConeCyclesProj hK hL f i
  zero i := mappingConeCyclesIncl_proj_zero hK hL f i
  conflation i := mappingConeCyclesConflation hK hL f i
  d_eq i := mappingConeCyclesProj_incl hK hL f i

/-- Corrected metrizable cycle-object acyclicity is closed under mapping cones
of maps between corrected exact-acyclic complexes. -/
theorem exactAcyclicWithCycles_mappingCone
    {K L : CochainComplex MetrizableLCA.{u} ℤ} (f : K ⟶ L)
    (hK : exactAcyclicWithCycles MetrizableLCA.{u} K)
    (hL : exactAcyclicWithCycles MetrizableLCA.{u} L) :
    exactAcyclicWithCycles MetrizableLCA.{u}
      (CochainComplex.mappingCone f) := by
  obtain ⟨hK⟩ := hK
  obtain ⟨hL⟩ := hL
  exact ⟨cyclesDataMappingCone hK hL f⟩

theorem exactAt_of_cyclesData
    (hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i)
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (h : ExactAcyclicWithCyclesData MetrizableLCA.{u} K) (i : ℤ) :
    K.ExactAt i := by
  letI : K.HasHomology i := hasHomology K i
  haveI : (K.sc' (i - 1) i (i + 1)).HasHomology :=
    ShortComplex.hasHomology_of_iso (K.isoSc' (i - 1) i (i + 1) (by simp) (by simp))
  rw [HomologicalComplex.exactAt_iff' (K := K) (i := i - 1) (j := i) (k := i + 1)
    (by simp) (by simp)]
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  · let dout : K.X i ⟶ K.X (i + 1) := K.d i (i + 1)
    let din : K.X (i - 1) ⟶ K.X i := K.d (i - 1) i
    let pprev : K.X (i - 1) ⟶ h.Z i :=
      h.proj (i - 1) ≫ eqToHom (congrArg h.Z (show i - 1 + 1 = i by omega))
    let hker := cyclesData_incl_kernel_d h i
    let e := (kernelIsKernel dout).conePointUniqueUpToIso hker
    have hprojEpi : Epi (h.proj (i - 1)) := by
      exact ConcreteCategory.epi_of_surjective _
        (MetrizableLCA.surjective_of_quillenDeflation (h.deflation_proj (i - 1)))
    have hpprevEpi : Epi pprev := by
      dsimp [pprev]
      infer_instance
    have hdprev : pprev ≫ h.incl i = din := by
      dsimp [pprev, din]
      exact cyclesData_proj_eqToHom_comp_incl h (show i - 1 + 1 = i by omega)
    have heinv : e.inv ≫ kernel.ι dout = h.incl i := by
      exact IsLimit.conePointUniqueUpToIso_inv_comp (kernelIsKernel dout) hker
        WalkingParallelPair.zero
    have hfac : pprev ≫ e.inv =
        kernel.lift dout din (by dsimp [din, dout]; exact K.d_comp_d (i - 1) i (i + 1)) := by
      apply (cancel_mono (kernel.ι dout)).1
      calc
        (pprev ≫ e.inv) ≫ kernel.ι dout = pprev ≫ e.inv ≫ kernel.ι dout := by
          rw [Category.assoc]
        _ = pprev ≫ h.incl i := by
          simpa [Category.assoc] using congrArg (fun q => pprev ≫ q) heinv
        _ = din := hdprev
        _ = kernel.lift dout din (by dsimp [din, dout]; exact K.d_comp_d (i - 1) i (i + 1)) ≫
            kernel.ι dout := by
          rw [kernel.lift_ι]
    have hcompEpi : Epi (pprev ≫ e.inv) := by infer_instance
    rw [hfac] at hcompEpi
    exact hcompEpi

theorem exactAt_of_exactAcyclicWithCycles
    (hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i)
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : exactAcyclicWithCycles MetrizableLCA.{u} K) (i : ℤ) :
    K.ExactAt i := by
  obtain ⟨h⟩ := hK
  exact exactAt_of_cyclesData hasHomology h i

/-- Corrected cycle-object data are degreewise exact after forgetting topology. -/
theorem forgetToAddCommGrpCat_exactAt_of_cyclesData
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (h : ExactAcyclicWithCyclesData MetrizableLCA.{u} K) (i : ℤ) :
    (((forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt i := by
  let Kf : CochainComplex AddCommGrpCat.{u} ℤ :=
    ((forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  change Kf.ExactAt i
  rw [HomologicalComplex.exactAt_iff' (K := Kf) (i := i - 1) (j := i) (k := i + 1)
    (by simp) (by simp)]
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  have hstrict_i : strictShortExact (h.shortComplex i) :=
    strictShortExact_shortComplex_of_cyclesData h i
  have hstrict_prev : strictShortExact (h.shortComplex (i - 1)) :=
    strictShortExact_shortComplex_of_cyclesData h (i - 1)
  have hstrict_next : strictShortExact (h.shortComplex (i + 1)) :=
    strictShortExact_shortComplex_of_cyclesData h (i + 1)
  have hproj_zero : h.proj i y = 0 := by
    have hycomp : (h.proj i ≫ h.incl (i + 1)) y = 0 := by
      rw [h.d_eq i]
      change K.d i (i + 1) y = 0 at hy
      exact hy
    have hycomp' : h.incl (i + 1) (h.proj i y) = h.incl (i + 1) 0 := by
      simpa using hycomp
    exact hstrict_next.closed_inclusion.injective hycomp'
  rcases hstrict_i.algebraic_exact y hproj_zero with ⟨z, hz⟩
  let eprev : h.Z (i - 1 + 1) ≅ h.Z i :=
    eqToIso (congrArg h.Z (show i - 1 + 1 = i by omega))
  let zprev : h.Z (i - 1 + 1) := eprev.inv z
  rcases hstrict_prev.surjective zprev with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hzprev : eprev.hom (h.proj (i - 1) x) = z := by
    change eprev.hom ((h.shortComplex (i - 1)).g x) = z
    rw [hx]
    exact eprev.inv_hom_id_apply z
  have hdprev := congrArg
    (fun f : K.X (i - 1) ⟶ K.X i => f x)
    (cyclesData_proj_eqToHom_comp_incl h (show i - 1 + 1 = i by omega))
  have hdx : K.d (i - 1) i x = y := by
    calc
      K.d (i - 1) i x = h.incl i (eprev.hom (h.proj (i - 1) x)) := by
        simpa [eprev, Category.assoc] using hdprev.symm
      _ = h.incl i z := by rw [hzprev]
      _ = y := hz
  change K.d (i - 1) i x = y
  exact hdx

/-- Corrected acyclic complexes are degreewise exact after forgetting topology. -/
theorem forgetToAddCommGrpCat_exactAt_of_exactAcyclicWithCycles
    {K : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : exactAcyclicWithCycles MetrizableLCA.{u} K) (i : ℤ) :
    (((forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt i := by
  obtain ⟨h⟩ := hK
  exact forgetToAddCommGrpCat_exactAt_of_cyclesData h i

/-- Degreewise exactness after forgetting topology reflects back to categorical exactness. -/
theorem exactAt_of_forgetToAddCommGrpCat_exactAt
    (hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i)
    {K : CochainComplex MetrizableLCA.{u} ℤ} {i : ℤ}
    (hExact :
      (((forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt i) :
    K.ExactAt i := by
  let Kf : CochainComplex AddCommGrpCat.{u} ℤ :=
    ((forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  have hExact' : Kf.ExactAt i := hExact
  rw [HomologicalComplex.exactAt_iff' (K := Kf) (i := i - 1) (j := i) (k := i + 1)
    (by simp) (by simp)] at hExact'
  rw [ShortComplex.ab_exact_iff] at hExact'
  letI : K.HasHomology i := hasHomology K i
  haveI : (K.sc' (i - 1) i (i + 1)).HasHomology :=
    ShortComplex.hasHomology_of_iso (K.isoSc' (i - 1) i (i + 1) (by simp) (by simp))
  rw [HomologicalComplex.exactAt_iff' (K := K) (i := i - 1) (j := i) (k := i + 1)
    (by simp) (by simp)]
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  let din : K.X (i - 1) ⟶ K.X i := K.d (i - 1) i
  let dout : K.X i ⟶ K.X (i + 1) := K.d i (i + 1)
  let Z : MetrizableLCA.{u} := kernel dout
  let κ : Z ⟶ K.X i := kernel.ι dout
  have hSurj :
      Function.Surjective
        (kernel.lift dout din (by dsimp [din, dout]; exact K.d_comp_d (i - 1) i (i + 1)) :
          K.X (i - 1) → Z) := by
    intro z
    have hz : dout (κ z) = 0 := by
      have hzcat := ConcreteCategory.congr_hom (kernel.condition dout) z
      change dout (κ z) = 0 at hzcat
      exact hzcat
    obtain ⟨x, hx⟩ := hExact' (κ z) (by
      change dout (κ z) = 0
      exact hz)
    refine ⟨x, ?_⟩
    have hinj : Function.Injective (κ : Z → K.X i) :=
      (MetrizableLCA.equalizer_ι_closedEmbedding (r := dout) (s := 0)).injective
    apply hinj
    calc
      κ
          (kernel.lift dout din
            (by dsimp [din, dout]; exact K.d_comp_d (i - 1) i (i + 1)) x) =
          din x := by
        simpa [κ] using ConcreteCategory.congr_hom
          (kernel.lift_ι dout din
            (by dsimp [din, dout]; exact K.d_comp_d (i - 1) i (i + 1))) x
      _ = κ z := by
        change din x = κ z at hx
        exact hx
  exact ConcreteCategory.epi_of_surjective _ hSurj

/-- The canonical boundary map from a term to the next kernel object. -/
noncomputable def exactAtCycleBoundary
    (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    K.X i ⟶ kernel (K.d (i + 1) (i + 1 + 1)) :=
  kernel.lift (K.d (i + 1) (i + 1 + 1)) (K.d i (i + 1))
    (K.d_comp_d i (i + 1) (i + 1 + 1))

@[simp]
theorem exactAtCycleBoundary_ι
    (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    exactAtCycleBoundary K i ≫ kernel.ι (K.d (i + 1) (i + 1 + 1)) =
      K.d i (i + 1) := by
  simp [exactAtCycleBoundary]

theorem exactAtCycleBoundary_zero
    (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    kernel.ι (K.d i (i + 1)) ≫ exactAtCycleBoundary K i = 0 := by
  apply (cancel_mono (kernel.ι (K.d (i + 1) (i + 1 + 1)))).1
  simp [Category.assoc]

/-- Degreewise `ExactAt` makes the canonical boundary map categorically epi. -/
lemma exactAtCycleBoundary_epi_of_exactAt
    (hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i)
    (K : CochainComplex MetrizableLCA.{u} ℤ) (hK : ∀ i : ℤ, K.ExactAt i) (i : ℤ) :
    Epi (exactAtCycleBoundary K i) := by
  letI : K.HasHomology (i + 1) := hasHomology K (i + 1)
  haveI : (K.sc' i (i + 1) (i + 1 + 1)).HasHomology :=
    ShortComplex.hasHomology_of_iso (K.isoSc' i (i + 1) (i + 1 + 1) (by simp) (by simp))
  have hsc : (K.sc' i (i + 1) (i + 1 + 1)).Exact := by
    have h := hK (i + 1)
    rw [HomologicalComplex.exactAt_iff' (K := K) (i := i) (j := i + 1)
      (k := i + 1 + 1) (by simp) (by simp)] at h
    exact h
  have hEpi :
      Epi (kernel.lift (K.d (i + 1) (i + 1 + 1)) (K.d i (i + 1))
        (K.d_comp_d i (i + 1) (i + 1 + 1))) := by
    exact (ShortComplex.exact_iff_epi_kernel_lift
      (S := K.sc' i (i + 1) (i + 1 + 1))).1 hsc
  simpa [exactAtCycleBoundary] using hEpi

/-- The canonical cycle short complex attached to degreewise `ExactAt` data. -/
noncomputable def exactAtCanonicalCycleShortComplex
    (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    ShortComplex MetrizableLCA.{u} :=
  ShortComplex.mk (kernel.ι (K.d i (i + 1))) (exactAtCycleBoundary K i)
    (exactAtCycleBoundary_zero K i)

/-- Elements killed by a metrizable LCA morphism lift to its categorical kernel. -/
lemma exists_preimage_kernel_ι_of_apply_eq_zero {A B : MetrizableLCA.{u}} (f : A ⟶ B)
    {a : A} (ha : f a = 0) :
    ∃ x : CategoryTheory.Limits.kernel (C := MetrizableLCA.{u}) f,
      (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u}) f) x = a := by
  let e : (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u}) f :
      MetrizableLCA.{u}) ≃ₜ+ equalizerObj f (0 : A ⟶ B) :=
    isoToContinuousAddEquiv (equalizerIsoEqualizerObj f (0 : A ⟶ B))
  let y : equalizerObj f (0 : A ⟶ B) := ⟨a, by simpa [equalizerSubgroup] using ha⟩
  refine ⟨e.symm y, ?_⟩
  have hhom : (equalizerIsoEqualizerObj f (0 : A ⟶ B)).hom ≫
      equalizerι f (0 : A ⟶ B) =
      CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u}) f := by
    simpa using equalizerIsoEqualizerObj_hom_ι f (0 : A ⟶ B)
  have happ := congrArg
    (fun q : CategoryTheory.Limits.kernel (C := MetrizableLCA.{u}) f ⟶ A =>
      q (e.symm y))
    hhom
  calc
    (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u}) f) (e.symm y) =
        ((equalizerIsoEqualizerObj f (0 : A ⟶ B)).hom ≫
          equalizerι f (0 : A ⟶ B)) (e.symm y) := by
      simpa using happ.symm
    _ = (equalizerι f (0 : A ⟶ B)) (e (e.symm y)) := by
      rfl
    _ = (equalizerι f (0 : A ⟶ B)) y := by rw [e.apply_symm_apply]
    _ = a := by rfl

/-- Degreewise `ExactAt` makes the canonical boundary map onto the next kernel. -/
lemma exactAtCycleBoundary_surjective_of_exactAt
    (hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i)
    (forgetPreservesHomology :
      (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology)
    (K : CochainComplex MetrizableLCA.{u} ℤ) (hK : ∀ i : ℤ, K.ExactAt i) (i : ℤ) :
    Function.Surjective
      (exactAtCycleBoundary K i : K.X i →
        (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
          (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u})) := by
  intro z
  letI : K.HasHomology (i + 1) := hasHomology K (i + 1)
  haveI : (K.sc' i (i + 1) (i + 1 + 1)).HasHomology :=
    ShortComplex.hasHomology_of_iso (K.isoSc' i (i + 1) (i + 1 + 1) (by simp) (by simp))
  letI : (forget₂ MetrizableLCA.{u} AddCommGrpCat.{u}).PreservesHomology :=
    forgetPreservesHomology
  have hsc : (K.sc' i (i + 1) (i + 1 + 1)).Exact := by
    have h := hK (i + 1)
    rw [HomologicalComplex.exactAt_iff' (K := K) (i := i) (j := i + 1)
      (k := i + 1 + 1) (by simp) (by simp)] at h
    exact h
  have hz :
      K.d (i + 1) (i + 1 + 1)
        ((CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
          (K.d (i + 1) (i + 1 + 1))) z) = 0 := by
    have hzcat := congrArg
      (fun q :
        (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
          (K.d (i + 1) (i + 1 + 1))) ⟶ K.X (i + 1 + 1) => q z)
      (CategoryTheory.Limits.kernel.condition (K.d (i + 1) (i + 1 + 1)))
    simp
  obtain ⟨x, hx⟩ :=
    (ShortComplex.exact_iff_of_hasForget (S := K.sc' i (i + 1) (i + 1 + 1))).mp hsc
      ((CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
        (K.d (i + 1) (i + 1 + 1))) z) hz
  refine ⟨x, ?_⟩
  have hinj :
      Function.Injective
        (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
          (K.d (i + 1) (i + 1 + 1)) :
          (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
            (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}) → K.X (i + 1)) :=
    (MetrizableLCA.equalizer_ι_closedEmbedding
      (r := K.d (i + 1) (i + 1 + 1)) (s := 0)).injective
  apply hinj
  calc
    (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
        (K.d (i + 1) (i + 1 + 1))) (exactAtCycleBoundary K i x) =
        K.d i (i + 1) x := by
      simp [exactAtCycleBoundary]
    _ = (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
        (K.d (i + 1) (i + 1 + 1))) z := hx

/-- An open map into an ambient space restricts to an open map into an injected subspace. -/
lemma isOpenMap_of_injective_comp_open {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [TopologicalSpace γ] {p : α → β} {i : β → γ} {d : α → γ}
    (hcomp : ∀ x, i (p x) = d x) (hinj : Function.Injective i)
    (hicont : Continuous i) (hdopen : IsOpenMap d) :
    IsOpenMap p := by
  intro U hU
  have hset : p '' U = i ⁻¹' (d '' U) := by
    ext y
    constructor
    · rintro ⟨x, hxU, rfl⟩
      exact ⟨x, hxU, (hcomp x).symm⟩
    · rintro ⟨x, hxU, hx⟩
      exact ⟨x, hxU, hinj ((hcomp x).trans hx)⟩
  rw [hset]
  exact hicont.isOpen_preimage _ (hdopen U hU)

/-- A surjective morphism out of a sigma-compact metrizable LCA group is open by mathlib's
topological-group open mapping theorem. -/
lemma isOpenMap_of_surjective_sigmaCompact {A B : MetrizableLCA.{u}} [SigmaCompactSpace A]
    (f : A ⟶ B) (hf : Function.Surjective (f : A → B)) :
    IsOpenMap (f : A → B) :=
  AddMonoidHom.isOpenMap_of_sigmaCompact f.hom.toAddMonoidHom hf f.hom.continuous

/-- If the ambient outgoing differential is open, then so is the canonical boundary to the
next kernel object. -/
lemma exactAtCycleBoundary_openMap_of_differential_openMap
    (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ)
    (hopen : IsOpenMap (K.d i (i + 1) : K.X i → K.X (i + 1))) :
    IsOpenMap
      (exactAtCycleBoundary K i : K.X i →
        (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
          (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u})) := by
  let κ : CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
      (K.d (i + 1) (i + 1 + 1)) ⟶ K.X (i + 1) :=
    CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
      (K.d (i + 1) (i + 1 + 1))
  have hinj :
      Function.Injective
        (κ : (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
          (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}) → K.X (i + 1)) :=
    (MetrizableLCA.equalizer_ι_closedEmbedding
      (r := K.d (i + 1) (i + 1 + 1)) (s := 0)).injective
  have hcomp : exactAtCycleBoundary K i ≫ κ = K.d i (i + 1) := by
    dsimp [κ]
    exact exactAtCycleBoundary_ι K i
  exact isOpenMap_of_injective_comp_open
    (p := exactAtCycleBoundary K i)
    (i := κ)
    (d := K.d i (i + 1))
    (fun x => congrArg (fun q : K.X i ⟶ K.X (i + 1) => q x) hcomp)
    hinj κ.hom.continuous hopen

/--
Differential-open input for the reverse direction.  This reduces the canonical boundary
open-map requirement to openness of the ordinary outgoing differential at exact degrees.
-/
structure ExactAtCanonicalCycleDifferentialOpenMapInput : Prop where
  hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i
  openDifferential :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, IsOpenMap (K.d i (i + 1) : K.X i → K.X (i + 1))

/--
Open-map input for the only topological part of the reverse direction from degreewise
exactness to corrected cycle-object acyclicity.
-/
structure ExactAtCanonicalCycleOpenMapInput : Prop where
  hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i
  openBoundary :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, IsOpenMap
        (exactAtCycleBoundary K i : K.X i →
          (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
            (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}))

/--
Sigma-compact source input for the reverse direction.  This is the precise extra
topological hypothesis under which the open mapping theorem makes the canonical boundary
maps open.
-/
structure ExactAtCanonicalCycleSigmaCompactSourceInput : Prop where
  hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i
  surjectiveBoundary :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, Function.Surjective
        (exactAtCycleBoundary K i : K.X i →
          (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
            (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}))
  sigmaCompactSource :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, SigmaCompactSpace (K.X i)

/--
Boundary-topology input for the canonical cycle reduction.  This records only the local
openness needed for the canonical boundary maps.  Surjectivity is then recovered from
`ExactAt`, categorical epimorphy, and openness, without the impossible global assertion
that the forgetful functor preserves all cokernels.
-/
structure ExactAtCanonicalCycleBoundaryTopologyInput : Prop where
  openBoundary :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, IsOpenMap
        (exactAtCycleBoundary K i : K.X i →
          (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
            (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}))

/--
Differential-open topology input for the canonical cycle reduction, separated from the
global forgetful-homology field.
-/
structure ExactAtCanonicalCycleDifferentialTopologyInput : Prop where
  openDifferential :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, IsOpenMap (K.d i (i + 1) : K.X i → K.X (i + 1))

/--
Sigma-compact source topology input for the canonical cycle reduction, separated from the
global forgetful-homology field.
-/
structure ExactAtCanonicalCycleSigmaCompactSourceTopologyInput : Prop where
  surjectiveBoundary :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, Function.Surjective
        (exactAtCycleBoundary K i : K.X i →
          (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
            (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}))
  sigmaCompactSource :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, SigmaCompactSpace (K.X i)

/-- Differential-open topology supplies boundary topology. -/
theorem exactAtCanonicalCycleBoundaryTopologyInput_of_differentialTopologyInput
    (input : ExactAtCanonicalCycleDifferentialTopologyInput.{u}) :
    ExactAtCanonicalCycleBoundaryTopologyInput.{u} where
  openBoundary := by
    intro K hK i
    exact exactAtCycleBoundary_openMap_of_differential_openMap K i
      (input.openDifferential K hK i)

/-- Sigma-compact source topology supplies boundary topology by the open mapping theorem. -/
theorem exactAtCanonicalCycleBoundaryTopologyInput_of_sigmaCompactSourceTopologyInput
    (input : ExactAtCanonicalCycleSigmaCompactSourceTopologyInput.{u}) :
    ExactAtCanonicalCycleBoundaryTopologyInput.{u} where
  openBoundary := by
    intro K hK i
    haveI : SigmaCompactSpace (K.X i) := input.sigmaCompactSource K hK i
    exact isOpenMap_of_surjective_sigmaCompact (exactAtCycleBoundary K i)
      (input.surjectiveBoundary K hK i)

/-- Differential-open input supplies the canonical boundary open-map input. -/
theorem exactAtCanonicalCycleOpenMapInput_of_differentialOpenMapInput
    (input : ExactAtCanonicalCycleDifferentialOpenMapInput.{u}) :
    ExactAtCanonicalCycleOpenMapInput.{u} where
  hasHomology := input.hasHomology
  openBoundary := by
    intro K hK i
    exact exactAtCycleBoundary_openMap_of_differential_openMap K i
      (input.openDifferential K hK i)

/-- Sigma-compact source input supplies the canonical boundary open-map input by the
topological-group open mapping theorem. -/
theorem exactAtCanonicalCycleOpenMapInput_of_sigmaCompactSourceInput
    (input : ExactAtCanonicalCycleSigmaCompactSourceInput.{u}) :
    ExactAtCanonicalCycleOpenMapInput.{u} where
  hasHomology := input.hasHomology
  openBoundary := by
    intro K hK i
    haveI : SigmaCompactSpace (K.X i) := input.sigmaCompactSource K hK i
    exact isOpenMap_of_surjective_sigmaCompact (exactAtCycleBoundary K i)
      (input.surjectiveBoundary K hK i)

/--
Topology input for the reverse direction from degreewise exactness to corrected cycle-object
acyclicity, reduced to the canonical kernel cycle objects.
-/
structure ExactAtCanonicalCycleStrictInput : Prop where
  hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i
  strictCycle :
    ∀ (K : CochainComplex MetrizableLCA.{u} ℤ), (∀ i : ℤ, K.ExactAt i) →
      ∀ i : ℤ, strictShortExact (exactAtCanonicalCycleShortComplex K i)

/-- Canonical boundary topology supplies the canonical strict cycle input. -/
theorem exactAtCanonicalCycleStrictInput_of_boundaryTopologyInput
    (hasHomology : ∀ (K : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ), K.HasHomology i)
    (input : ExactAtCanonicalCycleBoundaryTopologyInput.{u}) :
    ExactAtCanonicalCycleStrictInput.{u} where
  hasHomology := hasHomology
  strictCycle := by
    intro K hK i
    refine
      { closed_inclusion := ?_
        open_map := ?_
        surjective := ?_
        algebraic_exact := ?_ }
    · simpa [exactAtCanonicalCycleShortComplex] using
        (MetrizableLCA.equalizer_ι_closedEmbedding
          (r := K.d i (i + 1)) (s := 0))
    · simpa [exactAtCanonicalCycleShortComplex] using input.openBoundary K hK i
    · haveI : Epi (exactAtCycleBoundary K i) :=
        exactAtCycleBoundary_epi_of_exactAt hasHomology K hK i
      exact surjective_of_cokernelSubgroup_eq_top_of_isOpenMap (exactAtCycleBoundary K i)
        (cokernelSubgroup_eq_top_of_cokernelπ_eq_zero _
          (cokernelπ_eq_zero_of_epi _))
        (input.openBoundary K hK i)
    · intro x₂ hx₂
      dsimp [exactAtCanonicalCycleShortComplex] at hx₂
      have hboundary :
          (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
            (K.d (i + 1) (i + 1 + 1))) (exactAtCycleBoundary K i x₂) =
              K.d i (i + 1) x₂ := by
        simp [exactAtCycleBoundary]
      have hd : K.d i (i + 1) x₂ = 0 := by
        have hzero := congrArg
          (fun z :
            (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
              (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}) =>
              (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
                (K.d (i + 1) (i + 1 + 1))) z)
          hx₂
        calc
          K.d i (i + 1) x₂ =
              (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
                (K.d (i + 1) (i + 1 + 1))) (exactAtCycleBoundary K i x₂) :=
            hboundary.symm
          _ = (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
                (K.d (i + 1) (i + 1 + 1))) 0 := hzero
          _ = 0 := map_zero _
      simpa [exactAtCanonicalCycleShortComplex] using
        exists_preimage_kernel_ι_of_apply_eq_zero (K.d i (i + 1)) hd

/-- Canonical boundary open maps supply the canonical strict cycle input. -/
theorem exactAtCanonicalCycleStrictInput_of_openMapInput
    (input : ExactAtCanonicalCycleOpenMapInput.{u}) :
    ExactAtCanonicalCycleStrictInput.{u} where
  hasHomology := input.hasHomology
  strictCycle := by
    intro K hK i
    refine
      { closed_inclusion := ?_
        open_map := ?_
        surjective := ?_
        algebraic_exact := ?_ }
    · simpa [exactAtCanonicalCycleShortComplex] using
        (MetrizableLCA.equalizer_ι_closedEmbedding
          (r := K.d i (i + 1)) (s := 0))
    · simpa [exactAtCanonicalCycleShortComplex] using input.openBoundary K hK i
    · haveI : Epi (exactAtCycleBoundary K i) :=
        exactAtCycleBoundary_epi_of_exactAt input.hasHomology K hK i
      exact surjective_of_cokernelSubgroup_eq_top_of_isOpenMap (exactAtCycleBoundary K i)
        (cokernelSubgroup_eq_top_of_cokernelπ_eq_zero _
          (cokernelπ_eq_zero_of_epi _))
        (input.openBoundary K hK i)
    · intro x₂ hx₂
      dsimp [exactAtCanonicalCycleShortComplex] at hx₂
      have hboundary :
          (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
            (K.d (i + 1) (i + 1 + 1))) (exactAtCycleBoundary K i x₂) =
              K.d i (i + 1) x₂ := by
        simp [exactAtCycleBoundary]
      have hd : K.d i (i + 1) x₂ = 0 := by
        have hzero := congrArg
          (fun z :
            (CategoryTheory.Limits.kernel (C := MetrizableLCA.{u})
              (K.d (i + 1) (i + 1 + 1)) : MetrizableLCA.{u}) =>
              (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
                (K.d (i + 1) (i + 1 + 1))) z)
          hx₂
        calc
          K.d i (i + 1) x₂ =
              (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
                (K.d (i + 1) (i + 1 + 1))) (exactAtCycleBoundary K i x₂) :=
            hboundary.symm
          _ = (CategoryTheory.Limits.kernel.ι (C := MetrizableLCA.{u})
                (K.d (i + 1) (i + 1 + 1))) 0 := hzero
          _ = 0 := map_zero _
      simpa [exactAtCanonicalCycleShortComplex] using
        exists_preimage_kernel_ι_of_apply_eq_zero (K.d i (i + 1)) hd

/-- Canonical strict cycle short complexes realize degreewise exactness as corrected
cycle-object acyclicity. -/
theorem exactAcyclicWithCycles_of_exactAtCanonicalCycleStrictInput
    (input : ExactAtCanonicalCycleStrictInput.{u}) (K : CochainComplex MetrizableLCA.{u} ℤ)
    (hK : ∀ i : ℤ, K.ExactAt i) :
    exactAcyclicWithCycles MetrizableLCA.{u} K := by
  refine ⟨
    { Z := fun i => kernel (K.d i (i + 1))
      incl := fun i => kernel.ι (K.d i (i + 1))
      proj := fun i => exactAtCycleBoundary K i
      zero := fun i => exactAtCycleBoundary_zero K i
      conflation := fun i =>
        quillenConflation_of_strictShortExact (input.strictCycle K hK i)
      d_eq := fun i => exactAtCycleBoundary_ι K i }⟩

/-- Naturality of the comparison between the explicit metrizable product model
and the categorical binary biproduct. -/
lemma biprodObjIsoBiprod_hom_naturality {A B A' B' : MetrizableLCA.{u}}
    (f : A ⟶ A') (g : B ⟶ B') :
    (biprodObjIsoBiprod A B).hom ≫ biprod.map f g =
      biprodMap f g ≫ (biprodObjIsoBiprod A' B').hom := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprodMap_biprodFst,
      biprodObjIsoBiprod_hom_fst]
    rw [← Category.assoc, biprodObjIsoBiprod_hom_fst]
  · simp only [Category.assoc, biprod.map_snd, biprodMap_biprodSnd,
      biprodObjIsoBiprod_hom_snd]
    rw [← Category.assoc, biprodObjIsoBiprod_hom_snd]

/-- The degreewise biproduct comparison intertwines the differentials of a
binary biproduct of metrizable cochain complexes. -/
lemma biprodXIso_hom_d (K L : CochainComplex MetrizableLCA.{u} ℤ) (i j : ℤ) :
    (K ⊞ L).d i j ≫ (HomologicalComplex.biprodXIso K L j).hom =
      (HomologicalComplex.biprodXIso K L i).hom ≫ biprod.map (K.d i j) (L.d i j) := by
  apply biprod.hom_ext
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst, Category.assoc,
      biprod.map_fst, ← Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      HomologicalComplex.Hom.comm]
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd, Category.assoc,
      biprod.map_snd, ← Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      HomologicalComplex.Hom.comm]

/-- Corrected cycle-object data for a binary biproduct of metrizable cochain
complexes: the cycle objects are the degreewise biproducts of the given cycle
objects, conjugated by the canonical comparison `(K ⊞ L).X i ≅ K.X i ⊞ L.X i`. -/
def cyclesDataBiprod {K L : CochainComplex MetrizableLCA.{u} ℤ}
    (hK : ExactAcyclicWithCyclesData MetrizableLCA.{u} K)
    (hL : ExactAcyclicWithCyclesData MetrizableLCA.{u} L) :
    ExactAcyclicWithCyclesData MetrizableLCA.{u} (K ⊞ L) where
  Z i := hK.Z i ⊞ hL.Z i
  incl i := biprod.map (hK.incl i) (hL.incl i) ≫
    (HomologicalComplex.biprodXIso K L i).inv
  proj i := (HomologicalComplex.biprodXIso K L i).hom ≫
    biprod.map (hK.proj i) (hL.proj i)
  zero i := by
    apply biprod.hom_ext
    · simp [hK.zero i]
    · simp [hL.zero i]
  conflation i := by
    have hzero : (biprod.map (hK.incl i) (hL.incl i) ≫
          (HomologicalComplex.biprodXIso K L i).inv) ≫
        ((HomologicalComplex.biprodXIso K L i).hom ≫
          biprod.map (hK.proj i) (hL.proj i)) = 0 := by
      apply biprod.hom_ext
      · simp [hK.zero i]
      · simp [hL.zero i]
    have eiso : strictShortExactBiprodComplex (hK.shortComplex i) (hL.shortComplex i) ≅
        ShortComplex.mk
          (biprod.map (hK.incl i) (hL.incl i) ≫
            (HomologicalComplex.biprodXIso K L i).inv)
          ((HomologicalComplex.biprodXIso K L i).hom ≫
            biprod.map (hK.proj i) (hL.proj i)) hzero :=
      ShortComplex.isoMk
        (biprodObjIsoBiprod _ _)
        (biprodObjIsoBiprod _ _ ≪≫ (HomologicalComplex.biprodXIso K L i).symm)
        (biprodObjIsoBiprod _ _)
        (by
          dsimp [strictShortExactBiprodComplex, ExactAcyclicWithCyclesData.shortComplex]
          rw [← Category.assoc, biprodObjIsoBiprod_hom_naturality, Category.assoc])
        (by
          dsimp [strictShortExactBiprodComplex, ExactAcyclicWithCyclesData.shortComplex]
          rw [Category.assoc, Iso.inv_hom_id_assoc]
          exact biprodObjIsoBiprod_hom_naturality _ _)
    exact quillenConflation_of_strictShortExact
      (strictShortExact_iso eiso
        (strictShortExact_biprod
          (strictShortExact_shortComplex_of_cyclesData hK i)
          (strictShortExact_shortComplex_of_cyclesData hL i)))
  d_eq i := by
    rw [← cancel_mono (HomologicalComplex.biprodXIso K L (i + 1)).hom,
      biprodXIso_hom_d]
    apply biprod.hom_ext
    · simp [hK.d_eq i]
    · simp [hL.d_eq i]

/-- Corrected metrizable cycle-object acyclicity is closed under binary
biproducts. This is the corrected analogue of `exactAcyclic_biprod`. -/
theorem exactAcyclicWithCycles_biprod
    (K L : CochainComplex MetrizableLCA.{u} ℤ)
    (hK : exactAcyclicWithCycles MetrizableLCA.{u} K)
    (hL : exactAcyclicWithCycles MetrizableLCA.{u} L) :
    exactAcyclicWithCycles MetrizableLCA.{u} (K ⊞ L) := by
  obtain ⟨hK⟩ := hK
  obtain ⟨hL⟩ := hL
  exact ⟨cyclesDataBiprod hK hL⟩

end MetrizableLCA

end LeanLCAExactChallenge
