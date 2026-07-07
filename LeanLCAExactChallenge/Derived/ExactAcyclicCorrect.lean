import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.LCA.ExactCategory

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
