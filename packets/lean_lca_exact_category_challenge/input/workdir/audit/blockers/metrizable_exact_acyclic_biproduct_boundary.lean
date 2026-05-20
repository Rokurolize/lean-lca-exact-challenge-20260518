import LeanLCAExactChallenge.Derived.Bounded
import Mathlib.Algebra.Homology.ShortComplex.Limits

/-!
Metrizable exact-acyclic biproduct boundary.

Finite-product stability of `boundedExactWeakEquivalence MetrizableLCA` eventually needs a
comparison between mapping cones and finite products.  This blocker file proves the easier
degreewise ingredient first: in the strict metrizable LCA exact structure, exact acyclicity is
closed under binary biproducts of cochain complexes.
-/

set_option autoImplicit false

universe u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace MetrizableExactAcyclicBiproductBoundary

noncomputable local instance :
    HasBinaryBiproducts (ShortComplex MetrizableLCA.{u}) :=
  HasBinaryBiproducts.of_hasBinaryProducts

noncomputable local instance :
    PreservesBinaryBiproducts
      (ShortComplex.π₁ : ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

noncomputable local instance :
    PreservesBinaryBiproducts
      (ShortComplex.π₂ : ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

noncomputable local instance :
    PreservesBinaryBiproducts
      (ShortComplex.π₃ : ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

@[reassoc (attr := simp)]
lemma biprodXIso_inv_fst
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (biprod.fst : K ⊞ L ⟶ K).f i =
      biprod.fst := by
  rw [Iso.inv_comp_eq]
  exact (HomologicalComplex.biprodXIso_hom_fst (K := K) (L := L) i).symm

@[reassoc (attr := simp)]
lemma biprodXIso_inv_snd
    (K L : CochainComplex MetrizableLCA.{u} ℤ) (i : ℤ) :
    (HomologicalComplex.biprodXIso K L i).inv ≫ (biprod.snd : K ⊞ L ⟶ L).f i =
      biprod.snd := by
  rw [Iso.inv_comp_eq]
  exact (HomologicalComplex.biprodXIso_hom_snd (K := K) (L := L) i).symm

@[simp]
lemma biprodMap_biprodFst {A B A' B' : MetrizableLCA.{u}}
    (f : A ⟶ A') (g : B ⟶ B') :
    MetrizableLCA.biprodMap f g ≫ MetrizableLCA.biprodFst A' B' =
      MetrizableLCA.biprodFst A B ≫ f := by
  ext p
  rfl

@[simp]
lemma biprodMap_biprodSnd {A B A' B' : MetrizableLCA.{u}}
    (f : A ⟶ A') (g : B ⟶ B') :
    MetrizableLCA.biprodMap f g ≫ MetrizableLCA.biprodSnd A' B' =
      MetrizableLCA.biprodSnd A B ≫ g := by
  ext p
  rfl

@[reassoc (attr := simp)]
lemma shortComplexπ₁_mapBiprod_inv_fst (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₁ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).inv ≫
      (biprod.fst : S ⊞ T ⟶ S).τ₁ =
      biprod.fst := by
  rw [Iso.inv_comp_eq]
  simp [ShortComplex.π₁_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₁_mapBiprod_inv_snd (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₁ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).inv ≫
      (biprod.snd : S ⊞ T ⟶ T).τ₁ =
      biprod.snd := by
  rw [Iso.inv_comp_eq]
  simp [ShortComplex.π₁_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₂_mapBiprod_inv_fst (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₂ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).inv ≫
      (biprod.fst : S ⊞ T ⟶ S).τ₂ =
      biprod.fst := by
  rw [Iso.inv_comp_eq]
  simp [ShortComplex.π₂_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₂_mapBiprod_inv_snd (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₂ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).inv ≫
      (biprod.snd : S ⊞ T ⟶ T).τ₂ =
      biprod.snd := by
  rw [Iso.inv_comp_eq]
  simp [ShortComplex.π₂_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₃_mapBiprod_inv_fst (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₃ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).inv ≫
      (biprod.fst : S ⊞ T ⟶ S).τ₃ =
      biprod.fst := by
  rw [Iso.inv_comp_eq]
  simp [ShortComplex.π₃_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₃_mapBiprod_inv_snd (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₃ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).inv ≫
      (biprod.snd : S ⊞ T ⟶ T).τ₃ =
      biprod.snd := by
  rw [Iso.inv_comp_eq]
  simp [ShortComplex.π₃_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₂_mapBiprod_hom_fst (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₂ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).hom ≫
      biprod.fst =
      (biprod.fst : S ⊞ T ⟶ S).τ₂ := by
  simp [ShortComplex.π₂_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₂_mapBiprod_hom_snd (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₂ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).hom ≫
      biprod.snd =
      (biprod.snd : S ⊞ T ⟶ T).τ₂ := by
  simp [ShortComplex.π₂_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₃_mapBiprod_hom_fst (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₃ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).hom ≫
      biprod.fst =
      (biprod.fst : S ⊞ T ⟶ S).τ₃ := by
  simp [ShortComplex.π₃_map]

@[reassoc (attr := simp)]
lemma shortComplexπ₃_mapBiprod_hom_snd (S T : ShortComplex MetrizableLCA.{u}) :
    ((ShortComplex.π₃ :
        ShortComplex MetrizableLCA.{u} ⥤ MetrizableLCA.{u}).mapBiprod S T).hom ≫
      biprod.snd =
      (biprod.snd : S ⊞ T ⟶ T).τ₃ := by
  simp [ShortComplex.π₃_map]

/-- The degreewise explicit biproduct short complex is strictly exact when both inputs are
exact-acyclic.  Transporting this result to `(K ⊞ L).sc i` is the remaining comparison step. -/
theorem strictShortExactBiprodComplex_exactAcyclic
    (K L : CochainComplex MetrizableLCA.{u} ℤ)
    (hK : exactAcyclic MetrizableLCA K)
    (hL : exactAcyclic MetrizableLCA L) :
    ∀ i : ℤ,
      MetrizableLCA.strictShortExact
        (MetrizableLCA.strictShortExactBiprodComplex (K.sc i) (L.sc i)) := by
  intro i
  exact MetrizableLCA.strictShortExact_biprod (hK i) (hL i)

section Checks

#check strictShortExactBiprodComplex_exactAcyclic
#check biprodXIso_inv_fst
#check biprodXIso_inv_snd
#check MetrizableLCA.strictShortExact_biprod
#check exactAcyclic
#check boundedExactWeakEquivalence

end Checks

end MetrizableExactAcyclicBiproductBoundary

end LeanLCAExactChallenge
