import LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration

/-!
# Kan extension across coherent-nerve path latching objects

The path latching subcomplex of a coherent inner horn is a cubical corner.

Its inclusion is anodyne, so maps from it into a Kan complex extend over the full path nerve.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty HomotopicalAlgebra
open Opposite Simplicial
open Path Chain Chain.PathChain

/-- Pullback of a subcomplex along an isomorphism is isomorphic to the original subcomplex. -/
private noncomputable def subcomplexPreimageIsoOfIso {X Y : SSet.{u}}
    (A : X.Subcomplex) (e : X ≅ Y) : (A.preimage e.inv : SSet) ≅ (A : SSet) where
  hom := A.fromPreimage e.inv
  inv := {
    app := fun U ↦ ↾fun x ↦ ⟨e.hom.app U x.1, by
      change e.inv.app U (e.hom.app U x.1) ∈ A.obj U
      simp [← NatTrans.comp_app_apply, x.2]⟩
    naturality := by
      intro U V f
      ext x
      apply Subtype.ext
      exact CategoryTheory.congr_fun (e.hom.naturality f) x.1 }
  hom_inv_id := by
    ext U x
    apply Subtype.ext
    change e.hom.app U (e.inv.app U x.1) = x.1
    simp [← NatTrans.comp_app_apply]
  inv_hom_id := by
    ext U x
    apply Subtype.ext
    change e.inv.app U (e.hom.app U x.1) = x.1
    simp [← NatTrans.comp_app_apply]

@[simp]
private theorem subcomplexPreimageIsoOfIso_inv_ι {X Y : SSet.{u}}
    (A : X.Subcomplex) (e : X ≅ Y) :
    (subcomplexPreimageIsoOfIso A e).inv ≫ (A.preimage e.inv).ι = A.ι ≫ e.hom :=
  rfl

/-- The coherent-inner-horn latching inclusion for one mapping object is an anodyne extension. -/
theorem knownPathSubcomplex_ι_anodyne
    {J : Type u} [LinearOrder J] {i j k : J}
    (hik : i < k) (hkj : k < j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n) :
    SSet.anodyneExtensions (knownPathSubcomplex i j k).ι := by
  let E := thickPathNerveCubeIsoExplicit
    (le_trans (le_of_lt hik) (le_of_lt hkj)) n e
  let A := knownPathSubcomplex i j k
  let B := liftedIntervalCubeCorner n (coherentCornerSign k hik hkj n e)
  have hAB : A.preimage E.inv = B :=
    knownPathSubcomplex_preimage_explicit_eq_corner i j k hik hkj n e
  have hn : n ≠ 0 := by
    intro hn
    have a : Fin n := e ⟨k, hik, hkj⟩
    subst n
    exact Fin.elim0 a
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hpre : SSet.anodyneExtensions (A.preimage E.inv).ι := by
    rw [hAB]
    exact liftedIntervalCubeCorner_anodyne m
      (coherentCornerSign k hik hkj (m + 1) e)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (subcomplexPreimageIsoOfIso A E).symm E (by
      change (subcomplexPreimageIsoOfIso A E).inv ≫
        (A.preimage E.inv).ι = A.ι ≫ E.hom
      exact subcomplexPreimageIsoOfIso_inv_ι A E))).2 hpre

/-- Finite ordered vertex sets supply the finite cubical presentation automatically. -/
theorem knownPathSubcomplex_ι_anodyne_of_fintype
    {J : Type u} [LinearOrder J] [Finite J] {i j k : J}
    (hik : i < k) (hkj : k < j) :
    SSet.anodyneExtensions (knownPathSubcomplex i j k).ι := by
  letI := Fintype.ofFinite J
  exact knownPathSubcomplex_ι_anodyne hik hkj
    (Fintype.card (InteriorVertex i j)) (Fintype.equivFin (InteriorVertex i j))

/-- The full strict-composition path-latching inclusion is an anodyne extension. -/
theorem fullyKnownPathSubcomplex_ι_anodyne
    {J : Type u} [LinearOrder J] {i j k : J}
    (hik : i < k) (hkj : k < j) (n : ℕ)
    (e : InteriorVertex i j ≃ Fin (n + 1))
    (hkLast : e ⟨k, hik, hkj⟩ = Fin.last n) :
    SSet.anodyneExtensions (fullyKnownPathSubcomplex i j k).ι := by
  let E := thickPathNerveCubeIsoExplicit
    (le_trans (le_of_lt hik) (le_of_lt hkj)) (n + 1) e
  let A := fullyKnownPathSubcomplex i j k
  let B := liftedIntervalCubeLastHorn n 1
  have hAB : A.preimage E.inv = B :=
    fullyKnownPathSubcomplex_preimage_explicit_eq_lastHorn
      i j k hik hkj n e hkLast
  have hpre : SSet.anodyneExtensions (A.preimage E.inv).ι := by
    rw [hAB]
    exact liftedIntervalCubeLastHorn_anodyne n 1
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff
    (Arrow.isoMk (subcomplexPreimageIsoOfIso A E).symm E (by
      change (subcomplexPreimageIsoOfIso A E).inv ≫
        (A.preimage E.inv).ι = A.ι ≫ E.hom
      exact subcomplexPreimageIsoOfIso_inv_ι A E))).2 hpre

/-- Number the finite internal vertices with the missing vertex last. -/
theorem fullyKnownPathSubcomplex_ι_anodyne_of_fintype
    {J : Type u} [LinearOrder J] [Finite J] {i j k : J}
    (hik : i < k) (hkj : k < j) :
    SSet.anodyneExtensions (fullyKnownPathSubcomplex i j k).ι := by
  letI := Fintype.ofFinite J
  let I := InteriorVertex i j
  let e₀ := Fintype.equivFin I
  have hcard : Fintype.card I ≠ 0 := by
    intro h
    have hk : I := ⟨k, hik, hkj⟩
    have := Fintype.card_pos_iff.mpr ⟨hk⟩
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hcard
  let e₁ : I ≃ Fin (n + 1) := e₀.trans (Equiv.cast (congrArg Fin hn))
  let q := e₁ ⟨k, hik, hkj⟩
  let e : I ≃ Fin (n + 1) := e₁.trans (Equiv.swap q (Fin.last n))
  have hkLast : e ⟨k, hik, hkj⟩ = Fin.last n := by
    simp [e, q]
  exact fullyKnownPathSubcomplex_ι_anodyne hik hkj n e hkLast

open SSet.modelCategoryQuillen in
/-- Maps into a Kan complex extend across an arbitrary anodyne extension. -/
theorem exists_extension_of_anodyne_of_kan
    {A B X : SSet.{u}} {i : A ⟶ B} [SSet.KanComplex X]
    (hi : SSet.anodyneExtensions i) (f : A ⟶ X) :
    ∃ g : B ⟶ X, i ≫ g = f := by
  let t : IsTerminal (⊤_ SSet.{u}) := terminalIsTerminal
  let sq : CommSq f i (t.from X) (t.from B) := ⟨t.hom_ext _ _⟩
  have hp : SSet.modelCategoryQuillen.J.rlp (t.from X) := by
    rw [← SSet.modelCategoryQuillen.fibration_iff]
    exact (isFibrant_iff X).1 inferInstance
  have hlift : HasLiftingProperty i (t.from X) := by
    rw [SSet.anodyneExtensions_eq_llp_rlp] at hi
    exact hi _ hp
  letI : HasLiftingProperty i (t.from X) := hlift
  exact ⟨sq.lift, sq.fac_left⟩

/-- A coherent latching map into a Kan mapping object extends over its path nerve. -/
theorem exists_knownPathSubcomplex_extension_of_kan
    {J : Type u} [LinearOrder J] {i j k : J}
    (hik : i < k) (hkj : k < j) (n : ℕ) (e : InteriorVertex i j ≃ Fin n)
    {X : SSet.{u}} [SSet.KanComplex X]
    (f : (knownPathSubcomplex i j k : SSet) ⟶ X) :
    ∃ g : CategoryTheory.nerve (ThickPath i j) ⟶ X,
      (knownPathSubcomplex i j k).ι ≫ g = f := by
  exact exists_extension_of_anodyne_of_kan
    (knownPathSubcomplex_ι_anodyne hik hkj n e) f

/-- Finite ordered vertex sets supply the path-cube presentation in the Kan extension theorem. -/
theorem exists_knownPathSubcomplex_extension_of_kan_of_fintype
    {J : Type u} [LinearOrder J] [Finite J] {i j k : J}
    (hik : i < k) (hkj : k < j) {X : SSet.{u}} [SSet.KanComplex X]
    (f : (knownPathSubcomplex i j k : SSet) ⟶ X) :
    ∃ g : CategoryTheory.nerve (ThickPath i j) ⟶ X,
      (knownPathSubcomplex i j k).ι ≫ g = f :=
  exists_extension_of_anodyne_of_kan
    (knownPathSubcomplex_ι_anodyne_of_fintype hik hkj) f

/-- A full path-latching map into a Kan complex extends over the path nerve. -/
theorem exists_fullyKnownPathSubcomplex_extension_of_kan_of_fintype
    {J : Type u} [LinearOrder J] [Finite J] {i j k : J}
    (hik : i < k) (hkj : k < j) {X : SSet.{u}} [SSet.KanComplex X]
    (f : (fullyKnownPathSubcomplex i j k : SSet) ⟶ X) :
    ∃ g : CategoryTheory.nerve (ThickPath i j) ⟶ X,
      (fullyKnownPathSubcomplex i j k).ι ≫ g = f :=
  exists_extension_of_anodyne_of_kan
    (fullyKnownPathSubcomplex_ι_anodyne_of_fintype hik hkj) f

end LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
