/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.StableEquivalenceTransfer
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Full stable-structure transfer across quasicategorical equivalences

This file transfers the bicartesian-square condition and hence the complete stable structure.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalClosed
open Simplicial
open scoped Bicategory MonoidalCategory

local instance qcatHomCategoryTransferFull (A B : SSet.QCat.{u}) : Category (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

local instance qcatPropertyTransferFull (Q : SSet.QCat.{u}) : SSet.Quasicategory Q.obj :=
  Q.property

universe w v

/-- Two right adjoints to the same map are canonically isomorphic. -/
noncomputable def bicategoryRightAdjointIso
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f : a ⟶ b} {g g' : b ⟶ a}
    (adj : Bicategory.Adjunction f g) (adj' : Bicategory.Adjunction f g') : g ≅ g' :=
  Bicategory.conjugateIsoEquiv adj adj' (Iso.refl f)

/-- Two left adjoints to the same map are canonically isomorphic. -/
noncomputable def bicategoryLeftAdjointIso
    {B : Type u} [Bicategory.{w, v} B] {a b : B} {f f' : a ⟶ b} {g : b ⟶ a}
    (adj : Bicategory.Adjunction f g) (adj' : Bicategory.Adjunction f' g) : f ≅ f' :=
  ((Bicategory.conjugateIsoEquiv adj adj').symm (Iso.refl g)).symm

/-- Evaluate an internal-hom simplex at a fixed vertex. -/
def internalHomEvaluationAtVertex (X Y : SSet.{u}) (x : X _⦋0⦌) :
    (ihom X).obj Y ⟶ Y :=
  (MonoidalCategory.leftUnitor _).inv ≫
    ((SSet.unitHomEquiv X).symm x ⊗ₘ 𝟙 _) ≫ (ihom.ev X).app Y

lemma internalHomEvaluationAtVertex_vertex
    {X Y : SSet.QCat.{u}} (f : X ⟶ Y) (x : X.obj _⦋0⦌) :
    (internalHomEvaluationAtVertex X.obj Y.obj x).app _
        (SSet.unitHomEquiv ((ihom X.obj).obj Y.obj) (MonoidalClosed.curry' f.hom)) =
      mapVertex f x := by
  apply (SSet.unitHomEquiv Y.obj).symm.injective
  rw [unitHomEquiv_symm_natural]
  rw [Equiv.symm_apply_apply]
  change MonoidalClosed.curry' f.hom ≫ internalHomEvaluationAtVertex X.obj Y.obj x =
    (SSet.unitHomEquiv Y.obj).symm (f.hom.app _ x)
  rw [unitHomEquiv_symm_natural]
  let p := (SSet.unitHomEquiv X.obj).symm x
  change MonoidalClosed.curry' f.hom ≫ (MonoidalCategory.leftUnitor _).inv ≫
      (p ⊗ₘ 𝟙 _) ≫ (ihom.ev X.obj).app Y.obj = p ≫ f.hom
  calc
    _ = p ≫ (MonoidalCategory.rightUnitor X.obj).inv ≫
        (X.obj ◁ MonoidalClosed.curry' f.hom) ≫ (ihom.ev X.obj).app Y.obj := by
      rw [MonoidalCategory.leftUnitor_inv_naturality_assoc]
      simp only [MonoidalCategory.tensorHom_def, MonoidalCategory.whiskerLeft_id,
        Category.comp_id]
      rw [MonoidalCategory.whisker_exchange_assoc]
      monoidal
    _ = p ≫ (MonoidalCategory.rightUnitor X.obj).inv ≫
        (MonoidalCategory.rightUnitor X.obj).hom ≫ f.hom := by
      rw [MonoidalClosed.whiskerLeft_curry'_ihom_ev_app]
      rfl
    _ = p ≫ f.hom := by simp

/-- Evaluate an invertible `2`-cell at a vertex. -/
noncomputable def twoIsoAppEdge
    {X Y : SSet.QCat.{u}} {f g : X ⟶ Y} (a : f ≅ g) (x : X.obj _⦋0⦌) :
    SSet.Edge (mapVertex f x) (mapVertex g x) :=
  SSet.Edge.castEndpoints
    (internalHomEvaluationAtVertex_vertex f x).symm
    (internalHomEvaluationAtVertex_vertex g x).symm
    ((internalHomEdgeOfTwoIso a).map
      (internalHomEvaluationAtVertex X.obj Y.obj x))

theorem twoIsoAppEdge_isEquivalence
    {X Y : SSet.QCat.{u}} {f g : X ⟶ Y} (a : f ≅ g) (x : X.obj _⦋0⦌) :
    EdgeIsEquivalence (twoIsoAppEdge a x) :=
  (internalHomEdgeOfTwoIso_isEquivalence a).map
      (internalHomEvaluationAtVertex X.obj Y.obj x) |>.castEndpoints
        (internalHomEvaluationAtVertex_vertex f x).symm
        (internalHomEvaluationAtVertex_vertex g x).symm

/-- Choose an edge representing the composite of two edges in the homotopy category. -/
noncomputable def equivalenceEdgeComp
    {X : SSet.{u}} [SSet.Quasicategory X] {x y z : X _⦋0⦌}
    (f : SSet.Edge x y) (g : SSet.Edge y z) : SSet.Edge x z :=
  SSet.Edge.ofTruncated
    (homotopyCategory_homMk_surjective_of_quasicategory
      (edgeHomotopyClass f ≫ edgeHomotopyClass g)).choose

theorem equivalenceEdgeComp_isEquivalence
    {X : SSet.{u}} [SSet.Quasicategory X] {x y z : X _⦋0⦌}
    {f : SSet.Edge x y} {g : SSet.Edge y z}
    (hf : EdgeIsEquivalence f) (hg : EdgeIsEquivalence g) :
    EdgeIsEquivalence (equivalenceEdgeComp f g) := by
  letI : IsIso (edgeHomotopyClass f) := hf
  letI : IsIso (edgeHomotopyClass g) := hg
  haveI hcomp : IsIso (edgeHomotopyClass f ≫ edgeHomotopyClass g) := inferInstance
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (homotopyCategory_homMk_surjective_of_quasicategory
      (edgeHomotopyClass f ≫ edgeHomotopyClass g)).choose)
  rw [(homotopyCategory_homMk_surjective_of_quasicategory
    (edgeHomotopyClass f ≫ edgeHomotopyClass g)).choose_spec]
  exact hcomp

/-- Essential images are invariant under an invertible `2`-cell between maps. -/
theorem inEssentialImage_iff_of_iso
    {X Y : SSet.QCat.{u}} {f g : X ⟶ Y} (a : f ≅ g)
    (y : Y.obj _⦋0⦌) : InEssentialImage f y ↔ InEssentialImage g y := by
  constructor
  · rintro ⟨x, e, he⟩
    let c := equivalenceEdgeComp (twoIsoAppEdge a.symm x) e
    exact ⟨x, c, equivalenceEdgeComp_isEquivalence
      (twoIsoAppEdge_isEquivalence a.symm x) he⟩
  · rintro ⟨x, e, he⟩
    let c := equivalenceEdgeComp (twoIsoAppEdge a x) e
    exact ⟨x, c, equivalenceEdgeComp_isEquivalence
      (twoIsoAppEdge_isEquivalence a x) he⟩

/-- Equivalent target vertices have the same essential-image membership. -/
theorem inEssentialImage_target_iff
    {X Y : SSet.QCat.{u}} (f : X ⟶ Y) {y z : Y.obj _⦋0⦌}
    (e : SSet.Edge y z) (e' : SSet.Edge z y)
    (he : EdgeIsEquivalence e) (he' : EdgeIsEquivalence e') :
    InEssentialImage f y ↔ InEssentialImage f z := by
  constructor
  · rintro ⟨x, q, hq⟩
    exact ⟨x, equivalenceEdgeComp q e, equivalenceEdgeComp_isEquivalence hq he⟩
  · rintro ⟨x, q, hq⟩
    exact ⟨x, equivalenceEdgeComp q e', equivalenceEdgeComp_isEquivalence hq he'⟩

/-- Mapping an essential-image witness through any map preserves it. -/
theorem InEssentialImage.postcomp
    {X Y Z : SSet.QCat.{u}} {f : X ⟶ Y} {y : Y.obj _⦋0⦌}
    (h : InEssentialImage f y) (g : Y ⟶ Z) :
    InEssentialImage (f ≫ g) (mapVertex g y) := by
  rcases h with ⟨x, e, he⟩
  exact ⟨x, e.map g.hom, he.map g.hom⟩

/-- Postcomposition by an equivalence preserves and reflects essential images. -/
theorem inEssentialImage_postcomp_equivalence_iff
    {X Y Z : SSet.QCat.{u}} {f : X ⟶ Y} (e : Bicategory.Equivalence Y Z)
    (y : Y.obj _⦋0⦌) :
    InEssentialImage (f ≫ e.hom) (mapVertex e.hom y) ↔ InEssentialImage f y := by
  constructor
  · rintro ⟨x, q, hq⟩
    let first := twoIsoAppEdge e.unit (mapVertex f x)
    let middle := q.map e.inv.hom
    let last := twoIsoAppEdge e.unit.symm y
    let c := equivalenceEdgeComp (equivalenceEdgeComp first middle) last
    have hfirst : EdgeIsEquivalence first := twoIsoAppEdge_isEquivalence e.unit _
    have hmiddle : EdgeIsEquivalence middle := hq.map e.inv.hom
    have hlast : EdgeIsEquivalence last := twoIsoAppEdge_isEquivalence e.unit.symm _
    exact ⟨x, c, equivalenceEdgeComp_isEquivalence
      (equivalenceEdgeComp_isEquivalence hfirst hmiddle) hlast⟩
  · intro h
    exact h.postcomp e.hom

/-- Precomposition by the inverse of an equivalence does not change an essential image. -/
theorem inEssentialImage_precomp_equivalence_inv_iff
    {X X' Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X X')
    (f : X ⟶ Y) (y : Y.obj _⦋0⦌) :
    InEssentialImage (e.inv ≫ f) y ↔ InEssentialImage f y := by
  constructor
  · rintro ⟨x, q, hq⟩
    exact ⟨mapVertex e.inv x, q, hq⟩
  · rintro ⟨x, q, hq⟩
    let first := (twoIsoAppEdge e.unit.symm x).map f.hom
    let c := equivalenceEdgeComp first q
    have hfirst : EdgeIsEquivalence first :=
      (twoIsoAppEdge_isEquivalence e.unit.symm x).map f.hom
    exact ⟨mapVertex e.hom x, c, equivalenceEdgeComp_isEquivalence hfirst hq⟩

/-- Conjugation through equivalences preserves a right adjoint's essential image. -/
theorem rightAdjoint_inEssentialImage_conjugate_iff
    {A A' B B' : SSet.QCat.{u}}
    (eA : Bicategory.Equivalence A A') (eB : Bicategory.Equivalence B B')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : B ⟶ A}
    (h : eA.hom ≫ f' = f ≫ eB.hom) (adj : Bicategory.Adjunction f g)
    (hf' : Bicategory.IsLeftAdjoint f') (y : A'.obj _⦋0⦌) :
    letI := hf'
    InEssentialImage (Bicategory.rightAdjoint f') y ↔
      InEssentialImage g (mapVertex eA.inv y) := by
  letI := hf'
  let transportedAdj : Bicategory.Adjunction f' ((eB.inv ≫ g) ≫ eA.hom) :=
    ((reverseBicategoricalEquivalenceAdjunction eA).comp
      (adj.comp (bicategoricalEquivalenceAdjunction eB))).ofIsoLeft
        (Bicategory.conjugateEquivalenceIso eA eB h)
  let chosenAdj := Bicategory.Adjunction.ofIsLeftAdjoint f'
  let i := bicategoryRightAdjointIso chosenAdj transportedAdj
  rw [inEssentialImage_iff_of_iso i]
  let ey := twoIsoAppEdge eA.counit y
  let ey' := twoIsoAppEdge eA.counit.symm y
  have heqTarget :
      InEssentialImage ((eB.inv ≫ g) ≫ eA.hom)
          (mapVertex eA.hom (mapVertex eA.inv y)) ↔
        InEssentialImage ((eB.inv ≫ g) ≫ eA.hom) y :=
    inEssentialImage_target_iff _ ey ey'
      (twoIsoAppEdge_isEquivalence eA.counit y)
      (twoIsoAppEdge_isEquivalence eA.counit.symm y)
  exact heqTarget.symm.trans
    ((inEssentialImage_postcomp_equivalence_iff eA (f := eB.inv ≫ g)
      (mapVertex eA.inv y)).trans
        (inEssentialImage_precomp_equivalence_inv_iff eB g (mapVertex eA.inv y)))

/-- Conjugation through equivalences preserves a left adjoint's essential image. -/
theorem leftAdjoint_inEssentialImage_conjugate_iff
    {A A' B B' : SSet.QCat.{u}}
    (eA : Bicategory.Equivalence A A') (eB : Bicategory.Equivalence B B')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : B ⟶ A}
    (h : eA.hom ≫ f' = f ≫ eB.hom) (adj : Bicategory.Adjunction g f)
    (hf' : Bicategory.IsRightAdjoint f') (y : A'.obj _⦋0⦌) :
    letI := hf'
    InEssentialImage (Bicategory.leftAdjoint f') y ↔
      InEssentialImage g (mapVertex eA.inv y) := by
  letI := hf'
  let transportedAdj : Bicategory.Adjunction ((eB.inv ≫ g) ≫ eA.hom) f' :=
    (((reverseBicategoricalEquivalenceAdjunction eB).comp adj).comp
      (bicategoricalEquivalenceAdjunction eA)).ofIsoRight
        (Bicategory.conjugateEquivalenceIso eA eB h)
  let chosenAdj := Bicategory.Adjunction.ofIsRightAdjoint f'
  let i := bicategoryLeftAdjointIso chosenAdj transportedAdj
  rw [inEssentialImage_iff_of_iso i]
  let ey := twoIsoAppEdge eA.counit y
  let ey' := twoIsoAppEdge eA.counit.symm y
  have heqTarget :
      InEssentialImage ((eB.inv ≫ g) ≫ eA.hom)
          (mapVertex eA.hom (mapVertex eA.inv y)) ↔
        InEssentialImage ((eB.inv ≫ g) ≫ eA.hom) y :=
    inEssentialImage_target_iff _ ey ey'
      (twoIsoAppEdge_isEquivalence eA.counit y)
      (twoIsoAppEdge_isEquivalence eA.counit.symm y)
  exact heqTarget.symm.trans
    ((inEssentialImage_postcomp_equivalence_iff eA (f := eB.inv ≫ g)
      (mapVertex eA.inv y)).trans
        (inEssentialImage_precomp_equivalence_inv_iff eB g (mapVertex eA.inv y)))

/-- A square is cartesian after an equivalence exactly when its inverse image is cartesian. -/
theorem isPullbackSquare_bicategoricalEquivalence_iff
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y)
    (hX : Bicategory.IsLeftAdjoint
      (pullbackRestriction X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PullbackCornerShape X)))
    (hY : Bicategory.IsLeftAdjoint
      (pullbackRestriction Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PullbackCornerShape Y)))
    (sq : (functorQCat SquareShape Y
      (canonicalFunctorQuasicategory SquareShape Y)).obj _⦋0⦌) :
    IsPullbackSquare Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PullbackCornerShape Y) hY sq ↔
      IsPullbackSquare X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PullbackCornerShape X) hX
        (mapVertex (internalHomPostcompBicategoricalEquivalence e SquareShape).inv sq) := by
  letI := hX
  let adjX := Bicategory.Adjunction.ofIsLeftAdjoint
    (pullbackRestriction X (canonicalFunctorQuasicategory SquareShape X)
      (canonicalFunctorQuasicategory PullbackCornerShape X))
  exact rightAdjoint_inEssentialImage_conjugate_iff
    (internalHomPostcompBicategoricalEquivalence e SquareShape)
    (internalHomPostcompBicategoricalEquivalence e PullbackCornerShape)
    (pullbackRestriction_naturality e.hom) adjX hY sq

/-- A square is cocartesian after an equivalence exactly when its inverse image is cocartesian. -/
theorem isPushoutSquare_bicategoricalEquivalence_iff
    {X Y : SSet.QCat.{u}} (e : Bicategory.Equivalence X Y)
    (hX : Bicategory.IsRightAdjoint
      (pushoutRestriction X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PushoutCornerShape X)))
    (hY : Bicategory.IsRightAdjoint
      (pushoutRestriction Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PushoutCornerShape Y)))
    (sq : (functorQCat SquareShape Y
      (canonicalFunctorQuasicategory SquareShape Y)).obj _⦋0⦌) :
    IsPushoutSquare Y (canonicalFunctorQuasicategory SquareShape Y)
        (canonicalFunctorQuasicategory PushoutCornerShape Y) hY sq ↔
      IsPushoutSquare X (canonicalFunctorQuasicategory SquareShape X)
        (canonicalFunctorQuasicategory PushoutCornerShape X) hX
        (mapVertex (internalHomPostcompBicategoricalEquivalence e SquareShape).inv sq) := by
  letI := hX
  let adjX := Bicategory.Adjunction.ofIsRightAdjoint
    (pushoutRestriction X (canonicalFunctorQuasicategory SquareShape X)
      (canonicalFunctorQuasicategory PushoutCornerShape X))
  exact leftAdjoint_inEssentialImage_conjugate_iff
    (internalHomPostcompBicategoricalEquivalence e SquareShape)
    (internalHomPostcompBicategoricalEquivalence e PushoutCornerShape)
    (pushoutRestriction_naturality e.hom) adjX hY sq

/-- A complete canonical square calculus transfers across a bicategorical equivalence. -/
noncomputable def StableSquareCalculus.ofBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (hX : StableSquareCalculus X)
    (e : Bicategory.Equivalence X Y) : StableSquareCalculus Y := by
  let hpullY := pullbackRestriction_isLeftAdjoint_of_bicategoricalEquivalence e
    hX.pullbackKanExtension
  let hpushY := pushoutRestriction_isRightAdjoint_of_bicategoricalEquivalence e
    hX.pushoutKanExtension
  refine
    { pointed := hX.pointed.ofBicategoricalEquivalence e
      finiteBicomplete := hX.finiteBicomplete.ofBicategoricalEquivalence e
      pullbackKanExtension := hpullY
      pushoutKanExtension := hpushY
      bicartesian := ?_ }
  intro sq
  let sqX := mapVertex
    (internalHomPostcompBicategoricalEquivalence e SquareShape).inv sq
  exact (isPullbackSquare_bicategoricalEquivalence_iff e
    hX.pullbackKanExtension hpullY sq).trans
      ((hX.bicartesian sqX).trans
        (isPushoutSquare_bicategoricalEquivalence_iff e
          hX.pushoutKanExtension hpushY sq).symm)

/-- A full stable infinity structure transfers across a bicategorical equivalence. -/
noncomputable def StableInfinityStructure.ofBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (hX : StableInfinityStructure X)
    (e : Bicategory.Equivalence X Y) : StableInfinityStructure Y :=
  ((StableSquareCalculus.ofStableInfinityStructure hX).ofBicategoricalEquivalence e)
    |>.toStableInfinityStructure

/-- A full stable infinity structure transfers along any bicategorical equivalence map. -/
noncomputable def StableInfinityStructure.ofIsBicategoricalEquivalence
    {X Y : SSet.QCat.{u}} (hX : StableInfinityStructure X) (f : X ⟶ Y)
    (hf : IsBicategoricalEquivalence f) : StableInfinityStructure Y :=
  hX.ofBicategoricalEquivalence hf.choose

end LeanLCAExactChallenge.Infinity
