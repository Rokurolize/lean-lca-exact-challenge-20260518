import LeanLCAExactChallenge.Derived.Bounded

set_option autoImplicit false

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

namespace LocalizedFunctorTriangulatedTransfer

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift D₁ ℤ] [HasShift D₂ ℤ]
  [HasZeroObject C₁] [HasZeroObject C₂] [HasZeroObject D₁] [HasZeroObject D₂]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D₁] [Preadditive D₂]
  [∀ (n : ℤ), (shiftFunctor C₁ n).Additive]
  [∀ (n : ℤ), (shiftFunctor C₂ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D₁ n).Additive]
  [∀ (n : ℤ), (shiftFunctor D₂ n).Additive]
  [Pretriangulated C₁] [Pretriangulated C₂] [Pretriangulated D₁] [Pretriangulated D₂]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  (Φ : LocalizerMorphism W₁ W₂)
  (L₁ : C₁ ⥤ D₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]
  [Φ.functor.CommShift ℤ] [L₁.CommShift ℤ] [L₂.CommShift ℤ]

omit [HasZeroObject C₂] [Preadditive C₂]
  [∀ (n : ℤ), (shiftFunctor C₂ n).Additive] [Pretriangulated C₂] in
/--
Reusable conditional transfer theorem for functors induced by a localizer morphism.

The important point is that the current mathlib shift-localization API supplies the
`CommShift` instance on `Φ.localizedFunctor L₁ L₂` and the `NatTrans.CommShift`
coherence for `CatCommSq.iso`, so the remaining inputs are triangulatedness of the
source localization functor, essential surjectivity on arrows for that source functor,
and triangulatedness of the lifted composite.
-/
theorem localizedFunctor_isTriangulated_of_catCommSq
    [W₁.IsCompatibleWithShift ℤ] [W₂.IsCompatibleWithShift ℤ]
    [L₁.mapArrow.EssSurj] [L₁.IsTriangulated] [(Φ.functor ⋙ L₂).IsTriangulated] :
    (Φ.localizedFunctor L₁ L₂).IsTriangulated := by
  let e₀ : Φ.functor ⋙ L₂ ≅ L₁ ⋙ Φ.localizedFunctor L₁ L₂ :=
    CatCommSq.iso Φ.functor L₁ L₂ (Φ.localizedFunctor L₁ L₂)
  haveI : NatTrans.CommShift e₀.hom ℤ :=
    LocalizerMorphism.natTransCommShift_hom Φ L₁ L₂
      (Φ.localizedFunctor L₁ L₂) e₀
  haveI : NatTrans.CommShift e₀.symm.hom ℤ := inferInstance
  exact Functor.isTriangulated_of_precomp_iso (F := L₁)
    (G := Φ.localizedFunctor L₁ L₂) (H := Φ.functor ⋙ L₂) e₀.symm

section DboundedChecks

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [QuillenExactCategory C]
  [HasZeroObject C] [HasBinaryBiproducts C]

#check Dbounded.homotopyComparison C
#check Dbounded.homotopyComparisonLocalizationIso C
#check boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence C
#check (boundedExactWeakEquivalenceToHomotopyExactWeakEquivalence C).localizedFunctor
#check LocalizerMorphism.commShift
#check LocalizerMorphism.natTransCommShift_hom
#check Functor.isTriangulated_of_precomp_iso
#check Triangulated.Localization.isTriangulated_functor

end DboundedChecks

end LocalizedFunctorTriangulatedTransfer

end LeanLCAExactChallenge
