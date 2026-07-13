import LeanLCAExactChallenge.Infinity.EquivalenceForcing
import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence
import LeanLCAExactChallenge.Infinity.MetrizableEquivalenceForcing
import LeanLCAExactChallenge.Infinity.MetrizableRelative
import LeanLCAExactChallenge.Infinity.OrdinaryToSimplicialNerve

/-!
# Comparing the ordinary and coherent direct dg carriers

The ordinary nerve maps canonically into the coherent direct dg nerve.

A pushout adds coherent inverses to corrected weak equivalences before fibrant replacement.

The resulting quasicategory is a candidate whose inversion property is proved here.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes

open CategoryTheory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.Limits
  Simplicial Opposite
open scoped MonoidalCategory Simplicial

/-- The ordinary nerve of the direct dg carrier maps to its homotopy-coherent nerve. -/
def directDGOrdinaryNerveToHomotopyCoherentNerve :
    nerve DirectDGSimplicialCategory ⟶ directDGHomotopyCoherentNerve :=
  OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve
    DirectDGSimplicialCategory

/-- The ordinary nerve maps canonically to the chosen quasicategorical replacement. -/
def directDGOrdinaryNerveToQCat :
    nerve DirectDGSimplicialCategory ⟶ directDGQCat.obj :=
  directDGOrdinaryNerveToHomotopyCoherentNerve ≫ directDGNerveToQCat

/-- Compare the ordinary bounded-complex nerve with the coherent direct dg carrier. -/
def metrizableComplexNerveToDirectDGHomotopyCoherentNerve :
    nerve ComplexCategory ⟶ directDGHomotopyCoherentNerve :=
  nerveMap directDGSimplicialCategoryOrdinaryEquivalence.inverse ≫
    directDGOrdinaryNerveToHomotopyCoherentNerve

/-- Compare the ordinary bounded-complex nerve with the chosen direct dg quasicategory. -/
def metrizableComplexNerveToDirectDGQCat :
    nerve ComplexCategory ⟶ directDGQCat.obj :=
  metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
    directDGNerveToQCat

@[simp]
lemma directDGOrdinaryNerveToHomotopyCoherentNerve_obj
    {n : ℕ} (F : ComposableArrows DirectDGSimplicialCategory n)
    (i : Fin (n + 1)) :
    (directDGOrdinaryNerveToHomotopyCoherentNerve.app
      (op (SimplexCategory.mk n)) F).obj
        (OrdinaryToSimplicialNerve.thickeningVertex i) =
      ForgetEnrichment.to SSet (F.obj i) :=
  rfl

lemma directDGOrdinaryNerveToHomotopyCoherentNerve_edge
    {X Y : DirectDGSimplicialCategory} (f : X ⟶ Y) :
    (directDGOrdinaryNerveToHomotopyCoherentNerve.app
      (op (SimplexCategory.mk 1)) (ComposableArrows.mk₁ f)).map
        (OrdinaryToSimplicialNerve.thickeningVertex (0 : Fin 2))
        (OrdinaryToSimplicialNerve.thickeningVertex (1 : Fin 2)) =
      toUnit _ ≫ ForgetEnrichment.homTo SSet f :=
  OrdinaryToSimplicialNerve.ordinaryNerveToSimplicialNerve_edge
    DirectDGSimplicialCategory f

/-- Send all generated corrected weak intervals into the coherent direct dg nerve. -/
def directDGWeakIntervalsToCoherentNerve :
    ∐ relativeCategory.weakIntervalFamily ⟶
      directDGHomotopyCoherentNerve :=
  relativeCategory.weakIntervalsToNerve ≫
    metrizableComplexNerveToDirectDGHomotopyCoherentNerve

/-- Adjoin coherent inverses to the corrected weak edges in the direct dg nerve. -/
abbrev directDGEquivalenceForcingPresentation : SSet.{1} :=
  pushout directDGWeakIntervalsToCoherentNerve
    relativeCategory.weakIntervalsToEquivalences

/-- The raw coherent direct dg nerve maps into its equivalence-forcing presentation. -/
def directDGCoherentNerveToEquivalenceForcingPresentation :
    directDGHomotopyCoherentNerve ⟶
      directDGEquivalenceForcingPresentation :=
  pushout.inl _ _

/-- The free-living equivalence attached to one generated corrected weak arrow. -/
def directDGEquivalenceCopy
    (a : WeakEquivalenceArrow ComplexCategory relativeCategory) :
    CategoryTheory.nerve EquivalenceInterval.{1} ⟶
      directDGEquivalenceForcingPresentation :=
  Sigma.ι (relativeCategory.weakEquivalenceFamily) a ≫
    pushout.inr _ _

@[reassoc]
theorem directDG_equivalenceIntervalInclusion_comp_equivalenceCopy
    (a : WeakEquivalenceArrow ComplexCategory relativeCategory) :
    equivalenceIntervalInclusion.{1} ≫ directDGEquivalenceCopy a =
      relativeCategory.weakArrowSimplex a ≫
        metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
          directDGCoherentNerveToEquivalenceForcingPresentation := by
  let i := Sigma.ι (relativeCategory.weakIntervalFamily) a
  let j := Sigma.ι (relativeCategory.weakEquivalenceFamily) a
  let f := directDGWeakIntervalsToCoherentNerve
  let g := relativeCategory.weakIntervalsToEquivalences
  let l := pushout.inl f g
  let r := pushout.inr f g
  have hiN : i ≫ relativeCategory.weakIntervalsToNerve =
      relativeCategory.weakArrowSimplex a := by
    exact Sigma.ι_desc (fun a => relativeCategory.weakArrowSimplex a) a
  have hif : i ≫ f = relativeCategory.weakArrowSimplex a ≫
      metrizableComplexNerveToDirectDGHomotopyCoherentNerve := by
    simp only [f, directDGWeakIntervalsToCoherentNerve,
      ← Category.assoc]
    rw [hiN]
  have hig : i ≫ g = equivalenceIntervalInclusion.{1} ≫ j := by
    exact Sigma.ι_desc
      (fun a => equivalenceIntervalInclusion.{1} ≫
        Sigma.ι (relativeCategory.weakEquivalenceFamily) a) a
  have hpush : f ≫ l = g ≫ r := pushout.condition
  change equivalenceIntervalInclusion.{1} ≫ (j ≫ r) =
    relativeCategory.weakArrowSimplex a ≫
      metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫ l
  calc
    _ = (equivalenceIntervalInclusion.{1} ≫ j) ≫ r :=
      (Category.assoc _ _ _).symm
    _ = (i ≫ g) ≫ r := congrArg (fun t => t ≫ r) hig.symm
    _ = i ≫ (g ≫ r) := Category.assoc _ _ _
    _ = i ≫ (f ≫ l) := congrArg (fun t => i ≫ t) hpush.symm
    _ = (i ≫ f) ≫ l := (Category.assoc _ _ _).symm
    _ = (relativeCategory.weakArrowSimplex a ≫
        metrizableComplexNerveToDirectDGHomotopyCoherentNerve) ≫ l :=
      congrArg (fun t => t ≫ l) hif
    _ = _ := Category.assoc _ _ _

/-- A generated corrected weak edge has a free-equivalence extension in the presentation. -/
def directDGToEquivalenceForcingPresentation_generatedExtension
    {K L : ComplexCategory} (f : K ⟶ L)
    (hf : GeneratedWeakEquivalence f) :
    EquivalenceIntervalExtension
      ((CategoryTheory.nerve.edgeMk f).map
        (metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
          directDGCoherentNerveToEquivalenceForcingPresentation)) where
  map := directDGEquivalenceCopy
    { source := K, target := L, hom := f, weak := hf }
  restrict := by
    rw [directDG_equivalenceIntervalInclusion_comp_equivalenceCopy]
    apply SSet.yonedaEquiv.injective
    simp only [RelativeCategoryData.weakArrowSimplex,
      SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      SSet.Edge.map_edge]

/-- A quasicategory obtained after adjoining inverses to corrected weak dg edges. -/
def directDGEquivalenceForcingQCat : SSet.QCat.{1} :=
  innerFibrantReplacementQCat directDGEquivalenceForcingPresentation

/-- The candidate localization map from the raw coherent dg nerve. -/
def directDGCoherentNerveToLocalizedQCat :
    directDGHomotopyCoherentNerve ⟶
      directDGEquivalenceForcingQCat.obj :=
  directDGCoherentNerveToEquivalenceForcingPresentation ≫
    toInnerFibrantReplacement directDGEquivalenceForcingPresentation

/-- The bounded-complex nerve maps into the equivalence-forced direct dg quasicategory. -/
def metrizableComplexNerveToLocalizedDirectDGQCat :
    CategoryTheory.nerve ComplexCategory ⟶
      directDGEquivalenceForcingQCat.obj :=
  metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
    directDGCoherentNerveToLocalizedQCat

/-- Every generated corrected weak edge is coherently invertible in the candidate. -/
def metrizableComplexNerveToLocalizedDirectDGQCat_generatedExtension
    {K L : ComplexCategory} (f : K ⟶ L)
    (hf : GeneratedWeakEquivalence f) :
    EquivalenceIntervalExtension
      ((CategoryTheory.nerve.edgeMk f).map
        metrizableComplexNerveToLocalizedDirectDGQCat) := by
  let h := directDGToEquivalenceForcingPresentation_generatedExtension f hf
  let r := toInnerFibrantReplacement directDGEquivalenceForcingPresentation
  refine { map := h.map ≫ r, restrict := ?_ }
  rw [← Category.assoc, h.restrict]
  apply SSet.yonedaEquiv.injective
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    SSet.Edge.map_edge, metrizableComplexNerveToLocalizedDirectDGQCat,
    directDGCoherentNerveToLocalizedQCat]
  rfl

/-- Every generated corrected weak edge is an equivalence in the candidate. -/
theorem metrizableComplexNerveToLocalizedDirectDGQCat_generatedIsEquivalence
    {K L : ComplexCategory} (f : K ⟶ L)
    (hf : GeneratedWeakEquivalence f) :
    EdgeIsEquivalence ((CategoryTheory.nerve.edgeMk f).map
      metrizableComplexNerveToLocalizedDirectDGQCat) :=
  (metrizableComplexNerveToLocalizedDirectDGQCat_generatedExtension f hf).edgeIsEquivalence

/-- Bundle the candidate as a map of quasicategories. -/
def metrizableComplexNerveToLocalizedDirectDGQCatMap :
    (⟨CategoryTheory.nerve ComplexCategory, inferInstance⟩ : SSet.QCat.{1}) ⟶
      directDGEquivalenceForcingQCat :=
  ObjectProperty.homMk metrizableComplexNerveToLocalizedDirectDGQCat

/-- The candidate inverts the complete marking generated by corrected weak arrows. -/
theorem metrizableComplexNerveToLocalizedDirectDGQCat_invertsMarkedEdges :
    InvertsMarkedEdges (relativeNerveEdgeMarking relativeCategory)
      metrizableComplexNerveToLocalizedDirectDGQCat := by
  exact relativeCategory.invertsMarkedEdges_of_weakEquivalence
    metrizableComplexNerveToLocalizedDirectDGQCat
    (fun a =>
      metrizableComplexNerveToLocalizedDirectDGQCat_generatedIsEquivalence
        a.hom a.weak)

/-- The universal property still required of the equivalence-forced direct dg candidate. -/
abbrev MetrizableDirectDGMappingLocalizationProperty : Prop :=
  MappingQuasicategoryLocalizationProperty
    (relativeNerveEdgeMarking relativeCategory)
    metrizableComplexNerveToLocalizedDirectDGQCatMap

/-- Base change from the ordinary equivalence-forcing presentation to the coherent dg one. -/
def metrizableOrdinaryToDirectDGPresentationBaseChange :
    metrizableEquivalenceForcingPresentation ⟶
      directDGEquivalenceForcingPresentation :=
  pushout.desc
    (metrizableComplexNerveToDirectDGHomotopyCoherentNerve ≫
      directDGCoherentNerveToEquivalenceForcingPresentation)
    (pushout.inr directDGWeakIntervalsToCoherentNerve
      relativeCategory.weakIntervalsToEquivalences)
    (by
      change directDGWeakIntervalsToCoherentNerve ≫
          pushout.inl directDGWeakIntervalsToCoherentNerve
            relativeCategory.weakIntervalsToEquivalences = _
      exact pushout.condition)

/-- The base-change comparison between the two inner-fibrant localization candidates. -/
def metrizableOrdinaryToDirectDGBaseChangeQCatMap :
    metrizableEquivalenceForcingQCat ⟶
      directDGEquivalenceForcingQCat :=
  ObjectProperty.homMk
    (innerFibrantReplacementFunctor.map
      metrizableOrdinaryToDirectDGPresentationBaseChange)

/-- The Dwyer--Kan or Drinfeld comparison theorem still required between the two localizations. -/
def MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence : Prop :=
  IsBicategoricalEquivalence
    metrizableOrdinaryToDirectDGBaseChangeQCatMap

end LeanLCAExactChallenge.Infinity.MetrizableBoundedComplexes
