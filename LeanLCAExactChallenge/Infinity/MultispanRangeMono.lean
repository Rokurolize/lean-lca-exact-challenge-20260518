import LeanLCAExactChallenge.Infinity.SimplicialJoin

/-! # Monomorphisms assembled from ranges over a multispan -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits

variable {I : Type} [LinearOrder I]

/-- The union of the ranges of the right objects of a linear multispan is the
range of its colimit map, provided every left object maps onto the
intersection of the corresponding two right ranges. -/
lemma range_eq_iSup_right_of_linearMultispan
    {F : WalkingMultispan (MultispanShape.ofLinearOrder I) ⥤ SSet.{u}}
    (c : Cocone F)
    (hc : IsColimit c) {X : SSet.{u}} (f : c.pt ⟶ X)
    (hinf : ∀ a : (MultispanShape.ofLinearOrder I).L,
      SSet.Subcomplex.range (c.ι.app (.left a) ≫ f) =
        SSet.Subcomplex.range
            (c.ι.app (.right ((MultispanShape.ofLinearOrder I).fst a)) ≫ f) ⊓
          SSet.Subcomplex.range
            (c.ι.app (.right ((MultispanShape.ofLinearOrder I).snd a)) ≫ f)) :
    SSet.Subcomplex.range f =
      ⨆ j : I, SSet.Subcomplex.range (c.ι.app (.right j) ≫ f) := by
  rw [SSet.range_eq_iSup_of_isColimit hc f]
  apply le_antisymm
  · apply iSup_le
    rintro (a | j)
    · rw [hinf]
      exact inf_le_left.trans (le_iSup (fun k : I ↦
        SSet.Subcomplex.range (c.ι.app (.right k) ≫ f))
          ((MultispanShape.ofLinearOrder I).fst a))
    · exact le_iSup (fun k : I ↦
        SSet.Subcomplex.range (c.ι.app (.right k) ≫ f)) j
  · apply iSup_le
    intro j
    exact le_iSup (fun k : WalkingMultispan (MultispanShape.ofLinearOrder I) ↦
      SSet.Subcomplex.range (c.ι.app k ≫ f)) (.right j)

section

variable {F : WalkingMultispan (MultispanShape.ofLinearOrder I) ⥤ SSet.{u}}
  (c : Cocone F) (hc : IsColimit c) {X : SSet.{u}} (f : c.pt ⟶ X)
  (hmono : ∀ j, Mono (c.ι.app j ≫ f))
  (hinf : ∀ a : (MultispanShape.ofLinearOrder I).L,
    SSet.Subcomplex.range (c.ι.app (.left a) ≫ f) =
      SSet.Subcomplex.range
          (c.ι.app (.right ((MultispanShape.ofLinearOrder I).fst a)) ≫ f) ⊓
        SSet.Subcomplex.range
          (c.ι.app (.right ((MultispanShape.ofLinearOrder I).snd a)) ≫ f))

noncomputable def linearMultispanRangeDiagram :
    SSet.Subcomplex.MulticoequalizerDiagram
      (SSet.Subcomplex.range f)
      (fun j : I ↦ SSet.Subcomplex.range (c.ι.app (.right j) ≫ f))
      (fun j k ↦
        SSet.Subcomplex.range (c.ι.app (.right j) ≫ f) ⊓
          SSet.Subcomplex.range (c.ι.app (.right k) ≫ f)) where
  iSup_eq := (range_eq_iSup_right_of_linearMultispan c hc f hinf).symm
  eq_inf _ _ := rfl

abbrev linearMultispanRangeFunctor :=
  (((linearMultispanRangeDiagram c hc f hinf).multispanIndex.toLinearOrder.map
    SSet.Subcomplex.toSSetFunctor).multispan)

noncomputable def linearMultispanComponentIso
    (j : WalkingMultispan (MultispanShape.ofLinearOrder I)) :
    F.obj j ≅ (linearMultispanRangeFunctor c hc f hinf).obj j := by
  rcases j with a | j
  · letI : Mono (c.ι.app (.left a) ≫ f) := hmono (.left a)
    exact simplicialSetIsoRangeOfMono (c.ι.app (.left a) ≫ f) ≪≫
      SSet.Subcomplex.toSSetFunctor.mapIso (eqToIso (hinf a))
  · letI : Mono (c.ι.app (.right j) ≫ f) := hmono (.right j)
    exact simplicialSetIsoRangeOfMono (c.ι.app (.right j) ≫ f)

set_option maxHeartbeats 2000000 in
noncomputable def linearMultispanDiagramIso :
    F ≅ linearMultispanRangeFunctor c hc f hinf :=
  WalkingMultispan.functorExt
    (fun a ↦ linearMultispanComponentIso c hc f hmono hinf (.left a))
    (fun j ↦ linearMultispanComponentIso c hc f hmono hinf (.right j))
    (by
      intro a
      dsimp [linearMultispanComponentIso, linearMultispanRangeFunctor]
      simp only [Iso.trans_hom]
      dsimp [simplicialSetIsoRangeOfMono]
      apply (cancel_mono (SSet.Subcomplex.range
        (c.ι.app (.right ((MultispanShape.ofLinearOrder I).fst a)) ≫ f)).ι).mp
      simp only [Category.assoc]
      change (F.map (WalkingMultispan.Hom.fst a) ≫
          c.ι.app (.right ((MultispanShape.ofLinearOrder I).fst a))) ≫ f =
        c.ι.app (.left a) ≫ f
      have hnat := c.ι.naturality (WalkingMultispan.Hom.fst a)
      exact congrArg (fun q ↦ q ≫ f) (hnat.trans (Category.comp_id _)))
    (by
      intro a
      dsimp [linearMultispanComponentIso, linearMultispanRangeFunctor]
      simp only [Iso.trans_hom]
      dsimp [simplicialSetIsoRangeOfMono]
      apply (cancel_mono (SSet.Subcomplex.range
        (c.ι.app (.right ((MultispanShape.ofLinearOrder I).snd a)) ≫ f)).ι).mp
      simp only [Category.assoc]
      change (F.map (WalkingMultispan.Hom.snd a) ≫
          c.ι.app (.right ((MultispanShape.ofLinearOrder I).snd a))) ≫ f =
        c.ι.app (.left a) ≫ f
      have hnat := c.ι.naturality (WalkingMultispan.Hom.snd a)
      exact congrArg (fun q ↦ q ≫ f) (hnat.trans (Category.comp_id _)))

noncomputable def linearMultispanRangeCocone :=
  (linearMultispanRangeDiagram c hc f hinf).multicofork.toLinearOrder.map
    SSet.Subcomplex.toSSetFunctor

noncomputable def linearMultispanRangeCoconePrecompose : Cocone F :=
  (Cocone.precompose (linearMultispanDiagramIso c hc f hmono hinf).hom).obj
    (linearMultispanRangeCocone c hc f hinf)

noncomputable def linearMultispanRangeCoconePrecomposeIsColimit :
    IsColimit (linearMultispanRangeCoconePrecompose c hc f hmono hinf) :=
  (IsColimit.precomposeHomEquiv (linearMultispanDiagramIso c hc f hmono hinf)
      (linearMultispanRangeCocone c hc f hinf)).symm
    (linearMultispanRangeDiagram c hc f hinf).isColimit'

noncomputable def linearMultispanPointIso :
    c.pt ≅ (linearMultispanRangeCoconePrecompose c hc f hmono hinf).pt :=
  hc.coconePointUniqueUpToIso
    (linearMultispanRangeCoconePrecomposeIsColimit c hc f hmono hinf)

set_option maxHeartbeats 800000 in
lemma linearMultispanPointIso_hom :
    (linearMultispanPointIso c hc f hmono hinf).hom =
      SSet.Subcomplex.toRange f := by
  apply hc.hom_ext
  intro j
  dsimp only [linearMultispanPointIso]
  rw [IsColimit.comp_coconePointUniqueUpToIso_hom]
  rcases j with a | j
  · dsimp [linearMultispanRangeCoconePrecompose, linearMultispanRangeCocone,
      linearMultispanDiagramIso, linearMultispanComponentIso,
      linearMultispanRangeFunctor]
    dsimp [simplicialSetIsoRangeOfMono]
    apply (cancel_mono (SSet.Subcomplex.range f).ι).mp
    rfl
  · dsimp [linearMultispanRangeCoconePrecompose, linearMultispanRangeCocone,
      linearMultispanDiagramIso, linearMultispanComponentIso,
      linearMultispanRangeFunctor]
    dsimp [simplicialSetIsoRangeOfMono]
    apply (cancel_mono (SSet.Subcomplex.range f).ι).mp
    rfl

/-- A map assembled as a linear multispan colimit is mono when every piece is
mono and every overlap piece has precisely the intersection range. -/
lemma mono_of_linearMultispan_ranges
    (hc : IsColimit c) (hmono : ∀ j, Mono (c.ι.app j ≫ f))
    (hinf : ∀ a : (MultispanShape.ofLinearOrder I).L,
      SSet.Subcomplex.range (c.ι.app (.left a) ≫ f) =
        SSet.Subcomplex.range
            (c.ι.app (.right ((MultispanShape.ofLinearOrder I).fst a)) ≫ f) ⊓
          SSet.Subcomplex.range
            (c.ι.app (.right ((MultispanShape.ofLinearOrder I).snd a)) ≫ f)) :
    Mono f := by
  letI : IsIso (SSet.Subcomplex.toRange f) := by
    rw [← linearMultispanPointIso_hom c hc f hmono hinf]
    infer_instance
  rw [← SSet.Subcomplex.toRange_ι (f := f)]
  infer_instance

end

end LeanLCAExactChallenge.Infinity
