import LeanLCAExactChallenge.Infinity.CoherentNerveKanExtension

/-!
# Compatibility of coherent-nerve path latching maps

Composition factors through the known-path latching subcomplex.

The through-vertex piece is the product of the two shorter path nerves.

Kan extension preserves the resulting enriched-composition equation.

The omitted-vertex map and its overlap equation remain to be constructed.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration

open CategoryTheory Simplicial MonoidalCategory
open CategoryTheory.SimplicialCategory CategoryTheory.EnrichedCategory
open Path Chain Chain.PathChain

/-- The enriched functor carried by one available codimension-one face of a coherent horn. -/
def innerHornFaceFunctor (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {n : ℕ} {k l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) :
    CategoryTheory.EnrichedFunctor SSet
      (CategoryTheory.SimplicialThickening (ULift (Fin (n + 2)))) C :=
  σ.app _ (SSet.horn.face k l hlk)

/-- Restriction of a horn face agrees with the corresponding face operator. -/
theorem innerHornFaceFunctor_restrict (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {n : ℕ} {k l : Fin (n + 3)}
    (σ : (SSet.horn (n + 2) k : SSet.{u}) ⟶ CategoryTheory.SimplicialNerve C)
    (hlk : l ≠ k) (a : Fin (n + 2)) :
    σ.app _ ((SSet.horn (n + 2) k : SSet).map (SimplexCategory.δ a).op
      (SSet.horn.face k l hlk)) =
      (CategoryTheory.SimplicialThickening.functor
        (SimplexCategory.δ a).toOrderHom.uliftMap).comp
          (E := C) SSet (innerHornFaceFunctor C σ hlk) := by
  exact σ.naturality_apply (SimplexCategory.δ a).op (SSet.horn.face k l hlk)

/-- Composition lands in paths whose least member contains the middle vertex. -/
def pathCompositionToKnownPathSubcomplex {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j)) ⟶
      (knownPathSubcomplex i.as j.as k.as : SSet) :=
  SSet.Subcomplex.lift (CategoryTheory.eComp SSet i k j) (by
    rintro U _ ⟨x, rfl⟩
    change (ofNerveSimplex ((CategoryTheory.eComp SSet i k j).app U x)).KnownAt k.as
    left
    change k.as ∈ (((x.1.prod' x.2) ⋙
      CategoryTheory.SimplicialThickening.compFunctor i k j).obj 0).I
    exact Or.inl (x.1.obj 0).right)

@[reassoc (attr := simp)]
theorem pathCompositionToKnownPathSubcomplex_ι {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    pathCompositionToKnownPathSubcomplex i k j ≫
      (knownPathSubcomplex i.as j.as k.as).ι = CategoryTheory.eComp SSet i k j :=
  rfl

/-- The subcomplex of path chains all of whose paths contain the intermediate vertex. -/
def throughPathSubcomplex {J : Type u} [LinearOrder J] (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex where
  obj U := {x | k ∈ (ofNerveSimplex x).first.I}
  map {U V} f x hx := by
    change k ∈ (ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x)).first.I
    rw [show ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x) =
        (ofNerveSimplex x).reindex f.unop.toOrderHom by
      rw [← toNerveSimplex_ofNerveSimplex x]
      exact ofNerveSimplex_map_toNerveSimplex _ _]
    exact (ofNerveSimplex x).first_le _ hx

/-- The subcomplex of path chains all of whose paths omit a specified vertex. -/
def avoidingPathSubcomplex {J : Type u} [LinearOrder J] (i j l : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex where
  obj U := {x | l ∉ (ofNerveSimplex x).last.I}
  map {U V} f x hx := by
    change l ∉ (ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x)).last.I
    rw [show ofNerveSimplex
      ((CategoryTheory.nerve (ThickPath i j)).map f x) =
        (ofNerveSimplex x).reindex f.unop.toOrderHom by
      rw [← toNerveSimplex_ofNerveSimplex x]
      exact ofNerveSimplex_map_toNerveSimplex _ _]
    exact (ofNerveSimplex x).not_mem_of_not_mem_last hx _

/-- Known paths are through paths or omit a nonmissing vertex. -/
theorem knownPathSubcomplex_eq_through_sup_avoiding {J : Type u} [LinearOrder J]
    (i j k : J) :
    knownPathSubcomplex i j k =
      throughPathSubcomplex i j k ⊔
        ⨆ (l : {l : J // i ≤ l ∧ l ≤ j ∧ l ≠ k}),
          avoidingPathSubcomplex i j l.1 := by
  ext U x
  constructor
  · intro h
    change (ofNerveSimplex x).KnownAt k at h
    rcases h with hk | ⟨l, hil, hlj, hlk, hl⟩
    · exact Or.inl hk
    · apply Or.inr
      simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
      exact ⟨⟨l, hil, hlj, hlk⟩, hl⟩
  · intro h
    change (ofNerveSimplex x).KnownAt k
    rcases h with hk | havoid
    · exact Or.inl hk
    · simp only [Subfunctor.iSup_obj, Set.mem_iUnion] at havoid
      obtain ⟨l, hl⟩ := havoid
      exact Or.inr ⟨l.1, l.2.1, l.2.2.1, l.2.2.2, hl⟩

/-- The union of all known-path pieces obtained by omitting a nonmissing vertex. -/
def avoidingKnownPathSubcomplex {J : Type u} [LinearOrder J] (i j k : J) :
    (CategoryTheory.nerve (ThickPath i j)).Subcomplex :=
  ⨆ (l : {l : J // i ≤ l ∧ l ≤ j ∧ l ≠ k}), avoidingPathSubcomplex i j l.1

/-- The binary through/omitted decomposition of the known-path latching subcomplex. -/
theorem knownPathSubcomplex_eq_through_sup_avoidingKnown {J : Type u}
    [LinearOrder J] (i j k : J) :
    knownPathSubcomplex i j k =
      throughPathSubcomplex i j k ⊔ avoidingKnownPathSubcomplex i j k :=
  knownPathSubcomplex_eq_through_sup_avoiding i j k

/-- Include through paths into known paths. -/
def throughPathSubcomplexToKnown {J : Type u} [LinearOrder J] (i j k : J) :
    (throughPathSubcomplex i j k : SSet) ⟶ (knownPathSubcomplex i j k : SSet) :=
  SSet.Subcomplex.homOfLE (by
    intro U x hx
    exact Or.inl hx)

/-- Include the omitted-vertex union into known paths. -/
def avoidingKnownPathSubcomplexToKnown {J : Type u} [LinearOrder J] (i j k : J) :
    (avoidingKnownPathSubcomplex i j k : SSet) ⟶
      (knownPathSubcomplex i j k : SSet) :=
  SSet.Subcomplex.homOfLE (by
    intro U x hx
    simp only [avoidingKnownPathSubcomplex, Subfunctor.iSup_obj, Set.mem_iUnion] at hx
    obtain ⟨l, hl⟩ := hx
    exact Or.inr ⟨l.1, l.2.1, l.2.2.1, l.2.2.2, hl⟩)

/-- Glue the through and omitted-vertex maps. -/
noncomputable def knownPathMapOfCompatibleParts {J : Type u} [LinearOrder J]
    (i j k : J) {X : SSet.{u}}
    (throughMap : (throughPathSubcomplex i j k : SSet) ⟶ X)
    (avoidingMap : (avoidingKnownPathSubcomplex i j k : SSet) ⟶ X)
    (hcompat :
      SSet.Subcomplex.homOfLE (inf_le_left :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            throughPathSubcomplex i j k) ≫ throughMap =
        SSet.Subcomplex.homOfLE (inf_le_right :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            avoidingKnownPathSubcomplex i j k) ≫ avoidingMap) :
    (knownPathSubcomplex i j k : SSet) ⟶ X :=
  (SSet.Subcomplex.eqToIso
    (knownPathSubcomplex_eq_through_sup_avoidingKnown i j k)).hom ≫
      (SSet.Subcomplex.inf_inclusions_isPushout
        (throughPathSubcomplex i j k) (avoidingKnownPathSubcomplex i j k)).desc
          throughMap avoidingMap hcompat

@[reassoc]
theorem throughPathSubcomplexToKnown_knownPathMapOfCompatibleParts
    {J : Type u} [LinearOrder J] (i j k : J) {X : SSet.{u}}
    (throughMap : (throughPathSubcomplex i j k : SSet) ⟶ X)
    (avoidingMap : (avoidingKnownPathSubcomplex i j k : SSet) ⟶ X)
    (hcompat :
      SSet.Subcomplex.homOfLE (inf_le_left :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            throughPathSubcomplex i j k) ≫ throughMap =
        SSet.Subcomplex.homOfLE (inf_le_right :
          throughPathSubcomplex i j k ⊓ avoidingKnownPathSubcomplex i j k ≤
            avoidingKnownPathSubcomplex i j k) ≫ avoidingMap) :
    throughPathSubcomplexToKnown i j k ≫
      knownPathMapOfCompatibleParts i j k throughMap avoidingMap hcompat = throughMap := by
  rw [knownPathMapOfCompatibleParts]
  have hinc : throughPathSubcomplexToKnown i j k ≫
      (SSet.Subcomplex.eqToIso
        (knownPathSubcomplex_eq_through_sup_avoidingKnown i j k)).hom =
      SSet.Subcomplex.homOfLE (le_sup_left : throughPathSubcomplex i j k ≤
        throughPathSubcomplex i j k ⊔ avoidingKnownPathSubcomplex i j k) := by
    rfl
  rw [← Category.assoc, hinc]
  exact (SSet.Subcomplex.inf_inclusions_isPushout
    (throughPathSubcomplex i j k) (avoidingKnownPathSubcomplex i j k)).inl_desc _ _ _

/-- Split every path of a through-vertex chain before the intermediate vertex. -/
def Chain.PathChain.beforeAt {J : Type u} [LinearOrder J] {r : ℕ} {i j k : J}
    (c : PathChain r i j) (hk : k ∈ c.first.I) : PathChain r i k where
  path a := beforePath (c.path a) (c.mem_of_mem_first hk a)
  monotone' {_a _b} hab _l hl := ⟨c.monotone' hab hl.1, hl.2⟩

/-- Split every path of a through-vertex chain after the intermediate vertex. -/
def Chain.PathChain.afterAt {J : Type u} [LinearOrder J] {r : ℕ} {i j k : J}
    (c : PathChain r i j) (hk : k ∈ c.first.I) : PathChain r k j where
  path a := afterPath (c.path a) (c.mem_of_mem_first hk a)
  monotone' {_a _b} hab _l hl := ⟨c.monotone' hab hl.1, hl.2⟩

@[simp]
theorem Chain.PathChain.join_beforeAt_afterAt {J : Type u} [LinearOrder J]
    {r : ℕ} {i j k : J} (c : PathChain r i j) (hk : k ∈ c.first.I)
    (a : Fin (r + 1)) :
    join ((c.beforeAt hk).path a) ((c.afterAt hk).path a) = c.path a :=
  beforePath_comp_afterPath (c.path a) (c.mem_of_mem_first hk a)

/-- Split a through-vertex path chain into the two shorter path chains. -/
noncomputable def throughPathSubcomplexToProduct {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (throughPathSubcomplex i.as j.as k.as : SSet) ⟶
      CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j) where
  app U := by
    obtain ⟨⟨r⟩⟩ := U
    exact ↾fun x ↦
      let c := ofNerveSimplex x.1
      ⟨(c.beforeAt x.2).toNerveSimplex, (c.afterAt x.2).toNerveSimplex⟩
  naturality := by
    rintro ⟨⟨r⟩⟩ ⟨⟨s⟩⟩ f
    ext x
    apply Prod.ext
    · exact CategoryTheory.Functor.ext
        (h_obj := fun _ ↦ rfl)
        (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
    · exact CategoryTheory.Functor.ext
        (h_obj := fun _ ↦ rfl)
        (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Compose shorter path chains into the through-path subcomplex. -/
def pathCompositionToThroughPathSubcomplex {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j)) ⟶
      (throughPathSubcomplex i.as j.as k.as : SSet) :=
  SSet.Subcomplex.lift (CategoryTheory.eComp SSet i k j) (by
    rintro U _ ⟨x, rfl⟩
    change k.as ∈ (ofNerveSimplex ((CategoryTheory.eComp SSet i k j).app U x)).first.I
    change k.as ∈ (((x.1.prod' x.2) ⋙
      CategoryTheory.SimplicialThickening.compFunctor i k j).obj 0).I
    exact Or.inl (x.1.obj 0).right)

/-- Composition followed by path splitting is the identity. -/
theorem pathCompositionToThrough_split {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    pathCompositionToThroughPathSubcomplex i k j ≫
        throughPathSubcomplexToProduct i k j = 𝟙 _ := by
  ext U x
  case h_fst =>
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ congrArg Prod.fst
        (splitCritical_joinCritical (x.1.obj a, x.2.obj a)))
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)
  case h_snd =>
    exact CategoryTheory.Functor.ext
      (h_obj := fun a ↦ congrArg Prod.snd
        (splitCritical_joinCritical (x.1.obj a, x.2.obj a)))
      (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- Splitting followed by composition is the identity on the through-vertex subcomplex. -/
theorem split_pathCompositionToThrough {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    throughPathSubcomplexToProduct i k j ≫
      pathCompositionToThroughPathSubcomplex i k j = 𝟙 _ := by
  ext U x
  apply Subtype.ext
  exact CategoryTheory.Functor.ext
    (h_obj := fun a ↦ (ofNerveSimplex x.1).join_beforeAt_afterAt x.2 a)
    (h_map := fun _ _ _ ↦ (thickPathHomSubsingleton _ _).elim _ _)

/-- The through-vertex latching piece is exactly the product of the two shorter path nerves. -/
noncomputable def throughPathSubcomplexProductIso {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    (CategoryTheory.nerve (i ⟶ k) ⊗ CategoryTheory.nerve (k ⟶ j)) ≅
      (throughPathSubcomplex i.as j.as k.as : SSet) where
  hom := pathCompositionToThroughPathSubcomplex i k j
  inv := throughPathSubcomplexToProduct i k j
  hom_inv_id := pathCompositionToThrough_split i k j
  inv_hom_id := split_pathCompositionToThrough i k j

@[reassoc (attr := simp)]
theorem pathCompositionToThrough_toKnown {J : Type u} [LinearOrder J]
    (i k j : CategoryTheory.SimplicialThickening J) :
    pathCompositionToThroughPathSubcomplex i k j ≫
      throughPathSubcomplexToKnown i.as j.as k.as =
        pathCompositionToKnownPathSubcomplex i k j :=
  rfl

/-- Shorter interval maps force the map on through paths. -/
noncomputable def forcedThroughPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j)) :
    (throughPathSubcomplex i.as j.as k.as : SSet) ⟶ (obj i ⟶[SSet] obj j) :=
  (throughPathSubcomplexProductIso i k j).inv ≫
    (leftMap ⊗ₘ rightMap) ≫ CategoryTheory.eComp SSet (obj i) (obj k) (obj j)

@[reassoc]
theorem pathCompositionToThrough_forcedThroughPathMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j)) :
    pathCompositionToThroughPathSubcomplex i k j ≫
      forcedThroughPathMap C obj i k j leftMap rightMap =
        (leftMap ⊗ₘ rightMap) ≫
          CategoryTheory.eComp SSet (obj i) (obj k) (obj j) := by
  rw [forcedThroughPathMap, ← Category.assoc]
  change (((throughPathSubcomplexProductIso i k j).hom ≫
      (throughPathSubcomplexProductIso i k j).inv) ≫ _) = _
  rw [(throughPathSubcomplexProductIso i k j).hom_inv_id, Category.id_comp]

/-- A compatible latching map agrees with shorter-interval composition. -/
structure CompatibleKnownPathLatchingMap (C : Type u) [Category.{u} C]
    [CategoryTheory.SimplicialCategory C] {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j)) where
  map : (knownPathSubcomplex i.as j.as k.as : SSet) ⟶ (obj i ⟶[SSet] obj j)
  map_comp :
    pathCompositionToKnownPathSubcomplex i k j ≫ map =
      (leftMap ⊗ₘ rightMap) ≫ CategoryTheory.eComp SSet (obj i) (obj k) (obj j)

/-- An overlap equation glues an omitted-vertex map into a compatible latching map. -/
noncomputable def CompatibleKnownPathLatchingMap.ofAvoidingMap
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j))
    (avoidingMap : (avoidingKnownPathSubcomplex i.as j.as k.as : SSet) ⟶
      (obj i ⟶[SSet] obj j))
    (hcompat :
      SSet.Subcomplex.homOfLE (inf_le_left :
          throughPathSubcomplex i.as j.as k.as ⊓
              avoidingKnownPathSubcomplex i.as j.as k.as ≤
            throughPathSubcomplex i.as j.as k.as) ≫
            forcedThroughPathMap C obj i k j leftMap rightMap =
        SSet.Subcomplex.homOfLE (inf_le_right :
          throughPathSubcomplex i.as j.as k.as ⊓
              avoidingKnownPathSubcomplex i.as j.as k.as ≤
            avoidingKnownPathSubcomplex i.as j.as k.as) ≫ avoidingMap) :
    CompatibleKnownPathLatchingMap C obj i k j leftMap rightMap where
  map := knownPathMapOfCompatibleParts i.as j.as k.as
    (forcedThroughPathMap C obj i k j leftMap rightMap) avoidingMap hcompat
  map_comp := by
    rw [← pathCompositionToThrough_toKnown i k j, Category.assoc,
      throughPathSubcomplexToKnown_knownPathMapOfCompatibleParts]
    exact pathCompositionToThrough_forcedThroughPathMap
      C obj i k j leftMap rightMap

/-- Kan extension preserves the forced composition equation. -/
theorem exists_pathMap_extension_preserving_comp
    (C : Type u) [Category.{u} C] [CategoryTheory.SimplicialCategory C]
    {J : Type u} [LinearOrder J] [Finite J]
    (obj : CategoryTheory.SimplicialThickening J → C)
    (i k j : CategoryTheory.SimplicialThickening J)
    (hik : i.as < k.as) (hkj : k.as < j.as)
    (leftMap : CategoryTheory.nerve (i ⟶ k) ⟶ (obj i ⟶[SSet] obj k))
    (rightMap : CategoryTheory.nerve (k ⟶ j) ⟶ (obj k ⟶[SSet] obj j))
    (latching : CompatibleKnownPathLatchingMap C obj i k j leftMap rightMap)
    [SSet.KanComplex (obj i ⟶[SSet] obj j)] :
    ∃ map : CategoryTheory.nerve (i ⟶ j) ⟶ (obj i ⟶[SSet] obj j),
      (knownPathSubcomplex i.as j.as k.as).ι ≫ map = latching.map ∧
        CategoryTheory.eComp SSet i k j ≫ map =
          (leftMap ⊗ₘ rightMap) ≫
            CategoryTheory.eComp SSet (obj i) (obj k) (obj j) := by
  obtain ⟨map, hmap⟩ := exists_knownPathSubcomplex_extension_of_kan_of_fintype
    hik hkj latching.map
  refine ⟨map, hmap, ?_⟩
  rw [← pathCompositionToKnownPathSubcomplex_ι i k j, Category.assoc, hmap]
  exact latching.map_comp

end LeanLCAExactChallenge.Infinity.CoherentNervePathFiltration
