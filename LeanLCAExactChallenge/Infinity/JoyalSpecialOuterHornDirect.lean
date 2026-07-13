import LeanLCAExactChallenge.Infinity.JoyalBoundaryDiagram
import LeanLCAExactChallenge.Infinity.JoyalDiagramProjection
import LeanLCAExactChallenge.Infinity.LeftFibrationIsoLift

/-! # Direct join-slice proof of Joyal's special outer horn theorem -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped CategoryTheory.MonoidalCategory.DayConvolution MonoidalCategory

/-- Recover the augmented map represented by an augmented-degree point of the Day internal
hom. -/
def mapOfDayInternalHomStar {F G : AugmentedSSet.{u}}
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) : F ⟶ G where
  app j := ConcreteCategory.ofHom (TypeCat.Fun.mk (fun x ↦
    G.map (ρ_ j).hom (ConcreteCategory.hom (v.1 j) x)))
  naturality {i j} f := by
    apply ConcreteCategory.hom_ext
    intro x
    have hv := v.2 f
    change G.map (ρ_ j).hom (ConcreteCategory.hom (v.1 j) (F.map f x)) =
      G.map f (G.map (ρ_ i).hom (ConcreteCategory.hom (v.1 i) x))
    have hx := ConcreteCategory.congr_hom hv x
    change G.map (f ▷ 𝟙_ _) (ConcreteCategory.hom (v.1 i) x) =
      ConcreteCategory.hom (v.1 j) (F.map f x) at hx
    rw [← hx]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun q ↦ ConcreteCategory.hom (G.map q)
      (ConcreteCategory.hom (v.1 i) x))
        (MonoidalCategory.rightUnitor_naturality f)

theorem mapOfDayInternalHomStar_dayInternalHomStarOfMap
    {F G : AugmentedSSet.{u}} (a : F ⟶ G) :
    mapOfDayInternalHomStar (dayInternalHomStarOfMap a) = a := by
  apply NatTrans.ext
  funext j
  apply ConcreteCategory.hom_ext
  intro x
  change G.map (ρ_ j).hom
      (ConcreteCategory.hom ((dayInternalHomStarOfMap a).1 j) x) = a.app j x
  unfold dayInternalHomStarOfMap
  dsimp
  change G.map (ρ_ j).hom (G.map (ρ_ j).inv (a.app j x)) = a.app j x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.inv_hom_id]
  exact ConcreteCategory.congr_hom (G.map_id j) (a.app j x)

theorem dayInternalHomStarOfMap_mapOfDayInternalHomStar
    {F G : AugmentedSSet.{u}}
    (v : (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star)) :
    dayInternalHomStarOfMap (mapOfDayInternalHomStar v) = v := by
  apply Subtype.ext
  funext j
  apply ConcreteCategory.hom_ext
  intro x
  unfold dayInternalHomStarOfMap mapOfDayInternalHomStar
  dsimp
  change G.map (ρ_ j).inv (G.map (ρ_ j).hom
      (ConcreteCategory.hom (v.1 j) x)) = ConcreteCategory.hom (v.1 j) x
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Iso.hom_inv_id]
  exact ConcreteCategory.congr_hom
    (G.map_id (j ⊗ (𝟙_ AugmentedSimplexCategoryᵒᵖ)))
    (ConcreteCategory.hom (v.1 j) x)

/-- Augmented-degree points of the Day internal hom are exactly augmented maps. -/
def dayInternalHomStarEquiv (F G : AugmentedSSet.{u}) :
    (F ⟶ G) ≃ (augmentedDayInternalHom F G).obj (Opposite.op WithInitial.star) where
  toFun := dayInternalHomStarOfMap
  invFun := mapOfDayInternalHomStar
  left_inv := mapOfDayInternalHomStar_dayInternalHomStarOfMap
  right_inv := dayInternalHomStarOfMap_mapOfDayInternalHomStar

/-- The base augmented map obtained by evaluating the transpose of a Day-convolution map
at the augmented point of its right input. -/
def dayConvolutionBaseMap
    (F G : AugmentedSSet.{u}) (L : SSet.{u})
    (tau : letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
      CategoryTheory.MonoidalCategory.DayConvolution.convolution F
        (emptyAugmentation.{u}.obj L) ⟶ G) : F ⟶ G := by
  letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
  exact mapOfDayInternalHomStar
    ((augmentedDayHomEquiv F (emptyAugmentation.{u}.obj L) G tau).app
      (Opposite.op WithInitial.star) (emptyAugmentationStarPoint L))

/-- Every Day-convolution map is canonically fixed over the base map extracted from its
augmented-degree value. -/
def fixedBaseDayConvolutionMapOfMap
    (F G : AugmentedSSet.{u}) (L : SSet.{u})
    (tau : letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
      CategoryTheory.MonoidalCategory.DayConvolution.convolution F
        (emptyAugmentation.{u}.obj L) ⟶ G) :
    FixedBaseDayConvolutionMapOver F G L (dayConvolutionBaseMap F G L tau) := by
  letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
  refine ⟨tau, ?_⟩
  exact (dayInternalHomStarOfMap_mapOfDayInternalHomStar
    ((augmentedDayHomEquiv F (emptyAugmentation.{u}.obj L) G tau).app
      (Opposite.op WithInitial.star) (emptyAugmentationStarPoint L))).symm

theorem dayConvolutionBaseMap_precomp_left
    {F F' G : AugmentedSSet.{u}} (uMap : F' ⟶ F) (L : SSet.{u})
    (tau : letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
      CategoryTheory.MonoidalCategory.DayConvolution.convolution F
        (emptyAugmentation.{u}.obj L) ⟶ G) :
    letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
    letI := augmentedDayConvolution F' (emptyAugmentation.{u}.obj L)
    dayConvolutionBaseMap F' G L
        (CategoryTheory.MonoidalCategory.DayConvolution.map uMap
          (𝟙 (emptyAugmentation.{u}.obj L)) ≫ tau) =
      uMap ≫ dayConvolutionBaseMap F G L tau := by
  letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
  letI := augmentedDayConvolution F' (emptyAugmentation.{u}.obj L)
  apply (dayInternalHomStarEquiv F' G).injective
  change dayInternalHomStarOfMap
      (dayConvolutionBaseMap F' G L
        (CategoryTheory.MonoidalCategory.DayConvolution.map uMap
          (𝟙 (emptyAugmentation.{u}.obj L)) ≫ tau)) =
    dayInternalHomStarOfMap (uMap ≫ dayConvolutionBaseMap F G L tau)
  dsimp only [dayConvolutionBaseMap]
  rw [dayInternalHomStarOfMap_mapOfDayInternalHomStar]
  rw [← augmentedDayInternalHomPre_starOfMap]
  rw [dayInternalHomStarOfMap_mapOfDayInternalHomStar]
  have h := congrArg (fun k ↦ k.app (Opposite.op WithInitial.star)
      (emptyAugmentationStarPoint L))
    (augmentedDayHomEquiv_precomp_left uMap tau)
  exact h

theorem dayConvolutionBaseMap_precomp_right
    {F G : AugmentedSSet.{u}} {L L' : SSet.{u}} (g : L' ⟶ L)
    (tau : letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
      CategoryTheory.MonoidalCategory.DayConvolution.convolution F
        (emptyAugmentation.{u}.obj L) ⟶ G) :
    letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
    letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L')
    dayConvolutionBaseMap F G L'
        ((augmentedDayTensorLeft F).map (emptyAugmentation.{u}.map g) ≫ tau) =
      dayConvolutionBaseMap F G L tau := by
  letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L)
  letI := augmentedDayConvolution F (emptyAugmentation.{u}.obj L')
  apply (dayInternalHomStarEquiv F G).injective
  change dayInternalHomStarOfMap
      (dayConvolutionBaseMap F G L'
        ((augmentedDayTensorLeft F).map (emptyAugmentation.{u}.map g) ≫ tau)) =
    dayInternalHomStarOfMap (dayConvolutionBaseMap F G L tau)
  dsimp only [dayConvolutionBaseMap]
  rw [dayInternalHomStarOfMap_mapOfDayInternalHomStar,
    dayInternalHomStarOfMap_mapOfDayInternalHomStar]
  have h := congrArg (fun k ↦ k.app (Opposite.op WithInitial.star)
      (emptyAugmentationStarPoint L'))
    (augmentedDayHomEquiv_precomp F (emptyAugmentation.{u}.obj L)
      (emptyAugmentation.{u}.obj L') G (emptyAugmentation.{u}.map g) tau)
  have hp : (emptyAugmentation.{u}.map g).app (Opposite.op WithInitial.star)
      (emptyAugmentationStarPoint L') = emptyAugmentationStarPoint L := by
    let uL : Unique ((emptyAugmentation.{u}.obj L).obj
        (Opposite.op WithInitial.star)) :=
      (Limits.Types.isTerminalEquivUnique _) (emptyAugmentationStarIsTerminal L)
    exact (uL.uniq _).trans (uL.uniq (emptyAugmentationStarPoint L)).symm
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, hp] using h

theorem augmentedJoinMapOfUnderlying_precomp
    {K K' L L' Q : SSet.{u}} (f : K' ⟶ K) (g : L' ⟶ L)
    (psi : simplicialJoin K L ⟶ Q) :
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj L)
    letI := augmentedDayConvolution
      (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj L')
    augmentedJoinMapOfUnderlying K' L' Q (simplicialJoinMap f g ≫ psi) =
      CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.{u}.map f) (emptyAugmentation.{u}.map g) ≫
          augmentedJoinMapOfUnderlying K L Q psi := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj L)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj L')
  apply augmentedMapToEmptyAugmentation_ext
  rw [Functor.map_comp, forgetAugmentation_augmentedJoinMapOfUnderlying,
    forgetAugmentation_augmentedJoinMapOfUnderlying]
  rfl

/-- The ordinary base diagram extracted from a map out of a simplicial join. -/
def joinMapBase (K L Q : SSet.{u}) (g : simplicialJoin K L ⟶ Q) : K ⟶ Q :=
  forgetAugmentation.{u}.map
    (dayConvolutionBaseMap (emptyAugmentation.{u}.obj K)
      (emptyAugmentation.{u}.obj Q) L (augmentedJoinMapOfUnderlying K L Q g))

lemma emptyAugmentation_map_joinMapBase
    (K L Q : SSet.{u}) (g : simplicialJoin K L ⟶ Q) :
    emptyAugmentation.{u}.map (joinMapBase K L Q g) =
      dayConvolutionBaseMap (emptyAugmentation.{u}.obj K)
        (emptyAugmentation.{u}.obj Q) L (augmentedJoinMapOfUnderlying K L Q g) := by
  apply augmentedMapToEmptyAugmentation_ext
  rfl

theorem joinMapBase_precomp_left
    {K K' L Q : SSet.{u}} (f : K' ⟶ K)
    (g : simplicialJoin K L ⟶ Q) :
    joinMapBase K' L Q (simplicialJoinMap f (𝟙 L) ≫ g) =
      f ≫ joinMapBase K L Q g := by
  unfold joinMapBase
  rw [augmentedJoinMapOfUnderlying_precomp]
  rw [emptyAugmentation.map_id]
  rw [dayConvolutionBaseMap_precomp_left]
  rw [Functor.map_comp]
  rfl

theorem joinMapBase_precomp_right
    {K L L' Q : SSet.{u}} (g : L' ⟶ L)
    (psi : simplicialJoin K L ⟶ Q) :
    joinMapBase K L' Q (simplicialJoinMap (𝟙 K) g ≫ psi) =
      joinMapBase K L Q psi := by
  unfold joinMapBase
  rw [augmentedJoinMapOfUnderlying_precomp]
  rw [emptyAugmentation.map_id]
  exact congrArg forgetAugmentation.{u}.map
    (dayConvolutionBaseMap_precomp_right
      (F := emptyAugmentation.{u}.obj K)
      (G := emptyAugmentation.{u}.obj Q) g
      (augmentedJoinMapOfUnderlying K L Q psi))

/-- The augmented join map bundled over the ordinary base diagram extracted from it. -/
def joinMapFixedBaseCone
    (K L Q : SSet.{u}) (g : simplicialJoin K L ⟶ Q) :
    FixedBaseDayConvolutionMapOver
      (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
      (emptyAugmentation.{u}.map (joinMapBase K L Q g)) := by
  let F := emptyAugmentation.{u}.obj K
  let G := emptyAugmentation.{u}.obj Q
  let tau := augmentedJoinMapOfUnderlying K L Q g
  refine ⟨tau, ?_⟩
  rw [emptyAugmentation_map_joinMapBase]
  exact (fixedBaseDayConvolutionMapOfMap F G L tau).2

/-- A map out of a join, curried into the diagram-under-slice over its extracted base. -/
noncomputable def joinMapDiagramUnderCurry
    (K L Q : SSet.{u}) (g : simplicialJoin K L ⟶ Q) :
    L ⟶ diagramUnderSlice Q K (joinMapBase K L Q g) := by
  let F := emptyAugmentation.{u}.obj K
  let G := emptyAugmentation.{u}.obj Q
  exact (relativeDaySliceOverMapFixedBaseEquiv F G L
    (emptyAugmentation.{u}.map (joinMapBase K L Q g))).symm
      (joinMapFixedBaseCone K L Q g)

theorem joinMapDiagramUnderCurry_fixedBaseCone
    (K L Q : SSet.{u}) (g : simplicialJoin K L ⟶ Q) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
          (emptyAugmentation.{u}.map (joinMapBase K L Q g)))
            (joinMapDiagramUnderCurry K L Q g)).1 = g := by
  let F := emptyAugmentation.{u}.obj K
  let G := emptyAugmentation.{u}.obj Q
  have h := Equiv.apply_symm_apply
    (relativeDaySliceOverMapFixedBaseEquiv F G L
      (emptyAugmentation.{u}.map (joinMapBase K L Q g)))
      (joinMapFixedBaseCone K L Q g)
  have hmap := congrArg (fun k ↦ forgetAugmentation.{u}.map k.1) h
  exact hmap.trans (forgetAugmentation_augmentedJoinMapOfUnderlying K L Q g)

/-- The normalized boundary-join corner at the last vertex is the corresponding right
outer horn. -/
noncomputable def normalizedJoinBoundaryRightOuterHornSourceIso
    (m : ℕ) [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))] :
    (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).pt ≅
      (SSet.horn (m + 3) (Fin.last (m + 3)) : SSet.{u}) :=
  simplicialSetIsoRangeOfMono
      (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2)) ≪≫
    SSet.Subcomplex.toSSetFunctor.mapIso
      (eqToIso (by
        rw [normalizedJoinBoundaryHornCornerMap_range_eq_horn]
        congr 1))

@[reassoc (attr := simp)]
lemma normalizedJoinBoundaryRightOuterHornSourceIso_hom_comp_ι
    (m : ℕ) [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))] :
    (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom ≫
        (SSet.horn (m + 3) (Fin.last (m + 3))).ι =
      normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2) := by
  dsimp [normalizedJoinBoundaryRightOuterHornSourceIso,
    simplicialSetIsoRangeOfMono]
  simp

def rightOuterHornCornerTop
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).pt ⟶ Q :=
  (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom ≫ h

def rightOuterHornFullLeg
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    simplicialJoin (Δ[m + 1] : SSet.{u}) Λ[1, (1 : Fin 2)] ⟶ Q :=
  (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).inl ≫
    rightOuterHornCornerTop m h

def rightOuterHornBoundaryLeg
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    simplicialJoin (SSet.boundary (m + 1) : SSet.{u}) Δ[1] ⟶ Q :=
  (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).inr ≫
    rightOuterHornCornerTop m h

def rightOuterHornBaseDiagram
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    (Δ[m + 1] : SSet.{u}) ⟶ Q :=
  joinMapBase (Δ[m + 1] : SSet.{u})
    (Λ[1, (1 : Fin 2)] : SSet.{u}) Q (rightOuterHornFullLeg m h)

theorem rightOuterHornBoundaryLeg_base
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    joinMapBase (SSet.boundary (m + 1) : SSet.{u}) (Δ[1] : SSet.{u}) Q
        (rightOuterHornBoundaryLeg m h) =
      (SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h := by
  have hw := congrArg (fun k ↦ k ≫ rightOuterHornCornerTop m h)
    (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).isPushout.w
  calc
    _ = joinMapBase (SSet.boundary (m + 1) : SSet.{u})
        (Λ[1, (1 : Fin 2)] : SSet.{u}) Q
          (simplicialJoinMap (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
            (SSet.horn 1 (1 : Fin 2)).ι ≫ rightOuterHornBoundaryLeg m h) :=
      (joinMapBase_precomp_right (SSet.horn 1 (1 : Fin 2)).ι
        (rightOuterHornBoundaryLeg m h)).symm
    _ = joinMapBase (SSet.boundary (m + 1) : SSet.{u})
        (Λ[1, (1 : Fin 2)] : SSet.{u}) Q
          (simplicialJoinMap (SSet.boundary (m + 1)).ι
            (𝟙 (Λ[1, (1 : Fin 2)] : SSet.{u})) ≫
              rightOuterHornFullLeg m h) := congrArg
        (joinMapBase (SSet.boundary (m + 1) : SSet.{u})
          (Λ[1, (1 : Fin 2)] : SSet.{u}) Q) hw.symm
    _ = _ := joinMapBase_precomp_left (SSet.boundary (m + 1)).ι
      (rightOuterHornFullLeg m h)

def diagramUnderBaseChangeEq
    {Q K : SSet.{u}} {a a' : K ⟶ Q} (e : a = a') :
    diagramUnderSlice Q K a ⟶ diagramUnderSlice Q K a' :=
  eqToHom (congrArg (diagramUnderSlice Q K) e)

theorem diagramUnderBaseChangeEq_fixedBaseCone
    {Q K L : SSet.{u}} {a a' : K ⟶ Q} (e : a = a')
    (f : L ⟶ diagramUnderSlice Q K a) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
          (emptyAugmentation.{u}.map a')) (f ≫ diagramUnderBaseChangeEq e)).1 =
      forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
          (emptyAugmentation.{u}.map a)) f).1 := by
  subst a'
  simp [diagramUnderBaseChangeEq]

noncomputable def rightOuterHornTargetVertex
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    (Λ[1, (1 : Fin 2)] : SSet.{u}) ⟶
      diagramUnderSlice Q (Δ[m + 1] : SSet.{u}) (rightOuterHornBaseDiagram m h) :=
  joinMapDiagramUnderCurry (Δ[m + 1] : SSet.{u})
    (Λ[1, (1 : Fin 2)] : SSet.{u}) Q (rightOuterHornFullLeg m h)

noncomputable def rightOuterHornBoundaryEdge
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    (Δ[1] : SSet.{u}) ⟶
      diagramUnderSlice Q (SSet.boundary (m + 1) : SSet.{u})
        ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h) :=
  joinMapDiagramUnderCurry (SSet.boundary (m + 1) : SSet.{u})
      (Δ[1] : SSet.{u}) Q (rightOuterHornBoundaryLeg m h) ≫
    diagramUnderBaseChangeEq (rightOuterHornBoundaryLeg_base m h)

theorem rightOuterHornTargetVertex_fixedBaseCone
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
          (emptyAugmentation.{u}.obj Q)
          (Λ[1, (1 : Fin 2)] : SSet.{u})
          (emptyAugmentation.{u}.map (rightOuterHornBaseDiagram m h)))
            (rightOuterHornTargetVertex m h)).1 =
      rightOuterHornFullLeg m h :=
  joinMapDiagramUnderCurry_fixedBaseCone (Δ[m + 1] : SSet.{u})
    (Λ[1, (1 : Fin 2)] : SSet.{u}) Q (rightOuterHornFullLeg m h)

theorem rightOuterHornBoundaryEdge_fixedBaseCone
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))
          (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
          (emptyAugmentation.{u}.map
            ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h)))
              (rightOuterHornBoundaryEdge m h)).1 =
      rightOuterHornBoundaryLeg m h := by
  exact (diagramUnderBaseChangeEq_fixedBaseCone
      (rightOuterHornBoundaryLeg_base m h)
      (joinMapDiagramUnderCurry (SSet.boundary (m + 1) : SSet.{u})
        (Δ[1] : SSet.{u}) Q (rightOuterHornBoundaryLeg m h))).trans
    (joinMapDiagramUnderCurry_fixedBaseCone
      (SSet.boundary (m + 1) : SSet.{u}) (Δ[1] : SSet.{u}) Q
        (rightOuterHornBoundaryLeg m h))

lemma directFixedBaseCone_precomp_right
    {Q K L L' : SSet.{u}} (a : K ⟶ Q) (j : L' ⟶ L)
    (f : L ⟶ diagramUnderSlice Q K a) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L'
          (emptyAugmentation.{u}.map a)) (j ≫ f)).1 =
      simplicialJoinMap (𝟙 K) j ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv
            (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
            (emptyAugmentation.{u}.map a)) f).1 := by
  let F := emptyAugmentation.{u}.obj K
  let G := emptyAugmentation.{u}.obj Q
  let aMap := emptyAugmentation.{u}.map a
  have h := congrArg forgetAugmentation.{u}.map
    (relativeDaySliceOverMapFixedBaseEquiv_precomp_fst F G aMap j f)
  calc
    _ = forgetAugmentation.{u}.map
        ((augmentedDayTensorLeft F).map (emptyAugmentation.{u}.map j) ≫
          ((relativeDaySliceOverMapFixedBaseEquiv F G L aMap) f).1) := h
    _ = forgetAugmentation.{u}.map
          ((augmentedDayTensorLeft F).map (emptyAugmentation.{u}.map j)) ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv F G L aMap) f).1 :=
      (forgetAugmentation.{u}).map_comp _ _
    _ = _ := congrArg (fun k ↦ k ≫ forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv F G L aMap) f).1)
      (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map K j).symm

lemma directFixedBaseCone_restriction_left
    {Q K K' L : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q)
    (f : L ⟶ diagramUnderSlice Q K a) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj Q) L
          (emptyAugmentation.{u}.map (j ≫ a)))
            (f ≫ diagramUnderRestriction j a)).1 =
      simplicialJoinMap j (𝟙 L) ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv
            (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
            (emptyAugmentation.{u}.map a)) f).1 := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj L)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj L)
  have h := congrArg forgetAugmentation.{u}.map
    (relativeDaySliceOverMapFixedBaseEquiv_diagramUnderRestriction j a f)
  simp only [Functor.map_comp] at h
  have hT : forgetAugmentation.{u}.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.{u}.map j)
        (𝟙 (emptyAugmentation.{u}.obj L))) = simplicialJoinMap j (𝟙 L) := by
    unfold simplicialJoinMap
    rw [emptyAugmentation.map_id]
    rfl
  rw [hT] at h
  exact h

theorem rightOuterHornSliceSquare
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    CommSq (rightOuterHornTargetVertex m h) (SSet.horn 1 (1 : Fin 2)).ι
      (diagramUnderRestriction (SSet.boundary (m + 1)).ι
        (rightOuterHornBaseDiagram m h))
      (rightOuterHornBoundaryEdge m h) := by
  refine ⟨?_⟩
  apply (relativeDaySliceOverMapFixedBaseEquiv
    (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))
    (emptyAugmentation.{u}.obj Q) (Λ[1, (1 : Fin 2)] : SSet.{u})
    (emptyAugmentation.{u}.map
      ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h))).injective
  apply Subtype.ext
  apply augmentedMapToEmptyAugmentation_ext
  have hw := congrArg (fun k ↦ k ≫ rightOuterHornCornerTop m h)
    (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).isPushout.w
  have hright : simplicialJoinMap
        (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
        (SSet.horn 1 (1 : Fin 2)).ι ≫ rightOuterHornBoundaryLeg m h =
      forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))
          (emptyAugmentation.{u}.obj Q) (Λ[1, (1 : Fin 2)] : SSet.{u})
          (emptyAugmentation.{u}.map
            ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h)))
              ((SSet.horn 1 (1 : Fin 2)).ι ≫ rightOuterHornBoundaryEdge m h)).1 :=
    (congrArg (fun k ↦ simplicialJoinMap
        (𝟙 (SSet.boundary (m + 1) : SSet.{u}))
        (SSet.horn 1 (1 : Fin 2)).ι ≫ k)
      (rightOuterHornBoundaryEdge_fixedBaseCone m h).symm).trans
        (directFixedBaseCone_precomp_right
          ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h)
          (SSet.horn 1 (1 : Fin 2)).ι (rightOuterHornBoundaryEdge m h)).symm
  rw [directFixedBaseCone_restriction_left
    (SSet.boundary (m + 1)).ι (rightOuterHornBaseDiagram m h)
      (rightOuterHornTargetVertex m h)]
  rw [rightOuterHornTargetVertex_fixedBaseCone]
  exact hw.trans hright

/-- A left fibration solves a one-dimensional last-horn square when the prescribed base
edge is an equivalence. -/
lemma LeftFibration.hasLift_equivalenceTarget
    {X Y : SSet.{u}} (p : X ⟶ Y) [LeftFibration p] [SSet.Quasicategory Y]
    {f : (Λ[1, (1 : Fin 2)] : SSet.{u}) ⟶ X} {b : (Δ[1] : SSet.{u}) ⟶ Y}
    (sq : CommSq f (SSet.horn 1 (1 : Fin 2)).ι p b)
    (he : EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv b))) :
    sq.HasLift := by
  let x : X.obj (Opposite.op (SimplexCategory.mk 0)) :=
    SSet.yonedaEquiv (hornOneOneIsoPoint.{u}.inv ≫ f)
  let e₀ := SSet.Edge.mk' (SSet.yonedaEquiv b)
  have hinv : hornOneOneIsoPoint.{u}.inv ≫
      (SSet.horn 1 (1 : Fin 2)).ι = SSet.stdSimplex.δ (0 : Fin 2) := by
    apply (cancel_epi hornOneOneIsoPoint.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact hornOneOneIsoPoint_hom_comp_coface.symm
  have htgt : Y.δ 0 e₀.edge = p.app (Opposite.op (SimplexCategory.mk 0)) x := by
    have hmap : SSet.stdSimplex.δ (0 : Fin 2) ≫ b =
        (hornOneOneIsoPoint.{u}.inv ≫ f) ≫ p := by
      calc
        _ = (hornOneOneIsoPoint.{u}.inv ≫
              (SSet.horn 1 (1 : Fin 2)).ι) ≫ b :=
          congrArg (fun k ↦ k ≫ b) hinv.symm
        _ = hornOneOneIsoPoint.{u}.inv ≫
              ((SSet.horn 1 (1 : Fin 2)).ι ≫ b) :=
          Category.assoc _ _ _
        _ = hornOneOneIsoPoint.{u}.inv ≫ (f ≫ p) :=
          congrArg (fun k ↦ hornOneOneIsoPoint.{u}.inv ≫ k) sq.w.symm
        _ = _ := (Category.assoc _ _ _).symm
    have hy := congrArg SSet.yonedaEquiv hmap
    have hδ : SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2) ≫ b) =
        Y.δ 0 (SSet.yonedaEquiv b) := by
      change b.app _ ((Δ[1] : SSet.{u}).δ 0
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))) =
        Y.δ 0 (b.app _ (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))))
      exact SSet.δ_naturality_apply b 0
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    calc
      Y.δ 0 e₀.edge = SSet.yonedaEquiv
          (SSet.stdSimplex.δ (0 : Fin 2) ≫ b) := hδ.symm
      _ = SSet.yonedaEquiv ((hornOneOneIsoPoint.{u}.inv ≫ f) ≫ p) := hy
      _ = p.app (Opposite.op (SimplexCategory.mk 0)) x := by
        simp only [x, SSet.yonedaEquiv_comp]
  let e : SSet.Edge (Y.δ 1 e₀.edge)
      (p.app (Opposite.op (SimplexCategory.mk 0)) x) :=
    SSet.Edge.castEndpoints rfl htgt.symm e₀
  have he' : EdgeIsEquivalence e := he.castEndpoints rfl htgt.symm
  obtain ⟨lift⟩ := LeftFibration.nonempty_equivalenceTargetLift p x e he'
  let l : (Δ[1] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm lift.simplex
  apply CommSq.HasLift.mk'
  refine { l := l, fac_left := ?_, fac_right := ?_ }
  · apply (cancel_epi hornOneOneIsoPoint.inv).mp
    rw [← Category.assoc, hinv]
    apply SSet.yonedaEquiv.injective
    simp only [l, SSet.yonedaEquiv_comp]
    change X.δ 0 lift.simplex = SSet.yonedaEquiv
      (hornOneOneIsoPoint.{u}.inv ≫ f)
    rw [lift.target]
  · apply SSet.yonedaEquiv.injective
    simp only [l, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    change p.app _ lift.simplex = e₀.edge
    exact lift.map.trans (SSet.Edge.castEndpoints_edge _ _ _)

/-- Restricting the right join variable of a fixed-base cone is precomposition of the
corresponding diagram-slice simplex. -/
lemma diagramUnderFixedBaseCone_precomp_right
    {Q K L L' : SSet.{u}} (a : K ⟶ Q) (j : L' ⟶ L)
    (f : L ⟶ diagramUnderSlice Q K a) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L'
          (emptyAugmentation.{u}.map a)) (j ≫ f)).1 =
      simplicialJoinMap (𝟙 K) j ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv
            (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
            (emptyAugmentation.{u}.map a)) f).1 := by
  let F := emptyAugmentation.{u}.obj K
  let G := emptyAugmentation.{u}.obj Q
  let aMap := emptyAugmentation.{u}.map a
  have h := congrArg forgetAugmentation.{u}.map
    (relativeDaySliceOverMapFixedBaseEquiv_precomp_fst F G aMap j f)
  calc
    _ = forgetAugmentation.{u}.map
        ((augmentedDayTensorLeft F).map (emptyAugmentation.{u}.map j) ≫
          ((relativeDaySliceOverMapFixedBaseEquiv F G L aMap) f).1) := h
    _ = forgetAugmentation.{u}.map
          ((augmentedDayTensorLeft F).map (emptyAugmentation.{u}.map j)) ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv F G L aMap) f).1 :=
      (forgetAugmentation.{u}).map_comp _ _
    _ = _ := congrArg (fun k ↦ k ≫ forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv F G L aMap) f).1)
      (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map K j).symm

/-- Restriction of the fixed diagram is precomposition in the left join variable of its
fixed-base cone. -/
lemma diagramUnderFixedBaseCone_restriction_left
    {Q K K' L : SSet.{u}} (j : K' ⟶ K) (a : K ⟶ Q)
    (f : L ⟶ diagramUnderSlice Q K a) :
    forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj Q) L
          (emptyAugmentation.{u}.map (j ≫ a)))
            (f ≫ diagramUnderRestriction j a)).1 =
      simplicialJoinMap j (𝟙 L) ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv
            (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj Q) L
            (emptyAugmentation.{u}.map a)) f).1 := by
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K) (emptyAugmentation.{u}.obj L)
  letI := augmentedDayConvolution
    (emptyAugmentation.{u}.obj K') (emptyAugmentation.{u}.obj L)
  have h := congrArg forgetAugmentation.{u}.map
    (relativeDaySliceOverMapFixedBaseEquiv_diagramUnderRestriction j a f)
  simp only [Functor.map_comp] at h
  have hT : forgetAugmentation.{u}.map
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.{u}.map j)
        (𝟙 (emptyAugmentation.{u}.obj L))) = simplicialJoinMap j (𝟙 L) := by
    unfold simplicialJoinMap
    rw [emptyAugmentation.map_id]
    rfl
  rw [hT] at h
  exact h

/-- The curried data extracted from a special right outer horn. The two leg equations say
that the fixed-base cones recover the original map on the join pushout. -/
structure RightOuterHornSliceEncoding
    (Q : SSet.{u}) (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))] where
  horn : (SSet.horn (m + 3) (Fin.last (m + 3)) : SSet.{u}) ⟶ Q
  baseDiagram : (Δ[m + 1] : SSet.{u}) ⟶ Q
  targetVertex : (Λ[1, (1 : Fin 2)] : SSet.{u}) ⟶
    diagramUnderSlice Q (Δ[m + 1] : SSet.{u}) baseDiagram
  boundaryEdge : (Δ[1] : SSet.{u}) ⟶
    diagramUnderSlice Q (SSet.boundary (m + 1) : SSet.{u})
      ((SSet.boundary (m + 1)).ι ≫ baseDiagram)
  square : CommSq targetVertex (SSet.horn 1 (1 : Fin 2)).ι
    (diagramUnderRestriction (SSet.boundary (m + 1)).ι baseDiagram)
    boundaryEdge
  top_inl : (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).inl ≫
      (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom ≫ horn =
    forgetAugmentation.{u}.map
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
        (emptyAugmentation.{u}.obj Q)
        (Λ[1, (1 : Fin 2)] : SSet.{u})
        (emptyAugmentation.{u}.map baseDiagram)) targetVertex).1
  top_inr : (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).inr ≫
      (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom ≫ horn =
    forgetAugmentation.{u}.map
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))
        (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
        (emptyAugmentation.{u}.map
          ((SSet.boundary (m + 1)).ι ≫ baseDiagram))) boundaryEdge).1
  projectedEdgeIsEquivalence : EdgeIsEquivalence
    (SSet.Edge.mk' (SSet.yonedaEquiv
      (boundaryEdge ≫ diagramUnderProjection Q
        (SSet.boundary (m + 1) : SSet.{u})
        ((SSet.boundary (m + 1)).ι ≫ baseDiagram))))

/-- The two left fibrations in Land's argument lift the curried equivalence edge while
fixing its target. -/
theorem RightOuterHornSliceEncoding.hasLift
    {Q : SSet.{u}} [SSet.Quasicategory Q] {m : ℕ}
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (E : RightOuterHornSliceEncoding Q m)
    (hboundary : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i)) :
    E.square.HasLift := by
  let projection := diagramUnderProjection Q
    (SSet.boundary (m + 1) : SSet.{u})
    ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram)
  letI : LeftFibration projection :=
    diagramUnderProjection_leftFibration_of_innerAnodyne_corners
      Q (SSet.boundary (m + 1) : SSet.{u})
      ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram) hprojection
  letI : SSet.Quasicategory
      (diagramUnderSlice Q (SSet.boundary (m + 1) : SSet.{u})
        ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram)) :=
    quasicategory_of_leftFibration projection
  let restriction := diagramUnderRestriction
    (SSet.boundary (m + 1)).ι E.baseDiagram
  letI : LeftFibration restriction :=
    diagramUnderRestriction_boundary_leftFibration_of_normalized_corners
      Q m E.baseDiagram hboundary
  let e := SSet.Edge.mk' (SSet.yonedaEquiv E.boundaryEdge)
  let eProjection := SSet.Edge.mk' (SSet.yonedaEquiv
    (E.boundaryEdge ≫ projection))
  have hsrc : projection.app _
        ((diagramUnderSlice Q (SSet.boundary (m + 1) : SSet.{u})
          ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram)).δ 1 e.edge) =
      Q.δ 1 eProjection.edge := by
    change projection.app _
        ((diagramUnderSlice Q (SSet.boundary (m + 1) : SSet.{u})
          ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram)).δ 1
            (SSet.yonedaEquiv E.boundaryEdge)) =
      Q.δ 1 (projection.app _ (SSet.yonedaEquiv E.boundaryEdge))
    exact SSet.δ_naturality_apply projection 1 (SSet.yonedaEquiv E.boundaryEdge)
  have htgt : projection.app _
        ((diagramUnderSlice Q (SSet.boundary (m + 1) : SSet.{u})
          ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram)).δ 0 e.edge) =
      Q.δ 0 eProjection.edge := by
    change projection.app _
        ((diagramUnderSlice Q (SSet.boundary (m + 1) : SSet.{u})
          ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram)).δ 0
            (SSet.yonedaEquiv E.boundaryEdge)) =
      Q.δ 0 (projection.app _ (SSet.yonedaEquiv E.boundaryEdge))
    exact SSet.δ_naturality_apply projection 0 (SSet.yonedaEquiv E.boundaryEdge)
  have hecast : SSet.Edge.castEndpoints hsrc htgt eProjection = e.map projection := by
    apply SSet.Edge.ext
    simp only [SSet.Edge.castEndpoints_edge, SSet.Edge.map_edge, eProjection, e,
      SSet.Edge.mk'_edge, SSet.yonedaEquiv_comp]
  have heProjection : EdgeIsEquivalence (e.map projection) := by
    rw [← hecast]
    exact E.projectedEdgeIsEquivalence.castEndpoints hsrc htgt
  have he : EdgeIsEquivalence e :=
    LeftFibration.edgeIsEquivalence_of_map projection e heProjection
  exact LeftFibration.hasLift_equivalenceTarget restriction E.square he

/-- The join cone corresponding to the lifted edge in the full diagram slice. -/
noncomputable def RightOuterHornSliceEncoding.extensionCone
    {Q : SSet.{u}} [SSet.Quasicategory Q] {m : ℕ}
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (E : RightOuterHornSliceEncoding Q m)
    (hboundary : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i)) :
    simplicialJoin (Δ[m + 1] : SSet.{u}) Δ[1] ⟶ Q := by
  letI : E.square.HasLift := E.hasLift hboundary hprojection
  exact forgetAugmentation.{u}.map
    ((relativeDaySliceOverMapFixedBaseEquiv
      (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
      (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
      (emptyAugmentation.{u}.map E.baseDiagram)) E.square.lift).1

theorem RightOuterHornSliceEncoding.extensionCone_restrict_horn
    {Q : SSet.{u}} [SSet.Quasicategory Q] {m : ℕ}
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (E : RightOuterHornSliceEncoding Q m)
    (hboundary : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i)) :
    simplicialJoinMap (𝟙 (Δ[m + 1] : SSet.{u}))
        (SSet.horn 1 (1 : Fin 2)).ι ≫
      E.extensionCone hboundary hprojection =
    forgetAugmentation.{u}.map
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
        (emptyAugmentation.{u}.obj Q)
        (Λ[1, (1 : Fin 2)] : SSet.{u})
        (emptyAugmentation.{u}.map E.baseDiagram)) E.targetVertex).1 := by
  letI : E.square.HasLift := E.hasLift hboundary hprojection
  change simplicialJoinMap (𝟙 (Δ[m + 1] : SSet.{u}))
      (SSet.horn 1 (1 : Fin 2)).ι ≫
    forgetAugmentation.{u}.map
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
        (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
        (emptyAugmentation.{u}.map E.baseDiagram)) E.square.lift).1 = _
  exact (diagramUnderFixedBaseCone_precomp_right E.baseDiagram
    (SSet.horn 1 (1 : Fin 2)).ι E.square.lift).symm.trans
      (congrArg (fun k ↦ forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
          (emptyAugmentation.{u}.obj Q)
          (Λ[1, (1 : Fin 2)] : SSet.{u})
          (emptyAugmentation.{u}.map E.baseDiagram)) k).1)
        E.square.fac_left)

theorem RightOuterHornSliceEncoding.extensionCone_restrict_boundary
    {Q : SSet.{u}} [SSet.Quasicategory Q] {m : ℕ}
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (E : RightOuterHornSliceEncoding Q m)
    (hboundary : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i)) :
    simplicialJoinMap (SSet.boundary (m + 1)).ι (𝟙 (Δ[1] : SSet.{u})) ≫
      E.extensionCone hboundary hprojection =
    forgetAugmentation.{u}.map
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))
        (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
        (emptyAugmentation.{u}.map
          ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram))) E.boundaryEdge).1 := by
  letI : E.square.HasLift := E.hasLift hboundary hprojection
  change simplicialJoinMap (SSet.boundary (m + 1)).ι
      (𝟙 (Δ[1] : SSet.{u})) ≫
    forgetAugmentation.{u}.map
      ((relativeDaySliceOverMapFixedBaseEquiv
        (emptyAugmentation.{u}.obj (Δ[m + 1] : SSet.{u}))
        (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
        (emptyAugmentation.{u}.map E.baseDiagram)) E.square.lift).1 = _
  exact (diagramUnderFixedBaseCone_restriction_left
    (SSet.boundary (m + 1)).ι E.baseDiagram E.square.lift).symm.trans
      (congrArg (fun k ↦ forgetAugmentation.{u}.map
        ((relativeDaySliceOverMapFixedBaseEquiv
          (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))
          (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
          (emptyAugmentation.{u}.map
            ((SSet.boundary (m + 1)).ι ≫ E.baseDiagram))) k).1)
        E.square.fac_right)

theorem RightOuterHornSliceEncoding.corner_comp_extensionCone
    {Q : SSet.{u}} [SSet.Quasicategory Q] {m : ℕ}
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (E : RightOuterHornSliceEncoding Q m)
    (hboundary : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i)) :
    joinBoundaryHornCornerMap (m + 1) 1 (1 : Fin 2) ≫
        E.extensionCone hboundary hprojection =
      (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom ≫ E.horn := by
  apply (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).isPushout.hom_ext
  · rw [joinBoundaryHornCornerMap_inl_assoc]
    exact (E.extensionCone_restrict_horn hboundary hprojection).trans
      E.top_inl.symm
  · rw [joinBoundaryHornCornerMap_inr_assoc]
    exact (E.extensionCone_restrict_boundary hboundary hprojection).trans
      E.top_inr.symm

/-- Transport the lifted join cone back to the normalized ambient simplex. -/
noncomputable def RightOuterHornSliceEncoding.filler
    {Q : SSet.{u}} [SSet.Quasicategory Q] {m : ℕ}
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (E : RightOuterHornSliceEncoding Q m)
    (hboundary : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i)) :
    (Δ[m + 3] : SSet.{u}) ⟶ Q :=
  (leftJoinTargetIso.{u} m 1).hom ≫
    (simplicialJoinStdSimplexIsoNat (m + 1) 1).inv ≫
      E.extensionCone hboundary hprojection

theorem RightOuterHornSliceEncoding.filler_restrict
    {Q : SSet.{u}} [SSet.Quasicategory Q] {m : ℕ}
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (E : RightOuterHornSliceEncoding Q m)
    (hboundary : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i)) :
    (SSet.horn (m + 3) (Fin.last (m + 3))).ι ≫
      E.filler hboundary hprojection = E.horn := by
  apply (cancel_epi
    (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom).mp
  rw [← Category.assoc,
    normalizedJoinBoundaryRightOuterHornSourceIso_hom_comp_ι]
  calc
    normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2) ≫
        E.filler hboundary hprojection =
      joinBoundaryHornCornerMap (m + 1) 1 (1 : Fin 2) ≫
        E.extensionCone hboundary hprojection := by
          simp [RightOuterHornSliceEncoding.filler,
            normalizedJoinBoundaryHornCornerMap,
            joinBoundaryHornStandardCornerMap, Category.assoc]
    _ = _ := E.corner_comp_extensionCone hboundary hprojection

/-- The edge joining the final two vertices of `Δ[n+2]`. -/
def stdSimplexEdgeLastTwo (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[n + 2] :=
  SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.symm
    (SimplexCategory.mkHom
      { toFun := fun i ↦ ⟨n + 1 + i.val, by omega⟩
        monotone' := by
          intro i j h
          simp only [Fin.le_def] at h ⊢
          omega }))

/-- The trailing edge corestricted to the special right outer horn. -/
def specialRightHornTrailingEdge (n : ℕ) :
    (Δ[1] : SSet.{u}) ⟶ Λ[n + 2, Fin.last (n + 2)] :=
  SSet.Subcomplex.lift (stdSimplexEdgeLastTwo n) (by
    rw [SSet.Subcomplex.range_eq_ofSimplex, SSet.Subcomplex.ofSimplex_le_iff]
    apply (SSet.mem_horn_iff_notMem_range _ (Fin.last (n + 2))).2
    refine ⟨(0 : Fin (n + 3)), by simp, ?_⟩
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    change n + 1 + i.val = 0 at hv
    omega)

/-- The trailing edge of a right outer horn map. -/
def specialRightHornEdge {Q : SSet.{u}} {n : ℕ}
    (a : (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ Q) :
    Q.obj (Opposite.op (SimplexCategory.mk 1)) :=
  SSet.yonedaEquiv (specialRightHornTrailingEdge n ≫ a)

lemma normalizedRightJoinInclusion_eq_stdSimplexEdgeLastTwo (m : ℕ) :
    simplicialJoinRightInclusion (Δ[m + 1] : SSet.{u}) (Δ[1] : SSet.{u}) ≫
        (simplicialJoinStdSimplexIsoNat (m + 1) 1).hom ≫
          (leftJoinTargetIso m 1).inv =
      stdSimplexEdgeLastTwo (m + 1) := by
  rw [← Category.assoc, simplicialJoinRightInclusion_stdSimplex]
  apply SSet.yonedaEquiv.injective
  simp [stdSimplexEdgeLastTwo, leftJoinTargetIso, standardJoinRightOperator,
    SSet.yonedaEquiv_map]

lemma rightOuterHornCornerSource_trailingEdge
    (m : ℕ) [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))] :
    simplicialJoinRightInclusion (SSet.boundary (m + 1) : SSet.{u})
        (Δ[1] : SSet.{u}) ≫
      (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).inr ≫
        (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom =
      specialRightHornTrailingEdge (m + 1) := by
  apply (cancel_mono (SSet.horn (m + 3) (Fin.last (m + 3))).ι).mp
  rw [Category.assoc, Category.assoc,
    normalizedJoinBoundaryRightOuterHornSourceIso_hom_comp_ι]
  rw [specialRightHornTrailingEdge, SSet.Subcomplex.lift_ι]
  have hinr := joinBoundaryHornStandardCornerMap_inr_assoc
    (m + 1) 1 (1 : Fin 2) (leftJoinTargetIso.{u} m 1).inv
  have h₁ := congrArg (fun k ↦ simplicialJoinRightInclusion
    (SSet.boundary (m + 1) : SSet.{u}) (Δ[1] : SSet.{u}) ≫ k) hinr
  have hnat := simplicialJoinRightInclusion_naturality_left
    (Y := (Δ[1] : SSet.{u}))
    (SSet.boundary (m + 1)).ι
  have h₂ := congrArg (fun k ↦ k ≫
      (simplicialJoinStdSimplexIsoNat (m + 1) 1).hom ≫
        (leftJoinTargetIso.{u} m 1).inv) hnat
  have hfinal := h₁.trans
    (h₂.trans (normalizedRightJoinInclusion_eq_stdSimplexEdgeLastTwo m))
  have hnormalized : normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2) =
      joinBoundaryHornStandardCornerMap (m + 1) 1 (1 : Fin 2) ≫
        (leftJoinTargetIso.{u} m 1).inv := rfl
  rw [hnormalized]
  exact hfinal

theorem rightOuterHornBoundaryEdge_projection
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q) :
    rightOuterHornBoundaryEdge m h ≫
        diagramUnderProjection Q (SSet.boundary (m + 1) : SSet.{u})
          ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h) =
      specialRightHornTrailingEdge (m + 1) ≫ h := by
  calc
    _ = simplicialJoinRightInclusion (SSet.boundary (m + 1) : SSet.{u})
        (Δ[1] : SSet.{u}) ≫
          forgetAugmentation.{u}.map
            ((relativeDaySliceOverMapFixedBaseEquiv
              (emptyAugmentation.{u}.obj (SSet.boundary (m + 1) : SSet.{u}))
              (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
              (emptyAugmentation.{u}.map
                ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h)))
                  (rightOuterHornBoundaryEdge m h)).1 :=
      diagramUnderProjection_comp_eq_fixedBaseCone Q
        (SSet.boundary (m + 1) : SSet.{u}) (Δ[1] : SSet.{u})
        ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h)
        (rightOuterHornBoundaryEdge m h)
    _ = simplicialJoinRightInclusion (SSet.boundary (m + 1) : SSet.{u})
        (Δ[1] : SSet.{u}) ≫ rightOuterHornBoundaryLeg m h := congrArg
      (fun k ↦ simplicialJoinRightInclusion
        (SSet.boundary (m + 1) : SSet.{u}) (Δ[1] : SSet.{u}) ≫ k)
      (rightOuterHornBoundaryEdge_fixedBaseCone m h)
    _ = (simplicialJoinRightInclusion (SSet.boundary (m + 1) : SSet.{u})
          (Δ[1] : SSet.{u}) ≫
        (joinBoundaryHornCornerSq (m + 1) 1 (1 : Fin 2)).inr ≫
          (normalizedJoinBoundaryRightOuterHornSourceIso.{u} m).hom) ≫ h := by
      rfl
    _ = _ := congrArg (fun k ↦ k ≫ h) (rightOuterHornCornerSource_trailingEdge m)

theorem rightOuterHornBoundaryEdge_projected_isEquivalence
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence
      (SSet.Edge.mk' (specialRightHornEdge (n := m + 1) h))) :
    EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
      (rightOuterHornBoundaryEdge m h ≫
        diagramUnderProjection Q (SSet.boundary (m + 1) : SSet.{u})
          ((SSet.boundary (m + 1)).ι ≫ rightOuterHornBaseDiagram m h)))) := by
  rw [rightOuterHornBoundaryEdge_projection]
  exact he

noncomputable def rightOuterHornSliceEncoding
    {Q : SSet.{u}} (m : ℕ)
    [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence
      (SSet.Edge.mk' (specialRightHornEdge (n := m + 1) h))) :
    RightOuterHornSliceEncoding Q m where
  horn := h
  baseDiagram := rightOuterHornBaseDiagram m h
  targetVertex := rightOuterHornTargetVertex m h
  boundaryEdge := rightOuterHornBoundaryEdge m h
  square := rightOuterHornSliceSquare m h
  top_inl := (rightOuterHornTargetVertex_fixedBaseCone m h).symm
  top_inr := (rightOuterHornBoundaryEdge_fixedBaseCone m h).symm
  projectedEdgeIsEquivalence :=
    rightOuterHornBoundaryEdge_projected_isEquivalence m h he

/-- Exact remaining horn-encoding input for the direct proof in dimensions at least three. -/
def HasRightOuterHornSliceEncodings (Q : SSet.{u}) : Prop :=
  ∀ (m : ℕ) [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q),
    EdgeIsEquivalence (SSet.Edge.mk' (specialRightHornEdge (n := m + 1) h)) →
      Nonempty { E : RightOuterHornSliceEncoding Q m // E.horn = h }

theorem hasRightOuterHornSliceEncodings (Q : SSet.{u}) :
    HasRightOuterHornSliceEncodings Q := by
  intro m _ h he
  exact ⟨⟨rightOuterHornSliceEncoding m h he, rfl⟩⟩

/-- Once horn encoding and the two join-corner families are available, the direct slice
argument fills every special right outer horn of dimension at least three. -/
theorem specialRightOuterHorn_filling_succ
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (hencode : HasRightOuterHornSliceEncodings Q)
    (hboundary : ∀ (m s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (normalizedJoinBoundaryHornCornerMap.{u} m s i))
    (hprojection : ∀ (m s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i))
    (m : ℕ) [Mono (normalizedJoinBoundaryHornCornerMap.{u} m 0 (1 : Fin 2))]
    (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence
      (SSet.Edge.mk' (specialRightHornEdge (n := m + 1) h))) :
    ∃ σ : (Δ[m + 3] : SSet.{u}) ⟶ Q,
      (SSet.horn (m + 3) (Fin.last (m + 3))).ι ≫ σ = h := by
  obtain ⟨⟨E, rfl⟩⟩ := hencode m h he
  exact ⟨E.filler (hboundary m) (hprojection m),
    E.filler_restrict (hboundary m) (hprojection m)⟩

theorem specialRightOuterHorn_filling_succ_of_projection_corners
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (hprojection : ∀ (m s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) → SSet.innerAnodyneExtensions
        (diagramUnderProjectionHornCornerMap
          (SSet.boundary (m + 1) : SSet.{u}) (s + 1) i))
    (m : ℕ) (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence
      (SSet.Edge.mk' (specialRightHornEdge (n := m + 1) h))) :
    ∃ σ : (Δ[m + 3] : SSet.{u}) ⟶ Q,
      (SSet.horn (m + 3) (Fin.last (m + 3))).ι ≫ σ = h := by
  exact specialRightOuterHorn_filling_succ
    (hasRightOuterHornSliceEncodings Q)
    (fun m s i hi ↦ normalizedJoinBoundaryHornCornerMap_innerAnodyne m s i hi)
    hprojection m h he

/-- The direct slice argument fills every special right outer horn of dimension at least
three. -/
theorem specialRightOuterHorn_filling_succ_direct
    {Q : SSet.{u}} [SSet.Quasicategory Q]
    (m : ℕ) (h : (Λ[m + 3, Fin.last (m + 3)] : SSet.{u}) ⟶ Q)
    (he : EdgeIsEquivalence
      (SSet.Edge.mk' (specialRightHornEdge (n := m + 1) h))) :
    ∃ σ : (Δ[m + 3] : SSet.{u}) ⟶ Q,
      (SSet.horn (m + 3) (Fin.last (m + 3))).ι ≫ σ = h := by
  exact specialRightOuterHorn_filling_succ_of_projection_corners
    (fun m s i hi ↦
      boundaryDiagramUnderProjectionHornCornerMap_innerAnodyne m s i hi)
    m h he

end LeanLCAExactChallenge.Infinity
