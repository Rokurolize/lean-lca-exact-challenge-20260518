import LeanLCAExactChallenge.Infinity.JoyalSlices

/-! # Joyal's special left outer horn theorem -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

def underSliceVertexMap {Q : SSet.{u}} {x : Q _⦋0⦌}
    (v : (underSlice Q x) _⦋0⦌) :
    (Δ[0] : SSet.{u}) ⟶ underSlice Q x :=
  SSet.yonedaEquiv.symm v

theorem underSliceVertexMap_naturality
    {Q : SSet.{u}} {x : Q _⦋0⦌} {K : SSet.{u}}
    (j : (Δ[0] : SSet.{u}) ⟶ K) (c : K ⟶ underSlice Q x) :
    underSliceVertexMap (c.app (Opposite.op ⦋0⦌) (SSet.yonedaEquiv j)) =
      j ≫ c := by
  apply SSet.yonedaEquiv.injective
  exact Equiv.apply_symm_apply _ _

def underSliceVertexCone {Q : SSet.{u}} {x : Q _⦋0⦌}
    (v : (underSlice Q x) _⦋0⦌) :
    simplicialJoin (Δ[0] : SSet.{u}) Δ[0] ⟶ Q :=
  forgetAugmentation.{u}.map
    ((relativeDaySliceOverMapFixedBaseEquiv
      (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
      (emptyAugmentation.{u}.obj Q) (Δ[0] : SSet.{u})
      (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x)))
        (underSliceVertexMap v)).1

def underSliceVertexEdgeSimplex {Q : SSet.{u}} {x : Q _⦋0⦌}
    (v : (underSlice Q x) _⦋0⦌) : Q _⦋1⦌ :=
  SSet.yonedaEquiv
    ((simplicialJoinStdSimplexIsoNat 0 0).inv ≫ underSliceVertexCone v)

def underSliceVertexEdge {Q : SSet.{u}} {x : Q _⦋0⦌}
    (v : (underSlice Q x) _⦋0⦌) :
    SSet.Edge (Q.δ 1 (underSliceVertexEdgeSimplex v))
      (Q.δ 0 (underSliceVertexEdgeSimplex v)) :=
  SSet.Edge.mk' (underSliceVertexEdgeSimplex v)

@[simp]
theorem underSliceVertexEdge_edge {Q : SSet.{u}} {x : Q _⦋0⦌}
    (v : (underSlice Q x) _⦋0⦌) :
    (underSliceVertexEdge v).edge = underSliceVertexEdgeSimplex v := rfl

/-- The zeroth vertex of a positive-dimensional standard boundary.  It is
displayed through the final face, which always contains vertex zero. -/
def boundaryZeroVertex (k : ℕ) :
    (Δ[0] : SSet.{u}) ⟶ (SSet.boundary (k + 1) : SSet.{u}) :=
  SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (k + 1))) ≫
    SSet.boundary.ι (Fin.last (k + 1))

/-- The first vertex of a boundary diagram in an under-slice. -/
def underSliceBoundaryFirstVertex {Q : SSet.{u}} {x : Q _⦋0⦌}
    (k : ℕ) (c : (SSet.boundary (k + 1) : SSet.{u}) ⟶ underSlice Q x) :
    (underSlice Q x) _⦋0⦌ :=
  SSet.yonedaEquiv (boundaryZeroVertex k ≫ c)

/-- A relative boundary problem whose first cone edge is an equivalence.
The index `k = 0` is the two-vertex boundary used in the special outer
`2`-horn theorem. -/
structure UnderSliceEquivalenceBoundaryProblem
    (Q : SSet.{u}) (x : Q _⦋0⦌) (k : ℕ) where
  boundary : (SSet.boundary (k + 1) : SSet.{u}) ⟶ underSlice Q x
  source : ∀ v : (SSet.boundary (k + 1) : SSet.{u}) _⦋0⦌,
    Q.δ 1 (underSliceVertexEdgeSimplex (boundary.app (Opposite.op ⦋0⦌) v)) = x
  target : ∀ v : (SSet.boundary (k + 1) : SSet.{u}) _⦋0⦌,
    Q.δ 0 (underSliceVertexEdgeSimplex (boundary.app (Opposite.op ⦋0⦌) v)) =
      (underSliceProjection Q x).app (Opposite.op ⦋0⦌)
        (boundary.app (Opposite.op ⦋0⦌) v)
  firstIsEquivalence : EdgeIsEquivalence
    (underSliceVertexEdge (underSliceBoundaryFirstVertex k boundary))

def UnderSliceEquivalenceBoundaryProblem.edgeAt
    {Q : SSet.{u}} {x : Q _⦋0⦌} {k : ℕ}
    (P : UnderSliceEquivalenceBoundaryProblem Q x k)
    (v : (SSet.boundary (k + 1) : SSet.{u}) _⦋0⦌) :
    SSet.Edge x ((underSliceProjection Q x).app (Opposite.op ⦋0⦌)
      (P.boundary.app (Opposite.op ⦋0⦌) v)) :=
  SSet.Edge.castEndpoints (P.source v).symm (P.target v).symm
    (underSliceVertexEdge (P.boundary.app (Opposite.op ⦋0⦌) v))

def boundaryOneVertex :
    (Δ[0] : SSet.{u}) ⟶ (SSet.boundary 1 : SSet.{u}) :=
  SSet.boundary.ι (0 : Fin 2)

theorem boundaryZeroVertex_zero :
    boundaryZeroVertex 0 = (SSet.boundary.ι (1 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ (SSet.boundary 1 : SSet.{u})) := by
  unfold boundaryZeroVertex
  rw [show SSet.yonedaEquiv.symm
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
        𝟙 (Δ[0] : SSet.{u}) from
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _]
  exact Category.id_comp _

def boundaryZeroVertexElement : (SSet.boundary 1 : SSet.{u}) _⦋0⦌ :=
  SSet.yonedaEquiv (boundaryZeroVertex 0)

def boundaryOneVertexElement : (SSet.boundary 1 : SSet.{u}) _⦋0⦌ :=
  SSet.yonedaEquiv boundaryOneVertex

theorem underSliceBoundaryFirstVertex_zero
    {Q : SSet.{u}} {x : Q _⦋0⦌}
    (c : (SSet.boundary 1 : SSet.{u}) ⟶ underSlice Q x) :
    underSliceBoundaryFirstVertex 0 c =
      c.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement := by
  simp [underSliceBoundaryFirstVertex, boundaryZeroVertexElement,
    SSet.yonedaEquiv_comp]

theorem UnderSliceEquivalenceBoundaryProblem.firstFixedIsEquivalence
    {Q : SSet.{u}} {x : Q _⦋0⦌}
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    EdgeIsEquivalence (P.edgeAt boundaryZeroVertexElement) := by
  have he : EdgeIsEquivalence (underSliceVertexEdge
      (P.boundary.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement)) := by
    rw [← underSliceBoundaryFirstVertex_zero P.boundary]
    exact P.firstIsEquivalence
  exact he.castEndpoints (P.source boundaryZeroVertexElement).symm
    (P.target boundaryZeroVertexElement).symm

/-- The genuine inverse-triangle construction supplies the triangle needed
for the base boundary extension. -/
@[implicit_reducible]
noncomputable def UnderSliceEquivalenceBoundaryProblem.baseTriangleData
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    Nonempty (Σ e₁₂ : SSet.Edge
        ((underSliceProjection Q x).app (Opposite.op ⦋0⦌)
          (P.boundary.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement))
        ((underSliceProjection Q x).app (Opposite.op ⦋0⦌)
          (P.boundary.app (Opposite.op ⦋0⦌) boundaryOneVertexElement)),
      SSet.Edge.CompStruct (P.edgeAt boundaryZeroVertexElement) e₁₂
        (P.edgeAt boundaryOneVertexElement)) :=
  Truncated.specialOuterCompStruct₂₀ (P.edgeAt boundaryZeroVertexElement)
    (P.edgeAt boundaryOneVertexElement) P.firstFixedIsEquivalence

noncomputable def UnderSliceEquivalenceBoundaryProblem.baseTriangle
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :=
  Classical.choice P.baseTriangleData

noncomputable def UnderSliceEquivalenceBoundaryProblem.baseCone
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    simplicialJoin (Δ[0] : SSet.{u}) Δ[1] ⟶ Q :=
  (simplicialJoinStdSimplexIsoNat 0 1).hom ≫
    SSet.yonedaEquiv.symm P.baseTriangle.2.simplex

noncomputable def UnderSliceEquivalenceBoundaryProblem.baseConeAugmented
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :=
  augmentedJoinMapOfUnderlying (Δ[0] : SSet.{u}) Δ[1] Q P.baseCone

theorem UnderSliceEquivalenceBoundaryProblem.baseCone_first
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.stdSimplex.δ (1 : Fin 2)) ≫ P.baseCone =
      underSliceVertexCone
        (P.boundary.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement) := by
  rw [UnderSliceEquivalenceBoundaryProblem.baseCone,
    show SSet.stdSimplex.δ (1 : Fin 2) =
      SSet.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)) from rfl]
  rw [← Category.assoc,
    simplicialJoinStdSimplexIsoNat_naturality_rightCoface,
    Category.assoc]
  apply (cancel_epi (simplicialJoinStdSimplexIsoNat 0 0).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply SSet.yonedaEquiv.injective
  change Q.δ 2 P.baseTriangle.2.simplex =
    underSliceVertexEdgeSimplex
      (P.boundary.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement)
  rw [P.baseTriangle.2.d₂]
  simp [UnderSliceEquivalenceBoundaryProblem.edgeAt]

theorem UnderSliceEquivalenceBoundaryProblem.baseCone_second
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.stdSimplex.δ (0 : Fin 2)) ≫ P.baseCone =
      underSliceVertexCone
        (P.boundary.app (Opposite.op ⦋0⦌) boundaryOneVertexElement) := by
  rw [UnderSliceEquivalenceBoundaryProblem.baseCone,
    show SSet.stdSimplex.δ (0 : Fin 2) =
      SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)) from rfl]
  rw [← Category.assoc,
    simplicialJoinStdSimplexIsoNat_naturality_rightCoface,
    Category.assoc]
  apply (cancel_epi (simplicialJoinStdSimplexIsoNat 0 0).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply SSet.yonedaEquiv.injective
  change Q.δ 1 P.baseTriangle.2.simplex =
    underSliceVertexEdgeSimplex
      (P.boundary.app (Opposite.op ⦋0⦌) boundaryOneVertexElement)
  rw [P.baseTriangle.2.d₁]
  simp [UnderSliceEquivalenceBoundaryProblem.edgeAt]

noncomputable def UnderSliceEquivalenceBoundaryProblem.baseFixedCone
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    FixedBaseDayConvolutionMapOver
      (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
      (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
      (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x)) := by
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj Q
  let a := emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x)
  let v₀ := P.boundary.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement
  let φ₀ := (relativeDaySliceOverMapFixedBaseEquiv F G
    (Δ[0] : SSet.{u}) a) (underSliceVertexMap v₀)
  let τ := P.baseConeAugmented
  have hτ : (augmentedDayTensorLeft F).map
      (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2))) ≫ τ = φ₀.1 := by
    apply augmentedMapToEmptyAugmentation_ext
    rw [Functor.map_comp]
    have hforgetτ := forgetAugmentation_augmentedJoinMapOfUnderlying
      (Δ[0] : SSet.{u}) Δ[1] Q P.baseCone
    have hT : forgetAugmentation.map ((augmentedDayTensorLeft F).map
        (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2)))) =
        simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
          (SSet.stdSimplex.δ (1 : Fin 2)) := by
      unfold F simplicialJoinMap augmentedDayTensorLeft
      rw [emptyAugmentation.map_id]
      rfl
    change _ = underSliceVertexCone v₀
    calc
      _ = forgetAugmentation.map ((augmentedDayTensorLeft F).map
            (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2)))) ≫
          P.baseCone := congrArg (fun k ↦
            forgetAugmentation.map ((augmentedDayTensorLeft F).map
              (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2)))) ≫ k)
            hforgetτ
      _ = simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
            (SSet.stdSimplex.δ (1 : Fin 2)) ≫ P.baseCone :=
        congrArg (fun k ↦ k ≫ P.baseCone) hT
      _ = underSliceVertexCone v₀ := P.baseCone_first
  exact fixedBaseDayConvolutionMapOfRestriction F G a
    (SSet.stdSimplex.δ (1 : Fin 2)) φ₀ τ hτ

noncomputable def UnderSliceEquivalenceBoundaryProblem.baseExtension
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    (Δ[1] : SSet.{u}) ⟶ underSlice Q x :=
  (relativeDaySliceOverMapFixedBaseEquiv
    (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
    (emptyAugmentation.{u}.obj Q) (Δ[1] : SSet.{u})
    (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x))).symm
      P.baseFixedCone

theorem UnderSliceEquivalenceBoundaryProblem.baseConeAugmented_first
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
    (augmentedDayTensorLeft F).map
        (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2))) ≫
      P.baseConeAugmented =
        ((relativeDaySliceOverMapFixedBaseEquiv F
          (emptyAugmentation.{u}.obj Q) (Δ[0] : SSet.{u})
          (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x)))
            (underSliceVertexMap (P.boundary.app (Opposite.op ⦋0⦌)
              boundaryZeroVertexElement))).1 := by
  dsimp only
  apply augmentedMapToEmptyAugmentation_ext
  rw [Functor.map_comp]
  have hforget := forgetAugmentation_augmentedJoinMapOfUnderlying
    (Δ[0] : SSet.{u}) Δ[1] Q P.baseCone
  have hT : forgetAugmentation.map ((augmentedDayTensorLeft
      (emptyAugmentation.obj (Δ[0] : SSet.{u}))).map
        (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2)))) =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.stdSimplex.δ (1 : Fin 2)) := by
    unfold simplicialJoinMap augmentedDayTensorLeft
    rw [emptyAugmentation.map_id]
    rfl
  change _ = underSliceVertexCone
    (P.boundary.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement)
  calc
    _ = forgetAugmentation.map ((augmentedDayTensorLeft
          (emptyAugmentation.obj (Δ[0] : SSet.{u}))).map
            (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2)))) ≫
        P.baseCone := congrArg (fun k ↦ _ ≫ k) hforget
    _ = simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
          (SSet.stdSimplex.δ (1 : Fin 2)) ≫ P.baseCone :=
      congrArg (fun k ↦ k ≫ P.baseCone) hT
    _ = _ := P.baseCone_first

theorem UnderSliceEquivalenceBoundaryProblem.baseExtension_first
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    SSet.stdSimplex.δ (1 : Fin 2) ≫ P.baseExtension =
      underSliceVertexMap
        (P.boundary.app (Opposite.op ⦋0⦌) boundaryZeroVertexElement) := by
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj Q
  let a := emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x)
  apply (relativeDaySliceOverMapFixedBaseEquiv F G (Δ[0] : SSet.{u}) a).injective
  apply Subtype.ext
  have hpre := relativeDaySliceOverMapFixedBaseEquiv_precomp_fst
    F G a (SSet.stdSimplex.δ (1 : Fin 2)) P.baseExtension
  have hl : (relativeDaySliceOverMapFixedBaseEquiv F G
      (Δ[1] : SSet.{u}) a) P.baseExtension = P.baseFixedCone := by
    exact Equiv.apply_symm_apply _ P.baseFixedCone
  rw [hpre, hl]
  change (augmentedDayTensorLeft F).map
      (emptyAugmentation.map (SSet.stdSimplex.δ (1 : Fin 2))) ≫
        P.baseConeAugmented = _
  exact P.baseConeAugmented_first

theorem UnderSliceEquivalenceBoundaryProblem.baseConeAugmented_second
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
    (augmentedDayTensorLeft F).map
        (emptyAugmentation.map (SSet.stdSimplex.δ (0 : Fin 2))) ≫
      P.baseConeAugmented =
        ((relativeDaySliceOverMapFixedBaseEquiv F
          (emptyAugmentation.{u}.obj Q) (Δ[0] : SSet.{u})
          (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x)))
            (underSliceVertexMap (P.boundary.app (Opposite.op ⦋0⦌)
              boundaryOneVertexElement))).1 := by
  dsimp only
  apply augmentedMapToEmptyAugmentation_ext
  rw [Functor.map_comp]
  have hforget := forgetAugmentation_augmentedJoinMapOfUnderlying
    (Δ[0] : SSet.{u}) Δ[1] Q P.baseCone
  have hT : forgetAugmentation.map ((augmentedDayTensorLeft
      (emptyAugmentation.obj (Δ[0] : SSet.{u}))).map
        (emptyAugmentation.map (SSet.stdSimplex.δ (0 : Fin 2)))) =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
        (SSet.stdSimplex.δ (0 : Fin 2)) := by
    unfold simplicialJoinMap augmentedDayTensorLeft
    rw [emptyAugmentation.map_id]
    rfl
  change _ = underSliceVertexCone
    (P.boundary.app (Opposite.op ⦋0⦌) boundaryOneVertexElement)
  calc
    _ = forgetAugmentation.map ((augmentedDayTensorLeft
          (emptyAugmentation.obj (Δ[0] : SSet.{u}))).map
            (emptyAugmentation.map (SSet.stdSimplex.δ (0 : Fin 2)))) ≫
        P.baseCone := congrArg (fun k ↦ _ ≫ k) hforget
    _ = simplicialJoinMap (𝟙 (Δ[0] : SSet.{u}))
          (SSet.stdSimplex.δ (0 : Fin 2)) ≫ P.baseCone :=
      congrArg (fun k ↦ k ≫ P.baseCone) hT
    _ = _ := P.baseCone_second

theorem UnderSliceEquivalenceBoundaryProblem.baseExtension_second
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    SSet.stdSimplex.δ (0 : Fin 2) ≫ P.baseExtension =
      underSliceVertexMap
        (P.boundary.app (Opposite.op ⦋0⦌) boundaryOneVertexElement) := by
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj Q
  let a := emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm x)
  apply (relativeDaySliceOverMapFixedBaseEquiv F G (Δ[0] : SSet.{u}) a).injective
  apply Subtype.ext
  have hpre := relativeDaySliceOverMapFixedBaseEquiv_precomp_fst
    F G a (SSet.stdSimplex.δ (0 : Fin 2)) P.baseExtension
  have hl : (relativeDaySliceOverMapFixedBaseEquiv F G
      (Δ[1] : SSet.{u}) a) P.baseExtension = P.baseFixedCone := by
    exact Equiv.apply_symm_apply _ P.baseFixedCone
  rw [hpre, hl]
  change (augmentedDayTensorLeft F).map
      (emptyAugmentation.map (SSet.stdSimplex.δ (0 : Fin 2))) ≫
        P.baseConeAugmented = _
  exact P.baseConeAugmented_second

theorem UnderSliceEquivalenceBoundaryProblem.baseExtension_boundary
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) :
    (SSet.boundary 1).ι ≫ P.baseExtension = P.boundary := by
  apply SSet.boundary.hom_ext
  intro i
  fin_cases i
  · rw [← Category.assoc, SSet.boundary.ι_ι]
    change SSet.stdSimplex.δ (0 : Fin 2) ≫ P.baseExtension =
      SSet.boundary.ι (0 : Fin 2) ≫ P.boundary
    rw [P.baseExtension_second]
    exact underSliceVertexMap_naturality boundaryOneVertex P.boundary
  · rw [← Category.assoc, SSet.boundary.ι_ι]
    change SSet.stdSimplex.δ (1 : Fin 2) ≫ P.baseExtension =
      SSet.boundary.ι (1 : Fin 2) ≫ P.boundary
    rw [P.baseExtension_first]
    change underSliceVertexMap (P.boundary.app (Opposite.op ⦋0⦌)
      (SSet.yonedaEquiv (boundaryZeroVertex 0))) = _
    rw [underSliceVertexMap_naturality (boundaryZeroVertex 0) P.boundary]
    rw [boundaryZeroVertex_zero]

/-- A solution extends the entire boundary, while allowing the missing
opposite face in `Q` to be generated by the slice projection. -/
def UnderSliceEquivalenceBoundaryProblem.HasExtension
    {Q : SSet.{u}} {x : Q _⦋0⦌} {k : ℕ}
    (P : UnderSliceEquivalenceBoundaryProblem Q x k) : Prop :=
  ∃ l : (Δ[k + 1] : SSet.{u}) ⟶ underSlice Q x,
    (SSet.boundary (k + 1)).ι ≫ l = P.boundary

theorem UnderSliceEquivalenceBoundaryProblem.hasExtension_zero
    {Q : SSet.{u}} {x : Q _⦋0⦌} [SSet.Quasicategory Q]
    (P : UnderSliceEquivalenceBoundaryProblem Q x 0) : P.HasExtension :=
  ⟨P.baseExtension, P.baseExtension_boundary⟩

def UnderSliceEquivalenceBoundaryProblem.faceBoundary
    {Q : SSet.{u}} {x : Q _⦋0⦌} {k : ℕ}
    (P : UnderSliceEquivalenceBoundaryProblem Q x (k + 1))
    (i : Fin (k + 3)) :
    (SSet.boundary (k + 1) : SSet.{u}) ⟶ underSlice Q x :=
  (SSet.boundary (k + 1)).ι ≫ SSet.boundary.ι i ≫ P.boundary

structure UnderSliceEquivalenceBoundaryProblem.SuccessorState
    {Q : SSet.{u}} {x : Q _⦋0⦌} {k : ℕ}
    (P : UnderSliceEquivalenceBoundaryProblem Q x (k + 1)) where
  face : ∀ i : Fin (k + 3), 0 < i →
    ((Δ[k + 1] : SSet.{u}) ⟶ underSlice Q x)
  face_boundary : ∀ (i : Fin (k + 3)) (hi : 0 < i),
    (SSet.boundary (k + 1)).ι ≫ face i hi = P.faceBoundary i

end LeanLCAExactChallenge.Infinity
