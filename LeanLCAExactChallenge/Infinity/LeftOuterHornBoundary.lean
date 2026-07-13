import LeanLCAExactChallenge.Infinity.RightConeHorn

/-!
# A left cone on a simplex boundary is a left outer horn

This file isolates the recursive pushout construction identifying
`Δ[0] ⋆ ∂Δ[k]` with `Λ[k+1,0]`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace LeanLCAExactChallenge.Infinity

/-- The boundary of a simplex is obtained by adjoining its last face to the
horn which omits that face. -/
noncomputable def boundaryLastFaceBicartSq (k : ℕ) :
    SSet.Subcomplex.BicartSq
      (SSet.horn k (Fin.last k) ⊓ SSet.stdSimplex.face ({Fin.last k}ᶜ))
      (SSet.horn k (Fin.last k))
      (SSet.stdSimplex.face ({Fin.last k}ᶜ))
      (SSet.boundary k) where
  inf_eq := rfl
  sup_eq := by
    rw [SSet.horn_eq_iSup, SSet.boundary_eq_iSup]
    apply le_antisymm
    · apply sup_le
      · apply iSup_le
        intro j
        exact le_iSup (fun q : Fin (k + 1) => SSet.stdSimplex.face ({q}ᶜ)) j.1
      · exact le_iSup (fun q : Fin (k + 1) =>
          SSet.stdSimplex.face ({q}ᶜ)) (Fin.last k)
    · apply iSup_le
      intro j
      by_cases hj : j = Fin.last k
      · subst j
        exact le_sup_right
      · exact le_sup_of_le_left
          (le_iSup (fun q : ({Fin.last k}ᶜ : Set (Fin (k + 1))) =>
            SSet.stdSimplex.face ({q.1}ᶜ)) ⟨j, by simpa using hj⟩)

/-- The shifted right faces other than the last one, together with the last
shifted face, form the left outer horn. -/
noncomputable def leftOuterHornLastFaceBicartSq (n : ℕ) :
    SSet.Subcomplex.BicartSq
      (representableJoinHornInitial 0 (n + 1) (Fin.last (n + 1)) ⊓
        SSet.stdSimplex.face
          ({(⟨n + 2, by omega⟩ : Fin (0 + (n + 1) + 2))}ᶜ))
      (representableJoinHornInitial 0 (n + 1) (Fin.last (n + 1)))
      (SSet.stdSimplex.face
        ({(⟨n + 2, by omega⟩ : Fin (0 + (n + 1) + 2))}ᶜ))
      (SSet.horn (0 + (n + 1) + 1)
        (0 : Fin (0 + (n + 1) + 1 + 1))) where
  inf_eq := rfl
  sup_eq := by
    rw [representableJoinHornInitial_eq_iSup_shiftedRightFaces,
      SSet.horn_eq_iSup]
    apply le_antisymm
    · apply sup_le
      · apply iSup_le
        rintro ⟨j, hj⟩
        exact le_iSup
          (fun q : ({(0 : Fin (0 + (n + 1) + 1 + 1))}ᶜ :
              Set (Fin (0 + (n + 1) + 1 + 1))) =>
            SSet.stdSimplex.face ({q.1}ᶜ))
          ⟨⟨0 + 1 + j.val, by omega⟩, by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro h
            have hv := congrArg Fin.val h
            simp at hv⟩
      · exact le_iSup
          (fun q : ({(0 : Fin (0 + (n + 1) + 1 + 1))}ᶜ :
              Set (Fin (0 + (n + 1) + 1 + 1))) =>
            SSet.stdSimplex.face ({q.1}ᶜ))
          ⟨⟨n + 2, by omega⟩, by simp⟩
    · apply iSup_le
      rintro ⟨j, hj⟩
      have hj0 : j ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hj
      by_cases hlast : j = (⟨n + 2, by omega⟩ :
          Fin (0 + (n + 1) + 1 + 1))
      · subst j
        exact le_sup_right
      · let q : Fin (n + 2) := ⟨j.val - 1, by
          have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
          omega⟩
        have hq : q ≠ Fin.last (n + 1) := by
          intro h
          apply hlast
          apply Fin.ext
          have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
          have hv := congrArg Fin.val h
          dsimp [q] at hv
          simp only [] at hv ⊢
          omega
        have hshift : (⟨0 + 1 + q.val, by omega⟩ :
            Fin (0 + (n + 1) + 1 + 1)) = j := by
          apply Fin.ext
          have hjpos : 0 < j.val := Fin.pos_iff_ne_zero.mpr hj0
          dsimp [q]
          omega
        apply le_sup_of_le_left
        convert le_iSup
          (fun t : ({Fin.last (n + 1)}ᶜ : Set (Fin (n + 2))) =>
            SSet.stdSimplex.face
              ({(⟨0 + 1 + t.1.val, by omega⟩ :
                Fin (0 + (n + 1) + 1 + 1))}ᶜ))
          ⟨q, by simpa using hq⟩ using 1
        rw [hshift]

/-- The boundary of the last face, regarded as a subobject of the ambient
simplex one dimension higher. -/
def lastFaceBoundaryAmbientMap (n : ℕ) :
    (SSet.boundary n : SSet.{u}) ⟶ Δ[n + 1] :=
  (SSet.boundary n).ι ≫ SSet.stdSimplex.δ (Fin.last (n + 1))

noncomputable instance lastFaceBoundaryAmbientMap_mono (n : ℕ) :
    Mono (lastFaceBoundaryAmbientMap.{u} n) := by
  unfold lastFaceBoundaryAmbientMap
  infer_instance

lemma lastFaceBoundaryAmbientMap_range_succ (n : ℕ) :
    SSet.Subcomplex.range (lastFaceBoundaryAmbientMap.{u} (n + 1)) =
      SSet.horn (n + 2) (Fin.last (n + 2)) ⊓
        SSet.stdSimplex.face ({Fin.last (n + 2)}ᶜ) := by
  rw [lastFaceBoundaryAmbientMap, SSet.Subcomplex.range_comp,
    show SSet.Subcomplex.range (SSet.boundary (n + 1)).ι =
      SSet.boundary (n + 1) from Subfunctor.range_ι (SSet.boundary (n + 1)),
    SSet.boundary_eq_iSup,
    SSet.Subcomplex.image_iSup, SSet.horn_eq_iSup,
    subcomplex_iSup_inf_eq]
  have hcomponent (j : Fin (n + 2)) :
      (SSet.stdSimplex.face ({j}ᶜ)).image
          (SSet.stdSimplex.δ (Fin.last (n + 2))) =
        SSet.stdSimplex.face ({j.castSucc}ᶜ) ⊓
          SSet.stdSimplex.face ({Fin.last (n + 2)}ᶜ) := by
    let J : Fin (n + 3) := j.castSucc
    let L : Fin (n + 3) := Fin.last (n + 2)
    have hJL : J < L := by simp [J, L]
    have hpair :
        SSet.Subcomplex.range
            (SSet.stdSimplex.δ (n := n) j ≫
              SSet.stdSimplex.δ (n := n + 1) L) =
          SSet.stdSimplex.face ({J, L}ᶜ) := by
      symm
      have hface := SSet.stdSimplex.facePairComplIso_hom_ι J L hJL
      have hJ : J.castPred (Fin.ne_last_of_lt hJL) = j := by
        apply Fin.ext
        rfl
      simpa only [Subfunctor.range_ι] using
        (subcomplex_range_eq_of_precomp_iso
        (SSet.stdSimplex.facePairComplIso.{u} J L hJL).hom
        ((SSet.stdSimplex.face ({J, L}ᶜ) :
          (Δ[n + 2] : SSet.{u}).Subcomplex).ι)
        (SSet.stdSimplex.δ (n := n) j ≫
          SSet.stdSimplex.δ (n := n + 1) L)
        (by simpa only [hJ] using hface))
    rw [← stdSimplex_range_map_delta (n := n) j,
      ← SSet.Subcomplex.range_comp]
    change SSet.Subcomplex.range
        (SSet.stdSimplex.δ j ≫ SSet.stdSimplex.δ L) = _
    rw [hpair,
      SSet.stdSimplex.face_inter_face]
    congr 2
    ext x
    simp [J, L]
  apply le_antisymm
  · apply iSup_le
    intro j
    rw [hcomponent j]
    exact le_iSup
      (fun q : ({Fin.last (n + 2)}ᶜ : Set (Fin (n + 3))) =>
        SSet.stdSimplex.face ({q.1}ᶜ) ⊓
          SSet.stdSimplex.face ({Fin.last (n + 2)}ᶜ))
      ⟨j.castSucc, by simp⟩
  · apply iSup_le
    rintro ⟨q, hq⟩
    let j : Fin (n + 2) := q.castPred (by simpa using hq)
    have hle := le_iSup (fun t : Fin (n + 2) =>
      (SSet.stdSimplex.face ({t}ᶜ)).image
        (SSet.stdSimplex.δ (Fin.last (n + 2)))) j
    rw [hcomponent j] at hle
    convert hle using 1
    · congr 3

/-- The boundary of the last face is canonically the intersection appearing
in the boundary pushout square. -/
noncomputable def boundaryLastFaceIntersectionIsoSucc (n : ℕ) :
    (SSet.boundary (n + 1) : SSet.{u}) ≅
      ((SSet.horn (n + 2) (Fin.last (n + 2)) ⊓
        SSet.stdSimplex.face ({Fin.last (n + 2)}ᶜ) :
          (Δ[n + 2] : SSet.{u}).Subcomplex) : SSet.{u}) :=
  simplicialSetIsoRangeOfMono (lastFaceBoundaryAmbientMap (n + 1)) ≪≫
    SSet.Subcomplex.toSSetFunctor.mapIso
      (eqToIso (lastFaceBoundaryAmbientMap_range_succ n))

lemma strictSingletonAugmentation_map_isPushout
    {A B C D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPushout f g h k) :
    IsPushout (strictSingletonAugmentation.{u}.map f)
      (strictSingletonAugmentation.{u}.map g)
      (strictSingletonAugmentation.{u}.map h)
      (strictSingletonAugmentation.{u}.map k) := by
  apply IsPushout.of_forall_isPushout_app
  rintro ⟨U⟩
  rcases U with U | _
  · apply (sq.app (Opposite.op U)).of_iso'
      ((strictSingletonAugmentationEvalOfIso.{u} U).app A)
      ((strictSingletonAugmentationEvalOfIso.{u} U).app B)
      ((strictSingletonAugmentationEvalOfIso.{u} U).app C)
      ((strictSingletonAugmentationEvalOfIso.{u} U).app D)
    all_goals rfl
  · let hp : IsPushout (𝟙 PUnit.{u + 1}) (𝟙 PUnit.{u + 1})
        (𝟙 PUnit.{u + 1}) (𝟙 PUnit.{u + 1}) :=
      IsPushout.of_id_fst
    apply hp.of_iso'
      (strictSingletonAugmentationEvalStarIso.app A)
      (strictSingletonAugmentationEvalStarIso.app B)
      (strictSingletonAugmentationEvalStarIso.app C)
      (strictSingletonAugmentationEvalStarIso.app D)
    all_goals apply Limits.Types.isTerminalPUnit.hom_ext

lemma emptyAugmentation_map_isPushout
    {A B C D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {h : B ⟶ D} {k : C ⟶ D} (sq : IsPushout f g h k) :
    IsPushout (emptyAugmentation.{u}.map f) (emptyAugmentation.{u}.map g)
      (emptyAugmentation.{u}.map h) (emptyAugmentation.{u}.map k) := by
  apply (strictSingletonAugmentation_map_isPushout sq).of_iso
    (strictSingletonAugmentationIso.app A)
    (strictSingletonAugmentationIso.app B)
    (strictSingletonAugmentationIso.app C)
    (strictSingletonAugmentationIso.app D)
  all_goals simp

lemma simplicialJoinLeft_map_isPushout
    (X : SSet.{u}) {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {h : B ⟶ D} {k : C ⟶ D}
    (sq : IsPushout f g h k) :
    IsPushout (simplicialJoinMap (𝟙 X) f)
      (simplicialJoinMap (𝟙 X) g)
      (simplicialJoinMap (𝟙 X) h)
      (simplicialJoinMap (𝟙 X) k) := by
  let F := augmentedDayTensorLeft (emptyAugmentation.{u}.obj X)
  have hs := (emptyAugmentation_map_isPushout sq).map F
  have hf : IsPushout
      (forgetAugmentation.{u}.map (F.map (emptyAugmentation.{u}.map f)))
      (forgetAugmentation.{u}.map (F.map (emptyAugmentation.{u}.map g)))
      (forgetAugmentation.{u}.map (F.map (emptyAugmentation.{u}.map h)))
      (forgetAugmentation.{u}.map (F.map (emptyAugmentation.{u}.map k))) := by
    apply IsPushout.of_forall_isPushout_app
    intro U
    change IsPushout
      ((F.map (emptyAugmentation.{u}.map f)).app
        (AugmentedSimplexCategory.inclusion.op.obj U))
      ((F.map (emptyAugmentation.{u}.map g)).app
        (AugmentedSimplexCategory.inclusion.op.obj U))
      ((F.map (emptyAugmentation.{u}.map h)).app
        (AugmentedSimplexCategory.inclusion.op.obj U))
      ((F.map (emptyAugmentation.{u}.map k)).app
        (AugmentedSimplexCategory.inclusion.op.obj U))
    exact hs.app (AugmentedSimplexCategory.inclusion.op.obj U)
  have hA : simplicialJoin X A =
      forgetAugmentation.{u}.obj (F.obj (emptyAugmentation.{u}.obj A)) := rfl
  have hB : simplicialJoin X B =
      forgetAugmentation.{u}.obj (F.obj (emptyAugmentation.{u}.obj B)) := rfl
  have hC : simplicialJoin X C =
      forgetAugmentation.{u}.obj (F.obj (emptyAugmentation.{u}.obj C)) := rfl
  have hD : simplicialJoin X D =
      forgetAugmentation.{u}.obj (F.obj (emptyAugmentation.{u}.obj D)) := rfl
  let eA := eqToIso hA
  let eB := eqToIso hB
  let eC := eqToIso hC
  let eD := eqToIso hD
  apply hf.of_iso' eA eB eC eD
  · cases hA; cases hB
    simp only [eA, eB]
    exact (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map X f).symm
  · cases hA; cases hC
    simp only [eA, eC]
    exact (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map X g).symm
  · cases hB; cases hD
    simp only [eB, eD]
    exact (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map X h).symm
  · cases hC; cases hD
    simp only [eC, eD]
    exact (simplicialJoinMap_id_eq_augmentedDayTensorLeft_map X k).symm

/-- Embed the left outer horn in the last face of the next simplex.  Its
range is the upper-left corner of `leftOuterHornLastFaceBicartSq`. -/
def lastFaceOuterHornAmbientMap (n : ℕ) :
    (SSet.horn (n + 1) (0 : Fin (n + 2)) : SSet.{u}) ⟶ Δ[n + 2] :=
  (SSet.horn (n + 1) (0 : Fin (n + 2))).ι ≫
    SSet.stdSimplex.δ (Fin.last (n + 2))

noncomputable instance lastFaceOuterHornAmbientMap_mono (n : ℕ) :
    Mono (lastFaceOuterHornAmbientMap.{u} n) := by
  unfold lastFaceOuterHornAmbientMap
  infer_instance

end LeanLCAExactChallenge.Infinity
