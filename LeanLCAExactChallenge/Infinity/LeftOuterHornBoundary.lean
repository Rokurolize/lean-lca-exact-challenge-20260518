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
          simp only [Fin.val_last] at hv ⊢
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

end LeanLCAExactChallenge.Infinity
